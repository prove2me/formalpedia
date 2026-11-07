-- Prove2me | solution 1 for TwoAgentSched.sortC_spec
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-07T02:12:40.374733+00:00
-- url     : https://prove2.me/submissions/f720efb1-d5e7-43a6-91a9-5b209da6048c

import Mathlib
import Definitions.Def_TwoAgentSched_Timed
import Definitions.Def_TwoAgentSched_sortC

open TwoAgentSched

namespace TwoAgentSched.SortCProof

/-! ## Auxiliary simplification lemmas for the `Timed` cost monad -/

@[simp] theorem timed_pure_cost {α : Type} (a : α) : (pure a : Timed α).cost = 0 := rfl
@[simp] theorem timed_bind_cost {α β : Type} (x : Timed α) (f : α → Timed β) :
    (x >>= f).cost = x.cost + (f x.val).cost := rfl
@[simp] theorem timed_pure_val {α : Type} (a : α) : (pure a : Timed α).val = a := rfl
@[simp] theorem timed_bind_val {α β : Type} (x : Timed α) (f : α → Timed β) :
    (x >>= f).val = (f x.val).val := rfl
@[simp] theorem tick_cost : tick.cost = 1 := rfl
@[simp] theorem ticks_cost (k : ℕ) : (ticks k).cost = k := rfl
@[simp] theorem leC_cost {κ : Type} [LinearOrder κ] (a b : κ) : (leC a b).cost = 1 := rfl
@[simp] theorem leC_val {κ : Type} [LinearOrder κ] (a b : κ) :
    (leC a b).val = decide (a ≤ b) := rfl

variable {β κ : Type} [LinearOrder κ]

/-! ## Correctness of `mergeC` -/

theorem mergeC_perm (key : β → κ) (as bs : List β) :
    (mergeC key as bs).val.Perm (as ++ bs) := by
  induction as, bs using mergeC.induct with
  | case1 ys =>
      simp [mergeC]
  | case2 x xs =>
      simp [mergeC]
  | case3 x xs y ys ih1 ih2 =>
      by_cases h : key x ≤ key y
      · simp only [mergeC.eq_3, leC_val, decide_eq_true_eq, h, if_true, timed_bind_val,
          timed_pure_val]
        exact (ih1.cons x).trans (by simp)
      · simp only [mergeC.eq_3, leC_val, decide_eq_false_iff_not, h, if_false, timed_bind_val,
          timed_pure_val]
        have h1 : (y :: (mergeC key (x :: xs) ys).val).Perm (y :: ((x :: xs) ++ ys)) :=
          ih2.cons y
        have h2 : (y :: ((x :: xs) ++ ys)).Perm ((x :: xs) ++ (y :: ys)) := by
          simp only [List.cons_append]
          exact (List.Perm.swap x y (xs ++ ys)).trans (List.perm_middle.cons x).symm
        exact h1.trans h2

theorem mergeC_pairwise (key : β → κ) (as bs : List β)
    (ha : as.Pairwise (fun a b => key a ≤ key b))
    (hb : bs.Pairwise (fun a b => key a ≤ key b)) :
    (mergeC key as bs).val.Pairwise (fun a b => key a ≤ key b) := by
  revert ha hb
  induction as, bs using mergeC.induct with
  | case1 ys =>
      intro ha hb
      simpa [mergeC] using hb
  | case2 x xs =>
      intro ha hb
      simpa [mergeC] using ha
  | case3 x xs y ys ih1 ih2 =>
      intro ha hb
      have ha' := ha
      have hb' := hb
      rcases ha with _ | ⟨hx, hxs⟩
      rcases hb with _ | ⟨hy, hys⟩
      by_cases h : key x ≤ key y
      · simp only [mergeC.eq_3, leC_val, decide_eq_true_eq, h, if_true, timed_bind_val,
          timed_pure_val]
        apply List.Pairwise.cons
        · intro a ha_mem
          have hmem : a ∈ xs ++ (y :: ys) :=
            ((mergeC_perm key xs (y :: ys)).mem_iff).mp ha_mem
          rw [List.mem_append] at hmem
          rcases hmem with hmem | hmem
          · exact hx a hmem
          · rw [List.mem_cons] at hmem
            rcases hmem with rfl | hmem
            · exact h
            · exact le_trans h (hy a hmem)
        · exact ih1 hxs hb'
      · simp only [mergeC.eq_3, leC_val, h, if_false, timed_bind_val, timed_pure_val]
        apply List.Pairwise.cons
        · intro a ha_mem
          have hmem : a ∈ (x :: xs) ++ ys :=
            ((mergeC_perm key (x :: xs) ys).mem_iff).mp ha_mem
          rw [List.mem_append] at hmem
          rcases hmem with hmem | hmem
          · rw [List.mem_cons] at hmem
            rcases hmem with rfl | hmem
            · exact le_of_not_ge h
            · exact le_trans (le_of_not_ge h) (hx a hmem)
          · exact hy a hmem
        · exact ih2 ha' hys

theorem mergeC_cost_pos (key : β → κ) (x : β) (xs : List β) (y : β) (ys : List β)
    (h : key x ≤ key y) :
    (mergeC key (x :: xs) (y :: ys)).cost = 1 + (mergeC key xs (y :: ys)).cost + 1 := by
  rw [mergeC.eq_3]
  simp [leC, h]
  omega

theorem mergeC_cost_neg (key : β → κ) (x : β) (xs : List β) (y : β) (ys : List β)
    (h : ¬ key x ≤ key y) :
    (mergeC key (x :: xs) (y :: ys)).cost = 1 + (mergeC key (x :: xs) ys).cost + 1 := by
  rw [mergeC.eq_3]
  simp [leC, h]
  omega

theorem mergeC_cost_le (key : β → κ) (as bs : List β) :
    ((mergeC key as bs).cost : ℝ) ≤ 2 * ((as.length : ℝ) + (bs.length : ℝ)) + 1 := by
  induction as, bs using mergeC.induct with
  | case1 ys =>
      simp [mergeC]
  | case2 x xs =>
      simp [mergeC]
      positivity
  | case3 x xs y ys ih1 ih2 =>
      by_cases h : key x ≤ key y
      · rw [mergeC_cost_pos key x xs y ys h]
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at ih1 ⊢
        linarith
      · rw [mergeC_cost_neg key x xs y ys h]
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at ih2 ⊢
        linarith

/-! ## Correctness of `sortC` -/

theorem sortC_perm (key : β → κ) (l : List β) : (sortC key l).val.Perm l := by
  induction l using sortC.induct with
  | case1 => simp [sortC]
  | case2 x => simp [sortC]
  | case3 x y zs ih1 ih2 =>
      simp only [sortC.eq_3, timed_bind_val]
      exact (mergeC_perm key (sortC key (List.take ((zs.length + 2) / 2) (x :: y :: zs))).val
        (sortC key (List.drop ((zs.length + 2) / 2) (x :: y :: zs))).val).trans
        ((ih1.append ih2).trans (by rw [List.take_append_drop]))

theorem sortC_pairwise (key : β → κ) (l : List β) :
    (sortC key l).val.Pairwise (fun a b => key a ≤ key b) := by
  induction l using sortC.induct with
  | case1 => simp [sortC]
  | case2 x => simp [sortC]
  | case3 x y zs ih1 ih2 =>
      simp only [sortC.eq_3, timed_bind_val]
      exact mergeC_pairwise key _ _ ih1 ih2

/-! ## The `O(n log n)` cost bound -/

lemma log_four_thirds : (1/4 : ℝ) ≤ Real.log (4/3) := by
  have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 3/4 by norm_num)
  have h' : Real.log (3/4) = - Real.log (4/3) := by
    rw [show (3/4 : ℝ) = (4/3)⁻¹ by norm_num, Real.log_inv]
  linarith

lemma log_two_mul_div_self_add_one (x : ℝ) (hx : 2 ≤ x) :
    (1/5 : ℝ) ≤ Real.log (2*x/(x+1)) := by
  have hxpos : (0:ℝ) < x := by linarith
  have hx1 : (0:ℝ) < x+1 := by linarith
  have hratio : (4/3 : ℝ) ≤ 2*x/(x+1) := by
    rw [le_div_iff₀ hx1]
    nlinarith
  have hlog : Real.log (4/3) ≤ Real.log (2*x/(x+1)) :=
    Real.log_le_log (by norm_num) hratio
  linarith [log_four_thirds]

lemma key_ineq (x : ℝ) (hx : 2 ≤ x) :
    3*x + 1 + 20*x*Real.log ((x+1)/2) ≤ 20*x*Real.log x := by
  have hxpos : (0:ℝ) < x := by linarith
  have h1 : (0:ℝ) < (x+1)/2 := by positivity
  have h2 : (0:ℝ) < 2*x/(x+1) := by positivity
  have hmul : ((x+1)/2) * (2*x/(x+1)) = x := by
    field_simp
  have hlog_eq : Real.log ((x+1)/2) = Real.log x - Real.log (2*x/(x+1)) := by
    have h := Real.log_mul h1.ne' h2.ne'
    rw [hmul] at h
    linarith
  have hloglb := log_two_mul_div_self_add_one x hx
  have hxnonneg : (0:ℝ) ≤ 20*x := by positivity
  have hmul2 : 4*x ≤ 20*x*Real.log (2*x/(x+1)) := by
    have h := mul_le_mul_of_nonneg_left hloglb hxnonneg
    nlinarith
  rw [hlog_eq]
  nlinarith

lemma two_mul_log_le (a b n : ℕ) (hn : 2 ≤ n) (hab : a + b = n)
    (ha : a ≤ (n+1)/2) (hb : b ≤ (n+1)/2) :
    (a:ℝ) * Real.log (a:ℝ) + (b:ℝ) * Real.log (b:ℝ) ≤
      (n:ℝ) * Real.log (((n:ℝ)+1)/2) := by
  have ha1 : 1 ≤ a := by omega
  have hb1 : 1 ≤ b := by omega
  have hapos : (0:ℝ) < (a:ℝ) := by exact_mod_cast (by omega : 0 < a)
  have hbpos : (0:ℝ) < (b:ℝ) := by exact_mod_cast (by omega : 0 < b)
  have haR : (a:ℝ) ≤ ((n:ℝ)+1)/2 := by
    have h1 : (a:ℝ) ≤ ((n+1)/2 : ℕ) := by exact_mod_cast ha
    have h2 : (((n+1)/2 : ℕ) : ℝ) ≤ ((n:ℝ)+1)/2 := by
      have := Nat.cast_div_le (α := ℝ) (m := n+1) (n := 2)
      push_cast at this
      exact this
    linarith
  have hbR : (b:ℝ) ≤ ((n:ℝ)+1)/2 := by
    have h1 : (b:ℝ) ≤ ((n+1)/2 : ℕ) := by exact_mod_cast hb
    have h2 : (((n+1)/2 : ℕ) : ℝ) ≤ ((n:ℝ)+1)/2 := by
      have := Nat.cast_div_le (α := ℝ) (m := n+1) (n := 2)
      push_cast at this
      exact this
    linarith
  have hlog_a : Real.log (a:ℝ) ≤ Real.log (((n:ℝ)+1)/2) :=
    Real.log_le_log hapos haR
  have hlog_b : Real.log (b:ℝ) ≤ Real.log (((n:ℝ)+1)/2) :=
    Real.log_le_log hbpos hbR
  have hsumR : (a:ℝ) + (b:ℝ) = (n:ℝ) := by exact_mod_cast hab
  calc
    (a:ℝ) * Real.log (a:ℝ) + (b:ℝ) * Real.log (b:ℝ)
        ≤ (a:ℝ) * Real.log (((n:ℝ)+1)/2) + (b:ℝ) * Real.log (((n:ℝ)+1)/2) := by
          have h1 := mul_le_mul_of_nonneg_left hlog_a (by positivity : (0:ℝ) ≤ (a:ℝ))
          have h2 := mul_le_mul_of_nonneg_left hlog_b (by positivity : (0:ℝ) ≤ (b:ℝ))
          linarith
    _ = ((a:ℝ) + (b:ℝ)) * Real.log (((n:ℝ)+1)/2) := by ring
    _ = (n:ℝ) * Real.log (((n:ℝ)+1)/2) := by rw [hsumR]

lemma sortC_step_ineq (n a b : ℕ) (hn : 2 ≤ n) (hab : a + b = n)
    (ha : a ≤ (n+1)/2) (hb : b ≤ (n+1)/2)
    (ca cb cm : ℝ)
    (hca : ca ≤ 20 * (a:ℝ) * Real.log (a:ℝ))
    (hcb : cb ≤ 20 * (b:ℝ) * Real.log (b:ℝ))
    (hcm : cm ≤ 2 * ((a:ℝ) + (b:ℝ)) + 1) :
    (n:ℝ) + ca + cb + cm ≤ 20 * (n:ℝ) * Real.log (n:ℝ) := by
  have hlog := two_mul_log_le a b n hn hab ha hb
  have hkey := key_ineq (n:ℝ) (by exact_mod_cast hn)
  have hsum : (n:ℝ) = (a:ℝ) + (b:ℝ) := by exact_mod_cast hab.symm
  have hcm' : cm ≤ 2*(n:ℝ) + 1 := by rw [hsum]; linarith
  have hlog2 : 20*(a:ℝ)*Real.log (a:ℝ) + 20*(b:ℝ)*Real.log (b:ℝ) ≤
      20*(n:ℝ)*Real.log (((n:ℝ)+1)/2) := by
    nlinarith [hlog]
  linarith

theorem sortC_cost_le (key : β → κ) (l : List β) :
    ((sortC key l).cost : ℝ) ≤ 20 * (l.length : ℝ) * Real.log (l.length : ℝ) := by
  induction l using sortC.induct with
  | case1 => simp [sortC]
  | case2 x => simp [sortC]
  | case3 x y zs ih1 ih2 =>
      rw [sortC.eq_3]
      simp only [timed_bind_cost, timed_pure_cost, ticks_cost]
      push_cast
      have hn : 2 ≤ zs.length + 2 := by omega
      have htd : List.take ((zs.length + 2) / 2) (x :: y :: zs) ++
          List.drop ((zs.length + 2) / 2) (x :: y :: zs) = x :: y :: zs :=
        List.take_append_drop _ _
      have hab : (List.take ((zs.length+2)/2) (x::y::zs)).length +
          (List.drop ((zs.length+2)/2) (x::y::zs)).length = zs.length + 2 := by
        have hlen := congrArg List.length htd
        simp only [List.length_append, List.length_cons] at hlen
        omega
      have ha : (List.take ((zs.length+2)/2) (x::y::zs)).length ≤ (zs.length+2+1)/2 := by
        rw [List.length_take]
        simp only [List.length_cons]
        omega
      have hb : (List.drop ((zs.length+2)/2) (x::y::zs)).length ≤ (zs.length+2+1)/2 := by
        rw [List.length_drop]
        simp only [List.length_cons]
        omega
      have hcm : ((mergeC key
            (sortC key (List.take ((zs.length + 2) / 2) (x :: y :: zs))).val
            (sortC key (List.drop ((zs.length + 2) / 2) (x :: y :: zs))).val).cost : ℝ) ≤
          2 * (((List.take ((zs.length+2)/2) (x::y::zs)).length : ℝ) +
               ((List.drop ((zs.length+2)/2) (x::y::zs)).length : ℝ)) + 1 := by
        have h := mergeC_cost_le key
          (sortC key (List.take ((zs.length + 2) / 2) (x :: y :: zs))).val
          (sortC key (List.drop ((zs.length + 2) / 2) (x :: y :: zs))).val
        have ha_eq : ((sortC key (List.take ((zs.length + 2) / 2) (x :: y :: zs))).val.length : ℝ) =
            ((List.take ((zs.length + 2) / 2) (x :: y :: zs)).length : ℝ) := by
          rw [(sortC_perm key _).length_eq]
        have hb_eq : ((sortC key (List.drop ((zs.length + 2) / 2) (x :: y :: zs))).val.length : ℝ) =
            ((List.drop ((zs.length + 2) / 2) (x :: y :: zs)).length : ℝ) := by
          rw [(sortC_perm key _).length_eq]
        rw [ha_eq, hb_eq] at h
        exact h
      have hlen : ((x :: y :: zs).length : ℝ) = ((zs.length + 2 : ℕ) : ℝ) := by
        simp [List.length_cons]
        ring
      rw [hlen]
      simp only [Nat.cast_add, Nat.cast_one]
      have hstep := sortC_step_ineq (zs.length + 2)
        (List.take ((zs.length+2)/2) (x::y::zs)).length
        (List.drop ((zs.length+2)/2) (x::y::zs)).length
        hn hab ha hb _ _ _ ih1 ih2 hcm
      simp only [Nat.cast_add, Nat.cast_one] at hstep
      linarith

end TwoAgentSched.SortCProof

/-- Merge sort by `key` is a permutation of its input, is sorted by `key`, and runs in
`O(n log n)` unit-cost steps. -/
theorem solution :
    ∃ C : ℝ, ∀ (β κ : Type) [LinearOrder κ] (key : β → κ) (xs : List β),
      (sortC key xs).val.Perm xs ∧
      (sortC key xs).val.Pairwise (fun a b => key a ≤ key b) ∧
      ((sortC key xs).cost : ℝ) ≤ C * (xs.length : ℝ) * Real.log (xs.length : ℝ) := by
  refine ⟨20, ?_⟩
  intro β κ _ key xs
  exact ⟨TwoAgentSched.SortCProof.sortC_perm key xs,
    TwoAgentSched.SortCProof.sortC_pairwise key xs,
    TwoAgentSched.SortCProof.sortC_cost_le key xs⟩
