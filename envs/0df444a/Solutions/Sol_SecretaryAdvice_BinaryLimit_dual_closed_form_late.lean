-- Prove2me | solution 1 for SecretaryAdvice.BinaryLimit.dual_closed_form_late
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-16T08:30:37.826828+00:00
-- url     : https://prove2.me/submissions/20f728c6-67ed-42a0-9599-a6790d399f02

import Mathlib
import Definitions.Def_SecretaryAdvice_BinaryLimit_Dual
set_option autoImplicit false
open SecretaryAdvice.BinaryLimit
namespace SecretaryResearch

theorem stable (n : ℕ) (p pp : ℝ) (a b i : ℕ) (s : Bool) (hab : a ≤ b)
    (hi : n-a < i) : greedyStages n p pp b i s = greedyStages n p pp a i s := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
    simp only [greedyStages,if_neg (show i ≠ n-b by omega)]
    exact ih

theorem recurrence (n : ℕ) (p pp : ℝ) (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) (s : Bool) :
    w n p pp i s = max 0 ((if s then p else 1-p) -
      (if s then 1-pp else pp)/(i : ℝ) *
        ∑ j ∈ Finset.Ioc i n, (w n p pp j true + w n p pp j false)) := by
  have hbase : n-(n-i)=i := by omega
  rw [w, stable n p pp (n-i+1) n i s (by omega) (by omega)]
  simp only [greedyStages,hbase,↓reduceIte]
  congr 2
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_Ioc.mp hj
  congr 1 <;> symm <;> exact stable n p pp (n-i) n j _ (by omega) (by omega)

theorem nonneg (n : ℕ) (p pp : ℝ) (k i : ℕ) (s : Bool) :
    0 ≤ greedyStages n p pp k i s := by
  induction k with
  | zero => simp [greedyStages]
  | succ k ih =>
    simp only [greedyStages]
    split
    · exact le_max_left _ _
    · exact ih

theorem coord_mono (n : ℕ) (p pp : ℝ) (hpp0 : 0 ≤ pp) (hpp1 : pp ≤ 1)
    (i j : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) (hjn : j ≤ n) (s : Bool) :
    w n p pp i s ≤ w n p pp j s := by
  rw [recurrence n p pp i hi (hij.trans hjn) s,recurrence n p pp j (hi.trans hij) hjn s]
  apply max_le_max_left
  have ha : 0 ≤ (if s then 1-pp else pp) := by split <;> linarith
  have hFi : 0 ≤ ∑ k ∈ Finset.Ioc i n, (w n p pp k true + w n p pp k false) :=
    Finset.sum_nonneg (fun k _ => add_nonneg (nonneg ..) (nonneg ..))
  have hFj : 0 ≤ ∑ k ∈ Finset.Ioc j n, (w n p pp k true + w n p pp k false) :=
    Finset.sum_nonneg (fun k _ => add_nonneg (nonneg ..) (nonneg ..))
  have hF : (∑ k ∈ Finset.Ioc j n, (w n p pp k true + w n p pp k false)) ≤
      ∑ k ∈ Finset.Ioc i n, (w n p pp k true + w n p pp k false) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk
      simp only [Finset.mem_Ioc] at *
      omega
    · intro k _ _
      exact add_nonneg (nonneg ..) (nonneg ..)
  have hden : (if s then 1-pp else pp)/(j : ℝ) ≤ (if s then 1-pp else pp)/(i : ℝ) :=
    div_le_div_of_nonneg_left ha (by exact_mod_cast hi) (by exact_mod_cast hij)
  exact sub_le_sub_left (mul_le_mul hden hF hFj (div_nonneg ha (Nat.cast_nonneg i))) _

theorem stages_ordered (n : ℕ) (p pp : ℝ) (hp : (1/2 : ℝ) ≤ p)
    (hpp : (1/2 : ℝ) ≤ pp) (k i : ℕ) :
    greedyStages n p pp k i false ≤ greedyStages n p pp k i true := by
  induction k with
  | zero => simp [greedyStages]
  | succ k ih =>
    simp only [greedyStages]
    split
    · simp only [Bool.false_eq_true,if_false,if_true]
      apply max_le_max_left
      have hf : 0 ≤ ∑ j ∈ Finset.Ioc i n,
          (greedyStages n p pp k j true + greedyStages n p pp k j false) :=
        Finset.sum_nonneg (fun j _ => add_nonneg (nonneg ..) (nonneg ..))
      have hc : (1-pp)/(i : ℝ) ≤ pp/(i : ℝ) :=
        div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg i)
      have hm := mul_le_mul_of_nonneg_right hc hf
      linarith
    · exact ih

end SecretaryResearch
#print axioms SecretaryResearch.recurrence
#print axioms SecretaryResearch.coord_mono

-- Alexander Richard Towell (queelius), with Codex assistance.
-- Dütting et al., arXiv:2011.06726v1, late dual coordinates.
theorem solution (n : ℕ) (p pp : ℝ) (_hn : 1 ≤ n)
    (hp0 : (1/2 : ℝ) ≤ p) (_hp1 : p ≤ 1)
    (hpp0 : (1/2 : ℝ) ≤ pp) (hpp1 : pp ≤ 1)
    (i : ℕ) (hi : tN n p pp ≤ i) (hin : i ≤ n) :
    w n p pp i true = p-(∑ j ∈ Finset.Ico i n, (1-pp)/(j : ℝ)) ∧
    w n p pp i false = (1-p)-(∑ j ∈ Finset.Ico i n, pp/(j : ℝ)) := by
  classical
  have hNex : ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧ 0 < w n p pp k false := by
    by_contra h
    simp only [tN,if_neg h] at hi
    omega
  have htmem := Nat.sInf_mem hNex
  have ht : 1 ≤ tN n p pp := by
    unfold tN
    rw [if_pos hNex]
    exact htmem.1
  have hpos (j : ℕ) (hj : tN n p pp ≤ j) (hjn : j ≤ n) :
      0 < w n p pp j true ∧ 0 < w n p pp j false := by
    have hj' : sInf {k : ℕ | 1 ≤ k ∧ k ≤ n ∧ 0 < w n p pp k false} ≤ j := by
      simpa only [tN,if_pos hNex] using hj
    have hNpos := htmem.2.2.trans_le (SecretaryResearch.coord_mono n p pp (by linarith) hpp1
      _ j htmem.1 hj' hjn false)
    exact ⟨hNpos.trans_le (SecretaryResearch.stages_ordered n p pp hp0 hpp0 n j),hNpos⟩
  have heq (j : ℕ) (hj : tN n p pp ≤ j) (hjn : j ≤ n) (s : Bool) :
      w n p pp j s = (if s then p else 1-p)-(if s then 1-pp else pp)/(j : ℝ)*
        ∑ k ∈ Finset.Ioc j n, (w n p pp k true+w n p pp k false) := by
    have hrec := SecretaryResearch.recurrence n p pp j (ht.trans hj) hjn s
    have hpositive : 0 < w n p pp j s := by
      cases s
      · exact (hpos j hj hjn).2
      · exact (hpos j hj hjn).1
    rw [hrec] at hpositive
    exact hrec.trans (max_eq_right ((lt_max_iff.mp hpositive).resolve_left (lt_irrefl (0 : ℝ))).le)
  have hformula : ∀ d j : ℕ, n-j=d → tN n p pp ≤ j → j ≤ n →
      w n p pp j true = p-(∑ k ∈ Finset.Ico j n, (1-pp)/(k : ℝ)) ∧
      w n p pp j false = (1-p)-(∑ k ∈ Finset.Ico j n, pp/(k : ℝ)) := by
    intro d
    induction d with
    | zero =>
      intro j hd hj hjn
      have : j=n := by omega
      subst j
      simpa using And.intro (heq n hj le_rfl true) (heq n hj le_rfl false)
    | succ d ih =>
      intro j hd hj hjn
      have hj1 : j+1 ≤ n := by omega
      have hjt : tN n p pp ≤ j+1 := by omega
      obtain ⟨hy,hnn⟩ := ih (j+1) (by omega) hjt hj1
      have ey := heq j hj hjn true
      have en := heq j hj hjn false
      have ey1 := heq (j+1) hjt hj1 true
      have en1 := heq (j+1) hjt hj1 false
      simp only [if_true,if_false,Bool.false_eq_true] at ey en ey1 en1
      have hsplit : (∑ k ∈ Finset.Ioc j n, (w n p pp k true+w n p pp k false)) =
          w n p pp (j+1) true+w n p pp (j+1) false+
            ∑ k ∈ Finset.Ioc (j+1) n, (w n p pp k true+w n p pp k false) := by
        have hs : Finset.Ioc j n=insert (j+1) (Finset.Ioc (j+1) n) := by
          ext k; simp only [Finset.mem_Ioc,Finset.mem_insert]; omega
        rw [hs,Finset.sum_insert (by simp)]
      have hsum (a : ℝ) : (∑ k ∈ Finset.Ico j n, a/(k : ℝ)) =
          a/(j : ℝ)+∑ k ∈ Finset.Ico (j+1) n, a/(k : ℝ) := by
        have hs : Finset.Ico j n=insert j (Finset.Ico (j+1) n) := by
          ext k; simp only [Finset.mem_Ico,Finset.mem_insert]; omega
        rw [hs,Finset.sum_insert (by simp)]
      rw [hsplit] at ey en
      rw [hsum,hsum]
      have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
      have hj1R : (j : ℝ)+1 ≠ 0 := by positivity
      push_cast at ey1 en1
      constructor
      · calc
          _ = w n p pp (j+1) true - (1-pp)/(j : ℝ) := by
            field_simp [hjR,hj1R] at ey ey1 en1 ⊢
            have htot : (w n p pp (j+1) true+w n p pp (j+1) false+
                ∑ k ∈ Finset.Ioc (j+1) n, (w n p pp k true+w n p pp k false))*((j : ℝ)+1) =
                ((j : ℝ)+1)+(j : ℝ)*∑ k ∈ Finset.Ioc (j+1) n, (w n p pp k true+w n p pp k false) := by
              nlinarith only [ey1,en1]
            apply mul_right_cancel₀ hj1R
            nlinarith only [congrArg (fun x : ℝ => x*((j : ℝ)+1)) ey,
              congrArg (fun x : ℝ => x*(1-pp)) htot,
              congrArg (fun x : ℝ => x*(j : ℝ)) ey1]
          _ = _ := by rw [hy]; ring
      · calc
          _ = w n p pp (j+1) false - pp/(j : ℝ) := by
            field_simp [hjR,hj1R] at en ey1 en1 ⊢
            have htot : (w n p pp (j+1) true+w n p pp (j+1) false+
                ∑ k ∈ Finset.Ioc (j+1) n, (w n p pp k true+w n p pp k false))*((j : ℝ)+1) =
                ((j : ℝ)+1)+(j : ℝ)*∑ k ∈ Finset.Ioc (j+1) n, (w n p pp k true+w n p pp k false) := by
              nlinarith only [ey1,en1]
            apply mul_right_cancel₀ hj1R
            nlinarith only [congrArg (fun x : ℝ => x*((j : ℝ)+1)) en,
              congrArg (fun x : ℝ => x*pp) htot,
              congrArg (fun x : ℝ => x*(j : ℝ)) en1]
          _ = _ := by rw [hnn]; ring
  exact hformula (n-i) i rfl hi hin

#print axioms solution
