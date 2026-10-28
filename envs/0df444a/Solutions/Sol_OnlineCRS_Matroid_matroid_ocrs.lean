-- Prove2me | solution 1 for OnlineCRS.Matroid.matroid_ocrs
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-26T10:31:07.228424+00:00
-- url     : https://prove2.me/submissions/29bd47f8-b110-4a68-aa76-6a5add58d79d

import Mathlib
import Definitions.Def_OnlineCRS_Matroid_Basics
import Definitions.Def_OnlineCRS_Matroid_Polytope

set_option autoImplicit false

open scoped Pointwise Matroid

namespace OCRSMatroidH

open OnlineCRS.Matroid
open Classical

variable {α : Type} [Fintype α] [DecidableEq α]

lemma activeProb_nonneg (x : α → ℝ) (hx : ∀ e, 0 ≤ x e ∧ x e ≤ 1) (A : Finset α) :
    0 ≤ activeProb x A := by
  unfold activeProb
  apply Finset.prod_nonneg
  intro e _
  split_ifs
  · exact (hx e).1
  · linarith [(hx e).2]

lemma activeProb_sum (x : α → ℝ) : ∑ A : Finset α, activeProb x A = 1 := by
  have h := Fintype.prod_add (fun e => x e) (fun e => 1 - x e)
  simp only [add_sub_cancel, Finset.prod_const_one] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro A _
  unfold activeProb
  rw [← Finset.prod_mul_prod_compl A]
  congr 1
  · apply Finset.prod_congr rfl
    intro e he
    rw [if_pos he]
  · apply Finset.prod_congr rfl
    intro e he
    rw [if_neg (Finset.mem_compl.mp he)]

/-- expectation over the random active set `R(x)`. -/
noncomputable def Ex (x : α → ℝ) (f : Finset α → ℝ) : ℝ :=
  ∑ A : Finset α, activeProb x A * f A

lemma Ex_mono (x : α → ℝ) (hx : ∀ e, 0 ≤ x e ∧ x e ≤ 1) {f g : Finset α → ℝ}
    (h : ∀ A, f A ≤ g A) : Ex x f ≤ Ex x g := by
  unfold Ex
  apply Finset.sum_le_sum
  intro A _
  exact mul_le_mul_of_nonneg_left (h A) (activeProb_nonneg x hx A)

lemma Ex_add (x : α → ℝ) (f g : Finset α → ℝ) :
    Ex x (fun A => f A + g A) = Ex x f + Ex x g := by
  unfold Ex
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro A _
  ring

lemma Ex_sub (x : α → ℝ) (f g : Finset α → ℝ) :
    Ex x (fun A => f A - g A) = Ex x f - Ex x g := by
  unfold Ex
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro A _
  ring

lemma Ex_const (x : α → ℝ) (c : ℝ) : Ex x (fun _ => c) = c := by
  unfold Ex
  rw [← Finset.sum_mul, activeProb_sum, one_mul]

lemma Ex_sum (x : α → ℝ) (D : Finset α) (g : α → Finset α → ℝ) :
    Ex x (fun A => ∑ d ∈ D, g d A) = ∑ d ∈ D, Ex x (g d) := by
  unfold Ex
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

lemma activeProb_mem (x : α → ℝ) (e : α) (A : Finset α) :
    activeProb x A * (if e ∈ A then 1 else 0) = x e * activeProb (Function.update x e 1) A := by
  unfold activeProb
  have h1 := Finset.mul_prod_erase Finset.univ (fun f => if f ∈ A then x f else 1 - x f)
    (Finset.mem_univ e)
  have h2 := Finset.mul_prod_erase Finset.univ
    (fun f => if f ∈ A then Function.update x e 1 f else 1 - Function.update x e 1 f)
    (Finset.mem_univ e)
  rw [← h1, ← h2]
  have hrest : ∏ f ∈ Finset.univ.erase e,
      (if f ∈ A then Function.update x e 1 f else 1 - Function.update x e 1 f)
      = ∏ f ∈ Finset.univ.erase e, (if f ∈ A then x f else 1 - x f) := by
    apply Finset.prod_congr rfl
    intro f hf
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hf)]
  rw [hrest]
  by_cases he : e ∈ A
  · simp only [he, if_true, Function.update_self]
    ring
  · simp only [he, if_false, Function.update_self]
    ring

lemma Ex_mem (x : α → ℝ) (e : α) : Ex x (fun A => if e ∈ A then 1 else 0) = x e := by
  unfold Ex
  rw [Finset.sum_congr rfl (fun A _ => activeProb_mem x e A), ← Finset.mul_sum, activeProb_sum,
    mul_one]

/-! ### rank helpers -/

lemma eRk_ne_top (N : Matroid α) (X : Set α) : N.eRk X ≠ ⊤ :=
  (lt_of_le_of_lt (N.eRk_le_encard X) (Set.toFinite X).encard_lt_top).ne

/-- the rank as a natural number. -/
noncomputable def rho (N : Matroid α) (X : Set α) : ℕ := (N.eRk X).toNat

lemma eRk_eq_rho (N : Matroid α) (X : Set α) : N.eRk X = (rho N X : ℕ∞) :=
  (ENat.coe_toNat (eRk_ne_top N X)).symm

lemma rho_le_card (N : Matroid α) (W : Finset α) (hW : N.E = ↑W) (A : Finset α) :
    rho N ↑A ≤ (A ∩ W).card := by
  have h : N.eRk ↑A ≤ ((A ∩ W).card : ℕ∞) := by
    rw [← N.eRk_inter_ground, hW, ← Finset.coe_inter, ← Set.encard_coe_eq_coe_finsetCard]
    exact N.eRk_le_encard _
  rw [eRk_eq_rho] at h
  exact_mod_cast h

lemma rho_union_le (N : Matroid α) (X : Set α) (F : Finset α) :
    rho N (X ∪ ↑F) ≤ rho N X + (F.filter (fun f => f ∉ N.closure X)).card := by
  have h1 : (X ∪ ↑F) ∩ N.E ⊆ N.closure (X ∪ ↑(F.filter (fun f => f ∉ N.closure X))) := by
    rintro a ⟨ha, haE⟩
    rcases ha with ha | ha
    · exact N.inter_ground_subset_closure _ ⟨Or.inl ha, haE⟩
    · by_cases hc : a ∈ N.closure X
      · exact N.closure_subset_closure Set.subset_union_left hc
      · refine N.inter_ground_subset_closure _ ⟨Or.inr ?_, haE⟩
        simp only [Finset.coe_filter, Set.mem_setOf_eq]
        exact ⟨ha, hc⟩
  have h2 : N.eRk (X ∪ ↑F) ≤ N.eRk X + ((F.filter (fun f => f ∉ N.closure X)).card : ℕ∞) := by
    calc N.eRk (X ∪ ↑F) = N.eRk ((X ∪ ↑F) ∩ N.E) := (N.eRk_inter_ground _).symm
      _ ≤ N.eRk (N.closure (X ∪ ↑(F.filter (fun f => f ∉ N.closure X)))) := N.eRk_mono h1
      _ = N.eRk (X ∪ ↑(F.filter (fun f => f ∉ N.closure X))) := N.eRk_closure_eq _
      _ ≤ N.eRk X + (↑(F.filter (fun f => f ∉ N.closure X)) : Set α).encard :=
          N.eRk_union_le_eRk_add_encard _ _
      _ = N.eRk X + ((F.filter (fun f => f ∉ N.closure X)).card : ℕ∞) := by
          rw [Set.encard_coe_eq_coe_finsetCard]
  rw [eRk_eq_rho, eRk_eq_rho] at h2
  exact_mod_cast h2

lemma exists_ext (N : Matroid α) (S S' : Set α) (hSS' : S ⊆ S') :
    ∃ D : Finset α, (↑D : Set α) ⊆ S' ∧ rho N S + D.card = rho N S' ∧
      ∀ Y : Set α, rho N (Y ∪ S') ≤ rho N ((Y ∪ S) ∪ ↑D) := by
  obtain ⟨I, hI⟩ := N.exists_isBasis' S
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_isBasis'_of_subset (hI.subset.trans hSS')
  refine ⟨(J \ I).toFinset, ?_, ?_, ?_⟩
  · rw [Set.coe_toFinset]
    exact Set.diff_subset.trans hJ.subset
  · have h1 : (J \ I).encard + I.encard = J.encard := Set.encard_diff_add_encard_of_subset hIJ
    have h2 : (J \ I).encard = ((J \ I).toFinset.card : ℕ∞) := by
      rw [← Set.encard_coe_eq_coe_finsetCard, Set.coe_toFinset]
    have h3 : N.eRk S + ((J \ I).toFinset.card : ℕ∞) = N.eRk S' := by
      rw [hI.eRk_eq_encard, hJ.eRk_eq_encard, ← h2, add_comm, h1]
    rw [eRk_eq_rho, eRk_eq_rho] at h3
    exact_mod_cast h3
  · intro Y
    have hsub : (Y ∪ S') ∩ N.E ⊆ N.closure ((Y ∪ S) ∪ ↑(J \ I).toFinset) := by
      rintro a ⟨ha, haE⟩
      rcases ha with ha | ha
      · exact N.inter_ground_subset_closure _ ⟨Or.inl (Or.inl ha), haE⟩
      · have hJa : a ∈ N.closure J := by
          rw [hJ.closure_eq_closure]
          exact N.inter_ground_subset_closure _ ⟨ha, haE⟩
        refine N.closure_subset_closure ?_ hJa
        intro j hj
        by_cases hjI : j ∈ I
        · exact Or.inl (Or.inr (hI.subset hjI))
        · refine Or.inr ?_
          rw [Set.coe_toFinset]
          exact ⟨hj, hjI⟩
    have h : N.eRk (Y ∪ S') ≤ N.eRk ((Y ∪ S) ∪ ↑(J \ I).toFinset) :=
      calc N.eRk (Y ∪ S') = N.eRk ((Y ∪ S') ∩ N.E) := (N.eRk_inter_ground _).symm
        _ ≤ N.eRk (N.closure ((Y ∪ S) ∪ ↑(J \ I).toFinset)) := N.eRk_mono hsub
        _ = N.eRk ((Y ∪ S) ∪ ↑(J \ I).toFinset) := N.eRk_closure_eq _
    rw [eRk_eq_rho, eRk_eq_rho] at h
    exact_mod_cast h

/-! ### the refinement sequence -/

/-- `Pr[e ∈ span((R(x) ∪ T) \ {e})]`. -/
noncomputable def sp (N : Matroid α) (x : α → ℝ) (T : Finset α) (e : α) : ℝ :=
  Ex x (fun A => if e ∈ N.closure (((A ∪ T : Finset α) : Set α) \ {e}) then 1 else 0)

/-- `S₀ = ∅`, `S_{i+1} = {e : Pr[e ∈ span((R ∪ S_i) \ e)] > b}`. -/
noncomputable def Sq (N : Matroid α) (x : α → ℝ) (b : ℝ) : ℕ → Finset α
  | 0 => ∅
  | i + 1 => Finset.univ.filter fun e => b < sp N x (Sq N x b i) e

lemma Sq_succ (N : Matroid α) (x : α → ℝ) (b : ℝ) (i : ℕ) :
    Sq N x b (i + 1) = Finset.univ.filter fun e => b < sp N x (Sq N x b i) e := rfl

lemma mem_Sq_succ (N : Matroid α) (x : α → ℝ) (b : ℝ) (i : ℕ) (e : α) :
    e ∈ Sq N x b (i + 1) ↔ b < sp N x (Sq N x b i) e := by
  rw [Sq_succ]; simp

lemma sp_mono (N : Matroid α) (x : α → ℝ) (hx : ∀ e, 0 ≤ x e ∧ x e ≤ 1) {T T' : Finset α}
    (h : T ⊆ T') (e : α) : sp N x T e ≤ sp N x T' e := by
  unfold sp
  apply Ex_mono x hx
  intro A
  by_cases h1 : e ∈ N.closure (((A ∪ T : Finset α) : Set α) \ {e})
  · have h2 : e ∈ N.closure (((A ∪ T' : Finset α) : Set α) \ {e}) := by
      refine N.closure_subset_closure ?_ h1
      apply Set.diff_subset_diff_left
      exact_mod_cast Finset.union_subset_union (le_refl A) h
    rw [if_pos h1, if_pos h2]
  · rw [if_neg h1]
    split_ifs <;> norm_num

lemma Sq_mono (N : Matroid α) (x : α → ℝ) (hx : ∀ e, 0 ≤ x e ∧ x e ≤ 1) (b : ℝ) :
    ∀ i, Sq N x b i ⊆ Sq N x b (i + 1)
  | 0 => by intro e he; simp [Sq] at he
  | i + 1 => by
    intro e he
    rw [mem_Sq_succ] at he ⊢
    exact lt_of_lt_of_le he (sp_mono N x hx (Sq_mono N x hx b i) e)

lemma Sq_stable_ex (N : Matroid α) (x : α → ℝ) (hx : ∀ e, 0 ≤ x e ∧ x e ≤ 1) (b : ℝ) :
    ∃ k, Sq N x b (k + 1) = Sq N x b k := by
  by_contra hne
  push_neg at hne
  have hcard : ∀ k, k ≤ (Sq N x b k).card := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hss : Sq N x b k ⊂ Sq N x b (k + 1) :=
        Finset.ssubset_iff_subset_ne.mpr ⟨Sq_mono N x hx b k, (hne k).symm⟩
      have := Finset.card_lt_card hss
      omega
  have h1 := hcard (Fintype.card α + 1)
  have h2 := Finset.card_le_univ (Sq N x b (Fintype.card α + 1))
  omega

/-- the stable set `S` (first set of the chain). -/
noncomputable def Sstar (N : Matroid α) (x : α → ℝ) (b : ℝ) : Finset α :=
  Sq N x b (Classical.epsilon fun k => Sq N x b (k + 1) = Sq N x b k)

lemma Sstar_fix (N : Matroid α) (x : α → ℝ) (hx : ∀ e, 0 ≤ x e ∧ x e ≤ 1) (b : ℝ) {e : α}
    (he : e ∉ Sstar N x b) : sp N x (Sstar N x b) e ≤ b := by
  have hk := Classical.epsilon_spec (Sq_stable_ex N x hx b)
  unfold Sstar at he ⊢
  rw [← hk, mem_Sq_succ, not_lt] at he
  exact he

lemma sp_eq_zero (N : Matroid α) (x : α → ℝ) (T : Finset α) (e : α) (he : e ∉ N.E) :
    sp N x T e = 0 := by
  unfold sp Ex
  apply Finset.sum_eq_zero
  intro A _
  dsimp only
  rw [if_neg (fun h => he (N.closure_subset_ground _ h)), mul_zero]

lemma Sq_subset (N : Matroid α) (x : α → ℝ) (b : ℝ) (hb : 0 ≤ b) (i : ℕ) :
    ∀ e ∈ Sq N x b i, e ∈ N.E := by
  intro e he
  cases i with
  | zero => simp [Sq] at he
  | succ i =>
    rw [mem_Sq_succ] at he
    by_contra h
    rw [sp_eq_zero N x _ e h] at he
    linarith

lemma Sstar_subset (N : Matroid α) (x : α → ℝ) (b : ℝ) (hb : 0 ≤ b) :
    ∀ e ∈ Sstar N x b, e ∈ N.E :=
  Sq_subset N x b hb _

/-! ### the key estimate (Lemma 2.4 in rank form) -/

lemma K (N : Matroid α) (W : Finset α) (hW : N.E = ↑W) (x : α → ℝ)
    (hx : ∀ e, 0 ≤ x e ∧ x e ≤ 1) (b : ℝ) :
    ∀ i, Ex x (fun A => (rho N ↑(A ∪ Sq N x b i) : ℝ)) ≤
        ∑ e ∈ W, x e + (1 - b) * (rho N ↑(Sq N x b i) : ℝ) ∧
      (0 < rho N ↑(Sq N x b i) → Ex x (fun A => (rho N ↑(A ∪ Sq N x b i) : ℝ)) <
        ∑ e ∈ W, x e + (1 - b) * (rho N ↑(Sq N x b i) : ℝ)) := by
  intro i
  induction i with
  | zero =>
    have h0 : rho N ↑(Sq N x b 0) = 0 := by simp [Sq, rho]
    rw [h0]
    refine ⟨?_, fun h => absurd h (lt_irrefl 0)⟩
    simp only [Nat.cast_zero, mul_zero, add_zero]
    calc Ex x (fun A => (rho N ↑(A ∪ Sq N x b 0) : ℝ))
        ≤ Ex x (fun A => ∑ e ∈ W, if e ∈ A then (1:ℝ) else 0) := by
          apply Ex_mono x hx
          intro A
          have h1 := rho_le_card N W hW (A ∪ Sq N x b 0)
          have h2 : A ∪ Sq N x b 0 = A := by simp [Sq]
          rw [h2] at h1 ⊢
          have h3 : ((A ∩ W).card : ℝ) = ∑ e ∈ W, if e ∈ A then (1:ℝ) else 0 := by
            rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
            push_cast
            rfl
          rw [← h3]
          exact_mod_cast h1
      _ = ∑ e ∈ W, x e := by
          rw [Ex_sum]
          exact Finset.sum_congr rfl (fun d _ => Ex_mem x d)
  | succ i ih =>
    obtain ⟨ih1, ih2⟩ := ih
    obtain ⟨D, hDS', hcard, hY⟩ := exists_ext N (↑(Sq N x b i) : Set α) ↑(Sq N x b (i + 1))
      (Finset.coe_subset.mpr (Sq_mono N x hx b i))
    have hDb : ∀ d ∈ D, b < sp N x (Sq N x b i) d := by
      intro d hd
      have hd' : d ∈ Sq N x b (i + 1) := Finset.mem_coe.mp (hDS' (Finset.mem_coe.mpr hd))
      rwa [mem_Sq_succ] at hd'
    have hpt : ∀ A : Finset α, (rho N ↑(A ∪ Sq N x b (i + 1)) : ℝ) ≤
        (rho N ↑(A ∪ Sq N x b i) : ℝ) + ∑ d ∈ D,
          (1 - (if d ∈ N.closure (((A ∪ Sq N x b i : Finset α) : Set α) \ {d}) then (1:ℝ) else 0)) := by
      intro A
      have h1 := hY ↑A
      have h2 := rho_union_le N (↑A ∪ ↑(Sq N x b i)) D
      simp only [Finset.coe_union]
      have h3 : ((D.filter (fun f => f ∉ N.closure (↑A ∪ ↑(Sq N x b i)))).card : ℝ) ≤
          ∑ d ∈ D, (1 - (if d ∈ N.closure ((↑A ∪ ↑(Sq N x b i)) \ {d}) then (1:ℝ) else 0)) := by
        rw [Finset.card_filter]
        push_cast
        apply Finset.sum_le_sum
        intro d _
        by_cases hc : d ∈ N.closure (↑A ∪ ↑(Sq N x b i))
        · rw [if_neg (not_not.mpr hc)]
          split_ifs <;> norm_num
        · have hc' : d ∉ N.closure ((↑A ∪ ↑(Sq N x b i)) \ {d}) :=
            fun h => hc (N.closure_subset_closure Set.diff_subset h)
          rw [if_pos hc, if_neg hc']
          norm_num
      have h4 : (rho N (↑A ∪ ↑(Sq N x b (i + 1))) : ℝ) ≤ (rho N (↑A ∪ ↑(Sq N x b i)) : ℝ) +
          ((D.filter (fun f => f ∉ N.closure (↑A ∪ ↑(Sq N x b i)))).card : ℝ) := by
        exact_mod_cast h1.trans h2
      linarith
    have hE1 : Ex x (fun A => (rho N ↑(A ∪ Sq N x b (i + 1)) : ℝ)) ≤
        Ex x (fun A => (rho N ↑(A ∪ Sq N x b i) : ℝ)) + ∑ d ∈ D, (1 - sp N x (Sq N x b i) d) := by
      calc Ex x (fun A => (rho N ↑(A ∪ Sq N x b (i + 1)) : ℝ))
          ≤ Ex x (fun A => (rho N ↑(A ∪ Sq N x b i) : ℝ) + ∑ d ∈ D,
              (1 - (if d ∈ N.closure (((A ∪ Sq N x b i : Finset α) : Set α) \ {d})
                then (1:ℝ) else 0))) := Ex_mono x hx hpt
        _ = _ := by
          rw [Ex_add, Ex_sum]
          congr 1
          apply Finset.sum_congr rfl
          intro d _
          rw [Ex_sub, Ex_const]
          rfl
    have hsum : ∑ d ∈ D, (1 - sp N x (Sq N x b i) d) ≤ (1 - b) * (D.card : ℝ) := by
      calc ∑ d ∈ D, (1 - sp N x (Sq N x b i) d) ≤ ∑ _d ∈ D, (1 - b) :=
            Finset.sum_le_sum (fun d hd => by linarith [hDb d hd])
        _ = (1 - b) * (D.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
    have hsum' : D.Nonempty → ∑ d ∈ D, (1 - sp N x (Sq N x b i) d) < (1 - b) * (D.card : ℝ) := by
      intro hne
      calc ∑ d ∈ D, (1 - sp N x (Sq N x b i) d) < ∑ _d ∈ D, (1 - b) :=
            Finset.sum_lt_sum_of_nonempty hne (fun d hd => by linarith [hDb d hd])
        _ = (1 - b) * (D.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
    have hc : (rho N ↑(Sq N x b i) : ℝ) + (D.card : ℝ) = (rho N ↑(Sq N x b (i + 1)) : ℝ) := by
      exact_mod_cast hcard
    have hlin : (1 - b) * (rho N ↑(Sq N x b (i + 1)) : ℝ) =
        (1 - b) * (rho N ↑(Sq N x b i) : ℝ) + (1 - b) * (D.card : ℝ) := by
      rw [← hc]; ring
    refine ⟨by linarith, fun hpos => ?_⟩
    by_cases h0 : 0 < rho N ↑(Sq N x b i)
    · have := ih2 h0
      linarith
    · have h0' : rho N ↑(Sq N x b i) = 0 := by omega
      have hDne : D.Nonempty := by
        rw [← Finset.card_pos]
        have : rho N ↑(Sq N x b i) + D.card = rho N ↑(Sq N x b (i + 1)) := hcard
        omega
      have := hsum' hDne
      linarith

lemma Sq_ne (N : Matroid α) (W : Finset α) (hW : N.E = ↑W) (x : α → ℝ)
    (hx : ∀ e, 0 ≤ x e ∧ x e ≤ 1) (b : ℝ) (hpos : 0 < rho N ↑W)
    (hxW : ∑ e ∈ W, x e ≤ b * (rho N ↑W : ℝ)) (i : ℕ) : Sq N x b i ≠ W := by
  intro hEq
  have hK := (K N W hW x hx b i).2
  rw [hEq] at hK
  have hconst : Ex x (fun A => (rho N ↑(A ∪ W) : ℝ)) = (rho N ↑W : ℝ) := by
    have h : ∀ A : Finset α, rho N ↑(A ∪ W) = rho N ↑W := by
      intro A
      unfold rho
      rw [← N.eRk_inter_ground (↑(A ∪ W) : Set α), hW,
        Set.inter_eq_right.mpr (Finset.coe_subset.mpr Finset.subset_union_right)]
    simp_rw [h]
    exact Ex_const x _
  have h := hK hpos
  rw [hconst] at h
  nlinarith

/-! ### the chain and the family -/

/-- `N₀ = univ`, `N_{i+1} = S(M|N_i)` (guarded so that the chain always strictly decreases). -/
noncomputable def chainN (M : Matroid α) (x : α → ℝ) (b : ℝ) : ℕ → Finset α
  | 0 => Finset.univ
  | i + 1 => if Sstar (M ↾ (↑(chainN M x b i) : Set α)) x b ⊂ chainN M x b i
      then Sstar (M ↾ (↑(chainN M x b i) : Set α)) x b else ∅

lemma chainN_zero (M : Matroid α) (x : α → ℝ) (b : ℝ) : chainN M x b 0 = Finset.univ := rfl

lemma chainN_succ (M : Matroid α) (x : α → ℝ) (b : ℝ) (i : ℕ) :
    chainN M x b (i + 1) = if Sstar (M ↾ (↑(chainN M x b i) : Set α)) x b ⊂ chainN M x b i
      then Sstar (M ↾ (↑(chainN M x b i) : Set α)) x b else ∅ := rfl

lemma chainN_succ_subset (M : Matroid α) (x : α → ℝ) (b : ℝ) (i : ℕ) :
    chainN M x b (i + 1) ⊆ chainN M x b i := by
  rw [chainN_succ]
  split_ifs with h
  · exact h.subset
  · exact Finset.empty_subset _

lemma chainN_anti (M : Matroid α) (x : α → ℝ) (b : ℝ) {i j : ℕ} (hij : i ≤ j) :
    chainN M x b j ⊆ chainN M x b i := by
  induction hij with
  | refl => exact le_refl _
  | step _ ih => exact (chainN_succ_subset M x b _).trans ih

lemma chainN_card (M : Matroid α) (x : α → ℝ) (b : ℝ) :
    ∀ i, (chainN M x b i).card ≤ Fintype.card α - i := by
  intro i
  induction i with
  | zero => simp [chainN_zero, Finset.card_univ]
  | succ i ih =>
    rw [chainN_succ]
    split_ifs with h
    · have := Finset.card_lt_card h
      omega
    · simp

lemma chainN_empty (M : Matroid α) (x : α → ℝ) (b : ℝ) {i : ℕ} (hi : Fintype.card α ≤ i) :
    chainN M x b i = ∅ := by
  have := chainN_card M x b i
  rw [← Finset.card_eq_zero]
  omega

/-- the greedy family: every layer is independent in the corresponding minor. -/
noncomputable def famC (M : Matroid α) (x : α → ℝ) (b : ℝ) : Finset (Finset α) :=
  Finset.univ.filter fun I => ∀ i : ℕ, (M ／ (↑(chainN M x b (i + 1)) : Set α)).Indep
    (↑(I ∩ (chainN M x b i \ chainN M x b (i + 1))) : Set α)

lemma mem_famC (M : Matroid α) (x : α → ℝ) (b : ℝ) (I : Finset α) :
    I ∈ famC M x b ↔ ∀ i : ℕ, (M ／ (↑(chainN M x b (i + 1)) : Set α)).Indep
      (↑(I ∩ (chainN M x b i \ chainN M x b (i + 1))) : Set α) := by
  unfold famC; simp

lemma indep_union_contract (M : Matroid α) {J C X : Set α} (hJ : M.Indep J) (hJC : J ⊆ C)
    (hX : (M ／ C).Indep X) : M.Indep (X ∪ J) := by
  have h1 : M ／ J ／ (C \ J) = M ／ C := by
    rw [Matroid.contract_contract, Set.union_diff_cancel hJC]
  rw [← h1] at hX
  exact (hJ.contract_indep_iff.mp hX.of_contract).2

lemma famC_greedy (M : Matroid α) (x : α → ℝ) (b : ℝ) :
    IsGreedyFamily (fun I : Finset α => M.Indep (I : Set α)) (famC M x b) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_famC]
    intro i
    simp
  · intro I hI J hJI
    rw [mem_famC] at hI ⊢
    intro i
    exact (hI i).subset (Finset.coe_subset.mpr (Finset.inter_subset_inter_right hJI))
  · intro I hI
    rw [mem_famC] at hI
    have key : ∀ d i, Fintype.card α ≤ i + d → M.Indep (↑(I ∩ chainN M x b i) : Set α) := by
      intro d
      induction d with
      | zero =>
        intro i hi
        rw [chainN_empty M x b (by omega)]
        simp
      | succ d ih =>
        intro i hi
        have hsub := chainN_succ_subset M x b i
        have hsplit : (↑(I ∩ chainN M x b i) : Set α) =
            ↑(I ∩ (chainN M x b i \ chainN M x b (i + 1))) ∪ ↑(I ∩ chainN M x b (i + 1)) := by
          rw [← Finset.coe_union]
          congr 1
          ext a
          simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_union]
          by_cases ha : a ∈ chainN M x b (i + 1)
          · have := hsub ha
            tauto
          · tauto
        rw [hsplit]
        refine indep_union_contract M (ih (i + 1) (by omega)) ?_ (hI i)
        intro a ha
        exact Finset.mem_coe.mpr (Finset.mem_inter.mp (Finset.mem_coe.mp ha)).2
    have := key (Fintype.card α) 0 (by omega)
    simpa [chainN_zero] using this

lemma famC_selectable (M : Matroid α) (hE : M.E = Set.univ) (x : α → ℝ) (b : ℝ) (i : ℕ) (e : α)
    (hei : e ∈ chainN M x b i) (hei1 : e ∉ chainN M x b (i + 1)) (A : Finset α)
    (hA : e ∉ M.closure ((↑((A ∩ chainN M x b i) ∪ chainN M x b (i + 1)) : Set α) \ {e})) :
    Selectable (famC M x b) A e := by
  intro I hIA hI
  rw [mem_famC] at hI ⊢
  intro j
  by_cases hej : e ∈ chainN M x b j \ chainN M x b (j + 1)
  · have hji : j = i := by
      rcases Finset.mem_sdiff.mp hej with ⟨h1, h2⟩
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · exact h2 (chainN_anti M x b (by omega : j + 1 ≤ i) hei)
      · exact hei1 (chainN_anti M x b (by omega : i + 1 ≤ j) h1)
    subst hji
    rw [Finset.insert_inter_of_mem hej, Finset.coe_insert]
    have hJ := hI j
    by_cases heJ : e ∈ (↑(I ∩ (chainN M x b j \ chainN M x b (j + 1))) : Set α)
    · rw [Set.insert_eq_of_mem heJ]
      exact hJ
    · rw [hJ.insert_indep_iff_of_notMem heJ, Matroid.contract_closure_eq, Matroid.contract_ground,
        hE]
      refine ⟨⟨Set.mem_univ e, hei1⟩, ?_⟩
      intro hcl
      apply hA
      refine M.closure_subset_closure ?_ hcl.1
      intro a ha
      rcases ha with ha | ha
      · have ha' := Finset.mem_coe.mp ha
        simp only [Finset.mem_inter, Finset.mem_sdiff] at ha'
        refine ⟨?_, ?_⟩
        · simp only [Finset.coe_union, Finset.coe_inter, Set.mem_union, Set.mem_inter_iff,
            Finset.mem_coe]
          exact Or.inl ⟨hIA ha'.1, ha'.2.1⟩
        · intro hae
          rw [Set.mem_singleton_iff] at hae
          subst hae
          exact heJ ha
      · refine ⟨?_, ?_⟩
        · simp only [Finset.coe_union, Set.mem_union]
          exact Or.inr ha
        · intro hae
          rw [Set.mem_singleton_iff] at hae
          subst hae
          exact hei1 ha
  · rw [Finset.insert_inter_of_notMem hej]
    exact hI j

lemma selProb_ge (M : Matroid α) (hE : M.E = Set.univ) (x : α → ℝ)
    (hx : ∀ e, 0 ≤ x e ∧ x e ≤ 1) (b : ℝ) (i : ℕ) (e : α)
    (hei : e ∈ chainN M x b i) (hei1 : e ∉ chainN M x b (i + 1))
    (hN : chainN M x b (i + 1) = Sstar (M ↾ (↑(chainN M x b i) : Set α)) x b) :
    1 - b ≤ selProb x (famC M x b) e := by
  have hfix := Sstar_fix (M ↾ (↑(chainN M x b i) : Set α)) x hx b (e := e)
    (by rw [← hN]; exact hei1)
  rw [← hN] at hfix
  have hsub := chainN_succ_subset M x b i
  have h1 : 1 - sp (M ↾ (↑(chainN M x b i) : Set α)) x (chainN M x b (i + 1)) e ≤
      selProb x (famC M x b) e := by
    have hEq : 1 - sp (M ↾ (↑(chainN M x b i) : Set α)) x (chainN M x b (i + 1)) e =
        Ex x (fun A => (fun _ => (1:ℝ)) A - (fun A => if e ∈ (M ↾ (↑(chainN M x b i) : Set α)).closure
          (↑(A ∪ chainN M x b (i + 1)) \ {e}) then (1:ℝ) else 0) A) := by
      rw [Ex_sub, Ex_const]
      rfl
    rw [hEq]
    unfold selProb Ex
    apply Finset.sum_le_sum
    intro A _
    dsimp only
    by_cases hc : e ∈ (M ↾ (↑(chainN M x b i) : Set α)).closure
        (↑(A ∪ chainN M x b (i + 1)) \ {e})
    · rw [if_pos hc, sub_self, mul_zero]
      split_ifs
      · exact activeProb_nonneg x hx A
      · exact le_refl _
    · rw [if_neg hc, sub_zero, mul_one]
      have hsel : Selectable (famC M x b) A e := by
        refine famC_selectable M hE x b i e hei hei1 A ?_
        intro hcl
        apply hc
        rw [Matroid.restrict_closure_eq']
        left
        refine ⟨?_, hei⟩
        refine M.closure_subset_closure ?_ hcl
        intro a ha
        rcases ha with ⟨ha, hne⟩
        simp only [Finset.coe_union, Finset.coe_inter, Set.mem_union, Set.mem_inter_iff,
          Finset.mem_coe] at ha
        refine ⟨⟨?_, hne⟩, ?_⟩
        · simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe]
          rcases ha with ha | ha
          · exact Or.inl ha.1
          · exact Or.inr ha
        · rcases ha with ha | ha
          · exact Finset.mem_coe.mpr ha.2
          · exact Finset.mem_coe.mpr (hsub ha)
      rw [if_pos hsel]
  linarith

lemma main_sel (M : Matroid α) (hE : M.E = Set.univ) [M.Loopless] (b : ℝ) (hb0 : 0 ≤ b)
    (hb1 : b ≤ 1) (y : α → ℝ) (hy : y ∈ matroidPolytope M) (e : α) :
    1 - b ≤ selProb (b • y) (famC M (b • y) b) e := by
  obtain ⟨hy0, hyS⟩ := hy
  set x : α → ℝ := b • y with hxdef
  have hxe : ∀ f, x f = b * y f := fun f => by simp [hxdef]
  have hy1 : ∀ f, y f ≤ 1 := by
    intro f
    have h := hyS {f}
    simp only [Finset.sum_singleton, rank, Finset.coe_singleton] at h
    have h2 : M.eRk {f} ≤ 1 := M.eRk_singleton_le f
    rw [eRk_eq_rho] at h2
    have h3 : rho M {f} ≤ 1 := by exact_mod_cast h2
    have h4 : (rho M {f} : ℝ) ≤ 1 := by exact_mod_cast h3
    exact h.trans h4
  have hx : ∀ f, 0 ≤ x f ∧ x f ≤ 1 := by
    intro f
    rw [hxe]
    constructor
    · exact mul_nonneg hb0 (hy0 f)
    · nlinarith [hy0 f, hy1 f]
  have hex : ∃ i, e ∉ chainN M x b (i + 1) :=
    ⟨Fintype.card α, by rw [chainN_empty M x b (by omega)]; simp⟩
  have hi1 : e ∉ chainN M x b (Nat.find hex + 1) := Nat.find_spec hex
  have hi : e ∈ chainN M x b (Nat.find hex) := by
    rcases hk : Nat.find hex with _ | j
    · simp [chainN_zero]
    · have := Nat.find_min hex (by omega : j < Nat.find hex)
      exact not_not.mp this
  set i := Nat.find hex with hidef
  set W := chainN M x b i with hWdef
  have hWE : (M ↾ (↑W : Set α)).E = ↑W := rfl
  have hrho : rho (M ↾ (↑W : Set α)) ↑W = rho M ↑W := by
    unfold rho
    rw [Matroid.restrict_eRk_eq _ (subset_refl _)]
  have hpos : 0 < rho (M ↾ (↑W : Set α)) ↑W := by
    rw [hrho]
    have h1 : M.eRk {e} = 1 := Matroid.eRk_singleton_eq (by rw [hE]; trivial)
    have h2 : M.eRk {e} ≤ M.eRk ↑W := M.eRk_mono (by simpa using hi)
    rw [h1, eRk_eq_rho] at h2
    have h3 : 1 ≤ rho M ↑W := by exact_mod_cast h2
    omega
  have hxW : ∑ f ∈ W, x f ≤ b * (rho (M ↾ (↑W : Set α)) ↑W : ℝ) := by
    rw [hrho]
    have h := hyS W
    simp only [rank] at h
    simp_rw [hxe]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left h hb0
  have hN : chainN M x b (i + 1) = Sstar (M ↾ (↑W : Set α)) x b := by
    rw [chainN_succ, if_pos]
    refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · intro f hf
      exact Finset.mem_coe.mp (Sstar_subset (M ↾ (↑W : Set α)) x b hb0 f hf)
    · exact Sq_ne (M ↾ (↑W : Set α)) W hWE x hx b hpos hxW _
  exact selProb_ge M hE x hx b i e hi hi1 hN

end OCRSMatroidH

/-- arXiv:1508.00142v2, Theorem 2.1, p. 9, with the disclosed loopless correction. -/
theorem solution {α : Type} [Fintype α] [DecidableEq α]
    (M : Matroid α) (hE : M.E = Set.univ) [M.Loopless]
    (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    ∃ fam : (α → ℝ) → Finset (Finset α),
      OnlineCRS.Matroid.IsSelectableDet (fun I : Finset α => M.Indep (I : Set α))
        (OnlineCRS.Matroid.matroidPolytope M) b (1 - b) fam := by
  refine ⟨fun x => OCRSMatroidH.famC M x b, fun x => OCRSMatroidH.famC_greedy M x b, ?_⟩
  intro x hx e
  obtain ⟨y, hy, rfl⟩ := hx
  exact OCRSMatroidH.main_sel M hE b hb0 hb1 y hy e
