-- Prove2me | solution 1 for WeightedRainbowCycle.Weighted.boundary_derivative
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:46:58.561207+00:00
-- url     : https://prove2.me/submissions/c8bb64b5-1aa9-4f84-a6e3-2bd2143c6fb5

import Mathlib
import Definitions.Def_WeightedRainbowCycle_Weighted_Reachability
import Definitions.Def_DiffNeighbors_Bias_Model
import Theorems.Thm_WeightedRainbowCycle_Weighted_russo_margulis

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace WeightedRainbowCycle.Dev.BD

open WeightedRainbowCycle.Weighted

variable {V E C : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  [DecidableEq C]

theorem mem_reachable_iff (G : Model V E C) (x y : V) (S : Set C) :
    y ∈ G.reachable x S ↔
      ∃ (n : ℕ) (v : Fin (n + 1) → V) (e : Fin n → E),
        RainbowWalk G n v e ∧ v 0 = x ∧ v (Fin.last n) = y ∧
          ∀ i, ∀ c ∈ G.colors (e i), c ∈ S := by
  classical
  unfold Model.reachable
  simp

theorem reachable_mono (G : Model V E C) (x : V) {S T : Set C} (h : S ⊆ T) :
    G.reachable x S ⊆ G.reachable x T := by
  intro y hy
  rw [mem_reachable_iff] at hy ⊢
  obtain ⟨n, v, e, h1, h2, h3, h4⟩ := hy
  exact ⟨n, v, e, h1, h2, h3, fun i c hc => h (h4 i c hc)⟩

theorem self_mem_reachable (G : Model V E C) (x : V) (S : Set C) :
    x ∈ G.reachable x S := by
  rw [mem_reachable_iff]
  refine ⟨0, fun _ => x, fun i => i.elim0, ⟨fun i => i.elim0, fun i => i.elim0⟩, rfl, rfl, ?_⟩
  intro i; exact i.elim0

theorem reachable_extend (G : Model V E C) (x y z : V) (e0 : E) (S T : Set C)
    (hy : y ∈ G.reachable x S) (hl : G.graph.IsLink e0 y z)
    (hdis : ∀ c ∈ G.colors e0, c ∉ S) (hT : S ⊆ T) (hT' : ∀ c ∈ G.colors e0, c ∈ T) :
    z ∈ G.reachable x T := by
  rw [mem_reachable_iff] at hy ⊢
  obtain ⟨n, v, e, ⟨hlink, hdisj⟩, h2, h3, h4⟩ := hy
  refine ⟨n + 1, Fin.snoc (α := fun _ => V) v z, Fin.snoc (α := fun _ => E) e e0, ⟨?_, ?_⟩,
    ?_, ?_, ?_⟩
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last, Fin.snoc_castSucc]
      rw [← h3] at hl
      simpa using hl
    · simp only [Fin.snoc_castSucc]
      have := hlink j
      rw [Fin.succ_castSucc, Fin.snoc_castSucc]
      exact this
  · intro i j hij
    induction i using Fin.lastCases with
    | last => ?_
    | cast a => ?_
    all_goals induction j using Fin.lastCases with
      | last => ?_
      | cast b => ?_
    · exact absurd rfl hij
    · simp only [Fin.snoc_last, Fin.snoc_castSucc]
      rw [Finset.disjoint_left]
      intro c hc hc'
      exact hdis c hc (h4 b c hc')
    · simp only [Fin.snoc_last, Fin.snoc_castSucc]
      rw [Finset.disjoint_left]
      intro c hc hc'
      exact hdis c hc' (h4 a c hc)
    · simp only [Fin.snoc_castSucc]
      apply hdisj
      intro h; exact hij (by rw [h])
  · rw [← Fin.castSucc_zero, Fin.snoc_castSucc]; exact h2
  · simp
  · intro i c hc
    revert hc
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last]
      intro hc; exact hT' c hc
    · simp only [Fin.snoc_castSucc]
      intro hc; exact hT (h4 j c hc)

end WeightedRainbowCycle.Dev.BD
end
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace WeightedRainbowCycle.Dev.BD

open DiffNeighbors.Bias

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Probability weight of the subset `A` under the product measure. -/
def wt (q : ℝ) (A : Finset S) : ℝ := q ^ A.card * (1 - q) ^ (Fintype.card S - A.card)

def trueSet (z : S → Bool) : Finset S := Finset.univ.filter (fun s => z s = true)

theorem wt_nonneg {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (A : Finset S) : 0 ≤ wt q A := by
  unfold wt
  have : 0 ≤ 1 - q := by linarith
  positivity

theorem wt_union {q : ℝ} (h0 : 0 < q) (h1 : q < 1) {A B : Finset S} (h : Disjoint A B) :
    wt q (A ∪ B) = wt q A * (q / (1 - q)) ^ B.card := by
  have h1' : 0 < 1 - q := by linarith
  unfold wt
  rw [Finset.card_union_of_disjoint h]
  have hle : A.card + B.card ≤ Fintype.card S := by
    rw [← Finset.card_union_of_disjoint h]; exact Finset.card_le_univ _
  have : Fintype.card S - A.card = (Fintype.card S - (A.card + B.card)) + B.card := by omega
  rw [this, pow_add, pow_add, div_pow]
  field_simp

theorem wt_sdiff {q : ℝ} (h0 : 0 < q) (h1 : q < 1) {A B : Finset S} (h : B ⊆ A) :
    wt q (A \ B) = wt q A * ((1 - q) / q) ^ B.card := by
  have h1' : 0 < 1 - q := by linarith
  have := wt_union h0 h1 (A := A \ B) (B := B) Finset.sdiff_disjoint
  rw [Finset.sdiff_union_of_subset h] at this
  rw [this, mul_assoc, ← mul_pow]
  rw [show q / (1 - q) * ((1 - q) / q) = 1 by field_simp]
  simp

theorem prod_eq_wt (q : ℝ) (z : S → Bool) :
    (∏ j, if z j = true then q else 1 - q) = wt q (trueSet z) := by
  rw [Finset.prod_ite]
  unfold wt trueSet
  simp only [Finset.prod_const]
  congr 2
  have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset S))
    (fun j => z j = true)
  rw [Finset.card_univ] at this
  omega

theorem bernExp_eq_sum (q : ℝ) (H : Finset S → ℝ) (h : (S → Bool) → ℝ)
    (hh : ∀ z, h z = H (trueSet z)) :
    bernExp q h = ∑ A : Finset S, wt q A * H A := by
  unfold bernExp mlExt
  simp only [prod_eq_wt, hh]
  refine Fintype.sum_equiv
    { toFun := trueSet
      invFun := fun A s => decide (s ∈ A)
      left_inv := fun z => by funext s; simp [trueSet]
      right_inv := fun A => by ext s; simp [trueSet] } _ _ (fun z => rfl)

/-- Splitting a sum over subsets at a color. -/
theorem sum_split (c : S) (f : Finset S → ℝ) :
    ∑ A : Finset S, f A =
      ∑ A ∈ (Finset.univ.erase c).powerset, (f A + f (insert c A)) := by
  have := Finset.sum_powerset_insert (s := Finset.univ.erase c) (a := c)
    (Finset.notMem_erase c _) f
  rw [Finset.insert_erase (Finset.mem_univ c), Finset.powerset_univ] at this
  rw [this, Finset.sum_add_distrib]

theorem sum_toggle {q : ℝ} (h0 : 0 < q) (h1 : q < 1) (c : S) (g : Finset S → ℝ)
    (hg : ∀ A, g (insert c A) = g A) :
    (∑ A : Finset S, if c ∈ A then wt q A * g A else 0) = q * ∑ A : Finset S, wt q A * g A ∧
    (∑ A : Finset S, if c ∉ A then wt q A * g A else 0) =
      (1 - q) * ∑ A : Finset S, wt q A * g A := by
  have h1' : 0 < 1 - q := by linarith
  have hP : ∀ A ∈ (Finset.univ.erase c).powerset, c ∉ A := by
    intro A hA
    have := Finset.mem_powerset.1 hA
    intro hc; exact (Finset.notMem_erase c _) (this hc)
  have hw : ∀ A ∈ (Finset.univ.erase c).powerset, wt q (insert c A) = wt q A * (q / (1 - q)) := by
    intro A hA
    have := wt_union h0 h1 (A := A) (B := {c}) (Finset.disjoint_singleton_right.2 (hP A hA))
    rw [Finset.card_singleton, pow_one] at this
    rw [← this, Finset.insert_eq, Finset.union_comm]
  set X := ∑ A ∈ (Finset.univ.erase c).powerset, wt q A * g A with hX
  have hT : ∑ A : Finset S, wt q A * g A = X * (1 / (1 - q)) := by
    rw [sum_split c, hX, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun A hA => ?_)
    rw [hw A hA, hg]
    field_simp
    ring
  have e1 : (∑ A : Finset S, if c ∈ A then wt q A * g A else 0) = X * (q / (1 - q)) := by
    rw [sum_split c, hX, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun A hA => ?_)
    rw [if_neg (hP A hA), if_pos (Finset.mem_insert_self _ _), hw A hA, hg]
    ring
  have e2 : (∑ A : Finset S, if c ∉ A then wt q A * g A else 0) = X := by
    rw [sum_split c, hX]
    refine Finset.sum_congr rfl (fun A hA => ?_)
    rw [if_pos (hP A hA), if_neg (by simp)]
    ring
  rw [e1, e2, hT]
  constructor <;> field_simp

theorem sum_super {q : ℝ} (h0 : 0 < q) (h1 : q < 1) (A' T : Finset S) :
    (∑ A : Finset S, if A' ⊆ A ∧ A \ A' ⊆ T then wt q A else 0) ≤
      wt q A' * ((1 - q)⁻¹) ^ T.card := by
  have h1' : 0 < 1 - q := by linarith
  rw [← Finset.sum_filter]
  have hsub : Finset.univ.filter (fun A : Finset S => A' ⊆ A ∧ A \ A' ⊆ T) ⊆
      (T \ A').powerset.image (fun B => A' ∪ B) := by
    intro A hA
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA
    rw [Finset.mem_image]
    refine ⟨A \ A', ?_, Finset.union_sdiff_of_subset hA.1⟩
    rw [Finset.mem_powerset]
    intro s hs
    exact Finset.mem_sdiff.2 ⟨hA.2 hs, (Finset.mem_sdiff.1 hs).2⟩
  calc _ ≤ ∑ A ∈ (T \ A').powerset.image (fun B => A' ∪ B), wt q A :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun A _ _ => wt_nonneg h0.le h1.le A)
    _ = ∑ B ∈ (T \ A').powerset, wt q (A' ∪ B) := by
        refine Finset.sum_image (fun B hB B' hB' hBB => ?_)
        have hB1 := Finset.mem_powerset.1 hB
        have hB2 := Finset.mem_powerset.1 hB'
        have d1 : Disjoint A' B := Finset.disjoint_of_subset_right hB1 Finset.sdiff_disjoint.symm
        have d2 : Disjoint A' B' := Finset.disjoint_of_subset_right hB2 Finset.sdiff_disjoint.symm
        have := congrArg (fun X => X \ A') hBB
        simp only [Finset.union_sdiff_left] at this
        rwa [Finset.sdiff_eq_self_of_disjoint d1.symm, Finset.sdiff_eq_self_of_disjoint d2.symm]
          at this
    _ = ∑ B ∈ (T \ A').powerset, wt q A' * (q / (1 - q)) ^ B.card := by
        refine Finset.sum_congr rfl (fun B hB => ?_)
        have hB1 := Finset.mem_powerset.1 hB
        exact wt_union h0 h1 (Finset.disjoint_of_subset_right hB1 Finset.sdiff_disjoint.symm)
    _ = wt q A' * (1 + q / (1 - q)) ^ (T \ A').card := by
        rw [← Finset.mul_sum]
        congr 1
        have := Finset.sum_pow_mul_eq_add_pow (q / (1 - q)) 1 (T \ A')
        simpa [add_comm] using this
    _ ≤ wt q A' * ((1 - q)⁻¹) ^ T.card := by
        have hr : 1 + q / (1 - q) = (1 - q)⁻¹ := by field_simp; ring
        rw [hr]
        apply mul_le_mul_of_nonneg_left _ (wt_nonneg h0.le h1.le A')
        apply pow_le_pow_right₀
        · rw [one_le_inv₀ h1']; linarith
        · exact Finset.card_le_card Finset.sdiff_subset

theorem sum_sub {q : ℝ} (h0 : 0 < q) (h1 : q < 1) (A' T : Finset S) :
    (∑ A : Finset S, if A ⊆ A' ∧ A' \ A ⊆ T then wt q A else 0) ≤
      wt q A' * (q⁻¹) ^ T.card := by
  have h1' : 0 < 1 - q := by linarith
  rw [← Finset.sum_filter]
  have hsub : Finset.univ.filter (fun A : Finset S => A ⊆ A' ∧ A' \ A ⊆ T) ⊆
      (T ∩ A').powerset.image (fun B => A' \ B) := by
    intro A hA
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA
    rw [Finset.mem_image]
    refine ⟨A' \ A, ?_, Finset.sdiff_sdiff_eq_self hA.1⟩
    rw [Finset.mem_powerset]
    intro s hs
    rw [Finset.mem_inter]
    exact ⟨hA.2 hs, (Finset.mem_sdiff.1 hs).1⟩
  calc _ ≤ ∑ A ∈ (T ∩ A').powerset.image (fun B => A' \ B), wt q A :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun A _ _ => wt_nonneg h0.le h1.le A)
    _ = ∑ B ∈ (T ∩ A').powerset, wt q (A' \ B) := by
        refine Finset.sum_image (fun B hB B' hB' hBB => ?_)
        have hB1 : B ⊆ A' := fun s hs => (Finset.mem_inter.1 (Finset.mem_powerset.1 hB hs)).2
        have hB2 : B' ⊆ A' := fun s hs => (Finset.mem_inter.1 (Finset.mem_powerset.1 hB' hs)).2
        have := congrArg (fun X => A' \ X) hBB
        simp only [Finset.sdiff_sdiff_eq_self hB1, Finset.sdiff_sdiff_eq_self hB2] at this
        exact this
    _ = ∑ B ∈ (T ∩ A').powerset, wt q A' * ((1 - q) / q) ^ B.card := by
        refine Finset.sum_congr rfl (fun B hB => ?_)
        have hB1 : B ⊆ A' := fun s hs => (Finset.mem_inter.1 (Finset.mem_powerset.1 hB hs)).2
        exact wt_sdiff h0 h1 hB1
    _ = wt q A' * (1 + (1 - q) / q) ^ (T ∩ A').card := by
        rw [← Finset.mul_sum]
        congr 1
        have := Finset.sum_pow_mul_eq_add_pow ((1 - q) / q) 1 (T ∩ A')
        simpa [add_comm] using this
    _ ≤ wt q A' * (q⁻¹) ^ T.card := by
        have hr : 1 + (1 - q) / q = q⁻¹ := by field_simp; ring
        rw [hr]
        apply mul_le_mul_of_nonneg_left _ (wt_nonneg h0.le h1.le A')
        apply pow_le_pow_right₀
        · rw [one_le_inv₀ h0]; linarith
        · exact Finset.card_le_card Finset.inter_subset_left

end WeightedRainbowCycle.Dev.BD
end
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace WeightedRainbowCycle.Dev.BD

open WeightedRainbowCycle.Weighted
open scoped Classical

/-- The active colors as a type. -/
abbrev SC {V E C : Type*} [Fintype E] [DecidableEq C] (G : Model V E C) := {c // c ∈ G.activeColors}

section Abstract

variable {S : Type*} [Fintype S] [DecidableEq S] {W : Type*}

/-- Witness extraction for red edges. -/
theorem red_witness (U : Finset S → Set W) (u : W) (L : Finset S) :
    ∀ A : Finset S, u ∈ U A → u ∉ U (A \ L) →
      ∃ c ∈ L, ∃ A' : Finset S, A' ⊆ A ∧ A \ A' ⊆ L.erase c ∧ c ∈ A' ∧ u ∈ U A' ∧
        u ∉ U (A'.erase c) := by
  induction L using Finset.induction_on with
  | empty => intro A h1 h2; simp at h2; exact absurd h1 h2
  | insert a L0 ha ih =>
    intro A h1 h2
    have e : A \ insert a L0 = (A.erase a) \ L0 := by
      ext s; simp [and_assoc, and_comm, and_left_comm]
    by_cases hu : u ∈ U (A.erase a)
    · rw [e] at h2
      obtain ⟨c, hc, A', hA', hsub, hcA', hu1, hu2⟩ := ih (A.erase a) hu h2
      have hca : c ≠ a := fun h => by
        have := hA' hcA'; rw [h] at this; simp at this
      refine ⟨c, Finset.mem_insert_of_mem hc, A', hA'.trans (Finset.erase_subset _ _), ?_,
        hcA', hu1, hu2⟩
      intro s hs
      rw [Finset.mem_sdiff] at hs
      rw [Finset.mem_erase]
      refine ⟨?_, ?_⟩
      · by_cases hsa : s = a
        · subst hsa; exact hca.symm
        · have : s ∈ (A.erase a) \ A' := by
            rw [Finset.mem_sdiff, Finset.mem_erase]; exact ⟨⟨hsa, hs.1⟩, hs.2⟩
          exact (Finset.mem_erase.1 (hsub this)).1
      · by_cases hsa : s = a
        · subst hsa; exact Finset.mem_insert_self _ _
        · have : s ∈ (A.erase a) \ A' := by
            rw [Finset.mem_sdiff, Finset.mem_erase]; exact ⟨⟨hsa, hs.1⟩, hs.2⟩
          exact Finset.mem_insert_of_mem (Finset.mem_erase.1 (hsub this)).2
    · have haA : a ∈ A := by
        by_contra hn
        rw [Finset.erase_eq_of_notMem hn] at hu
        exact hu h1
      refine ⟨a, Finset.mem_insert_self _ _, A, subset_rfl, ?_, haA, h1, hu⟩
      simp

/-- The telescoping step function. -/
def stepT (P : Finset S → Prop) (a : Finset S → ℝ) (A' : Finset S) (c : S) : ℝ :=
  if P A' then 0 else (a A' - a (insert c A')) + (if P (insert c A') then a (insert c A') else 0)

theorem stepT_nonneg (P : Finset S → Prop) (a : Finset S → ℝ)
    (ha : ∀ A B, A ⊆ B → a B ≤ a A) (ha0 : ∀ A, 0 ≤ a A) (A' : Finset S) (c : S) :
    0 ≤ stepT P a A' c := by
  unfold stepT
  split_ifs
  · exact le_rfl
  · have := ha A' (insert c A') (Finset.subset_insert _ _); have := ha0 (insert c A'); linarith
  · have := ha A' (insert c A') (Finset.subset_insert _ _); linarith

theorem chain (P : Finset S → Prop) (a : Finset S → ℝ)
    (ha : ∀ A B, A ⊆ B → a B ≤ a A) (ha0 : ∀ A, 0 ≤ a A) (M : Finset S) :
    ∀ A : Finset S, Disjoint A M → ¬ P A → P (A ∪ M) →
      a A ≤ ∑ p ∈ Finset.univ.filter (fun p : S × Finset S =>
        p.1 ∈ M ∧ A ⊆ p.2 ∧ p.2 ⊆ A ∪ M ∧ p.1 ∉ p.2), stepT P a p.2 p.1 := by
  induction M using Finset.induction_on with
  | empty => intro A _ h1 h2; simp at h2; exact absurd h2 h1
  | insert d M0 hd ih =>
    intro A hdis hnP hP
    have hdA : d ∉ A := fun h => Finset.disjoint_left.1 hdis h (Finset.mem_insert_self _ _)
    have hdis0 : Disjoint A M0 := Finset.disjoint_of_subset_right (Finset.subset_insert _ _) hdis
    have hmem : (d, A) ∈ Finset.univ.filter (fun p : S × Finset S =>
        p.1 ∈ insert d M0 ∧ A ⊆ p.2 ∧ p.2 ⊆ A ∪ insert d M0 ∧ p.1 ∉ p.2) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨Finset.mem_insert_self _ _, subset_rfl, Finset.subset_union_left, hdA⟩
    by_cases hQ : P (insert d A)
    · have : a A = stepT P a A d := by
        unfold stepT; rw [if_neg hnP, if_pos hQ]; ring
      rw [this]
      exact Finset.single_le_sum (f := fun p : S × Finset S => stepT P a p.2 p.1)
        (fun p _ => stepT_nonneg P a ha ha0 p.2 p.1) hmem
    · have hUn : insert d A ∪ M0 = A ∪ insert d M0 := by
        ext s; simp [or_left_comm]
      have h1 := ih (insert d A) (by
        rw [Finset.disjoint_insert_left]; exact ⟨hd, hdis0⟩) hQ (by rw [hUn]; exact hP)
      have hsub : insert (d, A) (Finset.univ.filter (fun p : S × Finset S =>
          p.1 ∈ M0 ∧ insert d A ⊆ p.2 ∧ p.2 ⊆ insert d A ∪ M0 ∧ p.1 ∉ p.2)) ⊆
          Finset.univ.filter (fun p : S × Finset S =>
            p.1 ∈ insert d M0 ∧ A ⊆ p.2 ∧ p.2 ⊆ A ∪ insert d M0 ∧ p.1 ∉ p.2) := by
        intro p hp
        rw [Finset.mem_insert] at hp
        rcases hp with rfl | hp
        · exact hmem
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
          refine ⟨Finset.mem_insert_of_mem hp.1, (Finset.subset_insert _ _).trans hp.2.1, ?_,
            hp.2.2.2⟩
          rw [← hUn]; exact hp.2.2.1
      have hnot : (d, A) ∉ Finset.univ.filter (fun p : S × Finset S =>
          p.1 ∈ M0 ∧ insert d A ⊆ p.2 ∧ p.2 ⊆ insert d A ∪ M0 ∧ p.1 ∉ p.2) := by
        simp [hd]
      have h2 := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (f := fun p : S × Finset S => stepT P a p.2 p.1)
        (fun p _ _ => stepT_nonneg P a ha ha0 p.2 p.1)
      rw [Finset.sum_insert hnot] at h2
      have h3 : stepT P a A d = a A - a (insert d A) := by
        unfold stepT; rw [if_neg hnP, if_neg hQ]; ring
      simp only [h3] at h2
      linarith

end Abstract

section Model

variable {V E C : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  [DecidableEq C] (G : Model V E C) (x : V)

def toSet (A : Finset (SC G)) : Set C := {c | ∃ a ∈ A, a.val = c}

def UU (A : Finset (SC G)) : Finset V := G.reachable x (toSet G A)

def uu (A : Finset (SC G)) : ℝ := ((UU G x A).card : ℝ)

def Ls (e : E) : Finset (SC G) := Finset.univ.filter (fun a => a.1 ∈ G.colors e)

/-- An edge touches the set `P` of vertices. -/
def Touch (e : E) (P : Finset V) : Prop := ∃ a b, G.graph.IsLink e a b ∧ a ∈ P

variable {G x}

theorem toSet_mono {A B : Finset (SC G)} (h : A ⊆ B) : toSet G A ⊆ toSet G B := by
  rintro c ⟨a, ha, rfl⟩; exact ⟨a, h ha, rfl⟩

theorem UU_mono {A B : Finset (SC G)} (h : A ⊆ B) : UU G x A ⊆ UU G x B :=
  reachable_mono G x (toSet_mono h)

theorem x_mem_UU (A : Finset (SC G)) : x ∈ UU G x A := self_mem_reachable G x _

theorem one_le_uu (A : Finset (SC G)) : 1 ≤ uu G x A := by
  unfold uu
  exact_mod_cast Finset.card_pos.2 ⟨x, x_mem_UU A⟩

theorem uu_pos (A : Finset (SC G)) : 0 < uu G x A := lt_of_lt_of_le one_pos (one_le_uu A)

theorem uu_mono {A B : Finset (SC G)} (h : A ⊆ B) : uu G x A ≤ uu G x B := by
  unfold uu; exact_mod_cast Finset.card_le_card (UU_mono h)

theorem Ls_card (ell : ℕ) (hc : ∀ e, (G.colors e).card ≤ ell) (e : E) : (Ls G e).card ≤ ell := by
  refine le_trans ?_ (hc e)
  refine Finset.card_le_card_of_injOn (fun a => a.1) ?_ (fun a _ b _ h => Subtype.ext h)
  intro a ha
  simpa [Ls] using ha

theorem UU_extend (e : E) (A : Finset (SC G)) (a b : V) (hl : G.graph.IsLink e a b)
    (ha : a ∈ UU G x (A \ Ls G e)) : b ∈ UU G x (A ∪ Ls G e) := by
  refine reachable_extend G x a b e _ _ ha hl ?_ ?_ ?_
  · rintro c hc ⟨s, hs, rfl⟩
    rw [Finset.mem_sdiff] at hs
    exact hs.2 (by simpa [Ls] using hc)
  · exact toSet_mono (Finset.sdiff_subset.trans Finset.subset_union_left)
  · intro c hc
    have hmem : c ∈ G.activeColors := by
      unfold Model.activeColors; exact Finset.mem_biUnion.2 ⟨e, Finset.mem_univ _, hc⟩
    exact ⟨⟨c, hmem⟩, Finset.mem_union_right _ (by simpa [Ls] using hc), rfl⟩

theorem touch_bound (ell : ℕ) (delta : ℝ) (hadm : G.Admissible ell delta) (c : SC G)
    (P : Finset V) :
    (∑ e, if c ∈ Ls G e ∧ Touch G e P then G.weight e else 0) ≤ delta * P.card := by
  have h1 : ∀ e, (if c ∈ Ls G e ∧ Touch G e P then G.weight e else 0) ≤
      ∑ y ∈ P, (if G.graph.Inc e y ∧ c.1 ∈ G.colors e then G.weight e else 0) := by
    intro e
    split_ifs with h
    · obtain ⟨hc, a, b, hl, haP⟩ := h
      have hc' : c.1 ∈ G.colors e := by simpa [Ls] using hc
      calc G.weight e = (if G.graph.Inc e a ∧ c.1 ∈ G.colors e then G.weight e else 0) := by
            rw [if_pos ⟨⟨b, hl⟩, hc'⟩]
        _ ≤ _ := Finset.single_le_sum (f := fun y => if G.graph.Inc e y ∧ c.1 ∈ G.colors e
            then G.weight e else 0)
            (fun y _ => by split_ifs; exact G.weight_nonneg e; exact le_rfl) haP
    · exact Finset.sum_nonneg (fun y _ => by split_ifs; exact G.weight_nonneg e; exact le_rfl)
  calc _ ≤ ∑ e, ∑ y ∈ P, (if G.graph.Inc e y ∧ c.1 ∈ G.colors e then G.weight e else 0) :=
        Finset.sum_le_sum (fun e _ => h1 e)
    _ = ∑ y ∈ P, G.colorDegree y c.1 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        unfold Model.colorDegree
        refine Finset.sum_congr rfl (fun e _ => ?_)
        congr
    _ ≤ ∑ y ∈ P, delta := Finset.sum_le_sum (fun y _ => hadm.2 y c.1)
    _ = delta * P.card := by simp [mul_comm]

end Model

end WeightedRainbowCycle.Dev.BD
end
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace WeightedRainbowCycle.Dev.BD

open WeightedRainbowCycle.Weighted
open scoped Classical

theorem sum4 {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ d, ∑ c, ∑ b, ∑ a, f a b c d := by
  calc _ = ∑ b, ∑ a, ∑ c, ∑ d, f a b c d := Finset.sum_comm
    _ = ∑ b, ∑ c, ∑ a, ∑ d, f a b c d := Finset.sum_congr rfl (fun b _ => Finset.sum_comm)
    _ = ∑ b, ∑ c, ∑ d, ∑ a, f a b c d :=
        Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => Finset.sum_comm))
    _ = ∑ c, ∑ b, ∑ d, ∑ a, f a b c d := Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ b, ∑ a, f a b c d := Finset.sum_congr rfl (fun b _ => Finset.sum_comm)
    _ = _ := Finset.sum_comm

section Red

variable {V E C : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  [DecidableEq C] (G : Model V E C) (x : V)

def redInd (e : E) (A : Finset (SC G)) : Prop :=
  ∃ u v, G.graph.IsLink e u v ∧ u ∈ UU G x A ∧ v ∉ UU G x A ∧ u ∉ UU G x (A \ Ls G e)

theorem red_pointwise (e : E) (A : Finset (SC G)) :
    (if redInd G x e A then (1 : ℝ) else 0) ≤
      ∑ c : SC G, ∑ A' : Finset (SC G),
        if (c ∈ Ls G e ∧ c ∈ A' ∧ Touch G e (UU G x A' \ UU G x (A'.erase c)) ∧
          A' ⊆ A ∧ A \ A' ⊆ (Ls G e).erase c) then (1 : ℝ) else 0 := by
  by_cases hR : redInd G x e A
  · rw [if_pos hR]
    obtain ⟨u, v, hl, hu, hv, hnu⟩ := hR
    obtain ⟨c, hc, A', hA', hsub, hcA', hu1, hu2⟩ :=
      red_witness (fun A => (UU G x A : Set V)) u (Ls G e) A hu hnu
    have hcond : (c ∈ Ls G e ∧ c ∈ A' ∧ Touch G e (UU G x A' \ UU G x (A'.erase c)) ∧
          A' ⊆ A ∧ A \ A' ⊆ (Ls G e).erase c) :=
      ⟨hc, hcA', ⟨u, v, hl, Finset.mem_sdiff.2 ⟨hu1, hu2⟩⟩, hA', hsub⟩
    calc (1 : ℝ) = (fun A' : Finset (SC G) =>
          if (c ∈ Ls G e ∧ c ∈ A' ∧ Touch G e (UU G x A' \ UU G x (A'.erase c)) ∧
          A' ⊆ A ∧ A \ A' ⊆ (Ls G e).erase c) then (1 : ℝ) else 0) A' := by
            simp only [if_pos hcond]
      _ ≤ _ := le_trans
        (Finset.single_le_sum (f := fun A' : Finset (SC G) =>
          if (c ∈ Ls G e ∧ c ∈ A' ∧ Touch G e (UU G x A' \ UU G x (A'.erase c)) ∧
          A' ⊆ A ∧ A \ A' ⊆ (Ls G e).erase c) then (1 : ℝ) else 0)
          (fun _ _ => by split_ifs <;> norm_num) (Finset.mem_univ A'))
        (Finset.single_le_sum (f := fun c : SC G => ∑ A' : Finset (SC G),
          if (c ∈ Ls G e ∧ c ∈ A' ∧ Touch G e (UU G x A' \ UU G x (A'.erase c)) ∧
          A' ⊆ A ∧ A \ A' ⊆ (Ls G e).erase c) then (1 : ℝ) else 0)
          (fun _ _ => Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num))
          (Finset.mem_univ c))
  · rw [if_neg hR]
    exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num))

variable {G x} {ell : ℕ} {delta : ℝ} {q : ℝ}

theorem red_key (hadm : G.Admissible ell delta) (h0 : 0 < q) (h1 : q < 1) (e : E) (c : SC G)
    (A' : Finset (SC G)) :
    (∑ A : Finset (SC G), wt q A * (1 / uu G x A) *
      (if (c ∈ Ls G e ∧ c ∈ A' ∧ Touch G e (UU G x A' \ UU G x (A'.erase c)) ∧
          A' ⊆ A ∧ A \ A' ⊆ (Ls G e).erase c) then (1 : ℝ) else 0)) ≤
    (if (c ∈ Ls G e ∧ c ∈ A' ∧ Touch G e (UU G x A' \ UU G x (A'.erase c))) then (1 : ℝ) else 0) *
      (wt q A' / uu G x A') * ((1 - q)⁻¹) ^ (ell - 1) := by
  have h1' : 0 < 1 - q := by linarith
  by_cases hK : (c ∈ Ls G e ∧ c ∈ A' ∧ Touch G e (UU G x A' \ UU G x (A'.erase c)))
  · rw [if_pos hK]
    have hpt : ∀ A : Finset (SC G), wt q A * (1 / uu G x A) *
      (if (c ∈ Ls G e ∧ c ∈ A' ∧ Touch G e (UU G x A' \ UU G x (A'.erase c)) ∧
          A' ⊆ A ∧ A \ A' ⊆ (Ls G e).erase c) then (1 : ℝ) else 0) ≤
        (1 / uu G x A') * (if (A' ⊆ A ∧ A \ A' ⊆ (Ls G e).erase c) then wt q A else 0) := by
      intro A
      by_cases hP : (A' ⊆ A ∧ A \ A' ⊆ (Ls G e).erase c)
      · rw [if_pos hP, if_pos ⟨hK.1, hK.2.1, hK.2.2, hP⟩]
        have := one_div_le_one_div_of_le (uu_pos (x := x) A') (uu_mono (x := x) hP.1)
        have hw := wt_nonneg h0.le h1.le A
        nlinarith
      · rw [if_neg hP, if_neg (fun h => hP ⟨h.2.2.2.1, h.2.2.2.2⟩)]; simp
    have hβ : ((1 - q)⁻¹) ^ ((Ls G e).erase c).card ≤ ((1 - q)⁻¹) ^ (ell - 1) := by
      apply pow_le_pow_right₀
      · rw [one_le_inv₀ h1']; linarith
      · rw [Finset.card_erase_of_mem hK.1]
        have := Ls_card ell hadm.1 e
        omega
    calc _ ≤ ∑ A : Finset (SC G), (1 / uu G x A') *
          (if (A' ⊆ A ∧ A \ A' ⊆ (Ls G e).erase c) then wt q A else 0) :=
          Finset.sum_le_sum (fun A _ => hpt A)
      _ = (1 / uu G x A') * ∑ A : Finset (SC G),
          (if (A' ⊆ A ∧ A \ A' ⊆ (Ls G e).erase c) then wt q A else 0) := by
          rw [Finset.mul_sum]
      _ ≤ (1 / uu G x A') * (wt q A' * ((1 - q)⁻¹) ^ ((Ls G e).erase c).card) :=
          mul_le_mul_of_nonneg_left (sum_super h0 h1 A' _) (by have := uu_pos (x := x) A'; positivity)
      _ ≤ (1 / uu G x A') * (wt q A' * ((1 - q)⁻¹) ^ (ell - 1)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hβ (wt_nonneg h0.le h1.le A'))
            (by have := uu_pos (x := x) A'; positivity)
      _ = _ := by ring
  · rw [if_neg hK]
    have : ∀ A : Finset (SC G), wt q A * (1 / uu G x A) *
      (if (c ∈ Ls G e ∧ c ∈ A' ∧ Touch G e (UU G x A' \ UU G x (A'.erase c)) ∧
          A' ⊆ A ∧ A \ A' ⊆ (Ls G e).erase c) then (1 : ℝ) else 0) = 0 := by
      intro A
      rw [if_neg (fun h => hK ⟨h.1, h.2.1, h.2.2.1⟩)]; simp
    calc _ = 0 := Finset.sum_eq_zero (fun A _ => this A)
      _ ≤ _ := by simp

theorem red_bound (hadm : G.Admissible ell delta) (h0 : 0 < q) (h1 : q < 1) :
    (∑ A : Finset (SC G), wt q A *
      ((∑ e, if redInd G x e A then G.weight e else 0) / uu G x A)) ≤
    delta * ((1 - q)⁻¹) ^ (ell - 1) * ∑ A' : Finset (SC G), wt q A' *
      ∑ c : SC G, (if c ∈ A' then (uu G x A' - uu G x (A'.erase c)) / uu G x A' else 0) := by
  set β : ℝ := ((1 - q)⁻¹) ^ (ell - 1) with hβdef
  have h1' : 0 < 1 - q := by linarith
  have hβ0 : 0 ≤ β := by positivity
  calc (∑ A : Finset (SC G), wt q A *
      ((∑ e, if redInd G x e A then G.weight e else 0) / uu G x A))
      = ∑ A : Finset (SC G), ∑ e : E, G.weight e * (wt q A * (1 / uu G x A)) *
          (if redInd G x e A then (1 : ℝ) else 0) := by
        refine Finset.sum_congr rfl (fun A _ => ?_)
        rw [Finset.sum_div, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun e _ => ?_)
        split_ifs <;> ring
    _ ≤ ∑ A : Finset (SC G), ∑ e : E, ∑ c : SC G, ∑ A' : Finset (SC G),
          G.weight e * (wt q A * (1 / uu G x A)) *
          (if (c ∈ Ls G e ∧ c ∈ A' ∧ Touch G e (UU G x A' \ UU G x (A'.erase c)) ∧
          A' ⊆ A ∧ A \ A' ⊆ (Ls G e).erase c) then (1 : ℝ) else 0) := by
        refine Finset.sum_le_sum (fun A _ => Finset.sum_le_sum (fun e _ => ?_))
        have hnn : 0 ≤ G.weight e * (wt q A * (1 / uu G x A)) :=
          mul_nonneg (G.weight_nonneg e)
            (mul_nonneg (wt_nonneg h0.le h1.le A) (by have := uu_pos (x := x) A; positivity))
        calc _ ≤ (G.weight e * (wt q A * (1 / uu G x A))) *
              ∑ c : SC G, ∑ A' : Finset (SC G),
              (if (c ∈ Ls G e ∧ c ∈ A' ∧ Touch G e (UU G x A' \ UU G x (A'.erase c)) ∧
              A' ⊆ A ∧ A \ A' ⊆ (Ls G e).erase c) then (1 : ℝ) else 0) :=
              mul_le_mul_of_nonneg_left (red_pointwise G x e A) hnn
          _ = _ := by simp only [Finset.mul_sum]
    _ = ∑ A' : Finset (SC G), ∑ c : SC G, ∑ e : E, ∑ A : Finset (SC G),
          G.weight e * (wt q A * (1 / uu G x A)) *
          (if (c ∈ Ls G e ∧ c ∈ A' ∧ Touch G e (UU G x A' \ UU G x (A'.erase c)) ∧
          A' ⊆ A ∧ A \ A' ⊆ (Ls G e).erase c) then (1 : ℝ) else 0) :=
        sum4 (fun A e c A' => G.weight e * (wt q A * (1 / uu G x A)) *
          (if (c ∈ Ls G e ∧ c ∈ A' ∧ Touch G e (UU G x A' \ UU G x (A'.erase c)) ∧
          A' ⊆ A ∧ A \ A' ⊆ (Ls G e).erase c) then (1 : ℝ) else 0))
    _ ≤ ∑ A' : Finset (SC G), ∑ c : SC G, (wt q A' / uu G x A') * β *
          (if c ∈ A' then delta * (uu G x A' - uu G x (A'.erase c)) else 0) := by
        refine Finset.sum_le_sum (fun A' _ => Finset.sum_le_sum (fun c _ => ?_))
        have hP : (UU G x (A'.erase c)) ⊆ UU G x A' := UU_mono (Finset.erase_subset _ _)
        calc (∑ e : E, ∑ A : Finset (SC G), G.weight e * (wt q A * (1 / uu G x A)) *
              (if (c ∈ Ls G e ∧ c ∈ A' ∧ Touch G e (UU G x A' \ UU G x (A'.erase c)) ∧
              A' ⊆ A ∧ A \ A' ⊆ (Ls G e).erase c) then (1 : ℝ) else 0))
            ≤ ∑ e : E, G.weight e * ((if (c ∈ Ls G e ∧ c ∈ A' ∧
                Touch G e (UU G x A' \ UU G x (A'.erase c))) then (1 : ℝ) else 0) *
                (wt q A' / uu G x A') * β) := by
              refine Finset.sum_le_sum (fun e _ => ?_)
              calc _ = G.weight e * ∑ A : Finset (SC G), wt q A * (1 / uu G x A) *
                    (if (c ∈ Ls G e ∧ c ∈ A' ∧ Touch G e (UU G x A' \ UU G x (A'.erase c)) ∧
                    A' ⊆ A ∧ A \ A' ⊆ (Ls G e).erase c) then (1 : ℝ) else 0) := by
                    rw [Finset.mul_sum]
                    refine Finset.sum_congr rfl (fun A _ => by ring)
                _ ≤ _ := mul_le_mul_of_nonneg_left (red_key hadm h0 h1 e c A') (G.weight_nonneg e)
          _ = (wt q A' / uu G x A') * β * ∑ e : E,
                (if (c ∈ Ls G e ∧ Touch G e (UU G x A' \ UU G x (A'.erase c)))
                  then G.weight e else 0) * (if c ∈ A' then 1 else 0) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl (fun e _ => ?_)
              by_cases h1 : c ∈ Ls G e <;> by_cases h2 : c ∈ A' <;>
                by_cases h3 : Touch G e (UU G x A' \ UU G x (A'.erase c)) <;> simp [h1, h2, h3] <;> ring
          _ ≤ _ := by
              by_cases hc : c ∈ A'
              · simp only [if_pos hc, mul_one]
                apply mul_le_mul_of_nonneg_left _ (by
                  have := uu_pos (x := x) A'
                  have := wt_nonneg h0.le h1.le A'
                  positivity)
                refine le_trans (touch_bound ell delta hadm c _) ?_
                rw [Finset.card_sdiff_of_subset hP]
                unfold uu
                rw [Nat.cast_sub (Finset.card_le_card hP)]
              · simp [hc]
    _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun A' _ => ?_)
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun c _ => ?_)
        split_ifs
        · field_simp
        · simp

end Red

end WeightedRainbowCycle.Dev.BD
end
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace WeightedRainbowCycle.Dev.BD

open WeightedRainbowCycle.Weighted
open scoped Classical

section Blue

variable {V E C : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  [DecidableEq C] (G : Model V E C) (x : V)

def blueInd (e : E) (A : Finset (SC G)) : Prop :=
  ∃ u v, G.graph.IsLink e u v ∧ u ∈ UU G x A ∧ v ∉ UU G x A ∧ u ∈ UU G x (A \ Ls G e)

def blueTerm (e : E) (c : SC G) (A' : Finset (SC G)) : ℝ :=
  (if Touch G e (UU G x A') then (1 / uu G x A' - 1 / uu G x (insert c A')) else 0) +
  (if Touch G e (UU G x (insert c A') \ UU G x A') then 1 / uu G x (insert c A') else 0)

variable {G x}

theorem inv_uu_anti {A B : Finset (SC G)} (h : A ⊆ B) : 1 / uu G x B ≤ 1 / uu G x A :=
  one_div_le_one_div_of_le (uu_pos A) (uu_mono h)

theorem blueTerm_nonneg (e : E) (c : SC G) (A' : Finset (SC G)) : 0 ≤ blueTerm G x e c A' := by
  have h := inv_uu_anti (x := x) (Finset.subset_insert c A')
  have h2 : 0 < 1 / uu G x (insert c A') := by have := uu_pos (x := x) (insert c A'); positivity
  unfold blueTerm
  split_ifs <;> linarith

theorem blue_pointwise (e : E) (A : Finset (SC G)) :
    (if blueInd G x e A then 1 / uu G x A else 0) ≤
      ∑ c : SC G, ∑ A' : Finset (SC G),
        if (c ∈ Ls G e ∧ c ∉ A' ∧ A ⊆ A' ∧ A' \ A ⊆ Ls G e) then blueTerm G x e c A' else 0 := by
  by_cases hB : blueInd G x e A
  · rw [if_pos hB]
    obtain ⟨u, v, hl, hu, hv, hnu⟩ := hB
    have hch := chain (fun A' : Finset (SC G) => v ∈ UU G x A') (fun A => 1 / uu G x A)
      (fun A B h => inv_uu_anti h)
      (fun A => by have := uu_pos (x := x) A; positivity) (Ls G e \ A) A
      Finset.sdiff_disjoint.symm hv (by
        rw [Finset.union_sdiff_self_eq_union]
        exact UU_extend e A u v hl hnu)
    refine hch.trans ?_
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    refine Finset.sum_le_sum (fun c _ => Finset.sum_le_sum (fun A' _ => ?_))
    by_cases hp : (c, A').1 ∈ Ls G e \ A ∧ A ⊆ (c, A').2 ∧ (c, A').2 ⊆ A ∪ (Ls G e \ A) ∧
        (c, A').1 ∉ (c, A').2
    · obtain ⟨hcM, hAA', hA'sub, hcA'⟩ := hp
      simp only at hcM hAA' hA'sub hcA'
      have hcond : (c ∈ Ls G e ∧ c ∉ A' ∧ A ⊆ A' ∧ A' \ A ⊆ Ls G e) := by
        refine ⟨(Finset.mem_sdiff.1 hcM).1, hcA', hAA', ?_⟩
        intro s hs
        have := hA'sub (Finset.mem_sdiff.1 hs).1
        rw [Finset.mem_union, Finset.mem_sdiff] at this
        rcases this with h | h
        · exact absurd h (Finset.mem_sdiff.1 hs).2
        · exact h.1
      rw [if_pos ⟨hcM, hAA', hA'sub, hcA'⟩, if_pos hcond]
      by_cases hPA : v ∈ UU G x A'
      · unfold stepT
        simp only [hPA, if_true]
        exact blueTerm_nonneg e c A'
      · have hT1 : Touch G e (UU G x A') :=
          ⟨u, v, hl, UU_mono hAA' (UU_mono Finset.sdiff_subset hnu)⟩
        unfold stepT blueTerm
        simp only [hPA, if_false, hT1, if_true]
        by_cases hPI : v ∈ UU G x (insert c A')
        · have hT2 : Touch G e (UU G x (insert c A') \ UU G x A') :=
            ⟨v, u, hl.symm, Finset.mem_sdiff.2 ⟨hPI, hPA⟩⟩
          simp only [hPI, hT2, if_true]; exact le_rfl
        · simp only [hPI, if_false]
          have h := inv_uu_anti (x := x) (Finset.subset_insert c A')
          have h2 : 0 < 1 / uu G x (insert c A') := by
            have := uu_pos (x := x) (insert c A'); positivity
          split_ifs <;> linarith
    · rw [if_neg hp]
      split_ifs
      · exact blueTerm_nonneg e c A'
      · exact le_rfl
  · rw [if_neg hB]
    exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => by
      split_ifs
      · exact blueTerm_nonneg _ _ _
      · exact le_rfl))

variable {ell : ℕ} {delta q : ℝ}

theorem blue_key (hadm : G.Admissible ell delta) (h0 : 0 < q) (h1 : q < 1) (e : E) (c : SC G)
    (A' : Finset (SC G)) :
    (∑ A : Finset (SC G), wt q A *
      (if (c ∈ Ls G e ∧ c ∉ A' ∧ A ⊆ A' ∧ A' \ A ⊆ Ls G e) then blueTerm G x e c A' else 0)) ≤
    (if (c ∈ Ls G e ∧ c ∉ A') then (1 : ℝ) else 0) * blueTerm G x e c A' *
      (wt q A' * (q⁻¹) ^ (ell - 1)) := by
  by_cases hK : (c ∈ Ls G e ∧ c ∉ A')
  · rw [if_pos hK]
    have hpt : ∀ A : Finset (SC G), wt q A *
        (if (c ∈ Ls G e ∧ c ∉ A' ∧ A ⊆ A' ∧ A' \ A ⊆ Ls G e) then blueTerm G x e c A' else 0) =
        blueTerm G x e c A' *
          (if (A ⊆ A' ∧ A' \ A ⊆ (Ls G e).erase c) then wt q A else 0) := by
      intro A
      by_cases hP : (A ⊆ A' ∧ A' \ A ⊆ Ls G e)
      · have hP2 : A' \ A ⊆ (Ls G e).erase c := by
          intro s hs
          rw [Finset.mem_erase]
          refine ⟨?_, hP.2 hs⟩
          rintro rfl
          exact hK.2 (Finset.mem_sdiff.1 hs).1
        rw [if_pos ⟨hK.1, hK.2, hP⟩, if_pos ⟨hP.1, hP2⟩]; ring
      · have : ¬ (A ⊆ A' ∧ A' \ A ⊆ (Ls G e).erase c) := by
          rintro ⟨h1, h2⟩
          exact hP ⟨h1, h2.trans (Finset.erase_subset _ _)⟩
        rw [if_neg (fun h => hP ⟨h.2.2.1, h.2.2.2⟩), if_neg this]; simp
    have hβ : (q⁻¹) ^ ((Ls G e).erase c).card ≤ (q⁻¹) ^ (ell - 1) := by
      apply pow_le_pow_right₀
      · rw [one_le_inv₀ h0]; linarith
      · rw [Finset.card_erase_of_mem hK.1]
        have := Ls_card ell hadm.1 e
        omega
    have hbt := blueTerm_nonneg (x := x) e c A'
    calc _ = ∑ A : Finset (SC G), blueTerm G x e c A' *
          (if (A ⊆ A' ∧ A' \ A ⊆ (Ls G e).erase c) then wt q A else 0) :=
          Finset.sum_congr rfl (fun A _ => hpt A)
      _ = blueTerm G x e c A' * ∑ A : Finset (SC G),
          (if (A ⊆ A' ∧ A' \ A ⊆ (Ls G e).erase c) then wt q A else 0) := by
          rw [Finset.mul_sum]
      _ ≤ blueTerm G x e c A' * (wt q A' * (q⁻¹) ^ ((Ls G e).erase c).card) :=
          mul_le_mul_of_nonneg_left (sum_sub h0 h1 A' _) hbt
      _ ≤ blueTerm G x e c A' * (wt q A' * (q⁻¹) ^ (ell - 1)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hβ (wt_nonneg h0.le h1.le A')) hbt
      _ = _ := by ring
  · rw [if_neg hK]
    have : ∀ A : Finset (SC G), wt q A *
      (if (c ∈ Ls G e ∧ c ∉ A' ∧ A ⊆ A' ∧ A' \ A ⊆ Ls G e) then blueTerm G x e c A' else 0) = 0 := by
      intro A
      rw [if_neg (fun h => hK ⟨h.1, h.2.1⟩)]; simp
    calc _ = 0 := Finset.sum_eq_zero (fun A _ => this A)
      _ ≤ _ := by simp

/-- Sum of the term weights over the edges. -/
theorem blue_edge_sum (hadm : G.Admissible ell delta) (c : SC G) (A' : Finset (SC G))
    (hc : c ∉ A') :
    (∑ e : E, if c ∈ Ls G e then G.weight e * blueTerm G x e c A' else 0) ≤
      2 * delta * ((uu G x (insert c A') - uu G x A') / uu G x (insert c A')) := by
  have hP : UU G x A' ⊆ UU G x (insert c A') := UU_mono (Finset.subset_insert c A')
  have h1 : 0 ≤ 1 / uu G x A' - 1 / uu G x (insert c A') :=
    sub_nonneg.2 (inv_uu_anti (x := x) (Finset.subset_insert c A'))
  have h2 : 0 ≤ 1 / uu G x (insert c A') := by
    have := uu_pos (x := x) (insert c A'); positivity
  have e1 : ∀ e : E, (if c ∈ Ls G e then G.weight e * blueTerm G x e c A' else 0) =
      (1 / uu G x A' - 1 / uu G x (insert c A')) *
        (if (c ∈ Ls G e ∧ Touch G e (UU G x A')) then G.weight e else 0) +
      (1 / uu G x (insert c A')) *
        (if (c ∈ Ls G e ∧ Touch G e (UU G x (insert c A') \ UU G x A')) then G.weight e else 0) := by
    intro e
    unfold blueTerm
    by_cases a1 : c ∈ Ls G e <;> by_cases a2 : Touch G e (UU G x A') <;>
      by_cases a3 : Touch G e (UU G x (insert c A') \ UU G x A') <;> simp [a1, a2, a3] <;> ring
  rw [Finset.sum_congr rfl (fun e _ => e1 e), Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum]
  have b1 := touch_bound ell delta hadm c (UU G x A')
  have b2 := touch_bound ell delta hadm c (UU G x (insert c A') \ UU G x A')
  rw [Finset.card_sdiff_of_subset hP] at b2
  have hu := uu_pos (x := x) A'
  have hu' := uu_pos (x := x) (insert c A')
  have hc2 : ((UU G x (insert c A')).card - (UU G x A').card : ℕ) =
      uu G x (insert c A') - uu G x A' := by
    unfold uu; rw [Nat.cast_sub (Finset.card_le_card hP)]
  rw [hc2] at b2
  have b1' : (∑ e : E, if c ∈ Ls G e ∧ Touch G e (UU G x A') then G.weight e else 0) ≤
      delta * uu G x A' := b1
  calc _ ≤ (1 / uu G x A' - 1 / uu G x (insert c A')) * (delta * uu G x A') +
        (1 / uu G x (insert c A')) * (delta * (uu G x (insert c A') - uu G x A')) :=
        add_le_add (mul_le_mul_of_nonneg_left b1' h1) (mul_le_mul_of_nonneg_left b2 h2)
    _ = _ := by field_simp; ring

theorem blue_bound (hadm : G.Admissible ell delta) (h0 : 0 < q) (h1 : q < 1) :
    (∑ A : Finset (SC G), wt q A *
      ((∑ e, if blueInd G x e A then G.weight e else 0) / uu G x A)) ≤
    2 * delta * (q⁻¹) ^ (ell - 1) * ∑ A' : Finset (SC G), wt q A' *
      ∑ c : SC G, (if c ∉ A' then
        (uu G x (insert c A') - uu G x A') / uu G x (insert c A') else 0) := by
  set β : ℝ := (q⁻¹) ^ (ell - 1) with hβdef
  calc (∑ A : Finset (SC G), wt q A *
      ((∑ e, if blueInd G x e A then G.weight e else 0) / uu G x A))
      = ∑ A : Finset (SC G), ∑ e : E, G.weight e * wt q A *
          (if blueInd G x e A then 1 / uu G x A else 0) := by
        refine Finset.sum_congr rfl (fun A _ => ?_)
        rw [Finset.sum_div, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun e _ => ?_)
        split_ifs <;> ring
    _ ≤ ∑ A : Finset (SC G), ∑ e : E, ∑ c : SC G, ∑ A' : Finset (SC G),
          G.weight e * (wt q A *
          (if (c ∈ Ls G e ∧ c ∉ A' ∧ A ⊆ A' ∧ A' \ A ⊆ Ls G e) then blueTerm G x e c A' else 0)) := by
        refine Finset.sum_le_sum (fun A _ => Finset.sum_le_sum (fun e _ => ?_))
        have hnn : 0 ≤ G.weight e * wt q A :=
          mul_nonneg (G.weight_nonneg e) (wt_nonneg h0.le h1.le A)
        calc _ ≤ (G.weight e * wt q A) * ∑ c : SC G, ∑ A' : Finset (SC G),
              (if (c ∈ Ls G e ∧ c ∉ A' ∧ A ⊆ A' ∧ A' \ A ⊆ Ls G e) then blueTerm G x e c A'
                else 0) := mul_le_mul_of_nonneg_left (blue_pointwise e A) hnn
          _ = _ := by
            simp only [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun A' _ => ?_))
            ring
    _ = ∑ A' : Finset (SC G), ∑ c : SC G, ∑ e : E, ∑ A : Finset (SC G),
          G.weight e * (wt q A *
          (if (c ∈ Ls G e ∧ c ∉ A' ∧ A ⊆ A' ∧ A' \ A ⊆ Ls G e) then blueTerm G x e c A' else 0)) :=
        sum4 (fun A e c A' => G.weight e * (wt q A *
          (if (c ∈ Ls G e ∧ c ∉ A' ∧ A ⊆ A' ∧ A' \ A ⊆ Ls G e) then blueTerm G x e c A' else 0)))
    _ ≤ ∑ A' : Finset (SC G), ∑ c : SC G, wt q A' * β *
          (if c ∉ A' then 2 * delta * ((uu G x (insert c A') - uu G x A') /
            uu G x (insert c A')) else 0) := by
        refine Finset.sum_le_sum (fun A' _ => Finset.sum_le_sum (fun c _ => ?_))
        calc (∑ e : E, ∑ A : Finset (SC G), G.weight e * (wt q A *
          (if (c ∈ Ls G e ∧ c ∉ A' ∧ A ⊆ A' ∧ A' \ A ⊆ Ls G e) then blueTerm G x e c A' else 0)))
            ≤ ∑ e : E, G.weight e * ((if (c ∈ Ls G e ∧ c ∉ A') then (1 : ℝ) else 0) *
                blueTerm G x e c A' * (wt q A' * β)) := by
              refine Finset.sum_le_sum (fun e _ => ?_)
              rw [← Finset.mul_sum]
              exact mul_le_mul_of_nonneg_left (blue_key hadm h0 h1 e c A') (G.weight_nonneg e)
          _ = wt q A' * β * ∑ e : E, (if c ∉ A' then
                (if c ∈ Ls G e then G.weight e * blueTerm G x e c A' else 0) else 0) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl (fun e _ => ?_)
              by_cases h1 : c ∈ Ls G e <;> by_cases h2 : c ∈ A' <;> simp [h1, h2] <;> ring
          _ ≤ _ := by
              by_cases hc : c ∈ A'
              · simp [hc]
              · simp only [if_pos hc]
                exact mul_le_mul_of_nonneg_left (blue_edge_sum hadm c A' hc)
                  (mul_nonneg (wt_nonneg h0.le h1.le A') (by positivity))
    _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun A' _ => ?_)
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun c _ => ?_)
        split_ifs <;> ring

end Blue

end WeightedRainbowCycle.Dev.BD
end
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace WeightedRainbowCycle.Dev.BD

open WeightedRainbowCycle.Weighted DiffNeighbors.Bias
open scoped Classical

section Final

variable {V E C : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  [DecidableEq C] (G : Model V E C) (x : V)

theorem sampled_eq (z : SC G → Bool) : G.sampledColors z = toSet G (trueSet z) := by
  ext c
  simp [Model.sampledColors, toSet, trueSet]

theorem trueSet_update_true (z : SC G → Bool) (c : SC G) :
    trueSet (Function.update z c true) = insert c (trueSet z) := by
  ext s
  by_cases h : s = c <;> simp [trueSet, Function.update, h]

theorem trueSet_update_false (z : SC G → Bool) (c : SC G) :
    trueSet (Function.update z c false) = (trueSet z).erase c := by
  ext s
  by_cases h : s = c <;> simp [trueSet, Function.update, h]

variable {G x}

theorem logReach_eq (z : SC G → Bool) : G.logReach x z = Real.log (uu G x (trueSet z)) := by
  unfold Model.logReach uu UU
  rw [sampled_eq]

theorem boundaryRatio_eq (z : SC G → Bool) :
    G.boundaryRatio x z = G.boundaryMass (UU G x (trueSet z)) / uu G x (trueSet z) := by
  unfold Model.boundaryRatio uu UU
  rw [sampled_eq]

/-- The Russo-Margulis derivative as a sum over subsets. -/
theorem deriv_eq (q : ℝ) :
    deriv (fun p => bernExp p (G.logReach x)) q =
      ∑ A : Finset (SC G), wt q A *
        ∑ c : SC G, (Real.log (uu G x (insert c A)) - Real.log (uu G x (A.erase c))) := by
  rw [(russo_margulis (G.logReach x) q).deriv]
  refine bernExp_eq_sum q _ _ (fun z => ?_)
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [logReach_eq, logReach_eq, trueSet_update_true, trueSet_update_false]

theorem expect_eq (q : ℝ) :
    bernExp q (G.boundaryRatio x) = ∑ A : Finset (SC G), wt q A *
      (G.boundaryMass (UU G x A) / uu G x A) :=
  bernExp_eq_sum q _ _ (fun z => boundaryRatio_eq z)

theorem boundary_split (A : Finset (SC G)) :
    G.boundaryMass (UU G x A) ≤ (∑ e, if redInd G x e A then G.weight e else 0) +
      ∑ e, if blueInd G x e A then G.weight e else 0 := by
  unfold Model.boundaryMass
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun e _ => ?_)
  by_cases hb : ∃ u ∈ UU G x A, ∃ v, v ∉ UU G x A ∧ G.graph.IsLink e u v
  · rw [if_pos hb]
    obtain ⟨u, hu, v, hv, hl⟩ := hb
    by_cases hn : u ∈ UU G x (A \ Ls G e)
    · have : blueInd G x e A := ⟨u, v, hl, hu, hv, hn⟩
      rw [if_pos this]
      have : 0 ≤ (if redInd G x e A then G.weight e else 0) := by
        split_ifs; exact G.weight_nonneg e; exact le_rfl
      linarith
    · have : redInd G x e A := ⟨u, v, hl, hu, hv, hn⟩
      rw [if_pos this]
      have : 0 ≤ (if blueInd G x e A then G.weight e else 0) := by
        split_ifs; exact G.weight_nonneg e; exact le_rfl
      linarith
  · rw [if_neg hb]
    have h1 : 0 ≤ (if redInd G x e A then G.weight e else 0) := by
      split_ifs; exact G.weight_nonneg e; exact le_rfl
    have h2 : 0 ≤ (if blueInd G x e A then G.weight e else 0) := by
      split_ifs; exact G.weight_nonneg e; exact le_rfl
    linarith

theorem frac_le_log {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : (a - b) / a ≤ Real.log a - Real.log b := by
  have := Real.one_sub_inv_le_log_of_pos (x := a / b) (div_pos ha hb)
  rw [Real.log_div ha.ne' hb.ne'] at this
  have e : 1 - (a / b)⁻¹ = (a - b) / a := by field_simp
  linarith [e]

theorem red_log {q : ℝ} (h0 : 0 < q) (h1 : q < 1) :
    (∑ A' : Finset (SC G), wt q A' *
      ∑ c : SC G, (if c ∈ A' then (uu G x A' - uu G x (A'.erase c)) / uu G x A' else 0)) ≤
    q * ∑ A : Finset (SC G), wt q A *
        ∑ c : SC G, (Real.log (uu G x (insert c A)) - Real.log (uu G x (A.erase c))) := by
  calc _ ≤ ∑ A' : Finset (SC G), wt q A' *
        ∑ c : SC G, (if c ∈ A' then (Real.log (uu G x A') - Real.log (uu G x (A'.erase c)))
          else 0) := by
        refine Finset.sum_le_sum (fun A' _ => mul_le_mul_of_nonneg_left ?_ (wt_nonneg h0.le h1.le A'))
        refine Finset.sum_le_sum (fun c _ => ?_)
        split_ifs
        · exact frac_le_log (uu_pos _) (uu_pos _)
        · exact le_rfl
    _ = ∑ c : SC G, ∑ A : Finset (SC G), if c ∈ A then wt q A *
          (Real.log (uu G x (insert c A)) - Real.log (uu G x (A.erase c))) else 0 := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun A _ => ?_))
        by_cases h : c ∈ A
        · simp [h, Finset.insert_eq_of_mem h]
        · simp [h]
    _ = ∑ c : SC G, q * ∑ A : Finset (SC G), wt q A *
          (Real.log (uu G x (insert c A)) - Real.log (uu G x (A.erase c))) := by
        refine Finset.sum_congr rfl (fun c _ => ?_)
        exact (sum_toggle h0 h1 c (fun A => Real.log (uu G x (insert c A)) -
          Real.log (uu G x (A.erase c))) (fun A => by simp)).1
    _ = _ := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp only [Finset.mul_sum]

theorem blue_log {q : ℝ} (h0 : 0 < q) (h1 : q < 1) :
    (∑ A' : Finset (SC G), wt q A' *
      ∑ c : SC G, (if c ∉ A' then
        (uu G x (insert c A') - uu G x A') / uu G x (insert c A') else 0)) ≤
    (1 - q) * ∑ A : Finset (SC G), wt q A *
        ∑ c : SC G, (Real.log (uu G x (insert c A)) - Real.log (uu G x (A.erase c))) := by
  calc _ ≤ ∑ A' : Finset (SC G), wt q A' *
        ∑ c : SC G, (if c ∉ A' then (Real.log (uu G x (insert c A')) -
          Real.log (uu G x (A'.erase c))) else 0) := by
        refine Finset.sum_le_sum (fun A' _ => mul_le_mul_of_nonneg_left ?_ (wt_nonneg h0.le h1.le A'))
        refine Finset.sum_le_sum (fun c _ => ?_)
        by_cases h : c ∈ A'
        · simp [h]
        · rw [if_pos h, if_pos h, Finset.erase_eq_of_notMem h]
          exact frac_le_log (uu_pos _) (uu_pos _)
    _ = ∑ c : SC G, ∑ A : Finset (SC G), if c ∉ A then wt q A *
          (Real.log (uu G x (insert c A)) - Real.log (uu G x (A.erase c))) else 0 := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun A _ => ?_))
        by_cases h : c ∈ A <;> simp [h]
    _ = ∑ c : SC G, (1 - q) * ∑ A : Finset (SC G), wt q A *
          (Real.log (uu G x (insert c A)) - Real.log (uu G x (A.erase c))) := by
        refine Finset.sum_congr rfl (fun c _ => ?_)
        exact (sum_toggle h0 h1 c (fun A => Real.log (uu G x (insert c A)) -
          Real.log (uu G x (A.erase c))) (fun A => by simp)).2
    _ = _ := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp only [Finset.mul_sum]

theorem main {ell : ℕ} {delta : ℝ} (hdelta : 0 ≤ delta) (hadm : G.Admissible ell delta)
    {q : ℝ} (h0 : 0 < q) (h1 : q < 1) :
    bernExp q (G.boundaryRatio x) ≤
      delta * (q / (1 - q) ^ (ell - 1) + 2 * (1 - q) / q ^ (ell - 1)) *
        deriv (fun p => bernExp p (G.logReach x)) q := by
  have h1' : 0 < 1 - q := by linarith
  rw [expect_eq, deriv_eq]
  set D := ∑ A : Finset (SC G), wt q A *
        ∑ c : SC G, (Real.log (uu G x (insert c A)) - Real.log (uu G x (A.erase c))) with hD
  have hsplit : (∑ A : Finset (SC G), wt q A * (G.boundaryMass (UU G x A) / uu G x A)) ≤
      (∑ A : Finset (SC G), wt q A *
        ((∑ e, if redInd G x e A then G.weight e else 0) / uu G x A)) +
      ∑ A : Finset (SC G), wt q A *
        ((∑ e, if blueInd G x e A then G.weight e else 0) / uu G x A) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun A _ => ?_)
    rw [← mul_add, ← add_div]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (boundary_split A)
      (uu_pos A).le) (wt_nonneg h0.le h1.le A)
  have hr := (red_bound hadm h0 h1 (x := x)).trans
    (mul_le_mul_of_nonneg_left (red_log h0 h1 (x := x)) (by positivity :
      0 ≤ delta * ((1 - q)⁻¹) ^ (ell - 1)))
  have hb := (blue_bound hadm h0 h1 (x := x)).trans
    (mul_le_mul_of_nonneg_left (blue_log h0 h1 (x := x)) (by positivity :
      0 ≤ 2 * delta * (q⁻¹) ^ (ell - 1)))
  refine hsplit.trans ((add_le_add hr hb).trans (le_of_eq ?_))
  rw [← hD]
  rw [inv_pow, inv_pow]
  field_simp

end Final

end WeightedRainbowCycle.Dev.BD

namespace WeightedRainbowCycle.Weighted

theorem chk_boundary_derivative {V E C : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] [DecidableEq C]
    (G : Model V E C) (ell : ℕ) (hell : 1 ≤ ell) (delta : ℝ) (hdelta : 0 ≤ delta)
    (hadm : G.Admissible ell delta) (x : V) (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    DiffNeighbors.Bias.bernExp q (G.boundaryRatio x) ≤
      delta * (q / (1 - q) ^ (ell - 1) + 2 * (1 - q) / q ^ (ell - 1)) *
        deriv (fun p => DiffNeighbors.Bias.bernExp p (G.logReach x)) q :=
  Dev.BD.main hdelta hadm hq0 hq1

end WeightedRainbowCycle.Weighted
end
end

theorem solution : type_of% @WeightedRainbowCycle.Weighted.chk_boundary_derivative := @WeightedRainbowCycle.Weighted.chk_boundary_derivative
