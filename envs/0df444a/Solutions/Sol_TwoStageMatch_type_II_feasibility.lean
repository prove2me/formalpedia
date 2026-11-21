-- Prove2me | solution 1 for TwoStageMatch.type_II_feasibility
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T04:21:25.691788+00:00
-- url     : https://prove2.me/submissions/3fe310e4-77ee-499a-888a-7cd2d78760c5

import Mathlib
import Definitions.Def_TwoStageMatch_Algorithm1
import Definitions.Def_TwoStageMatch_DualAssignment

namespace Aux_TSM_typeII

open TwoStageMatch

variable {D₁ D₂ S : Type*} [Fintype D₁] [Fintype D₂] [Fintype S]
  [DecidableEq D₁] [DecidableEq D₂] [DecidableEq S]

lemma ind_matched (I : Instance D₁ D₂ S) (M : Finset ((D₁ ⊕ D₂) × S))
    (hM : IsFirstStageMatching I M) (j : S) :
    (if j ∈ matchedSupply M then (1 : ℝ) else 0) =
      ∑ i : D₁, (if ((Sum.inl i : D₁ ⊕ D₂), j) ∈ M then (1 : ℝ) else 0) := by
  have hM' : IsMatching I.E firstStage Finset.univ M := hM
  obtain ⟨hE, _, hsnd⟩ := hM'
  by_cases h : ∃ i : D₁, ((Sum.inl i : D₁ ⊕ D₂), j) ∈ M
  · obtain ⟨i, hi⟩ := h
    have hj : j ∈ matchedSupply M := Finset.mem_image.2 ⟨_, hi, rfl⟩
    rw [if_pos hj, Finset.sum_eq_single i]
    · rw [if_pos hi]
    · intro i' _ hi'
      have hn : ((Sum.inl i' : D₁ ⊕ D₂), j) ∉ M := by
        intro hmem
        have h1 := hsnd _ hmem _ hi rfl
        have h2 : (Sum.inl i' : D₁ ⊕ D₂) = Sum.inl i := congrArg Prod.fst h1
        exact hi' (Sum.inl_injective h2)
      rw [if_neg hn]
    · intro hn
      exact absurd (Finset.mem_univ i) hn
  · push_neg at h
    have hj : j ∉ matchedSupply M := by
      intro hj
      obtain ⟨e, he, hej⟩ := Finset.mem_image.1 hj
      obtain ⟨_, he1, _⟩ := hE e he
      unfold firstStage at he1
      obtain ⟨i, _, hi⟩ := Finset.mem_image.1 he1
      apply h i
      have : e = ((Sum.inl i : D₁ ⊕ D₂), j) := Prod.ext hi.symm hej
      rw [← this]
      exact he
    rw [if_neg hj]
    symm
    apply Finset.sum_eq_zero
    intro i _
    rw [if_neg (h i)]

lemma marg (I : Instance D₁ D₂ S) (x : D₁ → S → ℝ) (ρ : Finset ((D₁ ⊕ D₂) × S) → ℝ)
    (hx : IsFeasible I x) (hρ : IsRounding I x ρ) (j : S) :
    ∑ M, ρ M * (if j ∈ matchedSupply M then (1 : ℝ) else 0) = load x j := by
  obtain ⟨_, _, hsupp, hmarg⟩ := hρ
  have h1 : ∀ M, ρ M * (if j ∈ matchedSupply M then (1 : ℝ) else 0) =
      ∑ i : D₁, ρ M * (if ((Sum.inl i : D₁ ⊕ D₂), j) ∈ M then (1 : ℝ) else 0) := by
    intro M
    by_cases hM : ρ M = 0
    · rw [hM, zero_mul]
      symm
      exact Finset.sum_eq_zero (fun i _ => zero_mul _)
    · rw [ind_matched I M (hsupp M hM) j, Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun M _ => h1 M), Finset.sum_comm]
  unfold load
  apply Finset.sum_congr rfl
  intro i _
  by_cases hE : I.E (Sum.inl i) j
  · rw [← hmarg i j hE, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro M _
    by_cases h : ((Sum.inl i : D₁ ⊕ D₂), j) ∈ M
    · rw [if_pos h, if_pos h, mul_one]
    · rw [if_neg h, if_neg h, mul_zero]
  · rw [hx.2.1 i j hE]
    apply Finset.sum_eq_zero
    intro M _
    by_cases h : ((Sum.inl i : D₁ ⊕ D₂), j) ∈ M
    · have hM : ρ M = 0 := by
        by_contra hM
        have h3 := (hsupp M hM).1 _ h
        exact hE h3.1
      rw [hM, zero_mul]
    · rw [if_neg h, mul_zero]

lemma unmatched_ind (M : Finset ((D₁ ⊕ D₂) × S)) (j : S) :
    (if j ∈ Finset.univ \ matchedSupply M then (1 : ℝ) else 0) =
      1 - (if j ∈ matchedSupply M then (1 : ℝ) else 0) := by
  by_cases h : j ∈ matchedSupply M
  · have h' : j ∉ Finset.univ \ matchedSupply M := fun h'' => (Finset.mem_sdiff.1 h'').2 h
    rw [if_neg h', if_pos h]
    ring
  · have h' : j ∈ Finset.univ \ matchedSupply M := Finset.mem_sdiff.2 ⟨Finset.mem_univ _, h⟩
    rw [if_pos h', if_neg h]
    ring

lemma three_quarter (w y : ℝ) (hw : 0 ≤ w) : (3 / 4 : ℝ) * w ≤ w * (1 - y) + w * y ^ 2 := by
  have h := mul_nonneg hw (sq_nonneg (y - 1 / 2))
  nlinarith [h]

end Aux_TSM_typeII

open TwoStageMatch Aux_TSM_typeII in
theorem solution {D₁ D₂ S : Type*} [Fintype D₁] [Fintype D₂] [Fintype S]
    [DecidableEq D₁] [DecidableEq D₂] [DecidableEq S]
    (I : Instance D₁ D₂ S) (g : ℝ → ℝ) (hgd : Differentiable ℝ g) (hgm : Monotone g)
    (hgc : StrictConvexOn ℝ Set.univ g) (hw : ∀ j, 0 < I.w j) (r : Run I g) (A : Finset D₂)
    (αh : Finset ((D₁ ⊕ D₂) × S) → D₁ ⊕ D₂ → ℝ) (βh : Finset ((D₁ ⊕ D₂) × S) → S → ℝ)
    (hopt : ∀ M, IsFirstStageMatching I M →
      IsDualFeasible I.E I.w (secondStage A) (Finset.univ \ matchedSupply M) (αh M) (βh M) ∧
      dualObj (secondStage A) (Finset.univ \ matchedSupply M) (αh M) (βh M) =
        maxWeightMatch I.E I.w (secondStage A) (Finset.univ \ matchedSupply M)) :
    ∀ i ∈ A, ∀ j, I.E (Sum.inr i) j →
      ∑ M, r.ρ M * (I.w j * (if j ∈ Finset.univ \ matchedSupply M then 1 else 0) +
            I.w j * (load r.x j) ^ 2) ≤
          ∑ M, r.ρ M * (dualAlpha I r.x (αh M) (Sum.inr i) + dualBeta I r.x M (βh M) j) ∧
        ∑ M, r.ρ M * (I.w j * (if j ∈ Finset.univ \ matchedSupply M then 1 else 0) +
            I.w j * (load r.x j) ^ 2) =
          I.w j * (1 - load r.x j) + I.w j * (load r.x j) ^ 2 ∧
        (3 / 4 : ℝ) * I.w j ≤ I.w j * (1 - load r.x j) + I.w j * (load r.x j) ^ 2 := by
  intro i hi j hij
  have hρ := r.ρ_rounding
  have hx := r.x_opt.1
  have hiX : (Sum.inr i : D₁ ⊕ D₂) ∈ secondStage A := by
    unfold secondStage
    exact Finset.mem_image.2 ⟨i, hi, rfl⟩
  refine ⟨?_, ?_, three_quarter (I.w j) (load r.x j) (hw j).le⟩
  · apply Finset.sum_le_sum
    intro M _
    by_cases hM0 : r.ρ M = 0
    · rw [hM0, zero_mul, zero_mul]
    · have hMm : IsFirstStageMatching I M := hρ.2.2.1 M hM0
      obtain ⟨⟨hα0, hβ0, hedge⟩, _⟩ := hopt M hMm
      apply mul_le_mul_of_nonneg_left _ (hρ.1 M)
      have hA : dualAlpha I r.x (αh M) (Sum.inr i) = αh M (Sum.inr i) := rfl
      have hB : dualBeta I r.x M (βh M) j = I.w j * (load r.x j) ^ 2 +
          (if j ∈ Finset.univ \ matchedSupply M then βh M j else 0) := rfl
      rw [hA, hB]
      by_cases hj : j ∈ Finset.univ \ matchedSupply M
      · rw [if_pos hj, if_pos hj]
        have h1 : I.w j ≤ αh M (Sum.inr i) + βh M j := hedge _ hiX j hj hij
        linarith
      · rw [if_neg hj, if_neg hj]
        have h1 : 0 ≤ αh M (Sum.inr i) := hα0 _ hiX
        linarith
  · have key : ∑ M, r.ρ M * (I.w j * (if j ∈ Finset.univ \ matchedSupply M then 1 else 0) +
            I.w j * (load r.x j) ^ 2) =
        ∑ M, (r.ρ M * (I.w j + I.w j * (load r.x j) ^ 2) -
          I.w j * (r.ρ M * (if j ∈ matchedSupply M then (1 : ℝ) else 0))) := by
      apply Finset.sum_congr rfl
      intro M _
      rw [unmatched_ind M j]
      ring
    rw [key, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hρ.2.1,
      marg I r.x r.ρ hx hρ j]
    ring
