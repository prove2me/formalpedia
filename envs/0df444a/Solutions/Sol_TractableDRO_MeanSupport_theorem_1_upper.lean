-- Prove2me | solution 1 for TractableDRO.MeanSupport.theorem_1_upper
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T06:52:15.864364+00:00
-- url     : https://prove2.me/submissions/6a352048-1043-4a8a-bdca-4706af830985

import Mathlib
import Definitions.Def_TractableDRO_MeanSupport_Model

open MeasureTheory TractableDRO.MeanSupport
open scoped BigOperators

private theorem int_dot {n : ℕ} (P : Measure (Fin n → ℝ)) (s : Fin n → ℝ)
    (hi : ∀ i, Integrable (fun z : Fin n → ℝ => z i) P) :
    Integrable (fun z => s ⬝ᵥ z) P ∧
      (∫ z, s ⬝ᵥ z ∂P) = s ⬝ᵥ MomentDRO.Conf.meanVec P := by
  constructor
  · exact integrable_finsetSum _ (fun i _ => (hi i).const_mul (s i))
  · simp only [dotProduct, MomentDRO.Conf.meanVec]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i _
      exact integral_const_mul _ _
    · intro i _
      exact (hi i).const_mul _

theorem solution {n : ℕ} (V Vhat : Set (Fin n → ℝ)) (r0 : ℝ) (r : Fin n → ℝ) :
    worstCase (family1 V Vhat) r0 r ≤ pi1 V Vhat r0 r := by
  classical
  unfold worstCase pi1
  apply iSup_le
  intro P
  apply iSup_le
  intro hP
  obtain ⟨hprob, hi, hmean, hsupp⟩ := hP
  letI := hprob
  apply le_iInf
  intro s
  let A : EReal := ⨆ z ∈ Vhat, ((s ⬝ᵥ z : ℝ) : EReal)
  let B : EReal := ⨆ z ∈ V,
    ((max (r0 + r ⬝ᵥ z - s ⬝ᵥ z) (-(s ⬝ᵥ z)) : ℝ) : EReal)
  change (expPos P r0 r : EReal) ≤ A + B
  have hA : ((s ⬝ᵥ MomentDRO.Conf.meanVec P : ℝ) : EReal) ≤ A :=
    le_iSup_of_le _ (le_iSup_of_le hmean le_rfl)
  obtain ⟨z, hz⟩ := hsupp.exists
  have hB : ((max (r0 + r ⬝ᵥ z - s ⬝ᵥ z) (-(s ⬝ᵥ z)) : ℝ) : EReal) ≤ B :=
    le_iSup_of_le _ (le_iSup_of_le hz le_rfl)
  have hAn : A ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hA
  have hBn : B ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hB
  by_cases hAt : A = ⊤
  · rw [hAt, EReal.top_add_of_ne_bot hBn]
    exact le_top
  by_cases hBt : B = ⊤
  · rw [hBt, EReal.add_top_of_ne_bot hAn]
    exact le_top
  have hAe := EReal.coe_toReal hAt hAn
  have hBe := EReal.coe_toReal hBt hBn
  have hbound : ∀ᵐ z ∂P, max (r0 + r ⬝ᵥ z) 0 ≤ s ⬝ᵥ z + B.toReal := by
    filter_upwards [hsupp] with z hz
    have hb : ((max (r0 + r ⬝ᵥ z - s ⬝ᵥ z) (-(s ⬝ᵥ z)) : ℝ) : EReal) ≤ B :=
      le_iSup_of_le _ (le_iSup_of_le hz le_rfl)
    rw [← hBe, EReal.coe_le_coe_iff] at hb
    have hb1 := (le_max_left (r0 + r ⬝ᵥ z - s ⬝ᵥ z) (-(s ⬝ᵥ z))).trans hb
    have hb2 := (le_max_right (r0 + r ⬝ᵥ z - s ⬝ᵥ z) (-(s ⬝ᵥ z))).trans hb
    apply max_le <;> linarith
  have hir := (int_dot P r hi).1
  have his := (int_dot P s hi).1
  have hip : Integrable (fun z => max (r0 + r ⬝ᵥ z) 0) P :=
    ((integrable_const r0).add hir).sup (integrable_const 0)
  have hiu : Integrable (fun z => s ⬝ᵥ z + B.toReal) P :=
    his.add (integrable_const _)
  have hb := integral_mono_ae hip hiu hbound
  have he : (∫ z, s ⬝ᵥ z + B.toReal ∂P) =
      s ⬝ᵥ MomentDRO.Conf.meanVec P + B.toReal := by
    rw [integral_add his (integrable_const _), (int_dot P s hi).2]
    simp
  rw [he] at hb
  have ha : s ⬝ᵥ MomentDRO.Conf.meanVec P ≤ A.toReal := by
    rw [← hAe, EReal.coe_le_coe_iff] at hA
    exact hA
  rw [← hAe, ← hBe, ← EReal.coe_add, EReal.coe_le_coe_iff]
  dsimp [expPos]
  linarith

#print axioms solution
