-- Prove2me | solution 1 for PI.ProdFormulaE.HaarBox.image_toLin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:25:33.387101+00:00
-- url     : https://prove2.me/submissions/1252b328-bfe1-4fb0-8c77-6ad64e02f0d8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_HaarBox
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_NormMod
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ResCharIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_HaarMain
import Theorems.Thm_P2M_PI_ProdFormulaE_HaarBox_modF_nonneg__f21040a49df2
import Theorems.Thm_PI_ProdFormulaE_HaarBox_coe_equivOfDet
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_PI_ProdFormulaE_HaarBox_image_eq_of_box
import Theorems.Thm_PI_ProdFormulaE_modF_mul
import Theorems.Thm_PI_ProdFormulaE_modF_of_ne
import Theorems.Thm_PI_ProdFormulaE_modF_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


section
noncomputable section
open MeasureTheory Measure ValuativeRel Topology Module
open scoped NNReal ENNReal Pointwise
namespace PI.ProdFormulaE.HaarBox
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {E : Type} [AddCommGroup E] [Module K E] [TopologicalSpace E] [IsModuleTopology K E]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable [MeasurableSpace E] [BorelSpace E]
private theorem measure_toLin_mul_image_of_forall (b : Basis ι K E) (μ : Measure E) (A B : Matrix ι ι K)
    (hA : ∀ S : Set E, μ (Matrix.toLin b b A '' S) = ENNReal.ofReal (modF K A.det) * μ S)
    (hB : ∀ S : Set E, μ (Matrix.toLin b b B '' S) = ENNReal.ofReal (modF K B.det) * μ S)
    (S : Set E) :
    μ (Matrix.toLin b b (A * B) '' S) = ENNReal.ofReal (modF K (A * B).det) * μ S := by
  rw [Matrix.toLin_mul b b b, LinearMap.coe_comp, Set.image_comp, hA, hB, Matrix.det_mul, modF_mul,
    ENNReal.ofReal_mul (modF_nonneg' _), mul_assoc]
private theorem measure_toLin_transvection_image (b : Basis ι K E) (μ : Measure E) [μ.IsAddHaarMeasure]
    (htrans : TransvBox b) (t : Matrix.TransvectionStruct ι K) (S : Set E) :
    μ (Matrix.toLin b b t.toMatrix '' S) = ENNReal.ofReal (modF K t.toMatrix.det) * μ S := by
  obtain ⟨γ, hγ, himg⟩ := htrans t
  have hdet : t.toMatrix.det ≠ 0 := by rw [Matrix.TransvectionStruct.det]; exact one_ne_zero
  rw [Matrix.TransvectionStruct.det, modF_one, ENNReal.ofReal_one, one_mul]
  have h := image_eq_of_box b μ (equivOfDet b t.toMatrix hdet) γ hγ 1
    (by rw [coe_equivOfDet, himg, one_mul]) S
  rwa [coe_equivOfDet, one_mul] at h
private theorem measure_toLin_diagonal_update_image (b : Basis ι K E) (μ : Measure E) [μ.IsAddHaarMeasure]
    (hscale : ScaleBox b μ) (i : ι) (a : K) (ha : a ≠ 0) (S : Set E) :
    μ (Matrix.toLin b b (Matrix.diagonal (Function.update 1 i a)) '' S) =
      ENNReal.ofReal (modF K (Matrix.diagonal (Function.update (1 : ι → K) i a)).det) * μ S := by
  have hdetv : (Matrix.diagonal (Function.update (1 : ι → K) i a)).det = a := by
    rw [Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ i)]
    simp
  have hdet : (Matrix.diagonal (Function.update (1 : ι → K) i a)).det ≠ 0 := by
    rw [hdetv]
    exact ha
  rw [hdetv, modF_of_ne ha, ENNReal.ofReal_coe_nnreal]
  have h := image_eq_of_box b μ (equivOfDet b _ hdet) 1 (fun _ => by simp) _
    (by rw [coe_equivOfDet]; exact hscale i a ha) S
  rwa [coe_equivOfDet] at h
private theorem measure_toLin_diagonal_image (b : Basis ι K E) (μ : Measure E) [μ.IsAddHaarMeasure]
    (hscale : ScaleBox b μ) (D : ι → K) (hD : ∀ i, D i ≠ 0) (S : Set E) :
    μ (Matrix.toLin b b (Matrix.diagonal D) '' S) =
      ENNReal.ofReal (modF K (Matrix.diagonal D).det) * μ S := by
  classical
  suffices h : ∀ s : Finset ι, ∀ D : ι → K, (∀ i, D i ≠ 0) → (∀ i ∉ s, D i = 1) → ∀ S : Set E,
      μ (Matrix.toLin b b (Matrix.diagonal D) '' S) =
        ENNReal.ofReal (modF K (Matrix.diagonal D).det) * μ S from
    h Finset.univ D hD (fun i hi => absurd (Finset.mem_univ i) hi) S
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro D _ h1 S
    have hD1 : D = 1 := funext fun i => h1 i (by simp)
    subst hD1
    have h1' : Matrix.diagonal (1 : ι → K) = 1 := Matrix.diagonal_one
    rw [h1', Matrix.toLin_one, LinearMap.id_coe, Set.image_id, Matrix.det_one, modF_one,
      ENNReal.ofReal_one, one_mul]
  | insert j s hj ih =>
    intro D h0 h1 S
    have hsplit : Matrix.diagonal D = Matrix.diagonal (Function.update D j 1) *
        Matrix.diagonal (Function.update 1 j (D j)) := by
      rw [Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      by_cases h : i = j
      · subst h; simp
      · simp [Function.update_of_ne h]
    rw [hsplit]
    refine measure_toLin_mul_image_of_forall b μ _ _ (ih _ ?_ ?_) (measure_toLin_diagonal_update_image b μ hscale j (D j) (h0 j)) S
    · intro i
      by_cases h : i = j
      · subst h; simp
      · simp [Function.update_of_ne h, h0 i]
    · intro i hi
      by_cases h : i = j
      · subst h; simp
      · rw [Function.update_of_ne h]
        exact h1 i (by simp [h, hi])
end PI.ProdFormulaE.HaarBox
namespace PI.ProdFormulaE.HaarAlgP
open HaarBox
end PI.ProdFormulaE.HaarAlgP
end
end

set_option autoImplicit false
noncomputable section
open MeasureTheory Measure ValuativeRel Topology Module
open scoped NNReal ENNReal Pointwise
open PI PI.ProdFormulaE PI.ProdFormulaE.HaarBox
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {E : Type} [AddCommGroup E] [Module K E] [TopologicalSpace E] [IsModuleTopology K E]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable [MeasurableSpace E] [BorelSpace E]
namespace PI.ProdFormulaE.HaarBox
theorem _root_.solution (b : Basis ι K E) (μ : Measure E) [μ.IsAddHaarMeasure]
    (hscale : ScaleBox b μ) (htrans : TransvBox b)
    (A : Matrix ι ι K) (hA : A.det ≠ 0) (S : Set E) :
    μ (Matrix.toLin b b A '' S) = ENNReal.ofReal (modF K A.det) * μ S := by
  classical
  revert S
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero
    (fun M => ∀ S : Set E, μ (Matrix.toLin b b M '' S) = ENNReal.ofReal (modF K M.det) * μ S)
    A hA ?_ ?_ ?_
  · intro D hD S
    refine measure_toLin_diagonal_image b μ hscale D (fun i => ?_) S
    rw [Matrix.det_diagonal] at hD
    exact Finset.prod_ne_zero_iff.1 hD i (Finset.mem_univ i)
  · intro t S
    exact measure_toLin_transvection_image b μ htrans t S
  · intro A B _ _ hA hB S
    exact measure_toLin_mul_image_of_forall b μ A B hA hB S
end PI.ProdFormulaE.HaarBox
