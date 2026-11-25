-- Prove2me | solution 1 for PI.ZuckTensorWork.square_integrable_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:39:09.558453+00:00
-- url     : https://prove2.me/submissions/9a0cfe7d-3887-4ce1-a0ad-feadc1b93282

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_ZuckTensor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_SquareIntegrableConj
import Theorems.Thm_PI_ZuckTensorWork_SqInt_phiE_cont
import Theorems.Thm_PI_ZuckTensorWork_SqInt_phiE_symm_cont
import Theorems.Thm_PI_ZuckTensorWork_Cj_inner_def
import Theorems.Thm_PI_ZuckTensorWork_cjOp_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Finset
open scoped InnerProductSpace NNReal ENNReal
noncomputable section
open PI PI.ZuckTensorWork
open PI.UpqRep PI.ZuckTensor
open SqInt
namespace PI.ZuckTensorWork
theorem _root_.solution : SqIntConj := by
  intro n ε H _ _ σ hs v w
  have hmap : (Measure.map (phiE ε) (muG (revE ε))).IsHaarMeasure :=
    (phiE ε).isHaarMeasure_map (muG (revE ε)) (phiE_cont ε) (phiE_symm_cont ε)
  have heq := Measure.isMulLeftInvariant_eq_smul (Measure.map (phiE ε) (muG (revE ε))) (muG ε)
  have h1 : MemLp (coefOn (ε := ε) σ (Cj.un v) (Cj.un w)) 2 (Measure.map (phiE ε) (muG (revE ε))) := by
    rw [heq, ENNReal.smul_def]
    exact (hs _ _).smul_measure ENNReal.coe_ne_top
  have h2 := (memLp_map_measure_iff h1.1 (phiE_cont ε).measurable.aemeasurable).1 h1
  have e : coefOn (ε := revE ε) (sigC σ) v w = star (coefOn (ε := ε) σ (Cj.un v) (Cj.un w) ∘ phiE ε) := by
    funext g
    show ⟪w, cjOp (σ (revM (umat g))) v⟫_ℂ = star ⟪Cj.un w, σ (revM (umat g)) (Cj.un v)⟫_ℂ
    rw [Cj.inner_def, cjOp_apply]
    exact (inner_conj_symm _ _).symm
  rw [e]
  exact h2.star
end PI.ZuckTensorWork
