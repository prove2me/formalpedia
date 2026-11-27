-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.E2.P.specmeas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:20:24.455025+00:00
-- url     : https://prove2.me/submissions/7773d0ae-11ab-4e43-8cf5-4b51074a43be

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_OneStepOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_PositiveMeasureNorms_Specmeas
import Theorems.Thm_PositivityTheory_Rg_BcB_E2_P_Specmeas_exists_measure_of_positive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory ComplexConjugate ComplexOrder CompactlySupported
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E2 PositivityTheory.Rg.BcB.E2.P
namespace PositivityTheory.Rg.BcB.E2.P
theorem _root_.solution : SpecMeas := by
  intro K _ _ _ S _ _ _ _ _ π v
  let Λ : C(S, ℂ) →ₗ[ℂ] ℂ :=
  { toFun f := inner ℂ v (π f v)
    map_add' f g := by simp [map_add]
    map_smul' c f := by simp }
  have hΛ : ∀ f : C(S, ℂ), 0 ≤ Λ (star f * f) := by
    intro f
    show 0 ≤ inner ℂ v (π (star f * f) v)
    rw [map_mul, map_star, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
    exact pow_nonneg (Complex.zero_le_real.mpr (norm_nonneg (π f v))) 2
  obtain ⟨ν, h1, h2, h3⟩ := Specmeas.exists_measure_of_positive Λ hΛ
  exact ⟨ν, h1, h2, fun f => (h3 f).symm⟩
end PositivityTheory.Rg.BcB.E2.P
