-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.E2.P.Specmeas.nonneg_ofR
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:13:19.427807+00:00
-- url     : https://prove2.me/submissions/0a6b8c13-a2ef-41df-89a8-183c3bd48695

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_OneStepOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_PositiveMeasureNorms_Specmeas

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E2 PositivityTheory.Rg.BcB.E2.P PositivityTheory.Rg.BcB.E2.P.Specmeas
variable {X : Type} [TopologicalSpace X]
variable (Λ : C(X, ℂ) →ₗ[ℂ] ℂ) (hΛ : ∀ f : C(X, ℂ), 0 ≤ Λ (star f * f))
include hΛ
namespace PositivityTheory.Rg.BcB.E2.P.Specmeas
theorem _root_.solution {g : C(X, ℝ)} (hg : ∀ x, 0 ≤ g x) : 0 ≤ Λ (ofR g) := by
  let s : C(X, ℝ) := ⟨fun x => Real.sqrt (g x), by fun_prop⟩
  have : ofR g = star (ofR s) * ofR s := by
    ext x
    simp only [ofR_apply, ContinuousMap.mul_apply, ContinuousMap.star_apply, s,
      ContinuousMap.coe_mk]
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (hg x)]
  rw [this]; exact hΛ _
end PositivityTheory.Rg.BcB.E2.P.Specmeas
