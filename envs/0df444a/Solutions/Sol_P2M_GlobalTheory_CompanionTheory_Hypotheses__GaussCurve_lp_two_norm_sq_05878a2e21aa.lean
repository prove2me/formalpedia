-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_Hypotheses__GaussCurve_lp_two_norm_sq_05878a2e21aa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:59:42.648974+00:00
-- url     : https://prove2.me/submissions/c24da8f9-a233-471b-a46b-b82dd8c362f5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HolPartShear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_RealMpData
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_NormIteratedFDerivCexpCompLe
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_HasDerivAtLpOfDominated

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.CompanionTheory.Hypotheses₂ Filter Topology
open scoped Real SchwartzMap ComplexConjugate
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.GaussCurve
namespace GlobalTheory.CompanionTheory.Hypotheses₂.GaussCurve
theorem _root_.solution {E : Type*} [MeasurableSpace E] {μ : Measure E} (f : Lp ℂ 2 μ) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [@norm_sq_eq_re_inner ℂ, MeasureTheory.L2.inner_def,
    ← integral_re (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) f f)]
  simp_rw [inner_self_eq_norm_sq]
end GlobalTheory.CompanionTheory.Hypotheses₂.GaussCurve
