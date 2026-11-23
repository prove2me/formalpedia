-- Prove2me | solution 1 for P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_subst__564f1f6f92b9
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:31:57.44137+00:00
-- url     : https://prove2.me/submissions/dce41790-2d29-401e-906d-7461eb0a153f

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BallRing
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_iff_lift
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_constantCoeff_lift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7.LogarithmEquivalence
namespace Formalism.InvariantFactorPaths.G7.LogarithmEquivalence
theorem _root_.solution {K ι κ : Type} [Finite ι] [NormedField K] [IsUltrametricDist K]
    {f : MvPowerSeries ι K} {φ : ι → MvPowerSeries κ K}
    (h0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) (hφ : ∀ i, Integral (φ i))
    (hf : Integral f) : Integral (MvPowerSeries.subst φ f) := by
  obtain ⟨f₀, rfl⟩ := integral_iff_lift.1 hf
  choose φ₀ hφ₀ using fun i => integral_iff_lift.1 (hφ i)
  have hs : MvPowerSeries.HasSubst φ₀ := MvPowerSeries.hasSubst_of_constantCoeff_zero fun i =>
    constantCoeff_lift (c := 0) (by rw [hφ₀ i, h0 i]; rfl)
  refine integral_iff_lift.2 ⟨MvPowerSeries.subst φ₀ f₀, ?_⟩
  rw [MvPowerSeries.map_subst hs]
  congr 1
  funext i
  exact hφ₀ i
end Formalism.InvariantFactorPaths.G7.LogarithmEquivalence
