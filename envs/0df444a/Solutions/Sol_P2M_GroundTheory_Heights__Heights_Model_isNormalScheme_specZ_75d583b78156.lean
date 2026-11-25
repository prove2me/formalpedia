-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_isNormalScheme_specZ_75d583b78156
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:05:27.481236+00:00
-- url     : https://prove2.me/submissions/86df2c63-96c8-431f-8b2e-ab4bd13287cf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
open NumbersDVR ReciprocityTheory.ChartRestriction.G.Geo
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution : IsNormalScheme SpecZ := by
  intro x
  have hx : x.asIdeal.IsPrime := PrimeSpectrum.isPrime x
  let _ : Algebra ℤ (SpecZ.presheaf.stalk x) := StructureSheaf.stalkAlgebra (CommRingCat.of ℤ) x
  have : IsLocalization.AtPrime (SpecZ.presheaf.stalk x) x.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk (CommRingCat.of ℤ) x
  exact isIntegrallyClosed_of_isLocalization _ x.asIdeal.primeCompl
    (Ideal.primeCompl_le_nonZeroDivisors _)
end GroundTheory.Heights₂.Heights.Model
