-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_isPreimmersion_baseChangeMap_52e3bc354d38
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:05:38.349247+00:00
-- url     : https://prove2.me/submissions/a35720c4-8a82-4463-9d9b-baf6460cccce

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsBasisIsoFree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PVectorBundleRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PSpreadLocal

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
universe u
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution {X : Scheme.{0}} (f : X ⟶ SpecZ) (p : Nat.Primes) :
    IsPreimmersion (baseChangeMap f (ZLoc p)) := by
  have : IsPreimmersion (Spec.map (CommRingCat.ofHom (Int.castRingHom (ZLoc p)))) := by
    have h := IsPreimmersion.of_isLocalization (R := ℤ) (S := ZLoc p)
      (Ideal.span {((p : ℕ) : ℤ)}).primeCompl
    convert h using 3
    exact RingHom.ext_int _ _
  infer_instance
end GroundTheory.Heights₂.Heights.Model
