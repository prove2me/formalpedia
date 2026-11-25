-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_ChartGlue_hypotheses_inhabited_0ebd25719c21
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:11:59.185617+00:00
-- url     : https://prove2.me/submissions/b106da93-e2f1-4d12-ace8-7af7ef848a60

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_sameRationalSpan_onePoint_8fecdd4169a2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_exists_multiple_int_cbe6eae920c5

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
namespace ChartGlue
theorem _root_.solution (S : Finset Nat.Primes) (p : Nat.Primes)
    [Algebra (Localization.Away (primeProd S)) ℚ] [Algebra (ZLoc p) ℚ] :
    SameRationalSpan
      ((scaledTrivBundle (Localization.Away (primeProd S)) onePoint 1 (one_ne_zero (α := ℚ))).lat ())
      ((scaledTrivBundle (ZLoc p) onePoint 1 (one_ne_zero (α := ℚ))).lat ()) := by
  refine sameRationalSpan_onePoint _ _ (fun a => ?_) (fun a => ?_)
  · refine exists_multiple_int (Submonoid.powers (primeProd S)) ?_ _ (algebraMap _ ℚ) a
    rintro ⟨n, hn⟩
    exact pow_ne_zero n (primeProd_ne_zero S) hn
  · exact exists_multiple_int (Ideal.span {((p : ℕ) : ℤ)}).primeCompl
      (fun h => h (Ideal.zero_mem _)) _ (algebraMap _ ℚ) a
end ChartGlue
end GroundTheory.Heights₂.Heights.Model
