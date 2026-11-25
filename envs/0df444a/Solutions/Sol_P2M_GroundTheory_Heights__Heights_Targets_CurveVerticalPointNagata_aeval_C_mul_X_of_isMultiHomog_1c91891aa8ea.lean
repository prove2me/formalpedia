-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointNagata_aeval_C_mul_X_of_isMultiHomog_1c91891aa8ea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:33:13.086439+00:00
-- url     : https://prove2.me/submissions/d1ce7769-bdf3-4cd0-983a-436f49be97b3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveVertPointNagata
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_CurveCountObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PLocRingPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCurveVertPointNagata
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointNagata_aeval_eq_eval__e50f1199a6e0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointNagata_aeval_mul_of_isMultiHomog_1df7fe6be52b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointNagata
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointNagata
theorem _root_.solution {S : Type*} [CommRing S] [Algebra ℤ S] [Algebra ℤ (MvPolynomial K S)] (r : (Σ k, ι k) → S) {g : MRing ι}
    {e : K → ℕ} (hg : IsMultiHomog g e) :
    (aeval (fun p => MvPolynomial.C (r p) * MvPolynomial.X p.1) g : MvPolynomial K S) =
      MvPolynomial.C (aeval r g) * ∏ k, (MvPolynomial.X k : MvPolynomial K S) ^ e k := by
  refine (aeval_mul_of_isMultiHomog (fun p => (MvPolynomial.C (r p) : MvPolynomial K S)) MvPolynomial.X hg).trans ?_
  congr 1
  rw [aeval_eq_eval₂, aeval_eq_eval₂, MvPolynomial.eval₂_comp_left,
    show (MvPolynomial.C : S →+* MvPolynomial K S).comp (Int.castRingHom S) = Int.castRingHom _ from
      RingHom.ext_int _ _]
  rfl
end GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointNagata
