-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_recR_family_eq_65fe609818ce
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:00:40.23517+00:00
-- url     : https://prove2.me/submissions/5d8bc7a5-cfb1-4bee-93f3-2fb3388ac5ba

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedG
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermFubiniStudyO1
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsExtraBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_MultAtHorizontalEqZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_multAt_horizontal_eq_zero_6581e9cd0bbe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
theorem _root_.solution {P : Ideal (MRing ι)} {A : HermLine ι} {s : MRing ι}
    (hs : IsSectionOn P A s)
    (hind : ∀ (I : Family ι) (t : MRing ι), IsSectionOn P A t →
      recR I P (Fin.elim0 : Fin 0 → HermLine ι) A s = recR I P Fin.elim0 A t)
    (I J : Family ι) :
    recR I P (Fin.elim0 : Fin 0 → HermLine ι) A s = recR J P Fin.elim0 A s := by
  unfold recR
  congr 1
  refine finsum_mem_congr rfl fun W hW => ?_
  by_cases hh : IsHorizontal W
  · rw [multAt_horizontal_eq_zero hs hind hW hh, zero_mul, zero_mul]
  · simp [hh]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
