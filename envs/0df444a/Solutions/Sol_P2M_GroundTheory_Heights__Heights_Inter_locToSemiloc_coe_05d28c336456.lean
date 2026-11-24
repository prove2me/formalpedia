-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_locToSemiloc_coe_05d28c336456
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:35.716463+00:00
-- url     : https://prove2.me/submissions/b0e7a234-d06d-42d2-b59d-51de6fc69d36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IdDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LocRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocRing

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    (P' : Ideal (MRing ι')) [P'.IsPrime] (W : Ideal (MRing ι)) (x : locRing (imageZ v P') W) :
    ((locToSemiloc hv P' W x : semiLocRing P' (fibreOver v P' W)) : FractionRing (MRing ι' ⧸ P')) =
      fracMapZ v P' x :=
  rfl
end GroundTheory.Heights₂.Heights.Inter
