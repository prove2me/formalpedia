-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_weaklyRegular_eq_nil_of_socle_6d4a27b52f7e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:41.993872+00:00
-- url     : https://prove2.me/submissions/704ba88f-9c18-42eb-b8fb-5d1e2debaab1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCMRegularElement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFlatNormalFibres
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_ExistsMulEqZeroOfMemAssociatedPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open IsLocalRing RingTheory.Sequence Pointwise
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {R M : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    {z : M} (hz : z ≠ 0) (hk : ∀ r ∈ maximalIdeal R, r • z = 0) {rs : List R}
    (hm : ∀ r ∈ rs, r ∈ maximalIdeal R) (hreg : IsWeaklyRegular M rs) : rs = [] := by
  cases rs with
  | nil => rfl
  | cons r rs =>
    exfalso
    have h := ((isWeaklyRegular_cons_iff M r rs).mp hreg).1
    exact hz (h (show r • z = r • (0 : M) by rw [hk r (hm r List.mem_cons_self), smul_zero]))
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
