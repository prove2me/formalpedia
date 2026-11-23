-- Prove2me | solution 1 for PI.HtPlacesSumWork.plOf_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:33:38.792776+00:00
-- url     : https://prove2.me/submissions/f83e2c82-a266-453c-a895-317e29a343af

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_PlaceSumHeights_PlaceSumStatements_PlaceSumLemmas_GaussValuationSums_ValPlWtAddEqZero
import Theorems.Thm_PI_HtPlacesSumWork_valPl_mem_vRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.HtPlacesSumWork
open IsDedekindDomain WithZero IsLocalRing ReciprocityTheory.ChartRestriction.G.T0
variable (O F L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F]
  [Algebra O F] [IsFractionRing O F] [Field L] [Algebra F L] [Algebra O L] [IsScalarTower O F L]
variable {O F L}
variable [IsDedekindDomain (integralClosure O L)] [IsFractionRing (integralClosure O L) L]
  [FaithfulSMul O L]
namespace PI.HtPlacesSumWork
theorem _root_.solution {w : AddValuation L (WithTop ℤ)} (hw : w ∈ PlacesOver O L)
    (b : integralClosure O L) : 0 ≤ w (algebraMap (integralClosure O L) L b) := by
  have hO : ∀ a : O, algebraMap O L a ∈ vRing w := fun a => (valPl_mem_vRing w _).2 (hw.2 a).1
  let f : O →+* vRing w := (algebraMap O L).codRestrict (vRing w) hO
  have hc : (algebraMap (vRing w) L).comp f = algebraMap O L := RingHom.ext fun _ => rfl
  obtain ⟨p, hp, hpb⟩ := (mem_integralClosure_iff O L).1 b.2
  have hint : IsIntegral (vRing w) (b : L) := ⟨p.map f, hp.map f, by rw [Polynomial.eval₂_map, hc]; exact hpb⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  have hmem : (b : L) ∈ vRing w := by
    rw [← hy]
    exact y.2
  exact (valPl_mem_vRing w _).1 hmem
end PI.HtPlacesSumWork
