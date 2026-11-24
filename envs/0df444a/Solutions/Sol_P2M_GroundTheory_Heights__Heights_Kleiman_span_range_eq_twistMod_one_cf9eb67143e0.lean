-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_span_range_eq_twistMod_one_cf9eb67143e0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:10:00.491395+00:00
-- url     : https://prove2.me/submissions/487c2525-aeed-4055-a135-f6b3dde692a4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (I : Chart x) :
    Submodule.span (chartRing S x I) (Set.range x) = twistMod S x 1 I := by
  obtain ⟨i, hi⟩ := I.2.1
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact mem_twistMod_one I j
  · rw [twistMod_eq_span 1 I hi, zpow_one, Submodule.span_le, Set.singleton_subset_iff]
    exact Submodule.subset_span ⟨i, rfl⟩
end GroundTheory.Heights₂.Heights.Kleiman
