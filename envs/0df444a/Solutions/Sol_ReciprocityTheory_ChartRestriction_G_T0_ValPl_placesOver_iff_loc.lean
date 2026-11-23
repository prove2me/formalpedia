-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.ValPl.placesOver_iff_loc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:33:40.990517+00:00
-- url     : https://prove2.me/submissions/e5991ad4-04c3-4b52-ae93-5812af7e88da

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open ReciprocityTheory.ChartRestriction.G.T0.ValPl
open IsDedekindDomain WithZero IsLocalRing
namespace ReciprocityTheory.ChartRestriction.G.T0.ValPl
theorem _root_.solution {R O L : Type*} [CommRing R] [CommRing O] [IsLocalRing O] [Field L]
    [Algebra R O] [Algebra R L] [Algebra O L] [IsScalarTower R O L] (P : Ideal R) [P.IsPrime]
    [IsLocalization.AtPrime O P] (w : AddValuation L (WithTop ℤ)) :
    (∀ x : R, 0 ≤ w (algebraMap R L x) ∧ (0 < w (algebraMap R L x) ↔ x ∈ P)) ↔
      (∀ x : O, 0 ≤ w (algebraMap O L x) ∧ (0 < w (algebraMap O L x) ↔ x ∈ maximalIdeal O)) := by
  constructor
  · intro h x
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl x
    have hsP : (s : R) ∉ P := s.2
    have hs0 : w (algebraMap R L s) = 0 := by
      obtain ⟨h1, h2⟩ := h s
      exact le_antisymm (not_lt.mp fun hp => hsP (h2.mp hp)) h1
    have hspec : algebraMap O L (IsLocalization.mk' O r s) * algebraMap R L s =
        algebraMap R L r := by
      rw [IsScalarTower.algebraMap_apply R O L (s : R), IsScalarTower.algebraMap_apply R O L r,
        ← map_mul, IsLocalization.mk'_spec]
    have hw : w (algebraMap O L (IsLocalization.mk' O r s)) = w (algebraMap R L r) := by
      rw [← hspec, AddValuation.map_mul, hs0, add_zero]
    rw [hw]
    first
    | (rw [IsLocalization.AtPrime.mk'_mem_maximal_iff O P]; exact h r)
    | (rw [IsLocalization.AtPrime.mk'_mem_maximal_iff (S := O) (I := P)]; exact h r)
    | (rw [IsLocalization.AtPrime.mk'_mem_maximal_iff O]; exact h r)
  · intro h x
    have hx := h (algebraMap R O x)
    rw [← IsScalarTower.algebraMap_apply R O L x] at hx
    first
    | rwa [IsLocalization.AtPrime.to_map_mem_maximal_iff (S := O) (I := P)] at hx
    | (rw [IsLocalization.AtPrime.to_map_mem_maximal_iff O P] at hx; exact hx)
end ReciprocityTheory.ChartRestriction.G.T0.ValPl
