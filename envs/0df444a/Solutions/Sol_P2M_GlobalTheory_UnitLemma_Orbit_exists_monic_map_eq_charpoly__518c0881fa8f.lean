-- Prove2me | solution 1 for P2M_GlobalTheory_UnitLemma_Orbit_exists_monic_map_eq_charpoly__518c0881fa8f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:12:53.766868+00:00
-- url     : https://prove2.me/submissions/bd4b549d-5ddd-43a2-a4a1-2e3e9c9678b1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqZeroOfNotPrimary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Theorems.Thm_GlobalTheory_UnitLemma_Orbit_charpoly_dvd_map_of_aeval_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit
open GlobalTheory.UnitLemma Polynomial IsLocalRing ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion
variable {K : UQ}
namespace GlobalTheory.UnitLemma.Orbit
theorem _root_.solution (B : InvAlg K) (hs : B.P.Separable) (hi : IsIntegral K.O B.g) :
    ∃ p : K.O[X], p.Monic ∧ p.map (algebraMap K.O K.E) = B.P := by
  obtain ⟨m, hm, hm0⟩ := hi
  have hP : B.P.Monic := LinearMap.charpoly_monic _
  obtain ⟨p, hp⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K.E hm (charpoly_dvd_map_of_aeval_eq_zero B hs m hm0)
  rw [hP.leadingCoeff, C_1, mul_one] at hp
  exact ⟨p, monic_of_injective (IsFractionRing.injective K.O K.E) (hp ▸ hP), hp⟩
end GlobalTheory.UnitLemma.Orbit
