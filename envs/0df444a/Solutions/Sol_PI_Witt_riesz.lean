-- Prove2me | solution 1 for PI.Witt.riesz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:30:59.643948+00:00
-- url     : https://prove2.me/submissions/87691556-a481-436a-b17f-86410c211f33

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittDecomposition_Anisotropic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittDecomposition_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Witt
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
namespace PI.Witt
theorem _root_.solution [FiniteDimensional K V] (B : V →ₗ⋆[K] V →ₗ[K] K) (hB : ∀ x y, star (B x y) = B y x)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) (φ : V →ₗ[K] K) : ∃ v, ∀ z, B v z = φ z := by
  classical
  let b := Module.finBasis K V
  rcases isEmpty_or_nonempty (Fin (Module.finrank K V)) with hE | hNE
  · refine ⟨0, fun z => ?_⟩
    have hz : z = 0 := by rw [← b.sum_repr z]; simp
    simp [hz]
  have hli : LinearIndependent K (fun i => B (b i)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h1 : B (∑ j, star (g j) • b j) = 0 := by
      rw [map_sum]
      simp only [map_smulₛₗ, starRingEnd_apply, star_star]
      exact hg
    have h2 : ∑ j, star (g j) • b j = 0 := hnd _ (fun y => by rw [h1, LinearMap.zero_apply])
    have h3 := (Fintype.linearIndependent_iff.mp b.linearIndependent) _ h2 i
    exact star_eq_zero.mp h3
  have hcard : Fintype.card (Fin (Module.finrank K V)) = Module.finrank K (V →ₗ[K] K) := by
    rw [Fintype.card_fin]; exact (Subspace.dual_finrank_eq).symm
  let b' := basisOfLinearIndependentOfCardEqFinrank hli hcard
  refine ⟨∑ i, star (b'.repr φ i) • b i, fun z => ?_⟩
  conv_rhs => rw [← b'.sum_repr φ]
  rw [map_sum, LinearMap.sum_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smulₛₗ, LinearMap.smul_apply, LinearMap.smul_apply, starRingEnd_apply, star_star,
    coe_basisOfLinearIndependentOfCardEqFinrank]
end PI.Witt
