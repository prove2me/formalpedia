-- Prove2me | solution 1 for PI.Dv.GLatHermW.isHermE_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:15:52.865964+00:00
-- url     : https://prove2.me/submissions/1ead2eae-d046-40dd-ac58-f2d1f460a9f9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianGroupLattices_AsAlgebraHomEG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianGroupLattices_IsCMFormEOf
import Theorems.Thm_PI_Dv_GLatHermW_star_cf
import Theorems.Thm_PI_Dv_GLatHermW_asAlgebraHom_eG


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.GLatHermW
open PI.Dv Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
namespace PI.Dv.GLatHermW
theorem _root_.solution (T : GoodSet K G) (A : HLat K) (ρ : Representation K G A.V)
    (h : A.V →ₗ⋆[K] A.V →ₗ[K] K) (hS : StarIsConj K) (hH : IsGHerm A ρ h) :
    IsHermE A (ρ.asAlgebraHom (eG T)) h := by
  obtain ⟨h1, h2, h3⟩ := hH
  refine ⟨h1, h2, fun x y => ?_⟩
  have hinv : ∀ g : G, h (ρ g x) y = h x (ρ g⁻¹ y) := by
    intro g
    have := h3 g x (ρ g⁻¹ y)
    rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
  have hl : h ((ρ.asAlgebraHom (eG T)) x) y = ∑ g : G, star (cf T g) * h (ρ g x) y := by
    rw [asAlgebraHom_eG, LinearMap.sum_apply, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [LinearMap.smul_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]
  have hr : h x ((ρ.asAlgebraHom (eG T)) y) = ∑ g : G, cf T g * h x (ρ g y) := by
    rw [asAlgebraHom_eG, LinearMap.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [LinearMap.smul_apply, map_smul, smul_eq_mul]
  rw [hl, hr]
  calc ∑ g : G, star (cf T g) * h (ρ g x) y = ∑ g : G, cf T g⁻¹ * h x (ρ g⁻¹ y) := by
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [star_cf hS, hinv]
    _ = ∑ g : G, cf T g * h x (ρ g y) :=
        Fintype.sum_equiv (Equiv.inv G) _ _ fun g => rfl
end PI.Dv.GLatHermW
