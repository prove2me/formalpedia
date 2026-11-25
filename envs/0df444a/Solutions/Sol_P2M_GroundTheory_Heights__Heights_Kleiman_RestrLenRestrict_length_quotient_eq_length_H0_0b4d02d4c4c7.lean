-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_length_quotient_eq_length_H0_0b4d02d4c4c7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:26:56.630876+00:00
-- url     : https://prove2.me/submissions/778c9711-b005-4442-86c5-eecd2fcf1e7b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrLenRestrictSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrLenRestrict
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_toH0OfCocycle_eq_zero_iff_4b1e54951f8f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_toH0OfCocycle_surjective_bd48e4ec923d

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
open MvPolynomial Filter
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.RestrLenRestrict
variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R] {G : Cell U → Type w}
  [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J}
  {M : Type w} [AddCommGroup M] [Module R M]
namespace GroundTheory.Heights₂.Heights.Kleiman.RestrLenRestrict
theorem _root_.solution (φ : M →ₗ[R] Cech.Cochain G 0) (hφ : ∀ m, Cech.d G ρ 0 (φ m) = 0)
    (h : ∀ z : Cech.Cochain G 0, Cech.d G ρ 0 z = 0 → ∃ m, φ m = z) (K : Submodule R M)
    (hK : ∀ m, φ m = 0 ↔ m ∈ K) : Module.length R (M ⧸ K) = Module.length R (Cech.H G ρ 0) := by
  have hker : LinearMap.ker (toH0OfCocycle φ hφ) = K := by
    ext m
    rw [LinearMap.mem_ker, toH0OfCocycle_eq_zero_iff, hK]
  rw [← hker]
  exact (LinearMap.quotKerEquivOfSurjective _ (toH0OfCocycle_surjective φ hφ h)).length_eq
end GroundTheory.Heights₂.Heights.Kleiman.RestrLenRestrict
