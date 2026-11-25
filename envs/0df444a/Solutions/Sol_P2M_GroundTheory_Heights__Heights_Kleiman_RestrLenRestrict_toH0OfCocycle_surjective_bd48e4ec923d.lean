-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_toH0OfCocycle_surjective_bd48e4ec923d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:15:48.762901+00:00
-- url     : https://prove2.me/submissions/2cb21aec-a089-449c-9e21-2b6462f7f635

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrLenRestrictSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrLenRestrict

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
    (h : ∀ z : Cech.Cochain G 0, Cech.d G ρ 0 z = 0 → ∃ m, φ m = z) : Function.Surjective (toH0OfCocycle φ hφ) := by
  intro ξ
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
  obtain ⟨m, hm⟩ := h z (LinearMap.mem_ker.mp z.2)
  refine ⟨m, ?_⟩
  have e : toH0OfCocycle φ hφ m = (Submodule.Quotient.mk (⟨φ m, LinearMap.mem_ker.mpr (hφ m)⟩ :
      LinearMap.ker (Cech.d G ρ 0)) : Cech.H G ρ 0) := rfl
  rw [e]
  exact congrArg Submodule.Quotient.mk (Subtype.ext hm)
end GroundTheory.Heights₂.Heights.Kleiman.RestrLenRestrict
