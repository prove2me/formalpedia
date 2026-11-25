-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_QuotientH0Length_toH0OfCocycle_eq_zero_iff_bfe72cd64f6d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:19:06.951389+00:00
-- url     : https://prove2.me/submissions/8031169f-e9b6-4cf0-b3e5-8954e025c842

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_LengthQuotientEqLengthH0

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
open GroundTheory.Heights₂.Heights.Kleiman.QuotientH0Length
variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R] {G : Cell U → Type w}
  [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J}
  {M : Type w} [AddCommGroup M] [Module R M]
namespace GroundTheory.Heights₂.Heights.Kleiman.QuotientH0Length
theorem _root_.solution (φ : M →ₗ[R] Cech.Cochain G 0) (hφ : ∀ m, Cech.d G ρ 0 (φ m) = 0) (m : M) :
    toH0OfCocycle φ hφ m = 0 ↔ φ m = 0 := by
  have e : toH0OfCocycle φ hφ m = (Submodule.Quotient.mk (⟨φ m, LinearMap.mem_ker.mpr (hφ m)⟩ :
      LinearMap.ker (Cech.d G ρ 0)) : Cech.H G ρ 0) := rfl
  rw [e]
  exact (Submodule.Quotient.mk_eq_zero _).trans (Submodule.mem_comap.trans (Submodule.mem_bot R))
end GroundTheory.Heights₂.Heights.Kleiman.QuotientH0Length
