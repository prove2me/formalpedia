-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_Cech_subsingleton_H_one_iff_a50a0634e5b7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:34:24.18408+00:00
-- url     : https://prove2.me/submissions/30137ce9-a9e1-4882-b0b7-7638bc02f781

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PClaimVanishCech

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
open GroundTheory.Heights₂.Heights.Kleiman.Cech
variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R] {G : Cell U → Type v}
  [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J}
namespace GroundTheory.Heights₂.Heights.Kleiman.Cech
theorem _root_.solution :
    Subsingleton (H G ρ 1) ↔ ∀ z : Cochain G 1, d G ρ 1 z = 0 → ∃ w : Cochain G 0, d G ρ 0 w = z := by
  unfold H
  rw [Submodule.Quotient.subsingleton_iff, Submodule.comap_subtype_eq_top]
  constructor
  · intro h z hz
    exact h (LinearMap.mem_ker.mpr hz)
  · intro h z hz
    exact h z (LinearMap.mem_ker.mp hz)
end GroundTheory.Heights₂.Heights.Kleiman.Cech
