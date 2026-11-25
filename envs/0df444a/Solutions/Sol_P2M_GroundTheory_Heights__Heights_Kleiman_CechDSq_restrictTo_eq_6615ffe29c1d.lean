-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_CechDSq_restrictTo_eq_6615ffe29c1d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:01:34.76437+00:00
-- url     : https://prove2.me/submissions/d937b7ac-37d6-4684-8913-13fb1d08c3ae

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCechDSq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDSq

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
noncomputable section
universe u v
open GroundTheory.Heights₂.Heights.Kleiman.CechDSq
variable {n : ℕ}
variable {U : Finset (Fin n)} {R : Type u} [CommRing R] {G : Cell U → Type v}
  [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J}
namespace GroundTheory.Heights₂.Heights.Kleiman.CechDSq
theorem _root_.solution {i : ℕ} (s : Cech.Cochain G i) (K : Cell U) (L : Cech.Idx U i)
    (h : L.1.1 ⊆ K.1) : restrictTo (ρ := ρ) s K L.1.1 = ρ L.1 K h (s L) := by
  have hex : ∃ L' : Cech.Idx U i, L'.1.1 = L.1.1 ∧ L.1.1 ⊆ K.1 := ⟨L, rfl, h⟩
  have key : ∀ (L₁ L₂ : Cech.Idx U i) (_ : L₁ = L₂) (h₁ : L₁.1.1 ⊆ K.1) (h₂ : L₂.1.1 ⊆ K.1),
      ρ L₁.1 K h₁ (s L₁) = ρ L₂.1 K h₂ (s L₂) := by
    rintro _ _ rfl _ _; rfl
  rw [restrictTo, dif_pos hex]
  exact key _ _ (Subtype.ext (Subtype.ext hex.choose_spec.1)) _ _
end GroundTheory.Heights₂.Heights.Kleiman.CechDSq
