-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_mem_quotGraded_piece_498792b22d20
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:03:07.581925+00:00
-- url     : https://prove2.me/submissions/0d6b30ee-29eb-4d0b-bbea-ad24ef9a88a2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotGraded

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
open MvPolynomial DirectSum
noncomputable section
universe u
variable {S : Type u} [CommRing S] {N : ℕ}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {p : Ideal (Poly S N)} {hp : ∀ f ∈ p, ∀ d : ℕ, homogeneousComponent d f ∈ p}
    {c : ℤ} {m : Poly S N ⧸ p} :
    m ∈ (quotGraded p hp).piece c ↔ ∃ f : Poly S N,
      IsWeightedHomogeneous (fun _ => (1 : ℤ)) f c ∧ Ideal.Quotient.mk p f = m := by
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f, hf, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f, hf, rfl⟩
end GroundTheory.Heights₂.Heights.Kleiman
