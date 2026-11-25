-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_eq_zero_or_isHomogeneous_of_mem_piece_5f1230198ef9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:02:48.653267+00:00
-- url     : https://prove2.me/submissions/be807d16-9894-4c7e-811d-fff71ea1a9dd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerreOnto

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
universe u v w w'
variable {S : Type u} [CommRing S] {N : ℕ}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {p : Poly S N} {e : ℤ}
    (hp : p ∈ (polyGraded S N).piece e) : p = 0 ∨ ∃ n : ℕ, (n : ℤ) = e ∧ p.IsHomogeneous n := by
  classical
  change p ∈ weightedHomogeneousSubmodule S _ e at hp
  rw [mem_weightedHomogeneousSubmodule] at hp
  by_cases h0 : p = 0
  · exact Or.inl h0
  right
  have key : ∀ s : Fin (N + 1) →₀ ℕ, Finsupp.weight (fun _ => (1 : ℤ)) s =
      ((Finsupp.weight (1 : Fin (N + 1) → ℕ) s : ℕ) : ℤ) := by
    intro s
    simp only [Finsupp.weight_apply, Finsupp.sum, Pi.one_apply, smul_eq_mul, mul_one]
    push_cast
    exact Finset.sum_congr rfl fun _ _ => nsmul_one _
  obtain ⟨s0, hs0⟩ := ne_zero_iff.mp h0
  refine ⟨Finsupp.weight (1 : Fin (N + 1) → ℕ) s0, by rw [← key, hp hs0], fun s hs => ?_⟩
  have := (hp hs).trans (hp hs0).symm
  rw [key, key] at this
  exact_mod_cast this
end GroundTheory.Heights₂.Heights.Kleiman
