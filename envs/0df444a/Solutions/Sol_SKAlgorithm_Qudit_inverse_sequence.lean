-- Prove2me | solution 1 for SKAlgorithm.Qudit.inverse_sequence
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-11T20:49:03.447559+00:00
-- url     : https://prove2.me/submissions/2d2608a1-6b3f-427a-a75b-3b51702cfcea

import Mathlib
import Definitions.Def_SKAlgorithm_Qudit_Model

open scoped Matrix
open QAlgorithms
open scoped Matrix.Norms.L2Operator

open SKAlgorithm.Qudit


theorem solution {d : ℕ} (G : Finset (SU d)) (hG : ∀ g ∈ G, g⁻¹ ∈ G)
    (U : SU d) (S : List (SU d)) (hS : ∀ g ∈ S, g ∈ G) (ε : ℝ)
    (hU : opDist U (seqUnitary S) < ε) :
    (∀ g ∈ invSeq S, g ∈ G) ∧ opDist U⁻¹ (seqUnitary (invSeq S)) < ε := by
  classical
  constructor
  · intro g hg
    simp only [invSeq, List.mem_reverse, List.mem_map] at hg
    obtain ⟨a, ha, rfl⟩ := hg
    exact hG a (hS a ha)
  · have hp : seqUnitary (invSeq S) = (seqUnitary S)⁻¹ := by
      simpa only [seqUnitary, invSeq] using (List.prod_inv_reverse S).symm
    have hi (A B : SU d) : opDist A⁻¹ B⁻¹ = opDist A B := by
      unfold opDist
      change ‖star (A : Matrix (Fin d) (Fin d) ℂ) -
        star (B : Matrix (Fin d) (Fin d) ℂ)‖ =
        ‖(A : Matrix (Fin d) (Fin d) ℂ) - (B : Matrix (Fin d) (Fin d) ℂ)‖
      rw [← star_sub, norm_star]
    rw [hp, hi]
    exact hU



