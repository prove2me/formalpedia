-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_antisymSample_mem_5e7a0459a761
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:43:08.1855+00:00
-- url     : https://prove2.me/submissions/387a5830-45a0-4345-b9a7-f2ca512e65c8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_antisymSample_eq_6e77b6491340

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution : antisymSample ∈ antisymSpace (Fin 1) 3 2 ∧ antisymSample ≠ 0 := by
  have hX : ∀ p q : Fin 1 × Fin 3, IsHomogeneous ((X p - X q : MvPolynomial (Fin 1 × Fin 3) ℝ)) 1 :=
    fun p q => (isHomogeneous_X ℝ p).sub (isHomogeneous_X ℝ q)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [mem_homogeneousSubmodule, antisymSample_eq]
    have hdeg : antisymDegree (Fin 1) 3 + 1 = 1 + 1 + 1 + 1 := by
      simp [antisymDegree]
    rw [hdeg]
    exact (((hX _ _).mul (hX _ _)).mul (hX _ _)).mul
      (((isHomogeneous_X ℝ _).add (isHomogeneous_X ℝ _)).add (isHomogeneous_X ℝ _))
  · rintro σ ⟨τ, a, b, hab, hblk, rfl⟩
    fin_cases τ
    fin_cases a <;> fin_cases b <;> simp at hab hblk ⊢
    rw [antisymSample_eq]
    simp [Equiv.swap_apply_def]
    ring
  · intro h
    have := congrArg (eval (fun p : Fin 1 × Fin 3 => ((p.2 : ℕ) : ℝ))) h
    rw [antisymSample_eq] at this
    simp at this
    norm_num at this
end GroundTheory.Heights₂.Heights
