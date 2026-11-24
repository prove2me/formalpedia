-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SymplecticReduction_proof_c5ccc5b0fe5c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:21:25.510031+00:00
-- url     : https://prove2.me/submissions/cb77b939-f973-4ad9-8086-7154ad0a1d72

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix
namespace GroundTheory.Heights₂.Heights
namespace SymplecticReduction
theorem _root_.solution (hStep : SymplStep.Statement) (hDet : SymplDetBound.Statement) :
    SymplecticReduction.Statement := by
  intro g _ G hG hpos
  obtain ⟨n, rfl⟩ : ∃ n, g = n + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne g)
  obtain ⟨ρsq, hleast, hρ, hle, P, hP, hent, hdet⟩ :=
    hStep n ((2 * (n : ℝ)) ^ n) G hG hpos (fun H hH hHpos => hDet n H hH hHpos)
  refine ⟨ρsq, hleast, ?_, P, hP, hent, ?_⟩
  · push_cast; linarith
  · calc (symplGram P G).toBlocks₁₁.det ≤ ρsq * (2 * (n : ℝ)) ^ n := hdet
      _ ≤ ρsq * (2 * ((n + 1 : ℕ) : ℝ)) ^ (n + 1 - 1) := by
        rw [Nat.add_sub_cancel]
        apply mul_le_mul_of_nonneg_left _ hρ.le
        apply pow_le_pow_left₀ (by positivity)
        push_cast; linarith
end SymplecticReduction
end GroundTheory.Heights₂.Heights
