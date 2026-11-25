-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RootsOfUnityDenseAlt_rootsOfUnity_infinite_fb3881bcacd7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:14:54.158114+00:00
-- url     : https://prove2.me/submissions/c1f094bb-a308-4f17-9f86-9f736ab6ab2b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRootsOfUnityDense

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
open GroundTheory.Heights₂.Heights.RootsOfUnityDenseAlt
open Complex
namespace GroundTheory.Heights₂.Heights.RootsOfUnityDenseAlt
theorem _root_.solution :
    {z : ℂ | ∃ k : ℕ, 0 < k ∧ z ^ k = 1}.Infinite := by
  have hprim : ∀ m : ℕ,
      IsPrimitiveRoot (exp (2 * Real.pi * I / ((m + 1 : ℕ) : ℂ))) (m + 1) :=
    fun m => Complex.isPrimitiveRoot_exp (m + 1) (Nat.succ_ne_zero m)
  refine Set.infinite_of_injective_forall_mem
    (f := fun m : ℕ => exp (2 * Real.pi * I / ((m + 1 : ℕ) : ℂ))) ?_ ?_
  · intro a b hab
    have ha := hprim a
    have hb := hprim b
    simp only at hab
    rw [hab] at ha
    have := IsPrimitiveRoot.unique ha hb
    omega
  · intro m
    exact ⟨m + 1, Nat.succ_pos m, (hprim m).pow_eq_one⟩
end GroundTheory.Heights₂.Heights.RootsOfUnityDenseAlt
