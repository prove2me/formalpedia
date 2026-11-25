-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FrobeniusRectangleBound_intersectionNumber_baseChange_3a98f7db5654
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:21:34.229555+00:00
-- url     : https://prove2.me/submissions/4456f02f-86c6-48c8-b149-2bdbb39f7ab4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AltFrob
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KAlt_frobDim_eq_c066fd4b76d0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KAlt_frobDelta_add_const_877e0affda6b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KAlt_frobDelta_const_ee2617725f44
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KAlt_frobDelta_nonneg_c1cc390decae
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KAlt_prod_factorial_le_ed8781dc790b

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
open Finset
namespace GroundTheory.Heights₂.Heights
namespace FrobeniusRectangleBound
theorem _root_.solution : FrobeniusRectangleBound.Statement := by
  intro r s ν hν
  simp only [KAlt.frobDim_eq, KAlt.frobDelta_add_const, KAlt.frobDelta_const]
  have hsum : (∑ a : Fin r, (s + ν a)) = r * s + ∑ a, ν a := by
    rw [Finset.sum_add_distrib]; simp
  have hsum' : (∑ _a : Fin r, s) = r * s := by simp
  rw [hsum, hsum']
  set k := ∑ a, ν a with hk
  set A := ∏ a : Fin r, ((s + ν a + (r - 1 - (a : ℕ))).factorial : ℚ) with hA
  set B := ∏ a : Fin r, ((s + (r - 1 - (a : ℕ))).factorial : ℚ) with hB
  set E := ∏ a : Fin r, ((ν a + (r - 1 - (a : ℕ))).factorial : ℚ) with hE
  set F := ∏ a : Fin r, (((r - 1 - (a : ℕ)).factorial : ℕ) : ℚ) with hF
  set D := KAlt.frobDelta ν with hD
  have hA0 : 0 < A := prod_pos fun a _ => by positivity
  have hB0 : 0 < B := prod_pos fun a _ => by positivity
  have hE0 : 0 < E := prod_pos fun a _ => by positivity
  have hD0 : 0 ≤ D := KAlt.frobDelta_nonneg ν hν
  have key : B * E ≤ F * A := KAlt.prod_factorial_le s ν
  have hch : ((r * s + k).choose k : ℚ) * ((r * s).factorial : ℚ) * (k.factorial : ℚ) =
      ((r * s + k).factorial : ℚ) := by
    have h := Nat.choose_mul_factorial_mul_factorial (show k ≤ r * s + k by omega)
    rw [show r * s + k - k = r * s by omega] at h
    rw [← h]; push_cast; ring
  have hrhs : ((r * s + k).choose k : ℚ) * ((r * s).factorial * F / B) * (k.factorial * D / E) =
      ((r * s + k).factorial : ℚ) * D * F / (B * E) := by
    rw [← hch]; field_simp
  rw [hrhs, div_le_div_iff₀ hA0 (mul_pos hB0 hE0)]
  calc ((r * s + k).factorial : ℚ) * D * (B * E) ≤ ((r * s + k).factorial : ℚ) * D * (F * A) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = ((r * s + k).factorial : ℚ) * D * F * A := by ring
end FrobeniusRectangleBound
end GroundTheory.Heights₂.Heights
