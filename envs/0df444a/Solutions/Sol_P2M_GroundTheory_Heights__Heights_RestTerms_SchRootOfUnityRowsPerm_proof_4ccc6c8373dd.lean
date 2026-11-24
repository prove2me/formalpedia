-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_SchRootOfUnityRowsPerm_proof_4ccc6c8373dd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:08:31.649348+00:00
-- url     : https://prove2.me/submissions/598344be-4347-4439-b2eb-0003f3d5ab80

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchRootOfUnityRowsPerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open Finset
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace SchRootOfUnityRowsPerm
theorem _root_.solution : SchRootOfUnityRowsPerm.Statement := by
  intro k l π hk hl
  have hk0 : k ≠ 0 := Nat.pos_iff_ne_zero.mp hk
  have hζk : rootOfUnity k ^ k = 1 := by
    unfold rootOfUnity
    exact (Complex.isPrimitiveRoot_exp k hk0).pow_eq_one
  have hmod : ∀ j n : ℕ, rootOfUnity k ^ (j * n) = rootOfUnity k ^ (j * (n % k)) := by
    intro j n
    conv_lhs => rw [← Nat.mod_add_div n k]
    rw [mul_add, pow_add, mul_left_comm j k, pow_mul (rootOfUnity k) k, hζk, one_pow, mul_one]
  have hM : (Matrix.of fun i j : Fin k => rootOfUnity k ^ ((j : ℕ) * l i)) =
      (Matrix.of fun i j : Fin k => rootOfUnity k ^ ((j : ℕ) * (k - 1 - (i : ℕ)))).submatrix π id := by
    ext i j
    simp only [Matrix.of_apply, Matrix.submatrix_apply, id]
    rw [hmod, hl i]
  rw [hM, Matrix.det_permute]
end SchRootOfUnityRowsPerm
end GroundTheory.Heights₂.Heights.RestTerms
