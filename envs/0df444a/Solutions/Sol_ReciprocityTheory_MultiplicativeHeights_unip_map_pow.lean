-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.unip_map_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:17:46.434623+00:00
-- url     : https://prove2.me/submissions/08b1f7cb-79be-4d28-8984-390927f026c1

import Definitions.Def_ReciprocityTheory_SemistableReduction_UnipotentA
import Definitions.Def_ReciprocityTheory_SemistableReduction_UnipotentB
import Definitions.Def_ReciprocityTheory_SemistableReduction_Unipotent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField Polynomial
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {K : Type*} [Field K] {r : ℕ} (σ : K →+* ℂ) (M : Matrix (Fin r) (Fin r) K)
    (n : ℕ) : (M.map σ) ^ n = (M ^ n).map σ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, pow_succ, Matrix.map_mul]
end ReciprocityTheory.MultiplicativeHeights
