-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.chiPAux_neg_log_monoNormSq_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:36:31.961561+00:00
-- url     : https://prove2.me/submissions/1e9f1d56-f0a9-492d-b75e-34248591e017

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonoNormSq
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_ChiPSt
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_monoNormSq_pos
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_monoNormSq_le_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open Finset
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution {D : ℕ} (b : Fin (D + 1) → ℕ) : 0 ≤ -Real.log (monoNormSq b) := by
  have := Real.log_nonpos (monoNormSq_pos b).le (monoNormSq_le_one b)
  linarith
end ReciprocityTheory.GeometryOfNumbersTheory
