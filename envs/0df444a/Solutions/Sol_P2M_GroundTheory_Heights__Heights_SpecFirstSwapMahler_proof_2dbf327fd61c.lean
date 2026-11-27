-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SpecFirstSwapMahler_proof_2dbf327fd61c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:08:29.117782+00:00
-- url     : https://prove2.me/submissions/c2851495-4c38-42b4-931d-750279c07ea1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PSpecFirstSwapMahler
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mahler_C_mul_of_norm_eq_one_e40dc2cf86e3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_specFirst_C_mul_fda7cfa4cf95

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
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace SpecFirstSwapMahler
theorem _root_.solution (h1 : SpecFirstRename.Statement) (h2 : ChowCycleSwap.Statement) :
    SpecFirstSwapMahler.Statement := by
  intro n e h Z f u u' hf
  obtain ⟨c, hc2, hren⟩ := h2 ℂ n (e + 1 + 1) Z f hf (Equiv.swap 0 1)
  have hc : ‖c‖ = 1 := by
    have hsq : ‖c‖ ^ 2 = 1 := by rw [← norm_pow, hc2, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg c) two_ne_zero).1 hsq
  have key : specFirst (specFirst f u) u' = C c * specFirst (specFirst f u') u := by
    rw [← h1 n e f u' u, hren, specFirst_C_mul, specFirst_C_mul]
  rw [key, mahler_C_mul_of_norm_eq_one h c hc]
end SpecFirstSwapMahler
end GroundTheory.Heights₂.Heights
