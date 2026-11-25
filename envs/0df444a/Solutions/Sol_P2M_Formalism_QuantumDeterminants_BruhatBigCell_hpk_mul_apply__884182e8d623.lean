-- Prove2me | solution 1 for P2M_Formalism_QuantumDeterminants_BruhatBigCell_hpk_mul_apply__884182e8d623
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:47:27.307577+00:00
-- url     : https://prove2.me/submissions/80aa2e8b-9fac-46ed-8ab2-a56c235d869e

import Definitions.Def_Formalism_FormalDegreeBessel_StatementBF
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GroupFactorizationHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BFCell
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.QuantumDeterminants.BruhatBigCell
open GBasic
variable {k r : ℕ}
namespace Formalism.QuantumDeterminants.BruhatBigCell
theorem _root_.solution (A : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (p j : Fin (2 * r + k + 1)) : (Hpk k r * A) p j = sgn k r p * A (sig k r p) j := by
  rw [mul_apply, Finset.sum_eq_single (sig k r p)]
  · rw [Hpk_eq, if_pos rfl]
  · intro q _ hq; rw [Hpk_eq, if_neg hq, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h
end Formalism.QuantumDeterminants.BruhatBigCell
