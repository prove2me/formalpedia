-- Prove2me | solution 1 for UpperTheory.Ram.Rd.four_le_rdE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:40:05.423513+00:00
-- url     : https://prove2.me/submissions/f6e400bd-6834-428d-9941-198715f7735a

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_HostCls
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_FourMulQLeCondN
import Theorems.Thm_UpperTheory_Ram_Rd_rdE_nonneg
import Theorems.Thm_Formalism_BasicNotions_Ranks_n_eq_ord
import Theorems.Thm_P2M_Formalism_BasicNotions_Host_four_le_n__da3ddea1485c


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory UpperTheory.Ram UpperTheory.Ram.Rd
open Formalism.BasicNotions
variable {R : Ranks} (H : Host R)
namespace UpperTheory.Ram.Rd
theorem _root_.solution : 4 ≤ H.rdE := by
  have h : (4 * R.ord : ℝ) ≤ H.rdE ^ 2 := H.der.rd_sq_ge
  have h4 : (4 : ℝ) ≤ R.ord := by rw [← R.n_eq_ord]; exact_mod_cast H.four_le_n'
  have h0 := (rdE_nonneg H)
  nlinarith
end UpperTheory.Ram.Rd
