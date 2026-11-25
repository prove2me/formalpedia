-- Prove2me | solution 1 for PI.ET.HornW.emb_isom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:37:01.158746+00:00
-- url     : https://prove2.me/submissions/0e87d7f9-c7cf-4dbc-adc2-9cdc70733e50

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ExpTri
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_SortedSpec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_NormDetConjExp
import Theorems.Thm_PI_ET_HornW_emb_compress

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped MatrixOrder ComplexOrder
noncomputable section
open PI PI.ET
open PI.ET.HornW
variable {n : ℕ}
namespace PI.ET.HornW
theorem _root_.solution {k : ℕ} (hk : k ≤ n) : (emb hk)ᴴ * emb hk = 1 := by
  have h := emb_compress hk (fun _ => 1)
  simpa [Matrix.diagonal_one] using h
end PI.ET.HornW
