-- Prove2me | solution 1 for PI.ProdFormulaE.Frac.padicNorm_sub_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:06:00.792467+00:00
-- url     : https://prove2.me/submissions/630417a0-20a5-46ff-be4c-50d958cfa989

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_DenEqOneOfForallPadicNormLeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open PI PI.ProdFormulaE PI.ProdFormulaE.Frac
namespace PI.ProdFormulaE.Frac
theorem _root_.solution {q : ℕ} [Fact q.Prime] {a b : ℚ} (ha : padicNorm q a ≤ 1)
    (hb : padicNorm q b ≤ 1) : padicNorm q (a - b) ≤ 1 := by
  exact le_trans padicNorm.sub (max_le ha hb)
end PI.ProdFormulaE.Frac
