-- Prove2me | solution 1 for PI.ProdFormulaE.Frac.padicNorm_add_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:05:55.02522+00:00
-- url     : https://prove2.me/submissions/0aeb0241-5e51-4310-9576-89517ac2592d

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
    (hb : padicNorm q b ≤ 1) : padicNorm q (a + b) ≤ 1 := le_trans padicNorm.nonarchimedean (max_le ha hb)
end PI.ProdFormulaE.Frac
