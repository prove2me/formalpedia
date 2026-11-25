-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KSplit.prod_phase
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:04:43.475022+00:00
-- url     : https://prove2.me/submissions/e0521fa5-f419-4df5-8ff9-6522260d829b

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_NullSec
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ThetaSplitting_ActUDiagMonomial
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_chg_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KSplit
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
namespace PositivityTheory.SiegelWeilFormula.KSplit
theorem _root_.solution (a : Fin m) (z : ℂ) (hz : star z * z = 1) (s : Fin m × Fin n × Bool →₀ ℕ) :
    (s.prod fun k e => (if k.2.2 then star (if k.1 = a then z else 1) else (if k.1 = a then z else 1)) ^ e) =
      z ^ chg a s := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hs : star z = z⁻¹ := eq_inv_of_mul_eq_one_left hz
  induction s using Finsupp.induction with
  | zero => simp [chg]
  | single_add k e s _ _ ih =>
    rw [Finsupp.prod_add_index' (fun _ => by simp) (fun _ _ _ => by rw [pow_add]), Finsupp.prod_single_index (by simp), ih,
      chg_add, zpow_add₀ hz0]
    congr 1
    split_ifs with h1 h2 h2 <;> simp [hs, _root_.zpow_neg, zpow_natCast]
end PositivityTheory.SiegelWeilFormula.KSplit
