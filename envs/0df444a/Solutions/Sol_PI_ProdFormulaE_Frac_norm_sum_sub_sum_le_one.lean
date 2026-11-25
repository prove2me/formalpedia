-- Prove2me | solution 1 for PI.ProdFormulaE.Frac.norm_sum_sub_sum_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:05:48.381826+00:00
-- url     : https://prove2.me/submissions/5929b921-21fb-438a-b75e-eb6efaddc730

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
theorem _root_.solution {q : ℕ} [Fact q.Prime] {ι : Type*} (s : Finset ι)
    (T b : ι → ℚ_[q]) (h : ∀ i ∈ s, ‖T i - b i‖ ≤ 1) :
    ‖∑ i ∈ s, T i - ∑ i ∈ s, b i‖ ≤ 1 := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_induction _ (fun x : ℚ_[q] => ‖x‖ ≤ 1)
    (fun x y hx hy => le_trans (Padic.nonarchimedean x y) (max_le hx hy)) (by simp) h
end PI.ProdFormulaE.Frac
