-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.contr_eq_bf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:02:33.727443+00:00
-- url     : https://prove2.me/submissions/e15ae296-48b8-48ed-bf25-edeef33f3ca3

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoeffSmulX
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PartialDerivZeroSecondFamily
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_mem_first_family_iff
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_mem_second_family_iff
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_contr_sum
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_contr_mono
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_G_bf_monomial
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_G_bf_sum_left
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_G_bf_sum_right


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finsupp
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw.LC.CoreC
open PositivityTheory.Rg.Sw G
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.CoreC
theorem _root_.solution (ε : Fin m → Bool) (c : ℝ) {h g : PX m n} (hh : h ∈ F1 ε) (hg : g ∈ F2 ε) :
    contr c (h * g) = bf (fun s => (wt c s : ℂ)) h (rename pE g) := by
  conv_lhs => rw [h.as_sum, g.as_sum, Finset.sum_mul_sum, contr_sum]
  conv_rhs => rw [h.as_sum, g.as_sum, map_sum, bf_sum_left]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [contr_sum, bf_sum_right]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [contr_mono ε c ((mem_first_family_iff ε h).mp hh s hs) ((mem_second_family_iff ε g).mp hg u hu), rename_monomial, bf_monomial]
end PositivityTheory.Rg.Sw.LC.CoreC
