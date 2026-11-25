-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.T2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:09:45.645061+00:00
-- url     : https://prove2.me/submissions/309f58a9-66ef-4154-90fb-c6aca0891527

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoeffSmulX
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PartialDerivZeroSecondFamily
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_pE_pE
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_first_family_partner_iff
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_partial_deriv_mem_first_family
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_variable_mul_mem_second_family
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_contr_eq_bf
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_G_bf_pderiv
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_wt_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Sw.LC.CoreC.pE_pE

set_option autoImplicit false
noncomputable section
open MvPolynomial Finsupp
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw.LC.CoreC
open PositivityTheory.Rg.Sw G
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.CoreC
theorem _root_.solution (ε : Fin m → Bool) {c : ℝ} {k} (hk : inF1 ε k) {h g : PX m n} (hh : h ∈ F1 ε) (hg : g ∈ F2 ε) :
    ((2 * c : ℝ) : ℂ) * contr c (pderiv k h * g) = contr c (h * (X (pE k) * g)) := by
  rw [contr_eq_bf ε c (partial_deriv_mem_first_family ε _ hh) hg,
    contr_eq_bf ε c hh (variable_mul_mem_second_family ε (fun h' => (first_family_partner_iff ε k).mp h' hk) hg), bf_pderiv _ (wt_step c)]
  congr 1
  rw [map_mul, rename_X, pE_pE]
end PositivityTheory.Rg.Sw.LC.CoreC
