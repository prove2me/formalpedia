-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.T1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:09:39.496929+00:00
-- url     : https://prove2.me/submissions/3f8d4593-ec6f-49dc-93bb-604035bdb5bb

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoeffSmulX
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PartialDerivZeroSecondFamily
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_pE_pE
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_partial_deriv_mem_second_family
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_variable_mul_mem_first_family
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_contr_eq_bf
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_G_bf_X_mul
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
    contr c (X k * h * g) = ((2 * c : ℝ) : ℂ) * contr c (h * pderiv (pE k) g) := by
  rw [contr_eq_bf ε c (variable_mul_mem_first_family ε hk hh) hg, contr_eq_bf ε c hh (partial_deriv_mem_second_family ε _ hg), bf_X_mul _ (wt_step c)]
  congr 2
  have := pderiv_rename (R := ℂ) (τ := Fin m × Fin n × Bool) (σ := Fin m × Fin n × Bool) pE.injective (pE k) g
  rw [pE_pE] at this
  exact this
end PositivityTheory.Rg.Sw.LC.CoreC
