-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.opH_true_AT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:06:20.15531+00:00
-- url     : https://prove2.me/submissions/e5a75b53-3049-4900-874e-624000889e79

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivA
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_opH_apply
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_pderiv_true_AT
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_smul_mem_AT
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_yv_true_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.SP
theorem _root_.solution (s : ℂ) (m : ℕ) (k l : Fin n) {Q : Fm n} (hQ : Q ∈ AT n) : opH s m true k l Q ∈ AT n := by
  rw [opH_apply]
  refine Subalgebra.add_mem _ (smul_mem_AT _ ?_) (Subalgebra.sum_mem _ fun a _ => Subalgebra.sum_mem _ fun d _ =>
    smul_mem_AT _ ?_)
  · refine Subalgebra.mul_mem _ (Subalgebra.mul_mem _ ?_ (yv_true_mem _ _)) hQ
    rw [← MvPolynomial.algebraMap_eq]; exact Subalgebra.algebraMap_mem _ _
  · exact Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (yv_true_mem _ _) (yv_true_mem _ _)) (pderiv_true_AT hQ a d)
end PositivityTheory.Rg.Sw.SP
