-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.minorOp_true_AT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:14:10.771053+00:00
-- url     : https://prove2.me/submissions/852ad9b5-c6b1-4637-8ec9-b0a6e9e88bd8

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivA
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_smul_mem_AT
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_opH_true_AT
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_foldr_AT

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
theorem _root_.solution (s : ℂ) (m : ℕ) {ρ : ℕ} (I J : Fin ρ ↪ Fin n) {Q : Fm n} (hQ : Q ∈ AT n) :
    minorOp s m true I J Q ∈ AT n := by
  unfold minorOp
  rw [LinearMap.sum_apply]
  exact Subalgebra.sum_mem _ fun σ _ => by
    rw [LinearMap.smul_apply]
    exact smul_mem_AT _ (foldr_AT _ (fun k Q hQ => opH_true_AT s m _ _ hQ) _ hQ)
end PositivityTheory.Rg.Sw.SP
