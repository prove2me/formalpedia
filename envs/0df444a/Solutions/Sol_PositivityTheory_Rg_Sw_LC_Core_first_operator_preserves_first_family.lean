-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.Core.first_operator_preserves_first_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:02:45.978919+00:00
-- url     : https://prove2.me/submissions/b2aa1aa5-03a3-42e4-8edc-c4708b52baca

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_FformSmulRight
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_AdjoinFirstOperatorsPreservesFamily
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Core_pderiv_mem_supported
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Core_variable_mem_first_family

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.Core
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.Core
theorem _root_.solution (ε : Fin m → Bool) (c : ℝ) (a b : Fin m) (f : PX m n) (hf : f ∈ F1 ε) : D1 ε c a b f ∈ F1 ε := by
  have hp : ∀ k (g : PX m n), g ∈ F1 ε → pderiv k g ∈ F1 ε := fun k g hg => pderiv_mem_supported hg k
  have hm : ∀ g h : PX m n, g ∈ F1 ε → h ∈ F1 ε → g * h ∈ F1 ε := fun g h hg hh => Subalgebra.mul_mem _ hg hh
  unfold D1
  split_ifs with h1 h2 h2
  · refine Submodule.neg_mem _ (Submodule.sum_mem _ fun i _ => hm _ _ (variable_mem_first_family ε ?_) (hp _ _ hf))
    simp [inF1, h2]
  · refine Submodule.sum_mem _ fun i _ => hm _ _ (variable_mem_first_family ε ?_) (hp _ _ hf)
    simp [inF1, ← h1]; simpa using h2
  · refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ =>
      hm _ _ (hm _ _ (variable_mem_first_family ε ?_) (variable_mem_first_family ε ?_)) hf)
    · simp [inF1, h2]
    · simp [inF1]; cases hb : ε b <;> simp_all
  · refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => hp _ _ (hp _ _ hf))
end PositivityTheory.Rg.Sw.LC.Core
