-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.gen_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:03:54.475306+00:00
-- url     : https://prove2.me/submissions/1074c3e8-624c-4cdd-8000-bcedea73bdaa

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_BfSmulRight
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoeffSmulX
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_KopL_apply
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_term_mem_box

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
theorem _root_.solution (ε : Fin m → Bool) (i j : Fin n) (R : Set (Fin m → ℕ)) (s : Fin m × Fin n × Bool →₀ ℕ)
    (hs : ∀ k ∈ s.support, inF1 ε k) (hR : rdeg ε s ∈ R) : KopL ε i j (monomial s (1 : ℂ)) ∈ box ε R := by
  rw [KopL_apply]
  refine Submodule.sub_mem _ (Submodule.sum_mem _ fun a ha => ?_) (Submodule.sum_mem _ fun a ha => ?_)
  · have ha' : ε a = true := (Finset.mem_filter.mp ha).2
    exact term_mem_box ε R (a, i, false) (a, j, false) (by simp [inF1, ha']) (by simp [inF1, ha']) rfl s hs hR
  · have ha' : ε a = false := (Finset.mem_filter.mp ha).2
    exact term_mem_box ε R (a, j, true) (a, i, true) (by simp [inF1, ha']) (by simp [inF1, ha']) rfl s hs hR
end PositivityTheory.Rg.Sw.LC.CoreC
