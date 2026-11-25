-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.contr_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:54:34.129984+00:00
-- url     : https://prove2.me/submissions/71b761c6-e6ae-41b8-a082-386845ed00bc

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoeffSmulX
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PartialDerivZeroSecondFamily
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_contr_monomial
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_bal_iff
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_piC_eq_wt

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
theorem _root_.solution (ε : Fin m → Bool) (c : ℝ) {s u : Fin m × Fin n × Bool →₀ ℕ} (hs : ∀ k ∈ s.support, inF1 ε k)
    (hu : ∀ k ∈ u.support, ¬ inF1 ε k) (a b : ℂ) :
    contr c (monomial s a * monomial u b) = if s = u.mapDomain pE then a * b * (wt c s : ℂ) else 0 := by
  rw [monomial_mul, contr_monomial]
  by_cases h : s = u.mapDomain pE
  · rw [if_pos ((bal_iff ε hs hu).mpr h), if_pos h, piC_eq_wt ε c hu h]
  · rw [if_neg (fun hb => h ((bal_iff ε hs hu).mp hb)), if_neg h]
end PositivityTheory.Rg.Sw.LC.CoreC
