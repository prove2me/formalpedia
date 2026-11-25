-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.B1.list_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:52:57.043221+00:00
-- url     : https://prove2.me/submissions/a691280e-42aa-4714-8746-640c85733674

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PderivPowMonomial
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_pderiv_pow_monomial
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_list_single_apply

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.B1
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
local notation "σ" => Fin m × Fin n × Bool
namespace PositivityTheory.Rg.Sw.LC.B1
theorem _root_.solution (γ : σ → ℕ) (l : List σ) (hl : l.Nodup) (s : σ →₀ ℕ) (a : ℂ) :
    ((l.map fun k => (pderiv (R := ℂ) k).toLinearMap ^ (γ k)).prod (monomial s a) : PX m n) =
      monomial (s - (l.map fun k => Finsupp.single k (γ k)).sum)
        (a * (l.map fun k => ((s k).descFactorial (γ k) : ℂ)).prod) := by
  induction l generalizing s a with
  | nil => simp
  | cons k l ih =>
    rw [List.nodup_cons] at hl
    simp only [List.map_cons, List.prod_cons, List.sum_cons, Module.End.mul_apply]
    rw [ih hl.2, pderiv_pow_monomial]
    have hk := list_single_apply γ l k hl.1
    have e1 : s - (l.map fun k => Finsupp.single k (γ k)).sum - Finsupp.single k (γ k) =
        s - (Finsupp.single k (γ k) + (l.map fun k => Finsupp.single k (γ k)).sum) := by
      ext k'
      simp only [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_apply]
      split_ifs with h
      · subst h; rw [hk]; omega
      · omega
    have e2 : (s - (l.map fun k => Finsupp.single k (γ k)).sum) k = s k := by
      simp [hk]
    rw [e1, e2]
    congr 1
    ring
end PositivityTheory.Rg.Sw.LC.B1
