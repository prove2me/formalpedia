-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.B1.sf_mulL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:02:15.607337+00:00
-- url     : https://prove2.me/submissions/45540c9f-1b73-4819-86a3-8ed08675c9a9

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PderivPowMonomial
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_sf_monomial
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_sf_sum
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_goodT_add_inl

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
variable (ε : Fin m → Bool)
namespace PositivityTheory.Rg.Sw.LC.B1
theorem _root_.solution (μ : σ →₀ ℕ) (hμ : ∀ k ∈ μ.support, inF1 ε k) {s : Sym m n} (h : SymbolInFirstFamily ε s) (c : ℂ) :
    SymbolInFirstFamily ε (monomial (Finsupp.mapDomain Sum.inl μ) c * s) := by
  rw [s.as_sum, Finset.mul_sum]
  refine sf_sum ε _ _ fun t ht => ?_
  rw [monomial_mul]
  exact sf_monomial ε _ _ (goodT_add_inl ε t μ (h t ht) hμ)
end PositivityTheory.Rg.Sw.LC.B1
