-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.B1.opMono_shiftL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:52:59.228908+00:00
-- url     : https://prove2.me/submissions/34267d02-b81f-4b0a-a2f6-f1e6c4dce366

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PderivPowMonomial
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_comap_inl_add
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_inr_add

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
theorem _root_.solution (t : σ ⊕ σ →₀ ℕ) (μ : σ →₀ ℕ) (f : PX m n) :
    opMono (t + Finsupp.mapDomain Sum.inl μ) f = monomial μ 1 * opMono t f := by
  unfold opMono
  rw [comap_inl_add]
  simp only [inr_add]
  rw [← mul_assoc, monomial_mul, one_mul, add_comm]
end PositivityTheory.Rg.Sw.LC.B1
