-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.G.der_expand2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:52:24.726736+00:00
-- url     : https://prove2.me/submissions/75cc9b03-3e00-47aa-a8f7-7eb79befc8b2

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_BfSmulRight
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_G_der_expand

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.CoreC PositivityTheory.Rg.Sw.LC.CoreC.G
variable {τ : Type} [Fintype τ] [DecidableEq τ]
variable (w : (τ →₀ ℕ) → ℂ)
variable {w} (κ : ℂ) (hw : ∀ s k, w (Finsupp.single k 1 + s) = κ * ((s k : ℂ) + 1) * w s)
include hw
omit hw
namespace PositivityTheory.Rg.Sw.LC.CoreC.G
theorem _root_.solution (D : Derivation ℂ (MvPolynomial τ ℂ) (MvPolynomial τ ℂ))
    (hlin : ∀ v, D (X v) = ∑ u, (D (X v)).coeff (Finsupp.single u 1) • X u) (p : MvPolynomial τ ℂ) :
    D p = ∑ v, ∑ u, (D (X v)).coeff (Finsupp.single u 1) • (X u * pderiv v p) := by
  rw [der_expand D p]
  refine Finset.sum_congr rfl fun v _ => ?_
  conv_lhs => rw [hlin v]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [smul_mul_assoc]
end PositivityTheory.Rg.Sw.LC.CoreC.G
