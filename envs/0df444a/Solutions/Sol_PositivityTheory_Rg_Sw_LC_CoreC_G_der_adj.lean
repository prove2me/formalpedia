-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.G.der_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:10:00.255239+00:00
-- url     : https://prove2.me/submissions/9f094d54-8d1b-43ef-8a6f-b413cd03a7b0

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_BfSmulRight
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_G_gf_smul_left
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_G_gf_smul_right
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_G_gf_sum_left
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_G_gf_sum_right
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_G_gf_adj
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_G_der_expand2

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
theorem _root_.solution {w : (τ →₀ ℕ) → ℂ} (κ : ℂ) (hw : ∀ s k, w (Finsupp.single k 1 + s) = κ * ((s k : ℂ) + 1) * w s)
    (D D' : Derivation ℂ (MvPolynomial τ ℂ) (MvPolynomial τ ℂ))
    (hlin : ∀ v, D (X v) = ∑ u, (D (X v)).coeff (Finsupp.single u 1) • X u)
    (hlin' : ∀ v, D' (X v) = ∑ u, (D' (X v)).coeff (Finsupp.single u 1) • X u)
    (htr : ∀ v u, (D' (X u)).coeff (Finsupp.single v 1) = star ((D (X v)).coeff (Finsupp.single u 1)))
    (p q : MvPolynomial τ ℂ) : gf w (D p) q = gf w p (D' q) := by
  rw [der_expand2 D hlin p, der_expand2 D' hlin' q]
  simp_rw [gf_sum_left, gf_sum_right, gf_smul_left, gf_smul_right, gf_adj κ hw, htr]
  rw [Finset.sum_comm]
end PositivityTheory.Rg.Sw.LC.CoreC.G
