-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.G.gf_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:45:25.364128+00:00
-- url     : https://prove2.me/submissions/9b06ac5f-8178-45b7-a712-f761d753b045

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_BfSmulRight
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_G_gf_eq

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
namespace PositivityTheory.Rg.Sw.LC.CoreC.G
theorem _root_.solution (r : ℂ) (p q : MvPolynomial τ ℂ) : gf w (r • p) q = star r * gf w p q := by
  classical
  rw [gf_eq w (p.support ∪ q.support) ((MvPolynomial.support_smul).trans Finset.subset_union_left) Finset.subset_union_right,
    gf_eq w (p.support ∪ q.support) Finset.subset_union_left Finset.subset_union_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [coeff_smul, star_mul]; ring
end PositivityTheory.Rg.Sw.LC.CoreC.G
