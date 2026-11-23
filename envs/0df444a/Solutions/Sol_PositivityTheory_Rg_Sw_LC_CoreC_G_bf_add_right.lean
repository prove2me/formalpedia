-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.G.bf_add_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:23:24.391498+00:00
-- url     : https://prove2.me/submissions/be57f960-2a4f-4ee0-9e36-f2f2d77aaa27

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_BfSmulRight
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_G_bf_eq

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
theorem _root_.solution (w : (τ →₀ ℕ) → ℂ) (p q q' : MvPolynomial τ ℂ) : bf w p (q + q') = bf w p q + bf w p q' := by
  classical
  have h1 := support_add (p := q) (q := q')
  rw [bf_eq w (p.support ∪ (q.support ∪ q'.support)) Finset.subset_union_left (h1.trans Finset.subset_union_right),
    bf_eq w (p.support ∪ (q.support ∪ q'.support)) Finset.subset_union_left
      ((Finset.subset_union_left).trans Finset.subset_union_right),
    bf_eq w (p.support ∪ (q.support ∪ q'.support)) Finset.subset_union_left
      ((Finset.subset_union_right).trans Finset.subset_union_right), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [coeff_add]; ring
end PositivityTheory.Rg.Sw.LC.CoreC.G
