-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.G.gf_sum_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:45:25.710104+00:00
-- url     : https://prove2.me/submissions/740bbb42-fbe4-4c69-bf13-62ee04a18b2a

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_BfSmulRight
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_G_gf_add_left

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
theorem _root_.solution {ι : Type} (I : Finset ι) (f : ι → MvPolynomial τ ℂ) (q : MvPolynomial τ ℂ) :
    gf w (∑ i ∈ I, f i) q = ∑ i ∈ I, gf w (f i) q := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [gf]
  | insert a I ha ih => rw [Finset.sum_insert ha, gf_add_left, ih, Finset.sum_insert ha]
end PositivityTheory.Rg.Sw.LC.CoreC.G
