-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.G.gf_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:40:42.522493+00:00
-- url     : https://prove2.me/submissions/4a9f5fea-1e5b-4d51-a670-b3b04da20261

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_BfSmulRight

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
variable (w)
namespace PositivityTheory.Rg.Sw.LC.CoreC.G
theorem _root_.solution (hs : ∀ s, star (w s) = w s) (hp : ∀ s, 0 < (w s).re) (p : MvPolynomial τ ℂ) (h : p ≠ 0) :
    0 < (gf w p p).re := by
  unfold gf
  rw [Finset.union_self, Complex.re_sum]
  obtain ⟨s, hs0⟩ := (MvPolynomial.ne_zero_iff).mp h
  have hmem : s ∈ p.support := MvPolynomial.mem_support_iff.mpr hs0
  have key : ∀ t, (star (p.coeff t) * p.coeff t * w t).re = Complex.normSq (p.coeff t) * (w t).re := by
    intro t
    have hw' : (w t).im = 0 := by
      have := congrArg Complex.im (hs t); simp at this; linarith
    rw [show star (p.coeff t) * p.coeff t = (Complex.normSq (p.coeff t) : ℂ) by
      rw [Complex.normSq_eq_conj_mul_self]; rfl]
    simp [Complex.mul_re, hw']
  refine Finset.sum_pos' (fun t _ => ?_) ⟨s, hmem, ?_⟩
  · rw [key]; exact mul_nonneg (Complex.normSq_nonneg _) (hp t).le
  · rw [key]; exact mul_pos (Complex.normSq_pos.mpr hs0) (hp s)
end PositivityTheory.Rg.Sw.LC.CoreC.G
