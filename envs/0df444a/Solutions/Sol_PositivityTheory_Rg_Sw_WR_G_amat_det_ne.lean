-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.G.amat_det_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:51:32.735247+00:00
-- url     : https://prove2.me/submissions/953112c8-ad43-4ff4-9694-709c6b8a52c4

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GWickB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_EvXPderivPhiP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix MvPolynomial
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.G
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.G
theorem _root_.solution (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) (t : ℝ) {b : Matrix (Fin n) (Fin n) ℂ}
    (hb : b.IsHermitian) (a : Fin m) : (Amat ε c t b a).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have hA : Amat ε c t b a *ᵥ v = (c : ℂ) • v - (Complex.I * t * sgn ε a) • (bᵀ *ᵥ v) := by
    rw [Amat, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, one_mulVec]
  have key : (c : ℂ) * (star v ⬝ᵥ v) - (Complex.I * t * sgn ε a) * (star v ⬝ᵥ (bᵀ *ᵥ v)) = 0 := by
    have h1 : star v ⬝ᵥ (Amat ε c t b a *ᵥ v) = 0 := by rw [hv, dotProduct_zero]
    rw [hA, dotProduct_sub, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul] at h1
    exact h1
  have hq : (star v ⬝ᵥ (bᵀ *ᵥ v)).im = 0 := hb.transpose.im_star_dotProduct_mulVec_self v
  have hd : (star v ⬝ᵥ v).im = 0 := by
    have := Matrix.isHermitian_one.im_star_dotProduct_mulVec_self (𝕜 := ℂ) v
    rwa [one_mulVec] at this
  have hq' : star v ⬝ᵥ (bᵀ *ᵥ v) = ((star v ⬝ᵥ (bᵀ *ᵥ v)).re : ℂ) := Complex.ext (by simp) (by simp [hq])
  have hs' : sgn ε a = ((if ε a then 1 else -1 : ℝ) : ℂ) := by unfold sgn; split_ifs <;> simp
  have h0re : (Complex.I * t * sgn ε a * (star v ⬝ᵥ (bᵀ *ᵥ v))).re = 0 := by
    rw [hq', hs']; simp [Complex.mul_re]
  have hre := congrArg Complex.re key
  rw [Complex.sub_re, h0re, Complex.re_ofReal_mul, Complex.zero_re, sub_zero] at hre
  have hdre : (star v ⬝ᵥ v).re = 0 := by
    rcases mul_eq_zero.mp hre with h | h
    · exact absurd h hc.ne'
    · exact h
  have hd0 : star v ⬝ᵥ v = 0 := Complex.ext hdre hd
  exact hv0 (dotProduct_star_self_eq_zero.mp hd0)
end PositivityTheory.Rg.Sw.WR.G
