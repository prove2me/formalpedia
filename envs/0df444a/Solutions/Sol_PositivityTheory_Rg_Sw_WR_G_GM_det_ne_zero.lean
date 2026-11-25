-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.G.GM.det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:58:34.262257+00:00
-- url     : https://prove2.me/submissions/37b7e275-c933-4e83-920f-c9212a9bc789

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussS
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussM
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_GM_star_dot_herm

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
open PositivityTheory.Rg.Sw.WR.G.GM
namespace PositivityTheory.Rg.Sw.WR.G.GM
theorem _root_.solution {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) (r : ℝ) :
    (1 - (Complex.I * r) • b).det ≠ 0 := by
  intro h
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  have e1 : v = (Complex.I * r) • (b *ᵥ v) := by
    rw [sub_mulVec, one_mulVec, smul_mulVec] at hMv
    exact sub_eq_zero.mp hMv
  have e2 : star v ⬝ᵥ v = (Complex.I * r) * (star v ⬝ᵥ (b *ᵥ v)) := by
    calc star v ⬝ᵥ v = star v ⬝ᵥ ((Complex.I * r) • (b *ᵥ v)) := by rw [← e1]
      _ = _ := by rw [dotProduct_smul, smul_eq_mul]
  have hq : (star v ⬝ᵥ (b *ᵥ v)).im = 0 := by
    have := congrArg Complex.im (star_dot_herm hb v)
    simp only [Complex.star_def, Complex.conj_im] at this
    linarith
  have hs : (star v ⬝ᵥ v).im = 0 := by
    have : star (star v ⬝ᵥ v) = star v ⬝ᵥ v := by
      simp only [dotProduct, star_sum, star_mul', star_star, Pi.star_apply]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have := congrArg Complex.im this
    simp only [Complex.star_def, Complex.conj_im] at this
    linarith
  have hr : (star v ⬝ᵥ v).re = 0 := by
    rw [e2]; simp [Complex.mul_re, hq]
  exact hv (dotProduct_star_self_eq_zero.mp (Complex.ext (by simpa using hr) (by simpa using hs)))
end PositivityTheory.Rg.Sw.WR.G.GM
