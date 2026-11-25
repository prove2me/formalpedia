-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.Z.det_X_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:06:27.131355+00:00
-- url     : https://prove2.me/submissions/129b9abb-1990-481b-88fb-1b215181fd7e

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainA
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_herm_star
import Theorems.Thm_P2M_PositivityTheory_Rg_Sw_WR_Z_smul_mulVec__f726d66f1ccf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.Z
theorem _root_.solution (s : ℂ) (hs : s = 1 ∨ s = -1) (y : E n) : (1 - (Complex.I * s) • herm y).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hXv⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 h0
  set q : ℂ := star v ⬝ᵥ (herm y *ᵥ v) with hq
  have hqr : star q = q := by
    rw [hq]
    simp only [dotProduct, mulVec, Pi.star_apply, star_sum, star_mul', star_star, herm_star, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hqim : q.im = 0 := Complex.conj_eq_iff_im.1 hqr
  have hv2 : v = (Complex.I * s) • (herm y *ᵥ v) := by
    rw [sub_mulVec, one_mulVec, smul_mulVec'] at hXv
    exact sub_eq_zero.1 hXv
  have key : star v ⬝ᵥ v = (Complex.I * s) * q := by
    rw [hq, ← smul_eq_mul, ← dotProduct_smul, ← hv2]
  have hre : (star v ⬝ᵥ v).re = ∑ i, Complex.normSq (v i) := by
    simp only [dotProduct, Pi.star_apply, Complex.re_sum, Complex.mul_re, Complex.star_def, Complex.conj_re,
      Complex.conj_im, Complex.normSq_apply]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hpos : 0 < (star v ⬝ᵥ v).re := by
    rw [hre]
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
    exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ _, Complex.normSq_pos.2 hi⟩
  have h0' : (star v ⬝ᵥ v).re = 0 := by
    rw [key]
    rcases hs with rfl | rfl <;> simp [Complex.mul_re, hqim]
  linarith
end PositivityTheory.Rg.Sw.WR.Z
