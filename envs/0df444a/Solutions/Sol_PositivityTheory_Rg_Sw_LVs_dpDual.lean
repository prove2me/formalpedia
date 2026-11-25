-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.dpDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:23:16.499565+00:00
-- url     : https://prove2.me/submissions/8bc2796d-f667-4cdb-b1f4-ceee4a0be558

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DpDual
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_detD_congr
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_dp_detD_const_mul
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_contDiff_det_one_add
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_contDiffAt_det_zpow
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_dp_det_one_add_mul_embOn
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_embOn_mul_embOn_compl
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_u_mul_u_conj
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_det_u_ne
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_mX_one
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_inverse_first_block_unipotent_formula
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_dp_card_blkA
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_dp_card_blkB

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
open scoped ContDiff ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution (hC : Cayley) (hU : UAct) : DpDual := by
  intro n j p q x hj hx
  obtain ⟨h1, h2⟩ := det_u_ne hx
  have hu1 : IsUnit (u1 x).det := isUnit_iff_ne_zero.2 h1
  have hu2 : IsUnit (u2 x).det := isUnit_iff_ne_zero.2 h2
  have hwinv : (wM x)⁻¹ = (u1 x)⁻¹ * u2 x := by
    rw [wM, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hu2]
  have hu1w : u1 x * (wM x)⁻¹ = u2 x := by
    rw [hwinv, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu1, Matrix.one_mul]
  have hu2w : u2 x * wM x = u1 x := by
    rw [wM, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu2, Matrix.one_mul]
  have hwc : wM x * (u1 x)ᴴ = (u2 x)ᴴ := by
    rw [wM, Matrix.mul_assoc, u_mul_u_conj hx, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu2, Matrix.one_mul]
  have hub : ub1 x = (u1 x)ᴴ := by
    have := inverse_first_block_unipotent_formula hx 0 0 (by simp) (by simp)
    rw [mX_one, Matrix.mul_one, Matrix.zero_mul, add_zero] at this
    exact this
  have key : ∀ (T : Matrix (blkA (n := n) j) (blkA j) ℂ) (S : Matrix (blkB (n := n) j) (blkB j) ℂ),
      (1 + wM x * embOn (blkB j) S).det ≠ 0 →
      fV p q (x * mX 1 (embOn (blkB j) S) (embOn (blkA j) T) 1) =
        fV p q x * (1 + (wM x)⁻¹ * embOn (blkA j) T).det ^ (p - n) *
          (1 + wM x * embOn (blkB j) S).det ^ (q - n) := by
    intro T S hb
    obtain ⟨hSQ, hTQ⟩ := embOn_mul_embOn_compl j S T
    have e1 : u1 (x * mX 1 (embOn (blkB j) S) (embOn (blkA j) T) 1) =
        u1 x * (1 + (wM x)⁻¹ * embOn (blkA j) T) := by
      rw [(hU n x _ _ _ _).1, Matrix.mul_one, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, hu1w]
    have e2 : u2 (x * mX 1 (embOn (blkB j) S) (embOn (blkA j) T) 1) =
        u2 x * (1 + wM x * embOn (blkB j) S) := by
      rw [(hU n x _ _ _ _).2, Matrix.mul_one, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, hu2w, add_comm]
    have e3 : ub1 (x * mX 1 (embOn (blkB j) S) (embOn (blkA j) T) 1) =
        (1 + embOn (blkB j) S * wM x) * ub1 x := by
      rw [inverse_first_block_unipotent_formula hx _ _ hSQ hTQ, hub, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hwc]
    unfold fV
    rw [e1, e2, e3, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul,
      Matrix.det_one_add_mul_comm (embOn (blkB j) S) (wM x), mul_zpow, mul_zpow, mul_zpow]
    have hbb : (1 + wM x * embOn (blkB j) S).det ^ q * (1 + wM x * embOn (blkB j) S).det ^ (-(n : ℤ)) =
        (1 + wM x * embOn (blkB j) S).det ^ (q - n) := by
      rw [← zpow_add₀ hb]; ring_nf
    rw [← hbb]
    ring
  have hB : ∀ T : Matrix (blkA (n := n) j) (blkA j) ℂ,
      detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
          fV p q (x * mX 1 (embOn (blkB j) S) (embOn (blkA j) T) 1)) =
        fV p q x * (1 + (wM x)⁻¹ * embOn (blkA j) T).det ^ (p - n) *
          ((∏ i ∈ Finset.range (Fintype.card (blkB (n := n) j)), (((q - n : ℤ) : ℂ) + i)) *
            minorOn (blkB j) (wM x)) := by
    intro T
    have hev : (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
          fV p q (x * mX 1 (embOn (blkB j) S) (embOn (blkA j) T) 1)) =ᶠ[nhds 0]
        fun S => (fV p q x * (1 + (wM x)⁻¹ * embOn (blkA j) T).det ^ (p - n)) *
          (1 + (wM x).submatrix (fun i : blkB (n := n) j => (i : Fin n)) (fun i : blkB (n := n) j => (i : Fin n)) *
            S).det ^ (q - n) := by
      have hc : ContinuousAt (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
          (1 + (wM x).submatrix (fun i : blkB (n := n) j => (i : Fin n)) (fun i : blkB (n := n) j => (i : Fin n)) *
            S).det) 0 :=
        (contDiff_det_one_add _ (k := 0)).continuous.continuousAt
      have h0 : (1 + (wM x).submatrix (fun i : blkB (n := n) j => (i : Fin n))
          (fun i : blkB (n := n) j => (i : Fin n)) * (0 : Matrix (blkB (n := n) j) (blkB j) ℂ)).det ≠ 0 := by simp
      filter_upwards [hc.eventually_ne h0] with S hS
      rw [← dp_det_one_add_mul_embOn] at hS ⊢
      rw [key T S hS]
    have hCB := hC (blkB (n := n) j)
      ((wM x).submatrix (fun i : blkB (n := n) j => (i : Fin n)) (fun i : blkB (n := n) j => (i : Fin n))) (q - n)
    rw [detD_congr hev, dp_detD_const_mul _ (contDiffAt_det_zpow _ _), hCB]
    rfl
  have hOuter : (fun T : Matrix (blkA (n := n) j) (blkA j) ℂ => detD (fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
        fV p q (x * mX 1 (embOn (blkB j) S) (embOn (blkA j) T) 1))) =
      fun T => (fV p q x * ((∏ i ∈ Finset.range (Fintype.card (blkB (n := n) j)), (((q - n : ℤ) : ℂ) + i)) *
            minorOn (blkB j) (wM x))) *
        (1 + ((wM x)⁻¹).submatrix (fun i : blkA (n := n) j => (i : Fin n)) (fun i : blkA (n := n) j => (i : Fin n)) *
          T).det ^ (p - n) := by
    funext T
    rw [hB T, dp_det_one_add_mul_embOn]
    ring
  have hCA := hC (blkA (n := n) j)
    (((wM x)⁻¹).submatrix (fun i : blkA (n := n) j => (i : Fin n)) (fun i : blkA (n := n) j => (i : Fin n))) (p - n)
  rw [hOuter, dp_detD_const_mul _ (contDiffAt_det_zpow _ _), hCA, dp_card_blkA hj, dp_card_blkB hj]
  simp only [minorOn]
  push_cast
  ring
end PositivityTheory.Rg.Sw.LVs
