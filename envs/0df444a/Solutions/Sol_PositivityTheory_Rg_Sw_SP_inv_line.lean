-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.inv_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:50:14.805905+00:00
-- url     : https://prove2.me/submissions/d6a30f6d-fc06-4cc7-a5a2-cdbbce1b8b44

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeH
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_det_affine_eventually
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
open PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.SP
theorem _root_.solution (M0 A : Matrix (Fin n) (Fin n) ℂ) (h : M0.det ≠ 0)
    (hdiff : ∀ a d, DifferentiableAt ℂ (fun t : ℂ => (M0 + t • A)⁻¹ a d) 0) (a d : Fin n) :
    HasDerivAt (fun t : ℂ => (M0 + t • A)⁻¹ a d) ((-(M0⁻¹ * A * M0⁻¹)) a d) 0 := by
  set D : Matrix (Fin n) (Fin n) ℂ := fun a d => deriv (fun t : ℂ => (M0 + t • A)⁻¹ a d) 0 with hD
  have hY : ∀ a d, HasDerivAt (fun t : ℂ => (M0 + t • A)⁻¹ a d) (D a d) 0 := fun a d => (hdiff a d).hasDerivAt

  have hid : ∀ i j, HasDerivAt (fun t : ℂ => ((M0 + t • A) * (M0 + t • A)⁻¹) i j) ((A * M0⁻¹ + M0 * D) i j) 0 := by
    intro i j
    have e : (fun t : ℂ => ((M0 + t • A) * (M0 + t • A)⁻¹) i j) =
        fun t : ℂ => ∑ k, (M0 i k + t * A i k) * (M0 + t • A)⁻¹ k j := by
      funext t; simp [Matrix.mul_apply]
    rw [e]
    have hs : HasDerivAt (fun t : ℂ => ∑ k, (M0 i k + t * A i k) * (M0 + t • A)⁻¹ k j)
        (∑ k, (A i k * M0⁻¹ k j + M0 i k * D k j)) 0 := by
      apply HasDerivAt.fun_sum
      intro k _
      have h1 : HasDerivAt (fun t : ℂ => M0 i k + t * A i k) (A i k) 0 := by
        simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (A i k)).const_add (M0 i k)
      simpa using h1.fun_mul (hY k j)
    convert hs using 1
    simp [Matrix.add_apply, Matrix.mul_apply, Finset.sum_add_distrib]
  have hconst : ∀ i j, HasDerivAt (fun t : ℂ => ((M0 + t • A) * (M0 + t • A)⁻¹) i j) 0 0 := by
    intro i j
    have hev : (fun t : ℂ => ((M0 + t • A) * (M0 + t • A)⁻¹) i j) =ᶠ[𝓝 0] fun _ => (1 : Matrix (Fin n) (Fin n) ℂ) i j := by
      filter_upwards [det_affine_eventually M0 A h] with t ht
      rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr ht)]
    exact (hasDerivAt_const (0 : ℂ) ((1 : Matrix (Fin n) (Fin n) ℂ) i j)).congr_of_eventuallyEq hev
  have hzero : A * M0⁻¹ + M0 * D = 0 := by
    ext i j
    exact (hid i j).unique (hconst i j)
  have hDv : D = -(M0⁻¹ * A * M0⁻¹) := by
    have h1 : M0⁻¹ * M0 = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr h)
    have h2 : M0 * D = -(A * M0⁻¹) := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact hzero
    calc D = M0⁻¹ * M0 * D := by rw [h1, Matrix.one_mul]
      _ = M0⁻¹ * (M0 * D) := by rw [Matrix.mul_assoc]
      _ = -(M0⁻¹ * A * M0⁻¹) := by rw [h2, Matrix.mul_neg, Matrix.mul_assoc]
  rw [← hDv]
  exact hY a d
end PositivityTheory.Rg.Sw.SP
