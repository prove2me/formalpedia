-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KShort_pow_le_covolume_f25d525c2258
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:22:01.683936+00:00
-- url     : https://prove2.me/submissions/5f7dac59-4583-4e57-89aa-e00d61256d28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsMatrix
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ShortVectors
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KShort_volume_cube_3a64e2ae9337
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KShort_norm_lt_of_mem_cube_d47b19df4675
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KShort_convex_cube_06aa38fb496f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Module Metric
noncomputable section
open GroundTheory.Heights₂.Heights.KShort
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.KShort
theorem _root_.solution (hn : 0 < n) (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] [IsZLattice ℝ L] {lam : ℝ} (hlam : 0 < lam)
    (hmin : ∀ v ∈ L, v ≠ 0 → lam ≤ ‖v‖) :
    (lam / √n) ^ n ≤ ZLattice.covolume L := by
  set b := Module.Free.chooseBasis ℤ L
  set F := ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)
  have fund : IsAddFundamentalDomain L.toAddSubgroup F volume :=
    ZLattice.isAddFundamentalDomain b volume
  have hcov : ZLattice.covolume L = volume.real F :=
    ZLattice.covolume_eq_measure_fundamentalDomain L volume fund
  have hFfin : volume F ≠ ⊤ :=
    (Bornology.IsBounded.measure_lt_top (ZSpan.fundamentalDomain_isBounded _)).ne
  have hc : 0 ≤ lam / √n := by positivity
  have hle : volume (cube n (lam / √n)) ≤ volume F * 2 ^ finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
    by_contra hlt
    push Not at hlt
    have : Countable L.toAddSubgroup := (inferInstance : Countable L)
    have hsymm : ∀ y ∈ cube n (lam / √n), -y ∈ cube n (lam / √n) := by
      intro y hy i
      have := hy i
      simpa [abs_neg] using this
    obtain ⟨x, hx0, hx⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
      (L := L.toAddSubgroup) fund hsymm (convex_cube n _) hlt
    have h1 := norm_lt_of_mem_cube hn hlam hx
    have h2 := hmin (x : EuclideanSpace ℝ (Fin n)) x.2 (by
      intro h; apply hx0; exact Subtype.ext h)
    linarith
  rw [volume_cube n hc, finrank_euclideanSpace, Fintype.card_fin] at hle
  rw [← ENNReal.ofReal_toReal hFfin] at hle
  rw [show (2 : ENNReal) ^ n = ENNReal.ofReal (2 ^ n) by
    rw [ENNReal.ofReal_pow (by norm_num)]; simp] at hle
  rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hle
  rw [hcov, measureReal_def]
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  rw [mul_pow] at hle
  nlinarith
end GroundTheory.Heights₂.Heights.KShort
