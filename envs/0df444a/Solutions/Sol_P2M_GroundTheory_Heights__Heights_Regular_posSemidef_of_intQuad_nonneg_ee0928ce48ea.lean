-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_posSemidef_of_intQuad_nonneg_ee0928ce48ea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:49:41.51832+00:00
-- url     : https://prove2.me/submissions/fce47b19-80a8-4c08-8f4e-e2bcb74e3d18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PosSemidefOfIntQuadNonneg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_intQuad_cast_144727a14362

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Matrix Topology Filter
noncomputable section
namespace GroundTheory.Heights₂.Heights.Regular
theorem _root_.solution {g : ℕ} (B : Matrix (Fin g) (Fin g) ℤ) (hB : Bᵀ = B)
    (h : ∀ v, 0 ≤ intQuad B v) : (B.map (Int.cast : ℤ → ℝ)).PosSemidef := by
  refine .of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · change (B.map (Int.cast : ℤ → ℝ))ᴴ = _
    rw [conjTranspose, ← transpose_map, hB]
    ext i j
    simp
  rw [star_trivial]
  set M := B.map (Int.cast : ℤ → ℝ)
  set q : (Fin g → ℝ) → ℝ := fun y => y ⬝ᵥ M *ᵥ y with hq
  have hqc : Continuous q := by
    simp only [hq, dotProduct, mulVec]
    fun_prop
  let m : ℕ → Fin g → ℤ := fun N k => ⌊(N : ℝ) * x k⌋
  let y : ℕ → Fin g → ℝ := fun N => ((N : ℝ)⁻¹) • fun k => ((m N k : ℤ) : ℝ)
  have hy : Tendsto y atTop (𝓝 x) := by
    refine tendsto_pi_nhds.2 fun k => ?_
    have hlow : Tendsto (fun N : ℕ => x k - 1 / (N : ℝ)) atTop (𝓝 (x k)) := by
      simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => x k) atTop (𝓝 (x k))).sub
        tendsto_one_div_atTop_nhds_zero_nat
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with N hN
      have hN' : (0 : ℝ) < N := by exact_mod_cast hN
      have := Int.lt_floor_add_one ((N : ℝ) * x k)
      simp only [y, m, Pi.smul_apply, smul_eq_mul]
      rw [sub_le_iff_le_add, one_div, ← mul_add_one, inv_mul_eq_div, le_div_iff₀ hN']
      nlinarith
    · filter_upwards [eventually_gt_atTop 0] with N hN
      have hN' : (0 : ℝ) < N := by exact_mod_cast hN
      have := Int.floor_le ((N : ℝ) * x k)
      simp only [y, m, Pi.smul_apply, smul_eq_mul]
      rw [inv_mul_eq_div, div_le_iff₀ hN']
      linarith
  have hnn : ∀ N, 0 ≤ q (y N) := fun N => by
    simp only [hq, y, smul_dotProduct, mulVec_smul, dotProduct_smul, smul_eq_mul]
    have := intQuad_cast (R := ℝ) B (m N)
    rw [← this, ← mul_assoc]
    exact mul_nonneg (mul_self_nonneg _) (by exact_mod_cast h (m N))
  exact ge_of_tendsto' ((hqc.tendsto x).comp hy) hnn
end GroundTheory.Heights₂.Heights.Regular
