-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.stepK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:34:14.361819+00:00
-- url     : https://prove2.me/submissions/4e69e245-27d5-4e1b-9943-27928c624d68

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_MemSpanBn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_TileIntegral
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_MemSpanMap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_mem_P
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_vol_fdP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_mem_Q
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_vol_fdQ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_P_le_Q
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_fd_uniq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_mem_reps
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_tile_measure
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
open ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory MeasureTheory.Measure Complex Module Set Submodule
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
theorem _root_.solution : StepK := by
  intro E _ _ X q n π hq hπ K hK
  have hq0 : (q : ℝ) ≠ 0 := q_ne hq
  have hQ : (0 : ℝ) < (q : ℝ) ^ Fintype.card (Idx X.dim) := pow_pos (Nat.cast_pos.mpr (by omega)) _
  have hQ' : (q : ℝ) ^ Fintype.card (Idx X.dim) ≠ 0 := hQ.ne'
  have hV : 0 < volume.real (ZSpan.fundamentalDomain X.b) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (ZSpan.measure_fundamentalDomain_ne_zero X.b)
      (ZSpan.fundamentalDomain_isBounded X.b).measure_lt_top.ne
  have ht := tile_measure (μ := volume) (bP X hq hπ) (bQ X hq) (P_le_Q X hq hπ)
  rw [vol_fdP, vol_fdQ] at ht
  have hcR : ((reps (bP X hq hπ) (bQ X hq)).card : ℝ) = (q : ℝ) ^ Fintype.card (Idx X.dim) := by
    have h3 : ((reps (bP X hq hπ) (bQ X hq)).card : ℝ) *
        ((((q : ℝ) ^ Fintype.card (Idx X.dim)) ^ 2)⁻¹ * volume.real (ZSpan.fundamentalDomain X.b)) =
        ((q : ℝ) ^ Fintype.card (Idx X.dim)) *
        ((((q : ℝ) ^ Fintype.card (Idx X.dim)) ^ 2)⁻¹ * volume.real (ZSpan.fundamentalDomain X.b)) := by
      rw [← ht]
      field_simp
      try ring
    exact mul_right_cancel₀ (mul_pos (inv_pos.mpr (pow_pos hQ 2)) hV).ne' h3
  have hcR' : (reps (bP X hq hπ) (bQ X hq)).card = q ^ Fintype.card (Idx X.dim) := by exact_mod_cast hcR
  have hmemQ : ∀ c ∈ reps (bP X hq hπ) (bQ X hq), (q : ℂ) • c ∈ X.L := by
    intro c hc
    have h1 := (mem_Q X hq c).mp (mem_reps.mp hc).2
    rwa [Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℂ] at h1
  classical
  let T := Fintype.piFinset (fun _ : Fin n => reps (bP X hq hπ) (bQ X hq))
  have hT : ∀ c ∈ T, ∀ k, (q : ℂ) • c k ∈ X.L := fun c hc k =>
    hmemQ _ (Fintype.mem_piFinset.mp hc k)
  let f : (Fin n → Vsp X.dim) → (Fin n → Vsp X.dim) := fun c =>
    if h : ∀ k, (q : ℂ) • c k ∈ X.L then Classical.choose (hK.2 c h).exists else 0
  have hf : ∀ c ∈ T, f c ∈ K ∧ ∀ k, π (c k - f c k) ∈ X.L := by
    intro c hc
    have h := hT c hc
    simp only [f, dif_pos h]
    exact Classical.choose_spec (hK.2 c h).exists
  have hcard : T.card ≤ K.card := by
    apply Finset.card_le_card_of_injOn f
    · intro c hc
      have hc' : c ∈ T := by first | exact hc | exact Finset.mem_coe.mp hc
      exact (hf c hc').1
    · intro c1 hc1 c2 hc2 heq
      have hc1' : c1 ∈ T := by first | exact hc1 | exact Finset.mem_coe.mp hc1
      have hc2' : c2 ∈ T := by first | exact hc2 | exact Finset.mem_coe.mp hc2
      funext k
      have e1 := (hf c1 hc1').2 k
      have e2 := (hf c2 hc2').2 k
      rw [heq] at e1
      have e3 : π (c1 k - c2 k) ∈ X.L := by
        have h4 := X.L.sub_mem e1 e2
        rwa [← map_sub, sub_sub_sub_cancel_right] at h4
      have hP := (mem_P X hq hπ _).mpr e3
      have hc1k := (mem_reps.mp (Fintype.mem_piFinset.mp hc1' k)).1
      have hc2k := (mem_reps.mp (Fintype.mem_piFinset.mp hc2' k)).1
      have h5 := fd_uniq (bP X hq hπ) (x := c2 k) hP (Submodule.zero_mem _)
        (by rw [sub_add_cancel]; exact hc1k) (by rw [zero_add]; exact hc2k)
      exact sub_eq_zero.mp h5
  have hTc : T.card = q ^ (Fintype.card (Idx X.dim) * n) := by
    simp only [T, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hcR', pow_mul]
  rw [← hTc]
  exact hcard
end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
