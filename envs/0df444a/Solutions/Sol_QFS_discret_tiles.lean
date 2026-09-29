-- Prove2me | solution 1 for QFS.discret_tiles
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-07T09:07:14.688556+00:00
-- url     : https://prove2.me/submissions/eabd01ec-8e1f-41a2-9908-3c4d0572f774

import Theorems.Thm_QFS_corollaryThreeOne
import Theorems.Thm_QFS_lemma_cubes
import Theorems.Thm_QFS_measurableSet_cube
import Theorems.Thm_QFS_volume_cube
import Definitions.Def_QFS_Section3Kernel
import Definitions.Def_QFS_Translate
import Definitions.Def_QFS_Defs
import Definitions.Def_QFS_ConeGap
import Definitions.Def_QFS_RefCones
import Definitions.Def_QFS_Section4
import Definitions.Def_QFS_Cubes
import Definitions.Def_QFS_Section3
import Definitions.Def_QFS_Section5
import Definitions.Def_QFS_Section1
import Definitions.Def_QFS_ThinCones
import Definitions.Def_QFS_Renormalization
import Definitions.Def_QFS_FirstJump
import Definitions.Def_QFS_Assembly
import Definitions.Def_QFS_PathAssembly
import Definitions.Def_QFS_BlockPaths
import Definitions.Def_QFS_Section6
import Definitions.Def_QFS_Rescaling
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open Real Set Metric ENNReal MeasureTheory Filter

open QFS

variable {d : ℕ}

lemma volume_cube_prod {h : ℝ} (hh : 0 < h) (x y : EuclideanSpace ℝ (Fin d)) :
    volume (cube h x ×ˢ cube h y) = ENNReal.ofReal (h ^ d) * ENNReal.ofReal (h ^ d) := by
  rw [Measure.volume_eq_prod, Measure.prod_prod, volume_cube hh, volume_cube hh]

/-- The tile integral of the jump kernel over a pair of cubes is dominated by
`h^{2d}(2√d)^{d+α}` times its value at the two lattice points — Lemma 3.4 on
`hℤ^d`, integrated. -/
lemma tile_jumpKernel_le {h : ℝ} (hh : 0 < h) (hd : 0 < d) {α : ℝ} (hα : 0 ≤ α)
    {x y : EuclideanSpace ℝ (Fin d)} (hx : x ∈ scaledLattice d h)
    (hy : y ∈ scaledLattice d h) (hxy : Real.sqrt d * h < ‖x - y‖) :
    ∫⁻ q in cube h x ×ˢ cube h y, jumpKernel d α q.1 q.2
      ≤ ENNReal.ofReal ((h ^ (2 * d)) * (2 * Real.sqrt d) ^ ((d:ℝ) + α))
        * jumpKernel d α x y := by
  have hsd : (0:ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hxy0 : (0:ℝ) < ‖x - y‖ := lt_trans (by positivity) hxy
  have hexp : (-(d:ℝ) - α) ≤ 0 := by
    have : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg d
    linarith
  have hpt : ∀ q ∈ cube h x ×ˢ cube h y,
      jumpKernel d α q.1 q.2
        ≤ ENNReal.ofReal ((2 * Real.sqrt d) ^ ((d:ℝ) + α)) * jumpKernel d α x y := by
    rintro ⟨s, t⟩ ⟨hs, ht⟩
    obtain ⟨hlow, -⟩ := lemma_cubes hh hx hy hxy hs ht
    have hkey : ‖s - t‖ ^ (-(d:ℝ) - α)
        ≤ (2 * Real.sqrt d) ^ ((d:ℝ) + α) * ‖x - y‖ ^ (-(d:ℝ) - α) := by
      have hle : ‖x - y‖ / (2 * Real.sqrt d) ≤ ‖s - t‖ := by
        have h1 : (1 / (2 * Real.sqrt d) * ‖x - y‖) * (2 * Real.sqrt d)
            < ‖s - t‖ * (2 * Real.sqrt d) := mul_lt_mul_of_pos_right hlow (by positivity)
        have h2 : (1 / (2 * Real.sqrt d) * ‖x - y‖) * (2 * Real.sqrt d) = ‖x - y‖ := by
          field_simp
        rw [div_le_iff₀ (by positivity)]
        linarith [h1, h2.le, h2.ge]
      have h1 := Real.rpow_le_rpow_of_nonpos (by positivity) hle hexp
      have h2 : (‖x - y‖ / (2 * Real.sqrt d)) ^ (-(d:ℝ) - α)
          = (2 * Real.sqrt d) ^ ((d:ℝ) + α) * ‖x - y‖ ^ (-(d:ℝ) - α) := by
        rw [Real.div_rpow (norm_nonneg _) (by positivity)]
        have hneg : (-(d:ℝ) - α) = -((d:ℝ) + α) := by ring
        rw [hneg, Real.rpow_neg (by positivity : (0:ℝ) ≤ 2 * Real.sqrt d)]
        field_simp
      linarith [h1, h2.le, h2.ge]
    calc jumpKernel d α s t
        ≤ ENNReal.ofReal ((2 * Real.sqrt d) ^ ((d:ℝ) + α) * ‖x - y‖ ^ (-(d:ℝ) - α)) := by
          exact ENNReal.ofReal_le_ofReal hkey
      _ = ENNReal.ofReal ((2 * Real.sqrt d) ^ ((d:ℝ) + α)) * jumpKernel d α x y := by
          rw [jumpKernel, ENNReal.ofReal_mul (by positivity)]
  calc ∫⁻ q in cube h x ×ˢ cube h y, jumpKernel d α q.1 q.2
      ≤ ∫⁻ _ in cube h x ×ˢ cube h y,
          ENNReal.ofReal ((2 * Real.sqrt d) ^ ((d:ℝ) + α)) * jumpKernel d α x y := by
        refine lintegral_mono_ae (ae_restrict_of_forall_mem
          ((measurableSet_cube hh x).prod (measurableSet_cube hh y)) hpt)
    _ = ENNReal.ofReal ((h ^ (2 * d)) * (2 * Real.sqrt d) ^ ((d:ℝ) + α))
          * jumpKernel d α x y := by
        rw [setLIntegral_const, volume_cube_prod hh,
          ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ h ^ (2 * d))]
        rw [show (h:ℝ) ^ (2 * d) = h ^ d * h ^ d by rw [two_mul, pow_add],
          ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ h ^ d)]
        ring

/-- The tile-integrated form is `h^{2d}` times the discrete-kernel form: `ω^k_h`
*is* the tile average of `k`. -/
lemma discreteFormOn_tile_eq {h : ℝ} (hh : 0 < h) (S : Set (EuclideanSpace ℝ (Fin d)))
    (R₀ : ℝ) (k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) :
    discreteFormOn (scaledLattice d h) S R₀
        (fun x y => ∫⁻ q in cube h x ×ˢ cube h y, k q.1 q.2) f
      = ENNReal.ofReal (h ^ (2 * d)) *
        discreteFormOn (scaledLattice d h) S R₀ (discreteKernel d k h) f := by
  have hcoe : ∀ x y : EuclideanSpace ℝ (Fin d),
      (∫⁻ q in cube h x ×ˢ cube h y, k q.1 q.2)
        = ENNReal.ofReal (h ^ (2 * d)) * discreteKernel d k h x y := by
    intro x y
    rw [discreteKernel, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
      mul_inv_cancel₀ (by positivity : (h:ℝ) ^ (2 * d) ≠ 0), ENNReal.ofReal_one, one_mul]
  simp only [discreteFormOn, hcoe]
  rw [← ENNReal.tsum_mul_left]
  exact tsum_congr fun p => by ring

theorem solution (ϑ Λ α : ℝ) (hd : 0 < d) (hϑ : 0 < ϑ) (hΛ : 1 ≤ Λ) (hα : 0 < α)
    (hα2 : α < 2) :
    ∃ κ c : ℝ, 1 ≤ κ ∧ 0 < c ∧
      ∀ Γ : Configuration (EuclideanSpace ℝ (Fin d)), IsBounded Γ ϑ →
      ∀ h : ℝ, 0 < h →
      ∀ k : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ≥0∞,
        DiscreteKernelBounds Γ α Λ (Real.sqrt d * h) (scaledLattice d h)
          (discreteKernel d k h) →
      ∀ (x₀ : EuclideanSpace ℝ (Fin d)) (R : ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ),
        0 < R →
        ENNReal.ofReal c *
            discreteFormOn (scaledLattice d h) (ball x₀ R) (Real.sqrt d * h)
              (fun x y => ∫⁻ q in cube h x ×ˢ cube h y, jumpKernel d α q.1 q.2) f
          ≤ discreteFormOn (scaledLattice d h) (ball x₀ (κ * R)) (Real.sqrt d * h)
              (fun x y => ∫⁻ q in cube h x ×ˢ cube h y, k q.1 q.2) f := by
  have hsd : (0:ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  obtain ⟨κ, c₁, hκ, hc₁, hmain⟩ :=
    corollaryThreeOne (d := d) ϑ Λ α (Real.sqrt d) hϑ hΛ hα hα2 hsd
  refine ⟨κ, ((2 * Real.sqrt d) ^ ((d:ℝ) + α) * c₁)⁻¹, hκ, by positivity, ?_⟩
  intro Γ hΓ h hh k hk x₀ R f hR
  have hleft : discreteFormOn (scaledLattice d h) (ball x₀ R) (Real.sqrt d * h)
        (fun x y => ∫⁻ q in cube h x ×ˢ cube h y, jumpKernel d α q.1 q.2) f
      ≤ ENNReal.ofReal ((h ^ (2 * d)) * (2 * Real.sqrt d) ^ ((d:ℝ) + α)) *
        discreteFormOn (scaledLattice d h) (ball x₀ R) (Real.sqrt d * h)
          (jumpKernel d α) f := by
    simp only [discreteFormOn]
    rw [← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun p => ?_
    obtain ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩, hsep⟩ := p.2
    calc ENNReal.ofReal ((f p.1.1 - f p.1.2) ^ 2) *
          ∫⁻ q in cube h p.1.1 ×ˢ cube h p.1.2, jumpKernel d α q.1 q.2
        ≤ ENNReal.ofReal ((f p.1.1 - f p.1.2) ^ 2) *
            (ENNReal.ofReal ((h ^ (2 * d)) * (2 * Real.sqrt d) ^ ((d:ℝ) + α))
              * jumpKernel d α p.1.1 p.1.2) :=
          mul_le_mul' le_rfl (tile_jumpKernel_le hh hd hα.le hx2 hy2 hsep)
      _ = ENNReal.ofReal ((h ^ (2 * d)) * (2 * Real.sqrt d) ^ ((d:ℝ) + α)) *
            (ENNReal.ofReal ((f p.1.1 - f p.1.2) ^ 2) * jumpKernel d α p.1.1 p.1.2) := by
          ring
  have hcor := hmain Γ hΓ h hh (discreteKernel d k h) hk x₀ R f hR
  conv_rhs => rw [discreteFormOn_tile_eq hh]
  calc ENNReal.ofReal ((2 * Real.sqrt d) ^ ((d:ℝ) + α) * c₁)⁻¹ *
        discreteFormOn (scaledLattice d h) (ball x₀ R) (Real.sqrt d * h)
          (fun x y => ∫⁻ q in cube h x ×ˢ cube h y, jumpKernel d α q.1 q.2) f
      ≤ ENNReal.ofReal ((2 * Real.sqrt d) ^ ((d:ℝ) + α) * c₁)⁻¹ *
        (ENNReal.ofReal ((h ^ (2 * d)) * (2 * Real.sqrt d) ^ ((d:ℝ) + α)) *
          discreteFormOn (scaledLattice d h) (ball x₀ R) (Real.sqrt d * h)
            (jumpKernel d α) f) := mul_le_mul' le_rfl hleft
    _ ≤ ENNReal.ofReal ((2 * Real.sqrt d) ^ ((d:ℝ) + α) * c₁)⁻¹ *
        (ENNReal.ofReal ((h ^ (2 * d)) * (2 * Real.sqrt d) ^ ((d:ℝ) + α)) *
          (ENNReal.ofReal c₁ *
            discreteFormOn (scaledLattice d h) (ball x₀ (κ * R)) (Real.sqrt d * h)
              (discreteKernel d k h) f)) := mul_le_mul' le_rfl (mul_le_mul' le_rfl hcor)
    _ = ENNReal.ofReal (h ^ (2 * d)) *
        discreteFormOn (scaledLattice d h) (ball x₀ (κ * R)) (Real.sqrt d * h)
          (discreteKernel d k h) f := by
        rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        field_simp
