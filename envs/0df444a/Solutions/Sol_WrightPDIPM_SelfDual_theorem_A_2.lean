-- Prove2me | solution 1 for WrightPDIPM.SelfDual.theorem_A_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T13:02:59.939128+00:00
-- url     : https://prove2.me/submissions/f76071ef-2aab-4f08-9d77-c7a9eccc7111

import Mathlib
import Definitions.Def_WrightPDIPM_SelfDual_Setup
open WrightPDIPM.SelfDual

open Matrix

theorem g69b_norm2_smul {N : ℕ} (t : ℝ) (v : Fin N → ℝ) : norm2 (t • v) = |t| * norm2 v := by
  unfold norm2
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [← Finset.mul_sum, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq_eq_abs]

theorem g69b_fderiv_eq {N : ℕ} (f : (Fin N → ℝ) → ℝ) (u v : Fin N → ℝ) :
    fderiv ℝ f u v = v ⬝ᵥ gradVec f u := by
  have := (fderiv ℝ f u).toLinearMap.pi_apply_eq_sum_univ v
  simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at this
  rw [this]
  unfold dotProduct gradVec
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  funext j
  simp [Pi.single_apply, eq_comm]

theorem g69b_seg {N : ℕ} (a u : Fin N → ℝ) (t : ℝ) :
    (1 - t) • a + t • u = a + t • (u - a) := by
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
  ring

theorem solution {N k l : ℕ} (f : (Fin N → ℝ) → ℝ) (C : Matrix (Fin k) (Fin N) ℝ)
    (d : Fin k → ℝ) (G : Matrix (Fin l) (Fin N) ℝ) (h : Fin l → ℝ) (U : Set (Fin N → ℝ))
    (hUo : IsOpen U) (hUc : Convex ℝ U) (hf : ConvexOn ℝ (FeasibleA2 C d G h U) f) :
    (∀ ustar : Fin N → ℝ, ustar ∈ U → DifferentiableAt ℝ f ustar →
      ∀ (y : Fin k → ℝ) (z : Fin l → ℝ),
        gradVec f ustar - Cᵀ *ᵥ y - Gᵀ *ᵥ z = 0 →
        C *ᵥ ustar = d →
        (∀ i, h i ≤ (G *ᵥ ustar) i) →
        (∀ i, 0 ≤ z i) →
        z ⬝ᵥ (G *ᵥ ustar - h) = 0 →
        IsGlobalSolutionA2 f C d G h U ustar) ∧
    (StrictConvexOn ℝ (FeasibleA2 C d G h U) f →
      ∀ ustar : Fin N → ℝ, IsLocalSolutionA2 f C d G h U ustar →
        IsGlobalSolutionA2 f C d G h U ustar ∧
        ∀ u', IsGlobalSolutionA2 f C d G h U u' → u' = ustar) := by
  constructor
  · intro us hU hd y z hgrad hC hG hz hcomp
    have hus : us ∈ FeasibleA2 C d G h U := ⟨hU, hC, hG⟩
    refine ⟨hus, fun u hu => ?_⟩
    obtain ⟨huU, huC, huG⟩ := hu
    set v := u - us
    have hgr : gradVec f us = Cᵀ *ᵥ y + Gᵀ *ᵥ z := by
      rw [← sub_eq_zero, ← sub_sub]; exact hgrad
    have hD : 0 ≤ fderiv ℝ f us v := by
      rw [g69b_fderiv_eq, hgr, dotProduct_add, dotProduct_mulVec, dotProduct_mulVec,
        vecMul_transpose, vecMul_transpose]
      have hCv : C *ᵥ v = 0 := by simp only [v]; rw [mulVec_sub, huC, hC, sub_self]
      rw [hCv, zero_dotProduct, zero_add]
      have e : G *ᵥ v = (G *ᵥ u - h) - (G *ᵥ us - h) := by
        simp only [v]; rw [mulVec_sub]; abel
      rw [e, dotProduct_comm, dotProduct_sub, hcomp, sub_zero]
      exact Finset.sum_nonneg (fun i _ => mul_nonneg (hz i) (by
        simp only [Pi.sub_apply]; linarith [huG i]))
    have hT := (hd.hasFDerivAt.hasLineDerivAt v).tendsto_slope_zero_right
    have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        t⁻¹ • (f (us + t • v) - f us) ≤ f u - f us := by
      have : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
        Ioo_mem_nhdsGT (by norm_num)
      filter_upwards [this] with t ht
      obtain ⟨ht0, ht1⟩ := ht
      have hc := hf.2 hus ⟨huU, huC, huG⟩ (by linarith : (0:ℝ) ≤ 1 - t) ht0.le (by ring)
      rw [g69b_seg, smul_eq_mul, smul_eq_mul] at hc
      rw [smul_eq_mul, inv_mul_le_iff₀ ht0]
      linarith
    have := le_of_tendsto hT hev
    linarith
  · intro hsc us hloc
    obtain ⟨hus, ρ, hρ, hlo⟩ := hloc
    have hcv := hsc.convexOn
    have hglob : IsGlobalSolutionA2 f C d G h U us := by
      refine ⟨hus, fun u hu => ?_⟩
      set Nv := norm2 (u - us)
      have hNv : 0 ≤ Nv := Real.sqrt_nonneg _
      set t := min (1 / 2) (ρ / (2 * (Nv + 1)))
      have ht0 : 0 < t := lt_min (by norm_num) (by positivity)
      have ht1 : t ≤ 1 / 2 := min_le_left _ _
      have ht2 : t * Nv < ρ := by
        have : t ≤ ρ / (2 * (Nv + 1)) := min_le_right _ _
        have h3 : ρ / (2 * (Nv + 1)) * Nv < ρ := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith
        calc t * Nv ≤ ρ / (2 * (Nv + 1)) * Nv := mul_le_mul_of_nonneg_right this hNv
          _ < ρ := h3
      have hw : (1 - t) • us + t • u ∈ FeasibleA2 C d G h U :=
        hcv.1 hus hu (by linarith) ht0.le (by ring)
      have hc := hcv.2 hus hu (by linarith : (0:ℝ) ≤ 1 - t) ht0.le (by ring)
      have hl := hlo _ hw (by
        rw [g69b_seg, add_sub_cancel_left, g69b_norm2_smul, abs_of_pos ht0]; exact ht2)
      rw [smul_eq_mul, smul_eq_mul] at hc
      have : t * f us ≤ t * f u := by linarith
      exact le_of_mul_le_mul_left this ht0
    refine ⟨hglob, fun u' hu' => ?_⟩
    by_contra hne
    have h1 := hu'.2 us hus
    have h2 := hglob.2 u' hu'.1
    have hm := hsc.2 hu'.1 hus hne (by norm_num : (0:ℝ) < 1 / 2) (by norm_num : (0:ℝ) < 1 / 2)
      (by norm_num)
    have hmem : (1 / 2 : ℝ) • u' + (1 / 2 : ℝ) • us ∈ FeasibleA2 C d G h U :=
      hsc.1 hu'.1 hus (by norm_num) (by norm_num) (by norm_num)
    have h3 := hglob.2 _ hmem
    rw [smul_eq_mul, smul_eq_mul] at hm
    linarith
