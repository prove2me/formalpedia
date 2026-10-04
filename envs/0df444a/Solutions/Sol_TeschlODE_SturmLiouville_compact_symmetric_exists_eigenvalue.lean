-- Prove2me | solution 1 for TeschlODE.SturmLiouville.compact_symmetric_exists_eigenvalue
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T19:31:30.79014+00:00
-- url     : https://prove2.me/submissions/20c3ec16-b6cc-4ccc-92d9-90dcc6843c23

import Mathlib
import Definitions.Def_TeschlODE_SturmLiouville_IsCompactOp

open TeschlODE.SturmLiouville Filter Topology

theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [Nontrivial E] (A : E →ₗ[ℂ] E) (hA : IsCompactOp A)
    (hsym : A.IsSymmetric) :
    ∃ α₀ : ℂ, (∃ u : E, u ≠ 0 ∧ A u = α₀ • u) ∧
      IsLUB {x : ℝ | ∃ f : E, ‖f‖ = 1 ∧ x = ‖A f‖} ‖α₀‖ := by
  set S : Set ℝ := {x : ℝ | ∃ f : E, ‖f‖ = 1 ∧ x = ‖A f‖} with hS
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have hunit : ∀ x : E, x ≠ 0 → ‖((‖x‖⁻¹ : ℝ) : ℂ) • x‖ = 1 := by
    intro x hx
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hx)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
  have hne : S.Nonempty := ⟨_, _, hunit v hv, rfl⟩
  -- boundedness
  have hbdd : BddAbove S := by
    by_contra hnb
    rw [not_bddAbove_iff] at hnb
    choose x hxS hx using fun n : ℕ => hnb n
    choose f hf hfx using hxS
    have hbound : Bornology.IsBounded (Set.range f) := by
      rw [isBounded_iff_forall_norm_le]
      exact ⟨1, by rintro _ ⟨n, rfl⟩; rw [hf n]⟩
    obtain ⟨φ, hφ, g, hg⟩ := hA f hbound
    have hn := (hg.norm).eventually (gt_mem_nhds (show ‖g‖ < ‖g‖ + 1 by linarith))
    obtain ⟨N, hN⟩ := eventually_atTop.mp hn
    obtain ⟨k, hk⟩ := exists_nat_gt (‖g‖ + 1)
    have h1 := hN (max N k) (le_max_left _ _)
    have h2 := hx (φ (max N k))
    rw [hfx] at h2
    have h3 : (k : ℝ) ≤ (φ (max N k) : ℝ) := by
      exact_mod_cast le_trans (le_max_right N k) (hφ.id_le _)
    linarith
  set α := sSup S with hα
  have hα0 : 0 ≤ α := le_trans (norm_nonneg _) (le_csSup hbdd ⟨_, hunit v hv, rfl⟩)
  have hAle : ∀ x : E, ‖A x‖ ≤ α * ‖x‖ := by
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · have hu := le_csSup hbdd ⟨_, hunit x hx, rfl⟩
      rw [map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hx))] at hu
      have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
      rw [inv_mul_le_iff₀ hxpos] at hu
      linarith
  have hAcont : Continuous A := AddMonoidHomClass.continuous_of_bound A α hAle
  suffices h : ∃ α₀ : ℂ, (∃ u : E, u ≠ 0 ∧ A u = α₀ • u) ∧ ‖α₀‖ = α by
    obtain ⟨α₀, hu, hnorm⟩ := h
    refine ⟨α₀, hu, ?_⟩
    rw [hnorm, hα]
    exact isLUB_csSup hne hbdd
  rcases hα0.lt_or_eq with hαpos | hαzero
  swap
  · refine ⟨0, ⟨v, hv, ?_⟩, by simp [← hαzero]⟩
    have := hAle v
    rw [← hαzero, zero_mul] at this
    simpa using norm_le_zero_iff.mp this
  -- a maximizing sequence
  have happrox : ∀ n : ℕ, ∃ x ∈ S, α - 1 / (n + 1) < x := fun n =>
    exists_lt_of_lt_csSup hne (by have : (0 : ℝ) < 1 / (n + 1) := by positivity
                                  linarith)
  choose x hxS hx using happrox
  choose f hf hfx using hxS
  have hbound : Bornology.IsBounded (Set.range f) := by
    rw [isBounded_iff_forall_norm_le]
    exact ⟨1, by rintro _ ⟨n, rfl⟩; rw [hf n]⟩
  obtain ⟨φ, hφ, g, hg⟩ := hA f hbound
  set e : ℕ → E := fun n => A (A (f n)) - ((α ^ 2 : ℝ) : ℂ) • f n with he
  have hesq : ∀ n, ‖e n‖ ^ 2 ≤ α ^ 2 * (α ^ 2 - ‖A (f n)‖ ^ 2) := by
    intro n
    have h1 : ‖A (A (f n))‖ ≤ α * ‖A (f n)‖ := hAle _
    have h2 : RCLike.re (inner ℂ (A (A (f n))) (((α ^ 2 : ℝ) : ℂ) • f n)) =
        α ^ 2 * ‖A (f n)‖ ^ 2 := by
      rw [inner_smul_right, hsym (A (f n)) (f n), RCLike.re_to_complex, Complex.re_ofReal_mul]
      congr 1
      exact inner_self_eq_norm_sq (𝕜 := ℂ) (A (f n))
    have h3 : ‖((α ^ 2 : ℝ) : ℂ) • f n‖ = α ^ 2 := by
      rw [norm_smul, hf n, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have := @norm_sub_sq ℂ E _ _ _ (A (A (f n))) (((α ^ 2 : ℝ) : ℂ) • f n)
    rw [he]
    simp only
    rw [this, h2, h3]
    have h4 : ‖A (A (f n))‖ ^ 2 ≤ (α * ‖A (f n)‖) ^ 2 := by
      gcongr
    nlinarith
  have hAf_le : ∀ n, ‖A (f n)‖ ≤ α := fun n => by
    have := hAle (f n); rwa [hf n, mul_one] at this
  have hetend : Tendsto e atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hb : ∀ n, ‖e n‖ ≤ Real.sqrt (α ^ 2 * (2 * α / (n + 1))) := by
      intro n
      apply Real.le_sqrt_of_sq_le
      refine le_trans (hesq n) ?_
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have h1 := hx n
      rw [hfx n] at h1
      have h2 := hAf_le n
      have hn : (0 : ℝ) < n + 1 := by positivity
      have : α ^ 2 - ‖A (f n)‖ ^ 2 = (α - ‖A (f n)‖) * (α + ‖A (f n)‖) := by ring
      rw [this]
      have h5 : α - ‖A (f n)‖ ≤ 1 / (n + 1) := by linarith
      have h6 : α + ‖A (f n)‖ ≤ 2 * α := by linarith
      calc (α - ‖A (f n)‖) * (α + ‖A (f n)‖) ≤ 1 / (n + 1) * (2 * α) := by
            apply mul_le_mul h5 h6 (by linarith [norm_nonneg (A (f n))]) (by positivity)
        _ = 2 * α / (n + 1) := by ring
    apply squeeze_zero (fun n => norm_nonneg _) hb
    have : Tendsto (fun n : ℕ => α ^ 2 * (2 * α / ((n : ℝ) + 1))) atTop (𝓝 (α ^ 2 * 0)) := by
      apply Tendsto.const_mul
      simp_rw [div_eq_mul_inv]
      rw [show (0 : ℝ) = 2 * α * 0 by ring]
      apply Tendsto.const_mul
      exact tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    rw [mul_zero] at this
    have := (Real.continuous_sqrt.tendsto 0).comp this
    rw [Real.sqrt_zero] at this
    exact this
  -- the limit point
  set h : E := (((α ^ 2)⁻¹ : ℝ) : ℂ) • A g with hh
  have hαsq : (α ^ 2 : ℝ) ≠ 0 := by positivity
  have hfconv : Tendsto (fun n => f (φ n)) atTop (𝓝 h) := by
    have h1 : Tendsto (fun n => A (A (f (φ n)))) atTop (𝓝 (A g)) :=
      (hAcont.tendsto g).comp hg
    have h2 : Tendsto (fun n => e (φ n)) atTop (𝓝 0) := hetend.comp hφ.tendsto_atTop
    have h3 := (h1.sub h2).const_smul (((α ^ 2 : ℝ)⁻¹ : ℝ) : ℂ)
    rw [sub_zero] at h3
    convert h3 using 1
    funext n
    simp only [he, sub_sub_cancel, smul_smul]
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ hαsq, Complex.ofReal_one, one_smul]
  have hnorm_h : ‖h‖ = 1 := by
    have := hfconv.norm
    simp only [hf, tendsto_const_nhds_iff] at this
    exact this.symm
  have hh0 : h ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hnorm_h; exact zero_ne_one hnorm_h
  have hAAh : A (A h) = ((α ^ 2 : ℝ) : ℂ) • h := by
    have h1 : Tendsto (fun n => e (φ n)) atTop (𝓝 (A (A h) - ((α ^ 2 : ℝ) : ℂ) • h)) := by
      have := ((hAcont.comp hAcont).tendsto h).comp hfconv
      exact this.sub (hfconv.const_smul _)
    have h2 : Tendsto (fun n => e (φ n)) atTop (𝓝 0) := hetend.comp hφ.tendsto_atTop
    exact sub_eq_zero.mp (tendsto_nhds_unique h1 h2)
  clear_value h
  set w : E := A h + (α : ℂ) • h with hw
  by_cases hw0 : w = 0
  · refine ⟨-(α : ℂ), ⟨h, hh0, ?_⟩, ?_⟩
    · rw [neg_smul]; exact eq_neg_of_add_eq_zero_left hw0
    · rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hα0]
  · refine ⟨(α : ℂ), ⟨w, hw0, ?_⟩, ?_⟩
    · rw [hw, map_add, map_smul, hAAh, smul_add]
      rw [show ((α ^ 2 : ℝ) : ℂ) = (α : ℂ) * (α : ℂ) by push_cast; ring, mul_smul]
      abel
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hα0]

#print axioms solution
