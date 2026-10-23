-- Prove2me | solution 1 for SuBoydCandes2016.thm7_low_friction_faithful
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T02:38:10.643388+00:00
-- url     : https://prove2.me/submissions/aada67af-f873-496e-88c0-d2a35737ba79

import Mathlib
import Definitions.Def_NesterovODE_StrongCvx_Setting

open scoped RealInnerProductSpace

namespace SB85

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- first-order inequality for a convex function with a Fréchet derivative -/
theorem fo_ineq {f : F → ℝ} (hf : ConvexOn ℝ Set.univ f) {x y : F} {f' : F →L[ℝ] ℝ}
    (hd : HasFDerivAt f f' x) : f x + f' (y - x) ≤ f y := by
  let L := AffineMap.lineMap (k := ℝ) x y
  have hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (f ∘ L) :=
    (hf.comp_affineMap L).subset (Set.subset_univ _) (convex_Icc 0 1)
  have hD : HasDerivAt (f ∘ L) (f' (y - x)) 0 := by
    have hL : HasDerivAt L (y - x) 0 := AffineMap.hasDerivAt_lineMap
    have hF : HasFDerivAt f f' (L 0) := by
      have : L 0 = x := by simp [L]
      rw [this]; exact hd
    exact hF.comp_hasDerivAt (0 : ℝ) hL
  have := hconv.le_slope_of_hasDerivAt (x := 0) (y := 1) (by simp) (by simp) one_pos hD
  rw [slope_def_field] at this
  simp [L] at this
  rw [map_sub]
  linarith

/-- the key inequality `(2/(r-1)) (f x - f*) ≤ ⟪∇f x, x - x*⟫` -/
theorem key {f : F → ℝ} (hfc : ConvexOn ℝ Set.univ f) {r : ℝ} (hr1 : 1 < r)
    {xs x : F} (hxs : ∀ y, f xs ≤ f y)
    (hpow : ConvexOn ℝ Set.univ (fun x => (f x - f xs) ^ ((r - 1) / 2)))
    {g : F} (hg : HasFDerivAt f (InnerProductSpace.toDual ℝ F g) x) :
    2 / (r - 1) * (f x - f xs) ≤ ⟪g, x - xs⟫ := by
  have h1 := fo_ineq hfc (y := xs) hg
  change f x + ⟪g, xs - x⟫ ≤ f xs at h1
  have hneg : ⟪g, xs - x⟫ = -⟪g, x - xs⟫ := by
    rw [← inner_neg_right, neg_sub]
  set p := f x - f xs with hp
  have hp0 : 0 ≤ p := by linarith [hxs x]
  rcases hp0.eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]; linarith
  set q := (r - 1) / 2 with hq
  have hq0 : 0 < q := by rw [hq]; linarith
  have hd : HasFDerivAt (fun x => (f x - f xs) ^ q)
      ((q * (f x - f xs) ^ (q - 1)) • InnerProductSpace.toDual ℝ F g) x :=
    (hg.sub_const (f xs)).rpow_const (Or.inl hpos.ne')
  have h2 := fo_ineq hpow (y := xs) hd
  change (f x - f xs) ^ q + (q * (f x - f xs) ^ (q - 1)) * ⟪g, xs - x⟫ ≤ (f xs - f xs) ^ q at h2
  rw [sub_self, Real.zero_rpow hq0.ne'] at h2
  rw [← hp, hneg] at h2
  have hpq : p ^ q = p * p ^ (q - 1) := by
    rw [Real.rpow_sub hpos, Real.rpow_one]; field_simp
  have hpp : 0 < p ^ (q - 1) := Real.rpow_pos_of_pos hpos _
  rw [hpq] at h2
  -- p * P ≤ q * P * ⟪g, x - xs⟫
  have h3 : p * p ^ (q - 1) ≤ q * ⟪g, x - xs⟫ * p ^ (q - 1) := by nlinarith
  have h4 : p ≤ q * ⟪g, x - xs⟫ := le_of_mul_le_mul_right h3 hpp
  have e : 2 / (r - 1) = 1 / q := by rw [hq]; field_simp
  rw [e, one_div_mul_eq_div, div_le_iff₀ hq0]
  linarith

end SB85

open SB85 in
theorem solution {n : ℕ} (f : NesterovODE.WellPosed.E n → ℝ) (r : ℝ)
    (hr1 : 1 < r) (hr3 : r < 3)
    (hfc : ConvexOn ℝ Set.univ f) (hfd : ContDiff ℝ 1 f)
    (x₀ xstar : NesterovODE.WellPosed.E n) (hxstar : ∀ y, f xstar ≤ f y)
    (hpow : ConvexOn ℝ Set.univ (fun x => (f x - f xstar) ^ ((r - 1) / 2)))
    (X V : ℝ → NesterovODE.WellPosed.E n) (hX : NesterovODE.StrongCvx.IsSolution f r x₀ X V) :
    ∀ t : ℝ, 0 < t → f (X t) - f xstar ≤ (r - 1) ^ 2 * ‖x₀ - xstar‖ ^ 2 / (2 * t ^ 2) := by
  obtain ⟨hX0, hV0, hXd0, hVc0, hode⟩ := hX
  have hr : 0 < r - 1 := by linarith
  let En : ℝ → ℝ := fun t => 2 * t ^ 2 / (r - 1) * (f (X t) - f xstar) +
    (r - 1) * ‖X t + (t / (r - 1)) • V t - xstar‖ ^ 2
  have hdf : ∀ y, HasFDerivAt f (InnerProductSpace.toDual ℝ _ (gradient f y)) y := fun y =>
    ((hfd.differentiable (by norm_num)) y).hasGradientAt.hasFDerivAt
  -- derivative of the energy
  have hder : ∀ t : ℝ, 0 < t → HasDerivAt En
      (4 * t / (r - 1) * (f (X t) - f xstar) - 2 * t * ⟪gradient f (X t), X t - xstar⟫) t := by
    intro t ht
    obtain ⟨hXt, hVt⟩ := hode t ht
    have hfX : HasDerivAt (fun s => f (X s)) ⟪gradient f (X t), V t⟫ t :=
      (hdf (X t)).comp_hasDerivAt t hXt
    have hA := ((((hasDerivAt_pow 2 t).const_mul 2).div_const (r - 1))).mul (hfX.sub_const (f xstar))
    have hc : (1:ℝ) + t / (r - 1) * (-(r / t)) + 1 / (r - 1) = 0 := by
      field_simp; ring
    have hW : HasDerivAt (fun s => X s + (s / (r - 1)) • V s - xstar)
        (-(t / (r - 1)) • gradient f (X t)) t := by
      have := ((hXt.add (((hasDerivAt_id' t).div_const (r - 1)).smul hVt)).sub_const xstar)
      refine this.congr_deriv ?_
      calc V t + ((t / (r - 1)) • (-(r / t) • V t - gradient f (X t)) + (1 / (r - 1)) • V t)
          = ((1:ℝ) + t / (r - 1) * (-(r / t)) + 1 / (r - 1)) • V t
            - (t / (r - 1)) • gradient f (X t) := by module
        _ = _ := by rw [hc, zero_smul, zero_sub, neg_smul]
    have hB := hW.norm_sq.const_mul (r - 1)
    refine (hA.add hB).congr_deriv ?_
    simp only [inner_smul_right, inner_add_left, inner_sub_left, real_inner_smul_left]
    have e1 : ⟪gradient f (X t), X t⟫ = ⟪X t, gradient f (X t)⟫ := real_inner_comm _ _
    have e2 : ⟪gradient f (X t), xstar⟫ = ⟪xstar, gradient f (X t)⟫ := real_inner_comm _ _
    rw [inner_sub_right, e1, e2]
    norm_num
    field_simp
    ring
  have hderle : ∀ t : ℝ, 0 < t →
      4 * t / (r - 1) * (f (X t) - f xstar) - 2 * t * ⟪gradient f (X t), X t - xstar⟫ ≤ 0 := by
    intro t ht
    have := key hfc hr1 hxstar hpow (hdf (X t))
    have e : 4 * t / (r - 1) * (f (X t) - f xstar) = 2 * t * (2 / (r - 1) * (f (X t) - f xstar)) := by
      ring
    rw [e]
    nlinarith
  -- continuity at 0
  have hcont0 : ContinuousWithinAt En (Set.Ici 0) 0 := by
    have hXc : ContinuousWithinAt X (Set.Ici 0) 0 := hXd0.continuousWithinAt
    have hfXc : ContinuousWithinAt (fun s => f (X s)) (Set.Ici 0) 0 :=
      (hfd.continuous.continuousAt).comp_continuousWithinAt hXc
    apply ContinuousWithinAt.add
    · exact ((((continuous_pow 2).continuousWithinAt.const_mul 2).div_const _)).mul
        (hfXc.sub continuousWithinAt_const)
    · apply ContinuousWithinAt.const_mul
      exact ((hXc.add ((continuousWithinAt_id.div_const _).smul hVc0)).sub
        continuousWithinAt_const).norm.pow 2
  have hcont : ContinuousOn En (Set.Ici 0) := by
    intro t ht
    rcases (Set.mem_Ici.mp ht).eq_or_lt with h | h
    · rw [← h]; exact hcont0
    · exact (hder t h).continuousAt.continuousWithinAt
  have hanti : AntitoneOn En (Set.Ici 0) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0) hcont
    · intro t ht
      rw [interior_Ici] at ht ⊢
      exact (hder t ht).hasDerivWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      exact hderle t ht
  intro t ht
  have hle := hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht.le) ht.le
  have hE0 : En 0 = (r - 1) * ‖x₀ - xstar‖ ^ 2 := by
    simp [En, hX0, hV0]
  rw [hE0] at hle
  have hnn : 0 ≤ (r - 1) * ‖X t + (t / (r - 1)) • V t - xstar‖ ^ 2 := by positivity
  have h1 : 2 * t ^ 2 / (r - 1) * (f (X t) - f xstar) ≤ (r - 1) * ‖x₀ - xstar‖ ^ 2 := by
    simp only [En] at hle; linarith
  have ht2 : 0 < 2 * t ^ 2 := by positivity
  rw [le_div_iff₀ ht2]
  have e : 2 * t ^ 2 / (r - 1) * (f (X t) - f xstar) * (r - 1) = (f (X t) - f xstar) * (2 * t ^ 2) := by
    field_simp
  nlinarith
