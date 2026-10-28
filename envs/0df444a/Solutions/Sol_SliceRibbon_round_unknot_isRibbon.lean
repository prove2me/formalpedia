-- Prove2me | solution 1 for SliceRibbon.round_unknot_isRibbon
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T13:56:00.562896+00:00
-- url     : https://prove2.me/submissions/8a102867-db3b-46a7-b0b6-2938db6b1ed8

import Mathlib
import Definitions.Def_SliceRibbon_basic

open Real Metric
open scoped ContDiff

namespace S216SR
open SliceRibbon

noncomputable def nsq (z : R2) : ℝ := z 0 ^ 2 + z 1 ^ 2

lemma nsq_nonneg (z : R2) : 0 ≤ nsq z := by unfold nsq; positivity

lemma norm_sq_R2 (z : R2) : ‖z‖ ^ 2 = nsq z := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, nsq, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]

noncomputable def f (z : R2) : R4 :=
  !₂[2 * z 0 / (1 + nsq z), 2 * z 1 / (1 + nsq z), (1 - nsq z) / (1 + nsq z), 0]

noncomputable def g (y : R4) : R2 := !₂[y 0 / (1 + y 2), y 1 / (1 + y 2)]

lemma gf (z : R2) : g (f z) = z := by
  have h := nsq_nonneg z
  have h1 : (1 + nsq z) ≠ 0 := by positivity
  have h2 : 1 + (1 - nsq z) / (1 + nsq z) = 2 / (1 + nsq z) := by field_simp; ring
  ext i; fin_cases i <;> simp [g, f, h2] <;> field_simp

lemma nsq_contDiff : ContDiff ℝ ∞ nsq := by
  unfold nsq
  have h0 : ContDiff ℝ ∞ (fun z : R2 => z 0) := contDiff_piLp_apply (p := 2) (i := (0 : Fin 2))
  have h1 : ContDiff ℝ ∞ (fun z : R2 => z 1) := contDiff_piLp_apply (p := 2) (i := (1 : Fin 2))
  exact (h0.pow 2).add (h1.pow 2)

lemma f_contDiff : ContDiff ℝ ∞ f := by
  have h0 : ContDiff ℝ ∞ (fun z : R2 => z 0) := contDiff_piLp_apply (p := 2) (i := (0 : Fin 2))
  have h1 : ContDiff ℝ ∞ (fun z : R2 => z 1) := contDiff_piLp_apply (p := 2) (i := (1 : Fin 2))
  have hd : ContDiff ℝ ∞ (fun z : R2 => 1 + nsq z) := contDiff_const.add nsq_contDiff
  have hne : ∀ z : R2, 1 + nsq z ≠ 0 := fun z => by have := nsq_nonneg z; positivity
  rw [contDiff_piLp]
  intro i; fin_cases i <;> simp only [f]
  · exact (contDiff_const.mul h0).div hd hne
  · exact (contDiff_const.mul h1).div hd hne
  · exact (contDiff_const.sub nsq_contDiff).div hd hne
  · exact contDiff_const

lemma g_diff (y : R4) (hy : 1 + y 2 ≠ 0) : DifferentiableAt ℝ g y := by
  have p : ∀ i : Fin 4, DifferentiableAt ℝ (fun y : R4 => y i) y :=
    fun i => ((contDiff_piLp_apply (𝕜 := ℝ) (p := 2) (n := 1) (i := i)).differentiable (by simp)) y
  rw [differentiableAt_piLp]
  have q : DifferentiableAt ℝ (fun y : R4 => 1 + y 2) y := (differentiableAt_const _).add (p 2)
  intro i; fin_cases i
  · show DifferentiableAt ℝ (fun y : R4 => y 0 / (1 + y 2)) y
    simp only [div_eq_mul_inv]; exact (p 0).mul (q.inv hy)
  · show DifferentiableAt ℝ (fun y : R4 => y 1 / (1 + y 2)) y
    simp only [div_eq_mul_inv]; exact (p 1).mul (q.inv hy)

lemma f2 (z : R2) : 1 + f z 2 ≠ 0 := by
  have h := nsq_nonneg z
  have h2 : 1 + (1 - nsq z) / (1 + nsq z) = 2 / (1 + nsq z) := by field_simp; ring
  simp [f, h2]; positivity

lemma f_inj : Function.Injective f := Function.LeftInverse.injective gf

lemma fderiv_inj (z : R2) : Function.Injective (fderiv ℝ f z) := by
  have hc : fderiv ℝ (g ∘ f) z = (fderiv ℝ g (f z)).comp (fderiv ℝ f z) :=
    fderiv_comp z (g_diff _ (f2 z)) (f_contDiff.differentiable (by simp) z)
  have hid : g ∘ f = id := funext gf
  rw [hid, fderiv_id] at hc
  intro a b hab
  have ha : a = (fderiv ℝ g (f z)) ((fderiv ℝ f z) a) := by
    rw [← ContinuousLinearMap.comp_apply, ← hc]; rfl
  have hb : b = (fderiv ℝ g (f z)) ((fderiv ℝ f z) b) := by
    rw [← ContinuousLinearMap.comp_apply, ← hc]; rfl
  rw [ha, hb, hab]

lemma f_norm (z : R2) : ‖f z‖ = 1 := by
  have h := nsq_nonneg z
  have h1 : (1 + nsq z) ≠ 0 := by positivity
  have : ‖f z‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_four, f, sq_abs]
    field_simp
    unfold nsq; ring
  have hn : 0 ≤ ‖f z‖ := norm_nonneg _
  nlinarith [this]

noncomputable def γ (t : ℝ) : R4 := !₂[Real.cos (2 * π * t), Real.sin (2 * π * t), 0, 0]

lemma f_sphere (z : R2) (hz : ‖z‖ = 1) : f z = !₂[z 0, z 1, 0, 0] := by
  have : nsq z = 1 := by rw [← norm_sq_R2, hz]; norm_num
  ext i; fin_cases i <;> simp [f, this] <;> ring

lemma image_eq : f '' sphere 0 1 = Set.range γ := by
  ext y; constructor
  · rintro ⟨z, hz, rfl⟩
    rw [mem_sphere_zero_iff_norm] at hz
    have hn : nsq z = 1 := by rw [← norm_sq_R2, hz]; norm_num
    set w : ℂ := ⟨z 0, z 1⟩
    have hw : ‖w‖ = 1 := by
      rw [Complex.norm_eq_sqrt_sq_add_sq]; simp [w]; unfold nsq at hn; rw [hn]
    have hw0 : w ≠ 0 := by intro h; rw [h] at hw; simp at hw
    refine ⟨Complex.arg w / (2 * π), ?_⟩
    rw [f_sphere z hz]
    have e : 2 * π * (Complex.arg w / (2 * π)) = Complex.arg w := by field_simp
    simp only [γ, e, Complex.cos_arg hw0, Complex.sin_arg, hw, div_one]
    rfl
  · rintro ⟨t, rfl⟩
    refine ⟨!₂[Real.cos (2 * π * t), Real.sin (2 * π * t)], ?_, ?_⟩
    · rw [mem_sphere_zero_iff_norm]
      have : ‖(!₂[Real.cos (2 * π * t), Real.sin (2 * π * t)] : R2)‖ ^ 2 = 1 := by
        rw [norm_sq_R2]; simp [nsq]
      have hn := norm_nonneg (!₂[Real.cos (2 * π * t), Real.sin (2 * π * t)] : R2)
      nlinarith
    · have hn : nsq (!₂[Real.cos (2 * π * t), Real.sin (2 * π * t)] : R2) = 1 := by simp [nsq]
      ext i; fin_cases i <;> simp [f, γ, hn] <;> ring

lemma γ_contDiff : ContDiff ℝ ∞ γ := by
  rw [contDiff_piLp]
  intro i; fin_cases i <;> simp only [γ]
  · exact Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)
  · exact Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)
  · exact contDiff_const
  · exact contDiff_const

lemma γ_knot : IsKnot γ := by
  refine ⟨γ_contDiff, ?_, ?_, ?_, ?_⟩
  · intro t
    have e : 2 * π * (t + 1) = 2 * π * t + 2 * π := by ring
    simp only [γ, e, Real.cos_add_two_pi, Real.sin_add_two_pi]
  · intro t
    have : ‖γ t‖ ^ 2 = 1 := by
      rw [EuclideanSpace.norm_sq_eq]; simp [Fin.sum_univ_four, γ, sq_abs]
    have hn := norm_nonneg (γ t)
    nlinarith
  · intro a ha b hb hab
    have h0 := congrArg (fun y : R4 => y 0) hab
    have h1 := congrArg (fun y : R4 => y 1) hab
    simp [γ] at h0 h1
    have he : Complex.exp (↑(2 * π * a) * Complex.I) = Complex.exp (↑(2 * π * b) * Complex.I) := by
      rw [Complex.exp_mul_I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
        ← Complex.ofReal_cos, ← Complex.ofReal_sin, h0, h1]
    rw [Complex.exp_eq_exp_iff_exists_int] at he
    obtain ⟨k, hk⟩ := he
    have hk' : 2 * π * a = 2 * π * b + k * (2 * π) := by
      have := congrArg Complex.im hk
      simpa using this
    have hpi := Real.pi_pos
    have hab' : a - b = k := by
      have : (a - b - k) * (2 * π) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · linarith
    have : (k : ℝ) < 1 := by rw [← hab']; linarith [ha.1, ha.2, hb.1, hb.2]
    have : (-1 : ℝ) < k := by rw [← hab']; linarith [ha.1, ha.2, hb.1, hb.2]
    have hk0 : k = 0 := by
      have : k < 1 := by exact_mod_cast ‹(k : ℝ) < 1›
      have : -1 < k := by exact_mod_cast ‹(-1 : ℝ) < k›
      omega
    rw [hk0] at hab'; simp at hab'; linarith
  · intro t h
    have hd : HasDerivAt (fun s => γ s 0) (deriv γ t 0) t := by
      have := (EuclideanSpace.proj (0 : Fin 4)).hasFDerivAt.comp_hasDerivAt t
        ((γ_contDiff.differentiable (by simp)) t).hasDerivAt
      exact this
    have hd1 : HasDerivAt (fun s => γ s 1) (deriv γ t 1) t := by
      have := (EuclideanSpace.proj (1 : Fin 4)).hasFDerivAt.comp_hasDerivAt t
        ((γ_contDiff.differentiable (by simp)) t).hasDerivAt
      exact this
    have e0 : HasDerivAt (fun s => γ s 0) (-Real.sin (2 * π * t) * (2 * π)) t := by
      have := ((hasDerivAt_id t).const_mul (2 * π)).cos
      simpa [γ] using this
    have e1 : HasDerivAt (fun s => γ s 1) (Real.cos (2 * π * t) * (2 * π)) t := by
      have := ((hasDerivAt_id t).const_mul (2 * π)).sin
      simpa [γ] using this
    have a0 := hd.unique e0
    have a1 := hd1.unique e1
    rw [h] at a0 a1
    have hpi : 2 * π ≠ 0 := by positivity
    have s0 : Real.sin (2 * π * t) = 0 := by
      have : -Real.sin (2 * π * t) * (2 * π) = 0 := by rw [← a0]; simp
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · exact absurd h hpi
    have c0 : Real.cos (2 * π * t) = 0 := by
      have : Real.cos (2 * π * t) * (2 * π) = 0 := by rw [← a1]; simp
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h hpi
    have := Real.sin_sq_add_cos_sq (2 * π * t); rw [s0, c0] at this; norm_num at this

end S216SR

open S216SR SliceRibbon in
theorem solution :
    IsKnot (fun t : ℝ => !₂[Real.cos (2 * π * t), Real.sin (2 * π * t), 0, 0]) ∧
      IsRibbon (fun t : ℝ => !₂[Real.cos (2 * π * t), Real.sin (2 * π * t), 0, 0]) := by
  refine ⟨γ_knot, f, f_contDiff, fun z _ => f_norm z, fun z _ => fderiv_inj z, f_inj.injOn,
    image_eq, ?_, ?_, 0, Fin.elim0, Fin.elim0, ?_⟩
  · intro z₁ _ z₂ _ z₃ _ h _; exact Or.inl (f_inj h)
  · intro z _ w _ hzw h; exact absurd (f_inj h) hzw
  · refine ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0, ?_⟩
    ext z
    simp only [Set.mem_ofPred_eq, Set.iUnion_of_empty, Set.mem_empty_iff_false, iff_false]
    rintro ⟨_, w, _, hw, h⟩
    exact hw (f_inj h)
