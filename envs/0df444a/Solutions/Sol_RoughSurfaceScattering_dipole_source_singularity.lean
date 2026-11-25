-- Prove2me | solution 1 for RoughSurfaceScattering.dipole_source_singularity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-25T00:32:56.633479+00:00
-- url     : https://prove2.me/submissions/920e3280-b6e5-47a0-98df-7ff182b94797
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic
import Theorems.Thm_RoughSurfaceScattering_dipole_core_bound
import Theorems.Thm_RoughSurfaceScattering_dipole_diff_h1_uniform
import Theorems.Thm_RoughSurfaceScattering_dipole_contDiffOn
import Theorems.Thm_RoughSurfaceScattering_vCorr_contDiffOn
import Theorems.Thm_RoughSurfaceScattering_h1Norm_sub_le
import Theorems.Thm_RoughSurfaceScattering_cone_below_interface

open MeasureTheory
open RoughSurfaceScattering

lemma abs_coord_le_norm (v : R2) (i : Fin 2) : |v i| ≤ ‖v‖ := by
  have h := EuclideanSpace.norm_sq_eq v
  rw [Fin.sum_univ_two] at h
  have h0 : |v i| ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [h, sq_abs]
    fin_cases i
    · simp only [Fin.zero_eta, Real.norm_eq_abs, sq_abs]; nlinarith [sq_nonneg (v 1)]
    · simp only [Fin.mk_one, Real.norm_eq_abs, sq_abs]; nlinarith [sq_nonneg (v 0)]
  exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp h0

lemma normal_norm (f : ℝ → ℝ) (s : ℝ) : ‖normal f s‖ = 1 := by
  have hpos : 0 < arcDen f s := Real.sqrt_pos.mpr (by positivity)
  have hpt : ‖pt (deriv f s) (-1)‖ = arcDen f s := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp [pt, arcDen]
    ring_nf
  rw [normal, norm_smul, hpt, Real.norm_eq_abs, abs_inv, abs_of_pos hpos, inv_mul_cancel₀ hpos.ne']

/-- Mirror of `cone_below_interface`: points in a cone around `-n` lie above `Γ`. -/
lemma cone_above_interface (f : ℝ → ℝ) (s0 : ℝ) (hf : DifferentiableAt ℝ f s0) :
    ∃ r > (0 : ℝ), ∀ v : R2, v ≠ 0 → ‖v‖ < r →
      ‖v‖ ≤ -(2 * @inner ℝ R2 _ v (normal f s0)) → gpt f s0 + v ∈ Dplus f := by
  set d := deriv f s0 with hd
  set a := arcDen f s0 with ha
  have hapos : 0 < a := Real.sqrt_pos.mpr (by positivity)
  have hlo := hf.hasDerivAt.isLittleO
  have hev := hlo.def (c := a / 4) (by positivity)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨r, hr, fun v hv0 hvr hcone => ?_⟩
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have hinner : @inner ℝ R2 _ v (normal f s0) = a⁻¹ * (d * v 0 - v 1) := by
    simp [normal, pt, ← ha, ← hd, PiLp.inner_apply, Fin.sum_univ_two, inner_smul_right]
    ring_nf
    try simp
  rw [hinner] at hcone
  have hkey : a * ‖v‖ ≤ 2 * (v 1 - d * v 0) := by
    have := mul_le_mul_of_nonneg_left hcone hapos.le
    calc a * ‖v‖ ≤ a * -(2 * (a⁻¹ * (d * v 0 - v 1))) := this
      _ = 2 * (v 1 - d * v 0) := by field_simp; ring
  have h0 := abs_coord_le_norm v 0
  have hdist : dist (s0 + v 0) s0 < r := by
    rw [Real.dist_eq, add_sub_cancel_left]; linarith
  have htay := hball hdist
  simp only [add_sub_cancel_left, Real.norm_eq_abs, smul_eq_mul] at htay
  have hup : f (s0 + v 0) ≤ f s0 + v 0 * d + a / 4 * |v 0| := by
    have := (abs_le.mp htay).2
    linarith
  show f ((gpt f s0 + v) 0) < (gpt f s0 + v) 1
  simp only [gpt, pt, PiLp.add_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  have : a / 4 * |v 0| ≤ a / 4 * ‖v‖ := mul_le_mul_of_nonneg_left h0 (by positivity)
  nlinarith

theorem solution (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) (hf2 : IsC2Lambda lam f)
    (kp km μ : ℝ) (hpar : ParamCond kp km μ) (s0 : ℝ) :
    ∃ δ0 > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ < δ0 →
      (∀ j : ℕ, 1 ≤ j → gpt f s0 + (δ / (j : ℝ)) • normal f s0 ∈ Dminus f) ∧
      ∀ D0 : Set R2, IsC2LambdaDomain lam D0 →
        Metric.ball (gpt f s0) (2 * δ) ∩ Dminus f ⊆ D0 → D0 ⊆ Dminus f →
        ∀ u : ℕ → (R2 → ℂ) × (R2 → ℂ),
          (∀ j : ℕ, 1 ≤ j → IsTSPSolution f kp km μ
            (incData f (dipoleSource kp (gpt f s0 - (δ / (j : ℝ)) • normal f s0) (normal f s0))).1
            (incData f (dipoleSource kp (gpt f s0 - (δ / (j : ℝ)) • normal f s0) (normal f s0))).2
            (u j).1 (u j).2) →
          ∃ C : ℝ, ∀ j : ℕ, 1 ≤ j →
            h1Norm D0 (fun x => (u j).2 x - ((2 / (μ + 1) : ℝ) : ℂ) *
                dipoleSource 0 (gpt f s0 - (δ / (j : ℝ)) • normal f s0) (normal f s0) x -
                vCorr μ D0 (normal f s0) (gpt f s0 - (δ / (j : ℝ)) • normal f s0)
                  (gpt f s0 + (δ / (j : ℝ)) • normal f s0) x) ≤ ENNReal.ofReal C ∧
            l2Norm D0 (vCorr μ D0 (normal f s0) (gpt f s0 - (δ / (j : ℝ)) • normal f s0)
                  (gpt f s0 + (δ / (j : ℝ)) • normal f s0)) ≤ ENNReal.ofReal C := by
  obtain ⟨r, hr, hcone⟩ := cone_above_interface f s0 (hf.1 s0)
  obtain ⟨r', hr', hcone'⟩ := cone_below_interface f s0 (hf.1 s0)
  obtain ⟨δ1, hδ1, hcore⟩ := dipole_core_bound f hf lam hlam0 hlam1 hf2 kp km μ hpar s0
  have hkm : 0 < km := hpar.2.1
  have hn1 := normal_norm f s0
  have hn0 : normal f s0 ≠ 0 := fun h => by rw [h, norm_zero] at hn1; exact zero_ne_one hn1
  refine ⟨min (min r r') (min δ1 1), lt_min (lt_min hr hr') (lt_min hδ1 one_pos),
    fun δ hδ hδ0 => ?_⟩
  have hδr : δ < r := lt_of_lt_of_le hδ0 ((min_le_left _ _).trans (min_le_left _ _))
  have hδr' : δ < r' := lt_of_lt_of_le hδ0 ((min_le_left _ _).trans (min_le_right _ _))
  have hδ1' : δ < δ1 := lt_of_lt_of_le hδ0 ((min_le_right _ _).trans (min_le_left _ _))
  have hnt : ∀ j : ℕ, 1 ≤ j → ‖(δ / (j : ℝ)) • normal f s0‖ = δ / j := fun j hj => by
    have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
    rw [norm_smul, hn1, mul_one, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have htle : ∀ j : ℕ, 1 ≤ j → δ / (j : ℝ) ≤ δ := fun j hj =>
    div_le_self hδ.le (by exact_mod_cast hj)
  have htpos : ∀ j : ℕ, 1 ≤ j → 0 < δ / (j : ℝ) := fun j hj => by
    have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
    positivity
  have hinn : ∀ t : ℝ, @inner ℝ R2 _ (t • normal f s0) (normal f s0) = t := fun t => by
    rw [inner_smul_left, real_inner_self_eq_norm_sq, hn1]; simp
  have hxj : ∀ j : ℕ, 1 ≤ j → gpt f s0 - (δ / (j : ℝ)) • normal f s0 ∈ Dplus f := by
    intro j hj
    have := hcone (-((δ / (j : ℝ)) • normal f s0))
      (by rw [neg_ne_zero]; exact smul_ne_zero (htpos j hj).ne' hn0)
      (by rw [norm_neg, hnt j hj]; linarith [htle j hj])
      (by rw [norm_neg, hnt j hj, inner_neg_left, hinn]; linarith [htpos j hj])
    rwa [← sub_eq_add_neg] at this
  have hyj : ∀ j : ℕ, 1 ≤ j → gpt f s0 + (δ / (j : ℝ)) • normal f s0 ∈ Dminus f := by
    intro j hj
    exact hcone' _ (smul_ne_zero (htpos j hj).ne' hn0)
      (by rw [hnt j hj]; linarith [htle j hj])
      (by rw [hnt j hj, hinn]; linarith [htpos j hj])
  refine ⟨hyj, fun D0 hD0 hball hsub u hu => ?_⟩
  obtain ⟨C2, hC2⟩ := hcore δ hδ hδ1' D0 hD0 hball hsub u hu
  obtain ⟨C1, hC1⟩ := dipole_diff_h1_uniform km hkm.le (normal f s0) D0 hD0.1 hD0.2.2.1
    (gpt f s0) (-((2 / (μ + 1) : ℝ) : ℂ))
  refine ⟨max C2 0 + max C1 0, fun j hj => ⟨?_, (hC2 j hj).2.trans
    (ENNReal.ofReal_le_ofReal ((le_max_left _ _).trans (le_add_of_nonneg_right
      (le_max_right _ _))))⟩⟩
  set xj := gpt f s0 - (δ / (j : ℝ)) • normal f s0 with hxjdef
  set yj := gpt f s0 + (δ / (j : ℝ)) • normal f s0 with hyjdef
  set n0 := normal f s0
  set A : ℂ := ((2 / (μ + 1) : ℝ) : ℂ)
  have hclos : closure (Dminus f) ⊆ {x : R2 | x 1 ≤ f (x 0)} := by
    refine closure_minimal (fun x (hx : x 1 < f (x 0)) => (le_of_lt hx : x 1 ≤ f (x 0))) (isClosed_le (by fun_prop) ?_)
    exact hf.1.continuous.comp (by fun_prop)
  have hxjD : xj ∉ D0 := fun h => by
    have h1 := hsub h
    have h2 := hxj j hj
    simp only [Dminus, Dplus, Set.mem_setOf_eq] at h1 h2
    linarith
  have hxjF : xj ∉ frontier D0 := fun h => by
    have h1 := hclos (closure_mono hsub (frontier_subset_closure h))
    have h2 := hxj j hj
    simp only [Dplus, Set.mem_setOf_eq] at h1 h2
    linarith
  have hyjD : yj ∈ D0 := hball ⟨by
    rw [Metric.mem_ball, dist_eq_norm, hyjdef, add_sub_cancel_left, hnt j hj]
    linarith [htle j hj], hyj j hj⟩
  have hyjF : yj ∉ frontier D0 := by
    rw [hD0.1.frontier_eq]; exact fun h => h.2 hyjD
  have hxjball : xj ∈ Metric.ball (gpt f s0) 1 := by
    rw [Metric.mem_ball, dist_eq_norm, hxjdef, sub_sub_cancel_left, norm_neg, hnt j hj]
    have := htle j hj
    have : δ < 1 := lt_of_lt_of_le hδ0 ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  have hsubD : D0 ⊆ {x | x ≠ xj} := fun x hx h => hxjD (h ▸ hx)
  obtain ⟨hp, hm, Dup, Dum, -, -, -, hum, -⟩ := hu j hj
  have hv : ContDiffOn ℝ 1 (fun x => (u j).2 x - A * dipoleSource km xj n0 x -
      vCorr μ D0 n0 xj yj x) D0 :=
    (((hum.of_le (by norm_num)).mono hsub).sub
      (contDiffOn_const.mul ((dipole_contDiffOn km hkm.le xj n0).mono hsubD))).sub
      (vCorr_contDiffOn lam ⟨hlam0, hlam1⟩ μ D0 hD0 n0 xj yj hxjF hyjF)
  have hw : ContDiffOn ℝ 1 (fun x => -A * (dipoleSource km xj n0 x - dipoleSource 0 xj n0 x)) D0 :=
    contDiffOn_const.mul (((dipole_contDiffOn km hkm.le xj n0).mono hsubD).sub
      ((dipole_contDiffOn 0 le_rfl xj n0).mono hsubD))
  have htri := h1Norm_sub_le D0 hD0.1 _ _ hv hw
  have heq : (fun x => ((u j).2 x - A * dipoleSource km xj n0 x - vCorr μ D0 n0 xj yj x) -
      -A * (dipoleSource km xj n0 x - dipoleSource 0 xj n0 x)) =
      fun x => (u j).2 x - A * dipoleSource 0 xj n0 x - vCorr μ D0 n0 xj yj x := by
    funext x; ring
  rw [heq] at htri
  refine htri.trans ?_
  rw [ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)]
  exact add_le_add ((hC2 j hj).1.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
    ((hC1 xj hxjball).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
