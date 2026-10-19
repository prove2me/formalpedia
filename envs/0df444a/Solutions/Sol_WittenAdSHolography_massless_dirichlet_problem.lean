-- Prove2me | solution 1 for WittenAdSHolography.massless_dirichlet_problem
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T23:35:01.836531+00:00
-- url     : https://prove2.me/submissions/04d86ac3-c2b4-402e-8d14-32e283ab5c4d

import Mathlib
import Definitions.Def_WittenAdSHolography_Defs
import Theorems.Thm_WittenAdSHolography_bulkKernel_solution
import Theorems.Thm_WittenAdSHolography_kernel_approx_identity

-- ===== part A =====

open WittenAdSHolography MeasureTheory Filter Topology

namespace WDA

variable {d : ℕ}

/-- `g(t,y) = (t² + |y|²)^{-d}` -/
noncomputable def g (d : ℕ) (z : ℝ × Bdry d) : ℝ := ((z.1 ^ 2 + ‖z.2‖ ^ 2)⁻¹) ^ d

/-- `k(t,y) = t^d (t² + |y|²)^{-d}` -/
noncomputable def k (d : ℕ) (z : ℝ × Bdry d) : ℝ := z.1 ^ d * g d z

lemma q_pos {z : ℝ × Bdry d} (hz : z ≠ 0) : 0 < z.1 ^ 2 + ‖z.2‖ ^ 2 := by
  rcases eq_or_ne z.1 0 with h1 | h1
  · have h2 : z.2 ≠ 0 := fun h2 => hz (Prod.ext h1 h2)
    have := norm_pos_iff.mpr h2
    have : 0 ≤ z.1 ^ 2 := sq_nonneg _
    positivity
  · have : 0 < z.1 ^ 2 := by positivity
    have : 0 ≤ ‖z.2‖ ^ 2 := sq_nonneg _
    linarith

lemma isOpen_ne' : IsOpen {z : ℝ × Bdry d | z ≠ 0} := isOpen_ne

lemma qcd (n : ℕ∞) : ContDiff ℝ n (fun z : ℝ × Bdry d => z.1 ^ 2 + ‖z.2‖ ^ 2) :=
  (contDiff_fst.pow 2).add ((contDiff_norm_sq ℝ).comp contDiff_snd)

lemma g_cd (n : ℕ∞) : ContDiffOn ℝ n (g d) {z | z ≠ 0} := by
  unfold g
  exact ((qcd n).contDiffOn.inv (fun z hz => (q_pos hz).ne')).pow d

lemma k_cd (n : ℕ∞) : ContDiffOn ℝ n (k d) {z | z ≠ 0} := by
  unfold k
  exact ((contDiff_fst.pow d).contDiffOn).mul (g_cd n)

lemma g_smul (c : ℝ) (z : ℝ × Bdry d) : g d (c • z) = ((c ^ 2)⁻¹) ^ d * g d z := by
  unfold g
  have : (c • z).1 ^ 2 + ‖(c • z).2‖ ^ 2 = c ^ 2 * (z.1 ^ 2 + ‖z.2‖ ^ 2) := by
    simp only [Prod.smul_fst, Prod.smul_snd, norm_smul, Real.norm_eq_abs, smul_eq_mul]
    rw [mul_pow, mul_pow, sq_abs]; ring
  rw [this, mul_inv, mul_pow]

lemma cont_iter {f : ℝ × Bdry d → ℝ} (m : ℕ) (hf : ContDiffOn ℝ m f {z | z ≠ 0}) :
    ContinuousOn (fun z => iteratedFDeriv ℝ m f z) {z | z ≠ 0} := by
  have h1 := hf.continuousOn_iteratedFDerivWithin (m := m) le_rfl isOpen_ne'.uniqueDiffOn
  exact h1.congr (fun z hz => (iteratedFDerivWithin_of_isOpen m isOpen_ne' hz).symm)

/-- Homogeneity bound: `‖D^m g(z)‖ ≤ M ‖z‖^{-(2d+m)}`. -/
lemma gbound (m : ℕ) : ∃ M, 0 ≤ M ∧ ∀ z : ℝ × Bdry d, z ≠ 0 →
    ‖iteratedFDeriv ℝ m (g d) z‖ ≤ M * (‖z‖⁻¹) ^ (2 * d + m) := by
  have hS : IsCompact (Metric.sphere (0 : ℝ × Bdry d) 1) := isCompact_sphere 0 1
  have hsub : Metric.sphere (0 : ℝ × Bdry d) 1 ⊆ {z | z ≠ 0} := by
    intro z hz; simp only [mem_sphere_iff_norm, sub_zero] at hz
    intro h0; rw [h0, norm_zero] at hz; exact zero_ne_one hz
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn ((cont_iter m (g_cd m)).mono hsub)
  refine ⟨max C 0, le_max_right _ _, fun z hz => ?_⟩
  set R := ‖z‖ with hR
  have hRp : 0 < R := norm_pos_iff.mpr hz
  set c := R⁻¹ with hc
  have hcp : 0 < c := inv_pos.mpr hRp
  let L : (ℝ × Bdry d) ≃L[ℝ] (ℝ × Bdry d) := ContinuousLinearEquiv.smulLeft (Units.mk0 c hcp.ne')
  have hL : ∀ w, L w = c • w := fun w => rfl
  have hfun : g d = fun w => (c ^ 2) ^ d * (g d ∘ L) w := by
    funext w
    simp only [Function.comp, hL, g_smul]
    rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ (by positivity), one_pow, one_mul]
  have hLz : L z ≠ 0 := by
    rw [hL]; exact smul_ne_zero hcp.ne' hz
  have hnLz : ‖L z‖ = 1 := by
    rw [hL, norm_smul, Real.norm_eq_abs, abs_of_pos hcp, hc, inv_mul_cancel₀ hRp.ne']
  have hcdat : ContDiffAt ℝ m (g d ∘ L) z := by
    have : ContDiffAt ℝ m (g d) (L z) :=
      (g_cd m).contDiffAt (isOpen_ne'.mem_nhds hLz)
    exact this.comp z L.contDiff.contDiffAt
  have e1 : iteratedFDeriv ℝ m (g d) z = (c ^ 2) ^ d • iteratedFDeriv ℝ m (g d ∘ L) z := by
    conv_lhs => rw [hfun]
    have : (fun w => (c ^ 2) ^ d * (g d ∘ L) w) = (c ^ 2) ^ d • (g d ∘ L) := by
      funext w; simp [smul_eq_mul]
    rw [this, iteratedFDeriv_const_smul_apply hcdat]
  have e2 : iteratedFDeriv ℝ m (g d ∘ L) z =
      (iteratedFDeriv ℝ m (g d) (L z)).compContinuousLinearMap fun _ => (L : _ →L[ℝ] _) := by
    have := L.iteratedFDerivWithin_comp_right (g d) (s := Set.univ) uniqueDiffOn_univ
      (Set.mem_univ (L z)) m
    simpa [iteratedFDerivWithin_univ] using this
  have hLn : ‖(L : (ℝ × Bdry d) →L[ℝ] (ℝ × Bdry d))‖ ≤ c := by
    refine ContinuousLinearMap.opNorm_le_bound _ hcp.le (fun w => ?_)
    show ‖L w‖ ≤ c * ‖w‖
    rw [hL, norm_smul, Real.norm_eq_abs, abs_of_pos hcp]
  have hb : ‖iteratedFDeriv ℝ m (g d) (L z)‖ ≤ max C 0 :=
    (hC (L z) (by simp [hnLz])).trans (le_max_left _ _)
  rw [e1, e2, norm_smul]
  calc ‖(c ^ 2) ^ d‖ * ‖(iteratedFDeriv ℝ m (g d) (L z)).compContinuousLinearMap
          fun _ => (L : _ →L[ℝ] _)‖
      ≤ (c ^ 2) ^ d * (max C 0 * ∏ _i : Fin m, c) := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        gcongr
        refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le (𝕜 := ℝ)
          (E := fun _ : Fin m => ℝ × Bdry d) (E₁ := fun _ : Fin m => ℝ × Bdry d) (G := ℝ)
          (iteratedFDeriv ℝ m (g d) (L z))
          (fun _ : Fin m => (L : (ℝ × Bdry d) →L[ℝ] (ℝ × Bdry d)))).trans ?_
        gcongr with i
    _ = max C 0 * c ^ (2 * d + m) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_add, pow_mul]; ring

lemma powbound (i : ℕ) (B : ℝ) : ∃ A, 0 ≤ A ∧ ∀ z : ℝ × Bdry d, |z.1| ≤ B →
    ‖iteratedFDeriv ℝ i (fun z : ℝ × Bdry d => z.1 ^ d) z‖ ≤ A := by
  have hp : ContDiff ℝ ⊤ (fun t : ℝ => t ^ d) := contDiff_id.pow d
  have hc : Continuous (fun t : ℝ => iteratedFDeriv ℝ i (fun t : ℝ => t ^ d) t) :=
    hp.continuous_iteratedFDeriv (m := i) (by exact_mod_cast le_top)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -B) (b := B)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun z hz => ?_⟩
  let F : (ℝ × Bdry d) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ (Bdry d)
  have hfun : (fun z : ℝ × Bdry d => z.1 ^ d) = (fun t : ℝ => t ^ d) ∘ F := rfl
  rw [hfun, F.iteratedFDeriv_comp_right hp z (i := i) (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hF : ‖F‖ ≤ 1 := ContinuousLinearMap.norm_fst_le ℝ ℝ (Bdry d)
  have h1 : ∏ _i : Fin i, ‖F‖ ≤ 1 := Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => hF)
  have h2 : ‖iteratedFDeriv ℝ i (fun t : ℝ => t ^ d) (F z)‖ ≤ max C 0 :=
    (hC (F z) (by simpa [F, Set.mem_Icc, abs_le] using hz)).trans (le_max_left _ _)
  calc _ ≤ max C 0 * 1 := mul_le_mul h2 h1 (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
        (le_max_right _ _)
    _ = max C 0 := mul_one _

/-- Main bound: for `‖z‖ ≥ a > 0` and `|z.1| ≤ B`, `‖D^n k(z)‖ ≤ C ‖z‖^{-2d}`. -/
lemma kbound (n : ℕ) {a : ℝ} (ha : 0 < a) (B : ℝ) : ∃ C, 0 ≤ C ∧ ∀ z : ℝ × Bdry d,
    a ≤ ‖z‖ → |z.1| ≤ B → ‖iteratedFDeriv ℝ n (k d) z‖ ≤ C * (‖z‖⁻¹) ^ (2 * d) := by
  have hA : ∀ i, ∃ A, 0 ≤ A ∧ ∀ z : ℝ × Bdry d, |z.1| ≤ B →
      ‖iteratedFDeriv ℝ i (fun z : ℝ × Bdry d => z.1 ^ d) z‖ ≤ A := fun i => powbound i B
  have hM : ∀ m, ∃ M, 0 ≤ M ∧ ∀ z : ℝ × Bdry d, z ≠ 0 →
      ‖iteratedFDeriv ℝ m (g d) z‖ ≤ M * (‖z‖⁻¹) ^ (2 * d + m) := fun m => gbound m
  choose A hA0 hA using hA
  choose M hM0 hM using hM
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * A i * (M (n - i) * (a⁻¹) ^ (n - i)),
    Finset.sum_nonneg (fun i _ => by have := hA0 i; have := hM0 (n - i); positivity),
    fun z hza hzB => ?_⟩
  have hz : z ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hza; linarith
  have hzs : z ∈ {z : ℝ × Bdry d | z ≠ 0} := hz
  have hleib := norm_iteratedFDerivWithin_mul_le (n := n) (N := n)
    ((contDiff_fst.pow d).contDiffOn (s := {z : ℝ × Bdry d | z ≠ 0})) (g_cd n)
    isOpen_ne'.uniqueDiffOn hzs le_rfl
  have ek : iteratedFDeriv ℝ n (k d) z =
      iteratedFDerivWithin ℝ n (fun y => y.1 ^ d * g d y) {z | z ≠ 0} z :=
    (iteratedFDerivWithin_of_isOpen n isOpen_ne' hzs).symm
  rw [ek]
  refine hleib.trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum (fun i hi => ?_)
  rw [iteratedFDerivWithin_of_isOpen i isOpen_ne' hzs,
    iteratedFDerivWithin_of_isOpen (n - i) isOpen_ne' hzs]
  have h1 := hA i z hzB
  have h2 := hM (n - i) z hz
  have hR : 0 < ‖z‖ := lt_of_lt_of_le ha hza
  have hinv : ‖z‖⁻¹ ≤ a⁻¹ := inv_anti₀ ha hza
  have h3 : M (n - i) * (‖z‖⁻¹) ^ (2 * d + (n - i)) ≤
      M (n - i) * (a⁻¹) ^ (n - i) * (‖z‖⁻¹) ^ (2 * d) := by
    rw [pow_add, mul_comm ((‖z‖⁻¹) ^ (2 * d)), ← mul_assoc]
    have := hM0 (n - i)
    gcongr
  have := hA0 i
  calc (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y : ℝ × Bdry d => y.1 ^ d) z‖ *
        ‖iteratedFDeriv ℝ (n - i) (g d) z‖
      ≤ (n.choose i : ℝ) * A i * (M (n - i) * (‖z‖⁻¹) ^ (2 * d + (n - i))) := by
        gcongr
    _ ≤ (n.choose i : ℝ) * A i * (M (n - i) * (a⁻¹) ^ (n - i) * (‖z‖⁻¹) ^ (2 * d)) := by
        gcongr
    _ = _ := by ring

end WDA

-- ===== part B =====

open WittenAdSHolography MeasureTheory Filter Topology Metric

namespace WDB
open WDA

variable {d : ℕ}

/-- integrable weight -/
noncomputable def w (d : ℕ) (y : Bdry d) : ℝ := (1 + ‖y‖ ^ 2) ^ (-(d : ℝ))

noncomputable def rad (p₀ : ℝ × Bdry d) : ℝ := min (p₀.1 / 2) 1

lemma rad_pos {p₀ : ℝ × Bdry d} (h : 0 < p₀.1) : 0 < rad p₀ := by
  unfold rad; apply lt_min <;> linarith

lemma mem_ball_fst {p₀ p : ℝ × Bdry d} (h : p ∈ ball p₀ (rad p₀)) :
    p₀.1 / 2 < p.1 ∧ p.1 < 3 * p₀.1 / 2 ∧ ‖p.2 - p₀.2‖ < 1 := by
  rw [mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, dist_eq_norm] at h
  have h1 : rad p₀ ≤ p₀.1 / 2 := min_le_left _ _
  have h2 : rad p₀ ≤ 1 := min_le_right _ _
  have := abs_lt.mp (lt_of_lt_of_le h.1 h1)
  refine ⟨by linarith, by linarith, lt_of_lt_of_le h.2 h2⟩

lemma ball_pos {p₀ p : ℝ × Bdry d} (h : p ∈ ball p₀ (rad p₀)) (hp₀ : 0 < p₀.1) : 0 < p.1 := by
  have := mem_ball_fst h; linarith

lemma shift_fst (p : ℝ × Bdry d) (x' : Bdry d) : (p - ((0 : ℝ), x')).1 = p.1 := by simp

lemma shift_snd (p : ℝ × Bdry d) (x' : Bdry d) : (p - ((0 : ℝ), x')).2 = p.2 - x' := by simp

/-- the geometric estimate `‖z‖^{-2d} ≤ β^{2d} w(x' - p₀.2)` -/
lemma geom {p₀ p : ℝ × Bdry d} (hp₀ : 0 < p₀.1) (h : p ∈ ball p₀ (rad p₀)) (x' : Bdry d) :
    (‖p - ((0 : ℝ), x')‖⁻¹) ^ (2 * d) ≤ (1 + 2 / (p₀.1 / 2)) ^ (2 * d) * w d (x' - p₀.2) := by
  obtain ⟨h1, -, h3⟩ := mem_ball_fst h
  set z := p - ((0 : ℝ), x') with hz
  set a := p₀.1 / 2 with ha
  have hapos : 0 < a := by positivity
  have hza : a ≤ ‖z‖ := by
    have : |z.1| ≤ ‖z‖ := by simpa using norm_fst_le z
    rw [hz, shift_fst] at this
    rw [abs_of_pos (by linarith)] at this; linarith
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le hapos hza
  set s := ‖x' - p₀.2‖ with hs
  have hs1 : s ≤ ‖z‖ + 1 := by
    have h2 : ‖z.2‖ ≤ ‖z‖ := norm_snd_le z
    rw [hz, shift_snd] at h2
    have : s ≤ ‖p.2 - x'‖ + ‖p.2 - p₀.2‖ := by
      rw [hs]
      calc ‖x' - p₀.2‖ = ‖(p.2 - p₀.2) - (p.2 - x')‖ := by congr 1; abel
        _ ≤ ‖p.2 - p₀.2‖ + ‖p.2 - x'‖ := norm_sub_le _ _
        _ = _ := add_comm _ _
    linarith
  set β := 1 + 2 / a with hβ
  have hβz : 1 + s ≤ β * ‖z‖ := by
    have : 2 ≤ 2 / a * ‖z‖ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hapos]; linarith
    rw [hβ]; nlinarith
  have hs0 : 0 ≤ s := norm_nonneg _
  have hq : 1 + s ^ 2 ≤ (β * ‖z‖) ^ 2 := by nlinarith
  have hwq : w d (x' - p₀.2) = ((1 + s ^ 2) ^ d)⁻¹ := by
    unfold w
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
  rw [hwq, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc (‖z‖⁻¹) ^ (2 * d) * (1 + s ^ 2) ^ d ≤ (‖z‖⁻¹) ^ (2 * d) * ((β * ‖z‖) ^ 2) ^ d := by
        gcongr
    _ = β ^ (2 * d) := by
        rw [show (‖z‖⁻¹) ^ (2 * d) * ((β * ‖z‖) ^ 2) ^ d = (β * (‖z‖⁻¹ * ‖z‖)) ^ (2 * d) by ring,
          inv_mul_cancel₀ hzpos.ne', mul_one]

lemma dom (n : ℕ) {p₀ : ℝ × Bdry d} (hp₀ : 0 < p₀.1) : ∃ C, 0 ≤ C ∧ ∀ p ∈ ball p₀ (rad p₀),
    ∀ x', ‖iteratedFDeriv ℝ n (k d) (p - ((0 : ℝ), x'))‖ ≤ C * w d (x' - p₀.2) := by
  have ha : 0 < p₀.1 / 2 := by positivity
  obtain ⟨C, hC0, hC⟩ := kbound (d := d) n ha (3 * p₀.1 / 2)
  refine ⟨C * (1 + 2 / (p₀.1 / 2)) ^ (2 * d), by positivity, fun p hp x' => ?_⟩
  obtain ⟨h1, h2, -⟩ := mem_ball_fst hp
  have hza : p₀.1 / 2 ≤ ‖p - ((0 : ℝ), x')‖ := by
    have : |(p - ((0 : ℝ), x')).1| ≤ ‖p - ((0 : ℝ), x')‖ := by
      simpa using norm_fst_le (p - ((0 : ℝ), x'))
    rw [shift_fst, abs_of_pos (by linarith)] at this; linarith
  have hzB : |(p - ((0 : ℝ), x')).1| ≤ 3 * p₀.1 / 2 := by
    rw [shift_fst, abs_of_pos (by linarith)]; linarith
  refine (hC _ hza hzB).trans ?_
  rw [mul_assoc]
  gcongr
  exact geom hp₀ hp x'

lemma w_int (hd : 0 < d) : Integrable (w d) := by
  have h : ((Module.finrank ℝ (Bdry d) : ℕ) : ℝ) < 2 * (d : ℝ) := by
    rw [finrank_euclideanSpace_fin]
    have : (0 : ℝ) < d := by exact_mod_cast hd
    linarith
  have := integrable_rpow_neg_one_add_norm_sq (μ := (volume : Measure (Bdry d))) h
  refine this.congr (Eventually.of_forall fun y => ?_)
  simp only [w]
  congr 1; ring

lemma isOpen_V : IsOpen {z : ℝ × Bdry d | 0 < z.1} := isOpen_lt continuous_const continuous_fst

lemma shift_mem {p : ℝ × Bdry d} (hp : 0 < p.1) (x' : Bdry d) :
    p - ((0 : ℝ), x') ∈ {z : ℝ × Bdry d | 0 < z.1} := by
  show 0 < (p - ((0 : ℝ), x')).1
  rw [shift_fst]; exact hp

lemma cont_shift {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {h : ℝ × Bdry d → F} (hc : ContinuousOn h {z | 0 < z.1})
    (φ : Bdry d → ℝ) (hφ : Continuous φ) {p : ℝ × Bdry d} (hp : 0 < p.1) :
    Continuous (fun x' : Bdry d => φ x' • h (p - ((0 : ℝ), x'))) := by
  refine hφ.smul ?_
  refine hc.comp_continuous (by fun_prop) (fun x' => shift_mem hp x')

/-- Differentiation under the integral sign. -/
lemma gd {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (hd0 : 0 < d) (h : ℝ × Bdry d → F) (φ : Bdry d → ℝ) (hφ : Continuous φ) (Bφ : ℝ)
    (hB : ∀ x, |φ x| ≤ Bφ)
    (hdiff : DifferentiableOn ℝ h {z | 0 < z.1})
    (hc' : ContinuousOn (fderiv ℝ h) {z | 0 < z.1})
    (hbd : ∀ p₀ : ℝ × Bdry d, 0 < p₀.1 → ∃ C, ∀ p ∈ ball p₀ (rad p₀), ∀ x',
      ‖h (p - ((0 : ℝ), x'))‖ ≤ C * w d (x' - p₀.2) ∧
      ‖fderiv ℝ h (p - ((0 : ℝ), x'))‖ ≤ C * w d (x' - p₀.2))
    (p₀ : ℝ × Bdry d) (hp₀ : 0 < p₀.1) :
    HasFDerivAt (fun p => ∫ x', φ x' • h (p - ((0 : ℝ), x')))
      (∫ x', φ x' • fderiv ℝ h (p₀ - ((0 : ℝ), x'))) p₀ := by
  obtain ⟨C, hC⟩ := hbd p₀ hp₀
  have hBφ : 0 ≤ Bφ := (abs_nonneg _).trans (hB 0)
  have hwi : Integrable (fun x' => w d (x' - p₀.2)) := (w_int hd0).comp_sub_right p₀.2
  have hc : ContinuousOn h {z | 0 < z.1} := hdiff.continuousOn
  have hr := rad_pos hp₀
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := volume) (s := ball p₀ (rad p₀))
    (F := fun p x' => φ x' • h (p - ((0 : ℝ), x')))
    (F' := fun p x' => φ x' • fderiv ℝ h (p - ((0 : ℝ), x')))
    (bound := fun x' => Bφ * (C * w d (x' - p₀.2)))
    (ball_mem_nhds p₀ hr) ?_ ?_ ?_ ?_ (hwi.const_mul C |>.const_mul Bφ) ?_
  · filter_upwards [isOpen_V.mem_nhds (show p₀ ∈ {z : ℝ × Bdry d | 0 < z.1} from hp₀)] with p hp
    exact (cont_shift hc φ hφ hp).aestronglyMeasurable
  · refine Integrable.mono' (hwi.const_mul C |>.const_mul Bφ)
      (cont_shift hc φ hφ hp₀).aestronglyMeasurable (Eventually.of_forall fun x' => ?_)
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hB x') (hC p₀ (mem_ball_self hr) x').1 (norm_nonneg _) hBφ
  · exact (cont_shift hc' φ hφ hp₀).aestronglyMeasurable
  · refine Eventually.of_forall fun x' p hp => ?_
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hB x') (hC p hp x').2 (norm_nonneg _) hBφ
  · refine Eventually.of_forall fun x' p hp => ?_
    have hpp : 0 < p.1 := ball_pos hp hp₀
    have hda : DifferentiableAt ℝ h (p - ((0 : ℝ), x')) :=
      hdiff.differentiableAt (isOpen_V.mem_nhds (shift_mem hpp x'))
    have := hda.hasFDerivAt.comp p ((hasFDerivAt_id p).sub_const ((0 : ℝ), x'))
    have h2 := this.const_smul (φ x')
    simp only [ContinuousLinearMap.comp_id] at h2
    exact h2

end WDB

-- ===== part C =====

open WittenAdSHolography MeasureTheory Filter Topology

namespace WDC

variable {d : ℕ}

abbrev P (d : ℕ) := ℝ × Bdry d

lemma path0 (t : ℝ) (y : Bdry d) :
    HasDerivAt (fun s : ℝ => ((s, y) : P d)) ((1 : ℝ), (0 : Bdry d)) t :=
  (hasDerivAt_id t).prodMk (hasDerivAt_const t y)

lemma pathj (t : ℝ) (y v : Bdry d) (s₀ : ℝ) :
    HasDerivAt (fun s : ℝ => ((t, y + s • v) : P d)) ((0 : ℝ), v) s₀ := by
  refine (hasDerivAt_const s₀ t).prodMk ?_
  have := ((hasDerivAt_id s₀).smul_const v).const_add y
  simpa using this

lemma apply_deriv {W1 : P d → (P d →L[ℝ] ℝ)} {W2 : P d → (P d →L[ℝ] P d →L[ℝ] ℝ)} {p : P d}
    (h : HasFDerivAt W1 (W2 p) p) (v : P d) :
    HasFDerivAt (fun q => W1 q v) ((W2 p).flip v) p := by
  have := h.clm_apply (hasFDerivAt_const v p)
  simpa using this

lemma d0_eq {w : ℝ → Bdry d → ℝ} {W : P d → ℝ} {W1 : P d → (P d →L[ℝ] ℝ)}
    (hw : ∀ t y, 0 < t → w t y = W (t, y))
    (h1 : ∀ p : P d, 0 < p.1 → HasFDerivAt W (W1 p) p) {t : ℝ} (ht : 0 < t) (y : Bdry d) :
    d0 w t y = W1 (t, y) ((1 : ℝ), (0 : Bdry d)) := by
  unfold d0
  have hd := (h1 (t, y) ht).comp_hasDerivAt t (path0 t y)
  have hev : (fun s => w s y) =ᶠ[𝓝 t] (W ∘ fun s : ℝ => ((s, y) : P d)) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact hw s y hs
  exact (hd.congr_of_eventuallyEq hev).deriv

lemma dj_eq {w : ℝ → Bdry d → ℝ} {W : P d → ℝ} {W1 : P d → (P d →L[ℝ] ℝ)}
    (hw : ∀ t y, 0 < t → w t y = W (t, y))
    (h1 : ∀ p : P d, 0 < p.1 → HasFDerivAt W (W1 p) p) (j : Fin d) {t : ℝ} (ht : 0 < t)
    (y : Bdry d) :
    dj j w t y = W1 (t, y) ((0 : ℝ), EuclideanSpace.single j (1 : ℝ)) := by
  unfold dj
  have hp := pathj (d := d) t y (EuclideanSpace.single j (1 : ℝ)) 0
  have hd := (h1 (t, y + (0 : ℝ) • EuclideanSpace.single j (1 : ℝ)) (by simpa using ht)).comp_hasDerivAt
    (0 : ℝ) hp
  have heq : (fun s : ℝ => w t (y + s • EuclideanSpace.single j (1 : ℝ))) =
      (W ∘ fun s : ℝ => ((t, y + s • EuclideanSpace.single j (1 : ℝ)) : P d)) := by
    funext s; exact hw t _ ht
  rw [heq, hd.deriv]
  simp

/-- The hyperbolic Laplacian in terms of first and second Fréchet derivatives. -/
lemma lap {w : ℝ → Bdry d → ℝ} {W : P d → ℝ} {W1 : P d → (P d →L[ℝ] ℝ)}
    {W2 : P d → (P d →L[ℝ] P d →L[ℝ] ℝ)}
    (hw : ∀ t y, 0 < t → w t y = W (t, y))
    (h1 : ∀ p : P d, 0 < p.1 → HasFDerivAt W (W1 p) p)
    (h2 : ∀ p : P d, 0 < p.1 → HasFDerivAt W1 (W2 p) p) {t : ℝ} (ht : 0 < t) (y : Bdry d) :
    hypLaplacian w t y = t ^ 2 * (W2 (t, y) ((1 : ℝ), (0 : Bdry d)) ((1 : ℝ), (0 : Bdry d)) +
      ∑ j, W2 (t, y) ((0 : ℝ), EuclideanSpace.single j (1 : ℝ))
        ((0 : ℝ), EuclideanSpace.single j (1 : ℝ))) -
      ((d : ℝ) - 1) * t * W1 (t, y) ((1 : ℝ), (0 : Bdry d)) := by
  unfold hypLaplacian
  -- second x₀-derivative
  have e00 : d0 (d0 w) t y = W2 (t, y) ((1 : ℝ), (0 : Bdry d)) ((1 : ℝ), (0 : Bdry d)) := by
    have := d0_eq (w := d0 w) (W := fun q => W1 q ((1 : ℝ), (0 : Bdry d)))
      (W1 := fun q => (W2 q).flip ((1 : ℝ), (0 : Bdry d)))
      (fun s z hs => d0_eq hw h1 hs z) (fun q hq => apply_deriv (h2 q hq) _) ht y
    simpa using this
  have ejj : ∀ j : Fin d, dj j (dj j w) t y = W2 (t, y) ((0 : ℝ), EuclideanSpace.single j (1 : ℝ))
      ((0 : ℝ), EuclideanSpace.single j (1 : ℝ)) := by
    intro j
    have := dj_eq (w := dj j w) (W := fun q => W1 q ((0 : ℝ), EuclideanSpace.single j (1 : ℝ)))
      (W1 := fun q => (W2 q).flip ((0 : ℝ), EuclideanSpace.single j (1 : ℝ)))
      (fun s z hs => dj_eq hw h1 j hs z) (fun q hq => apply_deriv (h2 q hq) _) j ht y
    simpa using this
  rw [e00, d0_eq hw h1 ht y, Finset.sum_congr rfl (fun j _ => ejj j)]

end WDC

-- ===== part D =====

open WittenAdSHolography MeasureTheory Filter Topology Metric

set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 1024

namespace WDD
open WDA WDB

variable {d : ℕ}

noncomputable def K1 (d : ℕ) := fderiv ℝ (k d)
noncomputable def K2 (d : ℕ) := fderiv ℝ (K1 d)

lemma Vsub : {z : ℝ × Bdry d | 0 < z.1} ⊆ {z | z ≠ 0} := by
  intro z hz h0
  simp only [Set.mem_ofPred_eq] at hz
  rw [h0] at hz; simp at hz

lemma cd0 : ContDiffOn ℝ 4 (k d) {z | z ≠ 0} := k_cd 4

lemma cd1 : ContDiffOn ℝ 3 (K1 d) {z | z ≠ 0} :=
  cd0.fderiv_of_isOpen isOpen_ne' (by norm_num)

lemma cd2 : ContDiffOn ℝ 2 (K2 d) {z | z ≠ 0} :=
  cd1.fderiv_of_isOpen isOpen_ne' (by norm_num)

lemma nf {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : ℝ × Bdry d → F)
    (x : ℝ × Bdry d) : ‖fderiv ℝ f x‖ = ‖iteratedFDeriv ℝ 1 f x‖ := by
  have := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := f) (x := x) (n := 0)
  rw [norm_iteratedFDeriv_zero] at this
  exact this

lemma n0 (z : ℝ × Bdry d) : ‖k d z‖ = ‖iteratedFDeriv ℝ 0 (k d) z‖ :=
  (norm_iteratedFDeriv_zero).symm

lemma n1 (z : ℝ × Bdry d) : ‖K1 d z‖ = ‖iteratedFDeriv ℝ 1 (k d) z‖ := nf _ z

lemma n2 (z : ℝ × Bdry d) : ‖K2 d z‖ = ‖iteratedFDeriv ℝ 2 (k d) z‖ := by
  rw [K2, nf, K1, norm_iteratedFDeriv_fderiv]


lemma w_nonneg (y : Bdry d) : 0 ≤ w d y := Real.rpow_nonneg (by positivity) _

lemma two_bounds {F G : Type*} [NormedAddCommGroup F] [NormedAddCommGroup G]
    {h : ℝ × Bdry d → F} {h' : ℝ × Bdry d → G} (m : ℕ)
    (e : ∀ z, ‖h z‖ = ‖iteratedFDeriv ℝ m (k d) z‖)
    (e' : ∀ z, ‖h' z‖ = ‖iteratedFDeriv ℝ (m + 1) (k d) z‖) (p₀ : ℝ × Bdry d) (hp₀ : 0 < p₀.1) :
    ∃ C, ∀ p ∈ ball p₀ (rad p₀), ∀ x',
      ‖h (p - ((0 : ℝ), x'))‖ ≤ C * w d (x' - p₀.2) ∧
      ‖h' (p - ((0 : ℝ), x'))‖ ≤ C * w d (x' - p₀.2) := by
  obtain ⟨Ca, -, ha⟩ := dom (d := d) m hp₀
  obtain ⟨Cb, -, hb⟩ := dom (d := d) (m + 1) hp₀
  refine ⟨max Ca Cb, fun p hp x' => ⟨?_, ?_⟩⟩
  · rw [e]; exact (ha p hp x').trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (w_nonneg _))
  · rw [e']; exact (hb p hp x').trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (w_nonneg _))

/-- generic differentiation under the integral for `h` among the derivatives of `k`. -/
lemma gdk {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (hd0 : 0 < d) (h : ℝ × Bdry d → F) (m : ℕ) (hcd : ContDiffOn ℝ 2 h {z | z ≠ 0})
    (e : ∀ z, ‖h z‖ = ‖iteratedFDeriv ℝ m (k d) z‖)
    (e' : ∀ z, ‖fderiv ℝ h z‖ = ‖iteratedFDeriv ℝ (m + 1) (k d) z‖)
    {φ : Bdry d → ℝ} (hφ : Continuous φ) {Bφ : ℝ} (hB : ∀ x, |φ x| ≤ Bφ)
    (p : ℝ × Bdry d) (hp : 0 < p.1) :
    HasFDerivAt (fun p => ∫ x', φ x' • h (p - ((0 : ℝ), x')))
      (∫ x', φ x' • fderiv ℝ h (p - ((0 : ℝ), x'))) p :=
  gd hd0 h φ hφ Bφ hB ((hcd.differentiableOn (by norm_num)).mono Vsub)
    ((hcd.continuousOn_fderiv_of_isOpen isOpen_ne' (by norm_num)).mono Vsub)
    (fun p₀ hp₀ => two_bounds m e e' p₀ hp₀) p hp

section integrals

variable (φ : Bdry d → ℝ)

noncomputable def U0 (p : ℝ × Bdry d) : ℝ := ∫ x', φ x' • k d (p - ((0 : ℝ), x'))
noncomputable def U1 (p : ℝ × Bdry d) := ∫ x', φ x' • K1 d (p - ((0 : ℝ), x'))
noncomputable def U2 (p : ℝ × Bdry d) := ∫ x', φ x' • K2 d (p - ((0 : ℝ), x'))

variable {φ} (hd0 : 0 < d) (hφ : Continuous φ) {Bφ : ℝ} (hB : ∀ x, |φ x| ≤ Bφ)
include hd0 hφ hB

lemma hU0 (p : ℝ × Bdry d) (hp : 0 < p.1) : HasFDerivAt (U0 φ) (U1 φ p) p :=
  gdk hd0 (k d) 0 (cd0.of_le (by norm_num)) n0 n1 hφ hB p hp

lemma hU1 (p : ℝ × Bdry d) (hp : 0 < p.1) : HasFDerivAt (U1 φ) (U2 φ p) p :=
  gdk hd0 (K1 d) 1 (cd1.of_le (by norm_num)) n1 n2 hφ hB p hp

lemma hU2 (p : ℝ × Bdry d) (hp : 0 < p.1) : DifferentiableAt ℝ (U2 φ) p :=
  (gdk hd0 (K2 d) 2 cd2 n2
    (fun z => by rw [nf, K2, norm_iteratedFDeriv_fderiv, K1, norm_iteratedFDeriv_fderiv])
    hφ hB p hp).differentiableAt

lemma U0_cd : ContDiffOn ℝ 2 (U0 φ) {z : ℝ × Bdry d | 0 < z.1} := by
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiffOn_succ_iff_fderiv_of_isOpen isOpen_V]
  refine ⟨fun p hp => (hU0 hd0 hφ hB p hp).differentiableAt.differentiableWithinAt,
    by simp, ?_⟩
  have e1 : Set.EqOn (fderiv ℝ (U0 φ)) (U1 φ) {z : ℝ × Bdry d | 0 < z.1} :=
    fun p hp => (hU0 hd0 hφ hB p hp).fderiv
  refine ContDiffOn.congr ?_ e1
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_fderiv_of_isOpen isOpen_V]
  refine ⟨fun p hp => (hU1 hd0 hφ hB p hp).differentiableAt.differentiableWithinAt,
    by simp, ?_⟩
  have e2 : Set.EqOn (fderiv ℝ (U1 φ)) (U2 φ) {z : ℝ × Bdry d | 0 < z.1} :=
    fun p hp => (hU1 hd0 hφ hB p hp).fderiv
  refine ContDiffOn.congr ?_ e2
  rw [contDiffOn_zero]
  exact fun p hp => (hU2 hd0 hφ hB p hp).continuousAt.continuousWithinAt

end integrals

end WDD

-- ===== part E =====

open WittenAdSHolography MeasureTheory Filter Topology Metric

set_option synthInstance.maxHeartbeats 200000

namespace WDE
open WDA WDB WDD

variable {d : ℕ}

lemma bulk_eq {t : ℝ} (ht : 0 < t) (y : Bdry d) : bulkKernel (d : ℝ) t y = k d (t, y) := by
  unfold bulkKernel k g
  rw [Real.rpow_natCast, Real.rpow_natCast, div_eq_mul_inv, inv_pow]

lemma k_hasF (p : ℝ × Bdry d) (hp : 0 < p.1) : HasFDerivAt (k d) (K1 d p) p :=
  ((cd0.differentiableOn (by norm_num)).differentiableAt
    (isOpen_ne'.mem_nhds (Vsub hp))).hasFDerivAt

lemma K1_hasF (p : ℝ × Bdry d) (hp : 0 < p.1) : HasFDerivAt (K1 d) (K2 d p) p :=
  ((cd1.differentiableOn (by norm_num)).differentiableAt
    (isOpen_ne'.mem_nhds (Vsub hp))).hasFDerivAt

lemma integ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hd0 : 0 < d) (h : ℝ × Bdry d → F) (m : ℕ) (hcd : ContDiffOn ℝ 0 h {z | z ≠ 0})
    (e : ∀ z, ‖h z‖ = ‖iteratedFDeriv ℝ m (k d) z‖)
    {φ : Bdry d → ℝ} (hφ : Continuous φ) {Bφ : ℝ} (hB : ∀ x, |φ x| ≤ Bφ)
    (p : ℝ × Bdry d) (hp : 0 < p.1) :
    Integrable (fun x' => φ x' • h (p - ((0 : ℝ), x'))) := by
  obtain ⟨C, -, hC⟩ := dom (d := d) m hp
  have hBφ : 0 ≤ Bφ := (abs_nonneg _).trans (hB 0)
  refine Integrable.mono' (((w_int hd0).comp_sub_right p.2).const_mul C |>.const_mul Bφ)
    (cont_shift (hcd.continuousOn.mono Vsub) φ hφ hp).aestronglyMeasurable
    (Eventually.of_forall fun x' => ?_)
  rw [norm_smul, Real.norm_eq_abs, e]
  exact mul_le_mul (hB x') (hC p (mem_ball_self (rad_pos hp)) x') (norm_nonneg _) hBφ

/-- the kernel identity at every point -/
lemma kernel_lap {t : ℝ} (ht : 0 < t) (y : Bdry d) :
    t ^ 2 * (K2 d (t, y) ((1 : ℝ), (0 : Bdry d)) ((1 : ℝ), (0 : Bdry d)) +
      ∑ j, K2 d (t, y) ((0 : ℝ), EuclideanSpace.single j (1 : ℝ))
        ((0 : ℝ), EuclideanSpace.single j (1 : ℝ))) -
      ((d : ℝ) - 1) * t * K1 d (t, y) ((1 : ℝ), (0 : Bdry d)) = 0 := by
  have hs := (bulkKernel_solution d 0 (d : ℝ) (by ring)).2 t ht y
  rw [WDC.lap (W := k d) (W1 := K1 d) (W2 := K2 d) (fun s z hs => bulk_eq hs z)
    (fun p hp => k_hasF p hp) (fun p hp => K1_hasF p hp) ht y] at hs
  rw [hs, zero_mul]

lemma pI_eq (φ : Bdry d → ℝ) {t : ℝ} (ht : 0 < t) (y : Bdry d) :
    poissonIntegral (d : ℝ) φ t y = U0 φ (t, y) := by
  unfold poissonIntegral U0
  congr 1; funext x'
  rw [smul_eq_mul, mul_comm, Prod.mk_sub_mk, sub_zero, bulk_eq ht]

noncomputable def LamB (d : ℕ) (t : ℝ) :
    ((ℝ × Bdry d) →L[ℝ] (ℝ × Bdry d) →L[ℝ] ℝ) →L[ℝ] ℝ :=
  (t ^ 2) • ((ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : Bdry d))).comp
      (ContinuousLinearMap.apply ℝ ((ℝ × Bdry d) →L[ℝ] ℝ) ((1 : ℝ), (0 : Bdry d))) +
    ∑ j : Fin d, (ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), EuclideanSpace.single j (1 : ℝ))).comp
      (ContinuousLinearMap.apply ℝ ((ℝ × Bdry d) →L[ℝ] ℝ)
        ((0 : ℝ), EuclideanSpace.single j (1 : ℝ))))

noncomputable def LamA (d : ℕ) (t : ℝ) : ((ℝ × Bdry d) →L[ℝ] ℝ) →L[ℝ] ℝ :=
  (((d : ℝ) - 1) * t) • ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : Bdry d))

lemma LamB_apply (t : ℝ) (b : (ℝ × Bdry d) →L[ℝ] (ℝ × Bdry d) →L[ℝ] ℝ) :
    LamB d t b = t ^ 2 * (b ((1 : ℝ), (0 : Bdry d)) ((1 : ℝ), (0 : Bdry d)) +
      ∑ j, b ((0 : ℝ), EuclideanSpace.single j (1 : ℝ)) ((0 : ℝ), EuclideanSpace.single j (1 : ℝ))) := by
  simp [LamB, mul_add]

lemma LamA_apply (t : ℝ) (a : (ℝ × Bdry d) →L[ℝ] ℝ) :
    LamA d t a = ((d : ℝ) - 1) * t * a ((1 : ℝ), (0 : Bdry d)) := by
  simp [LamA]

theorem main_pos (hd0 : 0 < d) :
    ∃ c : ℝ, 0 < c ∧ ∀ φ₀ : Bdry d → ℝ, Continuous φ₀ → (∃ B : ℝ, ∀ x, |φ₀ x| ≤ B) →
      IsMassiveSolution d 0 (fun x₀ x => c * poissonIntegral (d : ℝ) φ₀ x₀ x) ∧
      ∀ x : Bdry d, Tendsto (fun x₀ : ℝ => c * poissonIntegral (d : ℝ) φ₀ x₀ x)
        (𝓝[>] 0) (𝓝 (φ₀ x)) := by
  set I := ∫ u : Bdry d, (1 + ‖u‖ ^ 2) ^ (-(d : ℝ)) with hI
  have hIpos : 0 < I := by
    rw [hI, integral_pos_iff_support_of_nonneg (fun u => Real.rpow_nonneg (by positivity) _)
      (w_int hd0)]
    have : Function.support (fun u : Bdry d => (1 + ‖u‖ ^ 2) ^ (-(d : ℝ))) = Set.univ := by
      ext u; simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact (Real.rpow_pos_of_pos (by positivity) _).ne'
    rw [this]
    exact Measure.measure_univ_pos.mpr (NeZero.ne _)
  refine ⟨I⁻¹, inv_pos.mpr hIpos, fun φ hφ ⟨Bφ, hB⟩ => ⟨⟨?_, ?_⟩, ?_⟩⟩
  · -- regularity
    have hset : (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Bdry d))) = {z | 0 < z.1} := by
      ext z; simp
    rw [hset]
    refine ((contDiffOn_const (c := I⁻¹)).mul (U0_cd hd0 hφ hB)).congr (fun p hp => ?_)
    show I⁻¹ * poissonIntegral (d : ℝ) φ p.1 p.2 = I⁻¹ * U0 φ p
    rw [pI_eq φ hp]
  · -- the equation
    intro t ht y
    have hl := WDC.lap (w := fun x₀ x => I⁻¹ * poissonIntegral (d : ℝ) φ x₀ x)
      (W := fun p => I⁻¹ * U0 φ p) (W1 := fun p => I⁻¹ • U1 φ p) (W2 := fun p => I⁻¹ • U2 φ p)
      (fun s z hs => by simp only [pI_eq φ hs])
      (fun p hp => (hU0 hd0 hφ hB p hp).const_mul I⁻¹)
      (fun p hp => (hU1 hd0 hφ hB p hp).const_smul I⁻¹) ht y
    rw [hl, zero_mul]
    have hI2 := integ hd0 (K2 d) 2 (cd2.of_le (by norm_num)) n2 hφ hB (t, y) ht
    have hI1 := integ hd0 (K1 d) 1 (cd1.of_le (by norm_num)) n1 hφ hB (t, y) ht
    have eB : LamB d t (U2 φ (t, y)) = ∫ x', φ x' * LamB d t (K2 d ((t, y) - ((0 : ℝ), x'))) := by
      rw [U2]
      have hc := ContinuousLinearMap.integral_comp_comm (𝕜 := ℝ) (LamB d t) hI2
      rw [← hc]
      simp
    have eA : LamA d t (U1 φ (t, y)) = ∫ x', φ x' * LamA d t (K1 d ((t, y) - ((0 : ℝ), x'))) := by
      rw [U1]
      have hc := ContinuousLinearMap.integral_comp_comm (𝕜 := ℝ) (LamA d t) hI1
      rw [← hc]
      simp
    have hz : LamB d t (U2 φ (t, y)) - LamA d t (U1 φ (t, y)) = 0 := by
      rw [eB, eA, ← integral_sub]
      · have : (fun x' => φ x' * LamB d t (K2 d ((t, y) - ((0 : ℝ), x'))) -
            φ x' * LamA d t (K1 d ((t, y) - ((0 : ℝ), x')))) = fun _ => 0 := by
          funext x'
          rw [← mul_sub, LamB_apply, LamA_apply, Prod.mk_sub_mk, sub_zero, kernel_lap ht, mul_zero]
        rw [this, integral_zero]
      · have := ContinuousLinearMap.integrable_comp (𝕜 := ℝ) (LamB d t) hI2
        refine this.congr (Eventually.of_forall fun x' => ?_)
        simp
      · have := ContinuousLinearMap.integrable_comp (𝕜 := ℝ) (LamA d t) hI1
        refine this.congr (Eventually.of_forall fun x' => ?_)
        simp
    rw [LamB_apply, LamA_apply] at hz
    simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum]
    linear_combination I⁻¹ * hz
  · -- boundary values
    intro x
    have h := kernel_approx_identity d (d : ℝ) (by
      have : (0 : ℝ) < d := by exact_mod_cast hd0
      linarith) φ hφ ⟨Bφ, hB⟩ x
    have e2 : (2 * (d : ℝ) - d) = d := by ring
    simp only [e2] at h
    have h2 := h.const_mul I⁻¹
    rw [← mul_assoc, inv_mul_cancel₀ hIpos.ne', one_mul] at h2
    refine h2.congr (fun t => ?_)
    rfl

end WDE

-- ===== part F =====

open WittenAdSHolography MeasureTheory Filter Topology

namespace WDF

lemma vol0 : (volume : Measure (Bdry 0)) Set.univ = 1 := by
  have h2 := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 0)).measure_preimage_equiv
    Set.univ
  simp only [Set.preimage_univ] at h2
  rw [h2, MeasureTheory.volume_pi, Measure.pi_univ]; simp

lemma key0 (φ : Bdry 0 → ℝ) (t : ℝ) (x : Bdry 0) : poissonIntegral ((0 : ℕ) : ℝ) φ t x = φ x := by
  unfold poissonIntegral bulkKernel
  simp only [Nat.cast_zero, Real.rpow_zero, div_one, one_mul]
  have : (fun x' => φ x') = fun _ => φ x := funext (fun x' => by rw [Subsingleton.elim x' x])
  rw [this, integral_const, measureReal_def, vol0]; simp

theorem main_zero :
    ∃ c : ℝ, 0 < c ∧ ∀ φ₀ : Bdry 0 → ℝ, Continuous φ₀ → (∃ B : ℝ, ∀ x, |φ₀ x| ≤ B) →
      IsMassiveSolution 0 0 (fun x₀ x => c * poissonIntegral ((0 : ℕ) : ℝ) φ₀ x₀ x) ∧
      ∀ x : Bdry 0, Tendsto (fun x₀ : ℝ => c * poissonIntegral ((0 : ℕ) : ℝ) φ₀ x₀ x)
        (𝓝[>] 0) (𝓝 (φ₀ x)) := by
  refine ⟨1, one_pos, fun φ _ _ => ?_⟩
  have hu : (fun x₀ x => (1 : ℝ) * poissonIntegral ((0 : ℕ) : ℝ) φ x₀ x) = fun _ x => φ x := by
    funext t x; rw [key0, one_mul]
  refine ⟨?_, fun x => ?_⟩
  swap
  · simp only [key0, one_mul]; exact tendsto_const_nhds
  rw [hu]
  refine ⟨?_, ?_⟩
  · refine (contDiffOn_const (c := φ 0)).congr (fun p _ => ?_)
    show φ p.2 = φ 0
    rw [Subsingleton.elim p.2 0]
  · intro t _ y
    simp [hypLaplacian, d0]

end WDF

theorem solution (d : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ φ₀ : Bdry d → ℝ, Continuous φ₀ → (∃ B : ℝ, ∀ x, |φ₀ x| ≤ B) →
      IsMassiveSolution d 0 (fun x₀ x => c * poissonIntegral (d : ℝ) φ₀ x₀ x) ∧
      ∀ x : Bdry d, Tendsto (fun x₀ : ℝ => c * poissonIntegral (d : ℝ) φ₀ x₀ x)
        (𝓝[>] 0) (𝓝 (φ₀ x)) := by
  rcases Nat.eq_zero_or_pos d with h | h
  · subst h; exact WDF.main_zero
  · exact WDE.main_pos h
