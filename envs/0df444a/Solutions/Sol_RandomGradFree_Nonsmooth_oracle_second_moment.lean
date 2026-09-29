-- Prove2me | solution 1 for RandomGradFree.Nonsmooth.oracle_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:44:49.75236+00:00
-- url     : https://prove2.me/submissions/02701c5f-c164-48dd-8481-60cb31b364ce

import Mathlib
import Definitions.Def_RandomGradFree_Nonsmooth_oracle

open MeasureTheory ProbabilityTheory

namespace RandomGradFree.Nonsmooth

lemma aux_osm_deriv (p p' q : ℝ → ℝ) (hp : ∀ t, HasDerivAt p (p' t) t)
    (hq : ∀ t, q t = p' t + t * p t) :
    deriv (fun t => p t * Real.exp (t ^ 2 / 2)) = fun t => q t * Real.exp (t ^ 2 / 2) := by
  funext t
  have h1 : HasDerivAt (fun t : ℝ => Real.exp (t ^ 2 / 2)) (Real.exp (t ^ 2 / 2) * t) t := by
    have := ((hasDerivAt_pow 2 t).div_const 2).exp
    convert this using 1
    ring
  have h2 : HasDerivAt (fun t => p t * Real.exp (t ^ 2 / 2))
      (p' t * Real.exp (t ^ 2 / 2) + p t * (Real.exp (t ^ 2 / 2) * t)) t := (hp t).mul h1
  rw [h2.deriv, hq]
  ring

lemma aux_osm_mgf : mgf id (gaussianReal 0 1) = fun t => 1 * Real.exp (t ^ 2 / 2) := by
  rw [mgf_id_gaussianReal]
  funext t
  simp

lemma aux_osm_d1 : deriv (fun t : ℝ => 1 * Real.exp (t ^ 2 / 2))
    = fun t => t * Real.exp (t ^ 2 / 2) :=
  aux_osm_deriv (fun _ => 1) (fun _ => 0) (fun t => t) (fun t => hasDerivAt_const t 1)
    (by intro t; ring)

lemma aux_osm_d2 : deriv (fun t : ℝ => t * Real.exp (t ^ 2 / 2))
    = fun t => (1 + t ^ 2) * Real.exp (t ^ 2 / 2) :=
  aux_osm_deriv (fun t => t) (fun _ => 1) (fun t => 1 + t ^ 2) (fun t => hasDerivAt_id t)
    (by intro t; ring)

lemma aux_osm_d3 : deriv (fun t : ℝ => (1 + t ^ 2) * Real.exp (t ^ 2 / 2))
    = fun t => (3 * t + t ^ 3) * Real.exp (t ^ 2 / 2) := by
  refine aux_osm_deriv (fun t => 1 + t ^ 2) (fun t => 2 * t) (fun t => 3 * t + t ^ 3) ?_
    (by intro t; ring)
  intro t
  have := ((hasDerivAt_pow 2 t).const_add 1)
  exact this.congr_deriv (by norm_num)

lemma aux_osm_d4 : deriv (fun t : ℝ => (3 * t + t ^ 3) * Real.exp (t ^ 2 / 2))
    = fun t => (3 + 6 * t ^ 2 + t ^ 4) * Real.exp (t ^ 2 / 2) := by
  refine aux_osm_deriv (fun t => 3 * t + t ^ 3) (fun t => 3 + 3 * t ^ 2)
    (fun t => 3 + 6 * t ^ 2 + t ^ 4) ?_ (by intro t; ring)
  intro t
  have : HasDerivAt (fun t : ℝ => 3 * t + t ^ 3) (3 * 1 + (3 : ℕ) * t ^ (3 - 1)) t :=
    ((hasDerivAt_id t).const_mul 3).add (hasDerivAt_pow 3 t)
  exact this.congr_deriv (by norm_num)

lemma aux_osm_moment2 : ∫ x, x ^ 2 ∂(gaussianReal 0 1) = 1 := by
  have h := iteratedDeriv_mgf_zero (X := id) (μ := gaussianReal 0 1) (by simp) 2
  rw [aux_osm_mgf, iteratedDeriv_eq_iterate] at h
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply] at h
  rw [aux_osm_d1, aux_osm_d2] at h
  simp only [Pi.pow_apply, id] at h
  rw [← h]
  simp

lemma aux_osm_moment4 : ∫ x, x ^ 4 ∂(gaussianReal 0 1) = 3 := by
  have h := iteratedDeriv_mgf_zero (X := id) (μ := gaussianReal 0 1) (by simp) 4
  rw [aux_osm_mgf, iteratedDeriv_eq_iterate] at h
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply] at h
  rw [aux_osm_d1, aux_osm_d2, aux_osm_d3, aux_osm_d4] at h
  simp only [Pi.pow_apply, id] at h
  rw [← h]
  simp

lemma aux_osm_memLp_sq : MemLp (fun y : ℝ => y ^ 2) 2 (gaussianReal 0 1) := by
  rw [memLp_two_iff_integrable_sq (by fun_prop)]
  have := (memLp_id_gaussianReal (μ := 0) (v := 1) 4).integrable_norm_pow (p := 4) (by norm_num)
  refine this.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [id, Real.norm_eq_abs]
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs]

lemma aux_osm_var : Var[fun y : ℝ => y ^ 2; gaussianReal 0 1] ≤ 3 := by
  refine (variance_le_expectation_sq (by fun_prop)).trans (le_of_eq ?_)
  rw [← aux_osm_moment4]
  congr 1
  funext y
  simp only [Pi.pow_apply]
  ring

lemma aux_osm_fourth {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    ∫ u, ‖u‖ ^ 4 ∂(stdGaussian E) ≤ ((Module.finrank ℝ E : ℝ) + 4) ^ 2 := by
  rw [stdGaussian]
  set n := Module.finrank ℝ E
  set b := stdOrthonormalBasis ℝ E
  have hmeas : Measurable (fun x : Fin n → ℝ => ∑ i, x i • b i) := by fun_prop
  have hcont : Continuous (fun u : E => ‖u‖ ^ 4) := by fun_prop
  rw [integral_map hmeas.aemeasurable hcont.aestronglyMeasurable]
  have hnorm : ∀ x : Fin n → ℝ, ‖∑ i, x i • b i‖ ^ 4 = (∑ i, x i ^ 2) ^ 2 := by
    intro x
    have hs : ∑ i, x i • b i = b.repr.symm (WithLp.toLp 2 x) := by
      have := b.sum_repr_symm (WithLp.toLp 2 x)
      simpa only [PiLp.toLp_apply] using this
    have : ‖∑ i, x i • b i‖ ^ 2 = ∑ i, x i ^ 2 := by
      rw [hs, LinearIsometryEquiv.norm_map, EuclideanSpace.real_norm_sq_eq]
    rw [show ‖∑ i, x i • b i‖ ^ 4 = (‖∑ i, x i • b i‖ ^ 2) ^ 2 by ring, this]
  simp_rw [hnorm]
  set π := Measure.pi (fun _ : Fin n ↦ gaussianReal 0 1)
  set Y : (Fin n → ℝ) → ℝ := ∑ i, fun ω => (fun y : ℝ => y ^ 2) (ω i) with hYdef
  have hY : ∀ x, Y x = ∑ i, x i ^ 2 := by
    intro x
    simp [Y, Finset.sum_apply]
  have hmem_i : ∀ i : Fin n, MemLp (fun ω : Fin n → ℝ => (fun y : ℝ => y ^ 2) (ω i)) 2 π :=
    fun i => aux_osm_memLp_sq.comp_measurePreserving (measurePreserving_eval _ i)
  have hmemY : MemLp Y 2 π := by
    rw [hYdef]
    exact memLp_finsetSum' _ (fun i _ => hmem_i i)
  have hvarY : Var[Y; π] = ∑ i : Fin n, Var[fun y : ℝ => y ^ 2; gaussianReal 0 1] :=
    variance_sum_pi (X := fun _ y => y ^ 2) (fun _ => aux_osm_memLp_sq)
  have hmeanY : π[Y] = (n : ℝ) := by
    have : ∫ x, Y x ∂π = ∫ x, ∑ i, x i ^ 2 ∂π := by simp_rw [hY]
    rw [this, integral_finsetSum]
    · have hi : ∀ i : Fin n, ∫ x, x i ^ 2 ∂π = 1 := fun i => by
        rw [← aux_osm_moment2]
        exact integral_comp_eval (μ := fun _ : Fin n ↦ gaussianReal 0 1) (i := i)
          (f := fun y : ℝ => y ^ 2) (by fun_prop)
      simp_rw [hi]
      simp [n]
    · intro i _
      exact integrable_comp_eval (μ := fun _ : Fin n ↦ gaussianReal 0 1)
        (f := fun y : ℝ => y ^ 2) (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_sq
  have hsq : ∫ x, (∑ i, x i ^ 2) ^ 2 ∂π = π[Y ^ 2] := by
    congr 1
    funext x
    simp only [Pi.pow_apply, hY]
  have hvar_le : Var[Y; π] ≤ 3 * n := by
    rw [hvarY]
    calc ∑ i : Fin n, Var[fun y : ℝ => y ^ 2; gaussianReal 0 1] ≤ ∑ _i : Fin n, (3 : ℝ) :=
          Finset.sum_le_sum (fun i _ => aux_osm_var)
      _ = 3 * n := by simp [n]; ring
  have h := variance_eq_sub hmemY
  rw [hsq]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  nlinarith [h, hmeanY, hvar_le]

end RandomGradFree.Nonsmooth

open RandomGradFree.Nonsmooth
open MeasureTheory ProbabilityTheory

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (L₀ : ℝ) (hL₀ : 0 ≤ L₀) (hLip : ∀ x y, |f x - f y| ≤ L₀ * ‖x - y‖)
    (μ : ℝ) (hμ : 0 < μ) (x : E) :
    ∫ u, ‖oracle f μ x u‖ ^ 2 ∂(stdGaussian E)
      ≤ L₀ ^ 2 * ((Module.finrank ℝ E : ℝ) + 4) ^ 2 := by
  have hpt : ∀ u, ‖oracle f μ x u‖ ^ 2 ≤ L₀ ^ 2 * ‖u‖ ^ 4 := by
    intro u
    have h1 : ‖oracle f μ x u‖ ≤ L₀ * ‖u‖ ^ 2 := by
      unfold oracle
      rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hμ]
      have := hLip (x + μ • u) x
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hμ] at this
      rw [div_mul_eq_mul_div, div_le_iff₀ hμ]
      calc |f (x + μ • u) - f x| * ‖u‖ ≤ (L₀ * (μ * ‖u‖)) * ‖u‖ := by gcongr
        _ = L₀ * ‖u‖ ^ 2 * μ := by ring
    calc ‖oracle f μ x u‖ ^ 2 ≤ (L₀ * ‖u‖ ^ 2) ^ 2 := by gcongr
      _ = L₀ ^ 2 * ‖u‖ ^ 4 := by ring
  have hint : Integrable (fun u : E => ‖u‖ ^ 4) (stdGaussian E) :=
    (IsGaussian.memLp_id (stdGaussian E) (4 : ℕ) (by simp)).integrable_norm_pow (by norm_num)
  calc ∫ u, ‖oracle f μ x u‖ ^ 2 ∂(stdGaussian E)
      ≤ ∫ u, L₀ ^ 2 * ‖u‖ ^ 4 ∂(stdGaussian E) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => by positivity)
          (hint.const_mul _) (Filter.Eventually.of_forall hpt)
    _ = L₀ ^ 2 * ∫ u, ‖u‖ ^ 4 ∂(stdGaussian E) := integral_const_mul _ _
    _ ≤ L₀ ^ 2 * ((Module.finrank ℝ E : ℝ) + 4) ^ 2 := by
        gcongr
        exact aux_osm_fourth
