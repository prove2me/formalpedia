-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P42.raisedMomentum_tangent
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T03:20:58.195076+00:00
-- url     : https://prove2.me/submissions/6dbb02b7-4725-4568-ac7f-d50c4e6b778d

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P42
open QAlgorithms.Papers.Independent.Renew46.P42

noncomputable section

open scoped BigOperators

open Filter Set MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

theorem g65g_cp {d : ℕ} (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) (i : Fin d)
    (hf : DifferentiableAt ℝ f x) :
    cartesianPartial f x i = deriv (fun t : ℝ => f (x + t • Pi.single i 1)) 0 := by
  have hL : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin d) => WithLp.ofLp y)
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ) : EuclideanSpace ℝ (Fin d) →L[ℝ] (Fin d → ℝ))
      (WithLp.toLp 2 x) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).toContinuousLinearMap.hasFDerivAt
  have hf' : HasFDerivAt f (fderiv ℝ f x) (WithLp.ofLp (WithLp.toLp 2 x)) := hf.hasFDerivAt
  have hc := hf'.comp (WithLp.toLp 2 x) hL
  have hline : HasDerivAt (fun t : ℝ => x + t • Pi.single i (1:ℝ)) (Pi.single i 1) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (Pi.single i (1:ℝ))).const_add x
  have h2 := (by simpa using hf.hasFDerivAt : HasFDerivAt f (fderiv ℝ f x) (x + (0:ℝ) • Pi.single i 1)).comp_hasDerivAt (0:ℝ) hline
  rw [show (fun t : ℝ => f (x + t • Pi.single i 1)) = (f ∘ fun t => x + t • Pi.single i 1) from rfl,
    h2.deriv, cartesianPartial, QAlgorithms.Papers.Independent.Dependency50.P20.coordinatePartial]
  simp only
  rw [show (fun y : EuclideanSpace ℝ (Fin d) => f (WithLp.ofLp y)) = f ∘ WithLp.ofLp from rfl, hc.fderiv]
  simp [EuclideanSpace.single]
  congr 1

theorem g65g_prodDU (a b : ℝ) (U : V4)
    (hQ : U 0 * U 0 - U 1 * U 1 - U 2 * U 2 - U 3 * U 3 = 1) (hab : a + b + a * b = 0) :
    (Matrix.of fun i j : Fin 4 => minkowskiMetric i j + a * apply4 minkowskiMetric U i * apply4 minkowskiMetric U j) *
    (Matrix.of fun i j : Fin 4 => minkowskiMetric i j + b * U i * U j) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_four, apply4, minkowskiMetric, Matrix.one_apply]
  · linear_combination (a * b * U 0 * U 0) * hQ + (U 0 * U 0) * hab
  · linear_combination (a * b * U 0 * U 1) * hQ + (U 0 * U 1) * hab
  · linear_combination (a * b * U 0 * U 2) * hQ + (U 0 * U 2) * hab
  · linear_combination (a * b * U 0 * U 3) * hQ + (U 0 * U 3) * hab
  · linear_combination (a * b * (-U 1) * U 0) * hQ + ((-U 1) * U 0) * hab
  · linear_combination (a * b * (-U 1) * U 1) * hQ + ((-U 1) * U 1) * hab
  · linear_combination (a * b * (-U 1) * U 2) * hQ + ((-U 1) * U 2) * hab
  · linear_combination (a * b * (-U 1) * U 3) * hQ + ((-U 1) * U 3) * hab
  · linear_combination (a * b * (-U 2) * U 0) * hQ + ((-U 2) * U 0) * hab
  · linear_combination (a * b * (-U 2) * U 1) * hQ + ((-U 2) * U 1) * hab
  · linear_combination (a * b * (-U 2) * U 2) * hQ + ((-U 2) * U 2) * hab
  · linear_combination (a * b * (-U 2) * U 3) * hQ + ((-U 2) * U 3) * hab
  · linear_combination (a * b * (-U 3) * U 0) * hQ + ((-U 3) * U 0) * hab
  · linear_combination (a * b * (-U 3) * U 1) * hQ + ((-U 3) * U 1) * hab
  · linear_combination (a * b * (-U 3) * U 2) * hQ + ((-U 3) * U 2) * hab
  · linear_combination (a * b * (-U 3) * U 3) * hQ + ((-U 3) * U 3) * hab

theorem g65g_prodUD (a b : ℝ) (U : V4)
    (hQ : U 0 * U 0 - U 1 * U 1 - U 2 * U 2 - U 3 * U 3 = 1) (hab : a + b + a * b = 0) :
    (Matrix.of fun i j : Fin 4 => minkowskiMetric i j + b * U i * U j) *
    (Matrix.of fun i j : Fin 4 => minkowskiMetric i j + a * apply4 minkowskiMetric U i * apply4 minkowskiMetric U j) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_four, apply4, minkowskiMetric, Matrix.one_apply]
  · linear_combination (a * b * U 0 * U 0) * hQ + (U 0 * U 0) * hab
  · linear_combination (a * b * U 0 * (-U 1)) * hQ + (U 0 * (-U 1)) * hab
  · linear_combination (a * b * U 0 * (-U 2)) * hQ + (U 0 * (-U 2)) * hab
  · linear_combination (a * b * U 0 * (-U 3)) * hQ + (U 0 * (-U 3)) * hab
  · linear_combination (a * b * U 1 * U 0) * hQ + (U 1 * U 0) * hab
  · linear_combination (a * b * U 1 * (-U 1)) * hQ + (U 1 * (-U 1)) * hab
  · linear_combination (a * b * U 1 * (-U 2)) * hQ + (U 1 * (-U 2)) * hab
  · linear_combination (a * b * U 1 * (-U 3)) * hQ + (U 1 * (-U 3)) * hab
  · linear_combination (a * b * U 2 * U 0) * hQ + (U 2 * U 0) * hab
  · linear_combination (a * b * U 2 * (-U 1)) * hQ + (U 2 * (-U 1)) * hab
  · linear_combination (a * b * U 2 * (-U 2)) * hQ + (U 2 * (-U 2)) * hab
  · linear_combination (a * b * U 2 * (-U 3)) * hQ + (U 2 * (-U 3)) * hab
  · linear_combination (a * b * U 3 * U 0) * hQ + (U 3 * U 0) * hab
  · linear_combination (a * b * U 3 * (-U 1)) * hQ + (U 3 * (-U 1)) * hab
  · linear_combination (a * b * U 3 * (-U 2)) * hQ + (U 3 * (-U 2)) * hab
  · linear_combination (a * b * U 3 * (-U 3)) * hQ + (U 3 * (-U 3)) * hab

theorem g65g_gordon (c n : ℝ) (u : V3)
    (hc : 0 < c) (hn : 1 ≤ n) (hu : dot3 u u < c ^ 2) :
    quadratic minkowskiMetric (fourFlow c u) = 1 ∧
    gDown c n u * gUp c n u = 1 ∧ gUp c n u * gDown c n u = 1 := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hpos : 0 < 1 - dot3 u u / c ^ 2 := by rw [sub_pos, div_lt_one hc2]; exact hu
  have hγ2 : lorentzFactor c u ^ 2 * (1 - dot3 u u / c ^ 2) = 1 := by
    have hcu : c ^ 2 - dot3 u u ≠ 0 := by linarith
    rw [lorentzFactor, div_pow, Real.sq_sqrt hpos.le]; field_simp
  have hs' : dot3 u u = u 0 * u 0 + u 1 * u 1 + u 2 * u 2 := by simp [dot3, Fin.sum_univ_three]
  have hQ : fourFlow c u 0 * fourFlow c u 0 - fourFlow c u 1 * fourFlow c u 1 -
      fourFlow c u 2 * fourFlow c u 2 - fourFlow c u 3 * fourFlow c u 3 = 1 := by
    simp only [fourFlow]
    simp
    rw [hs'] at hγ2
    rw [← hγ2]; field_simp; ring
  have hn0 : n ≠ 0 := by positivity
  have hab : (1 / n ^ 2 - 1) + (n ^ 2 - 1) + (1 / n ^ 2 - 1) * (n ^ 2 - 1) = 0 := by
    field_simp; ring
  refine ⟨?_, ?_, ?_⟩
  · simp only [quadratic, Fin.sum_univ_four, minkowskiMetric]
    simp
    linear_combination hQ
  · exact g65g_prodDU _ _ _ hQ hab
  · exact g65g_prodUD _ _ _ hQ hab

theorem g65g_apply_apply (A B : M4) (v : V4) : apply4 A (apply4 B v) = apply4 (A * B) v := by
  funext i
  simp only [apply4, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring

theorem g65g_apply_smul (A : M4) (r : ℝ) (v : V4) : apply4 A (r • v) = r • apply4 A v := by
  funext i
  simp only [apply4, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => by ring

theorem g65g_apply_one (v : V4) : apply4 1 v = v := by
  funext i
  simp [apply4, Matrix.one_apply]

theorem g65g_dot_line (v k : V3) (j : Fin 3) (t : ℝ) :
    dot3 v (k + t • Pi.single j 1) = dot3 v k + t * v j := by
  fin_cases j <;> simp [dot3, Fin.sum_univ_three] <;> ring

theorem g65g_dot_line2 (k : V3) (j : Fin 3) (t : ℝ) :
    dot3 (k + t • Pi.single j 1) (k + t • Pi.single j 1) = dot3 k k + 2 * t * k j + t ^ 2 := by
  fin_cases j <;> simp [dot3, Fin.sum_univ_three] <;> ring

theorem g65g_grad (c n : ℝ) (u k : V3) (j : Fin 3)
    (hA : 0 < c ^ 2 * dot3 k k -
      ((n ^ 2 * c ^ 2 - c ^ 2) / (n ^ 2 * c ^ 2 - dot3 u u)) * (dot3 u k) ^ 2) :
    rayVelocity c n u k j =
      Real.sqrt ((c ^ 2 - dot3 u u) / (n ^ 2 * c ^ 2 - dot3 u u)) *
        ((c ^ 2 * k j - ((n ^ 2 * c ^ 2 - c ^ 2) / (n ^ 2 * c ^ 2 - dot3 u u)) * dot3 u k * u j) /
          Real.sqrt (c ^ 2 * dot3 k k -
            ((n ^ 2 * c ^ 2 - c ^ 2) / (n ^ 2 * c ^ 2 - dot3 u u)) * (dot3 u k) ^ 2)) +
      ((n ^ 2 * c ^ 2 - c ^ 2) / (n ^ 2 * c ^ 2 - dot3 u u)) * u j := by
  set α := (n ^ 2 * c ^ 2 - c ^ 2) / (n ^ 2 * c ^ 2 - dot3 u u) with hα
  set s := Real.sqrt ((c ^ 2 - dot3 u u) / (n ^ 2 * c ^ 2 - dot3 u u)) with hs
  have hdiff : DifferentiableAt ℝ (rayHamiltonian c n u) k := by
    have hd : DifferentiableAt ℝ (fun k' : V3 => c ^ 2 * dot3 k' k' - α * dot3 u k' ^ 2) k := by
      unfold dot3; fun_prop
    have hd2 : DifferentiableAt ℝ (fun k' : V3 => dot3 u k') k := by
      unfold dot3; fun_prop
    have := ((hd.sqrt hA.ne').const_mul s).add (hd2.const_mul α)
    exact this
  rw [rayVelocity]
  unfold QAlgorithms.Papers.Independent.Renew46.P42.gradient
  rw [g65g_cp _ _ _ hdiff]
  have hfun : (fun t : ℝ => rayHamiltonian c n u (k + t • Pi.single j 1)) =
      fun t => s * Real.sqrt (c ^ 2 * (dot3 k k + (2 * k j * t + t ^ 2)) - α * (dot3 u k + u j * t) ^ 2) +
        α * (dot3 u k + u j * t) := by
    funext t
    rw [rayHamiltonian, g65g_dot_line2, g65g_dot_line]
    have e1 : dot3 k k + 2 * t * k j + t ^ 2 = dot3 k k + (2 * k j * t + t ^ 2) := by ring
    have e2 : dot3 u k + t * u j = dot3 u k + u j * t := by ring
    rw [e1, e2]
  rw [hfun]
  have h1 : HasDerivAt (fun t : ℝ => dot3 k k + (2 * k j * t + t ^ 2)) (2 * k j * 1 + ((2:ℕ):ℝ) * 0 ^ (2 - 1) * 1) 0 :=
    (((hasDerivAt_id' (0:ℝ)).const_mul (2 * k j)).add ((hasDerivAt_id' (0:ℝ)).pow 2)).const_add _
  have h2 : HasDerivAt (fun t : ℝ => dot3 u k + u j * t) (u j * 1) 0 :=
    ((hasDerivAt_id' (0:ℝ)).const_mul (u j)).const_add _
  have hg := (h1.const_mul (c ^ 2)).sub ((h2.pow 2).const_mul α)
  have hg0 : c ^ 2 * (dot3 k k + (2 * k j * 0 + 0 ^ 2)) - α * (dot3 u k + u j * 0) ^ 2 ≠ 0 := by
    simp only [mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact hA.ne'
  have hh := ((hg.sqrt hg0).const_mul s).add (h2.const_mul α)
  refine hh.deriv.trans ?_
  have hr : Real.sqrt (c ^ 2 * dot3 k k - α * dot3 u k ^ 2) ≠ 0 := (Real.sqrt_pos.2 hA).ne'
  simp only [Pi.sub_apply, Pi.pow_apply, mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_one]
  field_simp
  ring

theorem g65g_K (c n ω : ℝ) (u k : V3) :
    let K := apply4 (gUp c n u) (waveCovector c ω k)
    K 0 = ω / c + (n ^ 2 - 1) * lorentzFactor c u ^ 2 * (ω - dot3 u k) / c ∧
    (∀ j : Fin 3, spatial K j = k j + (n ^ 2 - 1) * lorentzFactor c u ^ 2 * (ω - dot3 u k) * u j / c ^ 2) := by
  intro K
  refine ⟨?_, ?_⟩
  · simp only [K, apply4, gUp, minkowskiMetric, fourFlow, waveCovector, Fin.sum_univ_four, dot3,
      Fin.sum_univ_three]
    simp
    ring
  · intro j
    fin_cases j <;>
    · simp only [K, spatial, apply4, gUp, minkowskiMetric, fourFlow, waveCovector, Fin.sum_univ_four, dot3,
        Fin.sum_univ_three]
      simp
      ring

theorem g65g_part1 (c n : ℝ) (u k : V3)
    (hc : 0 < c) (hn : 1 ≤ n) (hu : dot3 u u < c ^ 2) (hk : k ≠ 0) :
    let K := apply4 (gUp c n u) (waveCovector c (rayHamiltonian c n u k) k)
    0 < K 0 ∧ spatial K = (K 0 / c) • rayVelocity c n u k := by
  intro K
  obtain ⟨hK0, hKs⟩ := g65g_K c n (rayHamiltonian c n u k) u k
  have hc2 : 0 < c ^ 2 := by positivity
  have hD : 0 < c ^ 2 - dot3 u u := by linarith
  have hn2 : 1 ≤ n ^ 2 := by nlinarith
  have hN : 0 < n ^ 2 * c ^ 2 - dot3 u u := by nlinarith
  set α := (n ^ 2 * c ^ 2 - c ^ 2) / (n ^ 2 * c ^ 2 - dot3 u u) with hα
  have hα0 : 0 ≤ α := div_nonneg (by nlinarith) hN.le
  have hα1 : α ≤ 1 := by rw [hα, div_le_one hN]; linarith
  have hQ : 0 < dot3 k k := by
    have : ∃ i, k i ≠ 0 := by
      by_contra h; push_neg at h; exact hk (funext h)
    obtain ⟨i, hi⟩ := this
    have hsq : ∀ i, 0 ≤ k i * k i := fun i => mul_self_nonneg _
    simp only [dot3, Fin.sum_univ_three]
    fin_cases i <;> simp at hi <;> nlinarith [hsq 0, hsq 1, hsq 2, mul_self_pos.2 hi]
  have hCS : dot3 u k ^ 2 ≤ dot3 u u * dot3 k k := by
    simp only [dot3, Fin.sum_univ_three]
    nlinarith [sq_nonneg (u 0 * k 1 - u 1 * k 0), sq_nonneg (u 0 * k 2 - u 2 * k 0),
      sq_nonneg (u 1 * k 2 - u 2 * k 1)]
  have hu0 : 0 ≤ dot3 u u := by
    simp only [dot3, Fin.sum_univ_three]; nlinarith [mul_self_nonneg (u 0), mul_self_nonneg (u 1), mul_self_nonneg (u 2)]
  have hA : 0 < c ^ 2 * dot3 k k - α * dot3 u k ^ 2 := by
    have h1 : α * dot3 u k ^ 2 ≤ α * (dot3 u u * dot3 k k) := mul_le_mul_of_nonneg_left hCS hα0
    have h2 : α * dot3 u u ≤ dot3 u u := by nlinarith
    nlinarith
  set s := Real.sqrt ((c ^ 2 - dot3 u u) / (n ^ 2 * c ^ 2 - dot3 u u)) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 (div_pos hD hN)
  have hs2 : s ^ 2 = (c ^ 2 - dot3 u u) / (n ^ 2 * c ^ 2 - dot3 u u) := Real.sq_sqrt (div_pos hD hN).le
  set r := Real.sqrt (c ^ 2 * dot3 k k - α * dot3 u k ^ 2) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hA
  have hω : rayHamiltonian c n u k = s * r + α * dot3 u k := rfl
  have hpos : 0 < 1 - dot3 u u / c ^ 2 := by rw [sub_pos, div_lt_one hc2]; exact hu
  have hγ2 : lorentzFactor c u ^ 2 = c ^ 2 / (c ^ 2 - dot3 u u) := by
    rw [lorentzFactor, div_pow, Real.sq_sqrt hpos.le]; field_simp
  have hK0' : K 0 = (n ^ 2 * c ^ 2 - dot3 u u) / (c ^ 2 - dot3 u u) * s * r / c := by
    rw [show K 0 = _ from hK0, hγ2, hω, hα]
    field_simp
    ring
  refine ⟨?_, ?_⟩
  · rw [hK0']; positivity
  · funext j
    rw [show spatial K j = _ from hKs j, Pi.smul_apply, smul_eq_mul, g65g_grad c n u k j hA, hK0', hγ2, hω]
    rw [← hs, ← hα, ← hr]
    have e : (n ^ 2 * c ^ 2 - dot3 u u) / (c ^ 2 - dot3 u u) * s * r / c / c *
        (s * ((c ^ 2 * k j - α * dot3 u k * u j) / r) + α * u j) =
        (n ^ 2 * c ^ 2 - dot3 u u) / ((c ^ 2 - dot3 u u) * c ^ 2) * s ^ 2 * (c ^ 2 * k j - α * dot3 u k * u j) +
        (n ^ 2 * c ^ 2 - dot3 u u) / ((c ^ 2 - dot3 u u) * c ^ 2) * s * r * α * u j := by
      field_simp
    rw [e, hs2, hα]
    field_simp
    ring

theorem solution (c n : ℝ) (u k : V3)
    (hc : 0 < c) (hn : 1 ≤ n) (hu : dot3 u u < c ^ 2) (hk : k ≠ 0) :
    (let K := apply4 (gUp c n u) (waveCovector c (rayHamiltonian c n u k) k)
     0 < K 0 ∧ spatial K = (K 0 / c) • rayVelocity c n u k) ∧
    (∀ (m : ℝ) (v : V4), 0 < m → 0 < v 0 →
      0 < quadratic (gDown c n u) v →
      let K := apply4 (gUp c n u) (massiveCovector c m (gDown c n u) v)
      K = (m * c / Real.sqrt (quadratic (gDown c n u) v)) • v ∧
      K = (K 0 / c) • ((c / v 0) • v)) := by
  refine ⟨g65g_part1 c n u k hc hn hu hk, ?_⟩
  intro m v hm hv hq K
  have hinv := (g65g_gordon c n u hc hn hu).2.2
  have hK : K = (m * c / Real.sqrt (quadratic (gDown c n u) v)) • v := by
    show apply4 (gUp c n u) ((m * c / Real.sqrt (quadratic (gDown c n u) v)) • apply4 (gDown c n u) v) = _
    rw [g65g_apply_smul, g65g_apply_apply, hinv, g65g_apply_one]
  refine ⟨hK, ?_⟩
  rw [hK, smul_smul]
  congr 1
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp [hv.ne', hc.ne']
