-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P42.slowFlow_firstJet
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T05:40:59.798987+00:00
-- url     : https://prove2.me/submissions/0700fd25-dccc-4dee-83f6-859800d9e0de

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

theorem g66k2_even (P : ℝ → ℝ) (hP : DifferentiableAt ℝ P 0) :
    HasDerivAt (fun e : ℝ => P (e ^ 2)) 0 0 := by
  have h1 : HasDerivAt (fun e : ℝ => e ^ 2) 0 0 := by
    have := hasDerivAt_pow 2 (0:ℝ)
    simp at this
    exact this
  have h3 := HasDerivAt.comp_of_eq (0:ℝ) hP.hasDerivAt h1 (by simp)
  rw [mul_zero] at h3
  exact h3

theorem g66k2_evenodd (P Q : ℝ → ℝ) (hP : DifferentiableAt ℝ P 0)
    (hQ : DifferentiableAt ℝ Q 0) (b : ℝ) :
    HasDerivAt (fun e : ℝ => P (e ^ 2) + Q (e ^ 2) * (e * b)) (Q 0 * b) 0 := by
  have := (g66k2_even P hP).add ((g66k2_even Q hQ).mul ((hasDerivAt_id (0:ℝ)).mul_const b))
  refine this.congr_deriv ?_
  simp

theorem g66k2_dsl (e : ℝ) (u w : V3) : dot3 (e • u) w = e * dot3 u w := by
  simp [dot3, Fin.sum_univ_three]; ring

theorem g66k2_dss (e : ℝ) (u : V3) : dot3 (e • u) (e • u) = e ^ 2 * dot3 u u := by
  simp [dot3, Fin.sum_univ_three]; ring

theorem g66k2_kk (k : V3) (hk : k ≠ 0) : 0 < dot3 k k := by
  have : ∃ i, k i ≠ 0 := by
    by_contra h; push Not at h; exact hk (funext h)
  obtain ⟨i, hi⟩ := this
  have hsq : ∀ i, 0 ≤ k i * k i := fun i => mul_self_nonneg _
  simp only [dot3, Fin.sum_univ_three]
  fin_cases i <;> simp at hi <;> nlinarith [hsq 0, hsq 1, hsq 2, mul_self_pos.2 hi]

/-- auxiliary even functions -/
def g66k2_S (c n nu : ℝ) (t : ℝ) : ℝ := Real.sqrt ((c ^ 2 - t * nu) / (n ^ 2 * c ^ 2 - t * nu))
def g66k2_A (c n nu : ℝ) (t : ℝ) : ℝ := (n ^ 2 * c ^ 2 - c ^ 2) / (n ^ 2 * c ^ 2 - t * nu)
def g66k2_R (c n nu kk uk : ℝ) (t : ℝ) : ℝ := c ^ 2 * kk - g66k2_A c n nu t * (t * uk ^ 2)

theorem g66k2_A_diff (c n nu : ℝ) (hc : 0 < c) (hn : 1 ≤ n) :
    DifferentiableAt ℝ (g66k2_A c n nu) 0 := by
  have : n ^ 2 * c ^ 2 - 0 * nu ≠ 0 := by
    have : 0 < n ^ 2 * c ^ 2 := by positivity
    simpa using this.ne'
  unfold g66k2_A
  exact (differentiableAt_const _).div (by fun_prop) this

theorem g66k2_S_diff (c n nu : ℝ) (hc : 0 < c) (hn : 1 ≤ n) :
    DifferentiableAt ℝ (g66k2_S c n nu) 0 := by
  have hd : n ^ 2 * c ^ 2 - 0 * nu ≠ 0 := by
    have : 0 < n ^ 2 * c ^ 2 := by positivity
    simpa using this.ne'
  have hq : (c ^ 2 - 0 * nu) / (n ^ 2 * c ^ 2 - 0 * nu) ≠ 0 := by
    rw [zero_mul, sub_zero, sub_zero]; positivity
  unfold g66k2_S
  exact (((by fun_prop : DifferentiableAt ℝ (fun t : ℝ => c ^ 2 - t * nu) 0)).div
    (by fun_prop) hd).sqrt hq

theorem g66k2_A0 (c n nu : ℝ) (hc : 0 < c) (hn : 1 ≤ n) :
    g66k2_A c n nu 0 = 1 - 1 / n ^ 2 := by
  have : 0 < n := by linarith
  unfold g66k2_A; field_simp; ring

theorem g66k2_S0 (c n nu : ℝ) (hc : 0 < c) (hn : 1 ≤ n) :
    g66k2_S c n nu 0 = 1 / n := by
  have : 0 < n := by linarith
  unfold g66k2_S
  rw [show (c ^ 2 - 0 * nu) / (n ^ 2 * c ^ 2 - 0 * nu) = (1 / n) ^ 2 by field_simp; ring]
  exact Real.sqrt_sq (by positivity)

theorem g66k2_R0 (c n nu kk uk : ℝ) : g66k2_R c n nu kk uk 0 = c ^ 2 * kk := by
  simp [g66k2_R]

theorem g66k2_R_diff (c n nu kk uk : ℝ) (hc : 0 < c) (hn : 1 ≤ n) :
    DifferentiableAt ℝ (g66k2_R c n nu kk uk) 0 := by
  unfold g66k2_R
  exact (differentiableAt_const _).sub ((g66k2_A_diff c n nu hc hn).mul (by fun_prop))

theorem g66k2_sqrtR_diff (c n nu kk uk : ℝ) (hc : 0 < c) (hn : 1 ≤ n) (hkk : 0 < kk) :
    DifferentiableAt ℝ (fun t => Real.sqrt (g66k2_R c n nu kk uk t)) 0 :=
  (g66k2_R_diff c n nu kk uk hc hn).sqrt (by rw [g66k2_R0]; positivity)

theorem g66k2_H_eq (c n e : ℝ) (u k : V3) :
    rayHamiltonian c n (e • u) k =
      g66k2_S c n (dot3 u u) (e ^ 2) * Real.sqrt (g66k2_R c n (dot3 u u) (dot3 k k) (dot3 u k) (e ^ 2)) +
      g66k2_A c n (dot3 u u) (e ^ 2) * (e * dot3 u k) := by
  rw [rayHamiltonian, g66k2_dss, g66k2_dsl]
  simp only [g66k2_S, g66k2_R, g66k2_A]
  rw [mul_pow]; try ring_nf

theorem g66k2_H_jet (c n : ℝ) (u k : V3) (hc : 0 < c) (hn : 1 ≤ n) (hk : k ≠ 0) :
    rayHamiltonian c n ((0:ℝ) • u) k = c * length3 k / n ∧
    HasDerivAt (fun e : ℝ => rayHamiltonian c n (e • u) k) ((1 - 1 / n ^ 2) * dot3 u k) 0 := by
  have hkk := g66k2_kk k hk
  have hn0 : 0 < n := by linarith
  constructor
  · rw [g66k2_H_eq]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, mul_zero, add_zero]
    rw [g66k2_S0 c n _ hc hn, g66k2_R0, Real.sqrt_mul (by positivity), Real.sqrt_sq hc.le, length3]
    field_simp
  · have h := g66k2_evenodd (fun t => g66k2_S c n (dot3 u u) t *
        Real.sqrt (g66k2_R c n (dot3 u u) (dot3 k k) (dot3 u k) t)) (g66k2_A c n (dot3 u u))
      ((g66k2_S_diff c n _ hc hn).mul (g66k2_sqrtR_diff c n _ _ _ hc hn hkk))
      (g66k2_A_diff c n _ hc hn) (dot3 u k)
    rw [g66k2_A0 c n _ hc hn] at h
    convert h using 1
    funext e; exact g66k2_H_eq c n e u k

theorem g66k2_R_ev (c n nu kk uk : ℝ) (hc : 0 < c) (hn : 1 ≤ n) (hkk : 0 < kk) :
    ∀ᶠ e : ℝ in nhds 0, 0 < g66k2_R c n nu kk uk (e ^ 2) := by
  have hcont : ContinuousAt (fun e : ℝ => g66k2_R c n nu kk uk (e ^ 2)) 0 := by
    have h1 := (g66k2_R_diff c n nu kk uk hc hn).continuousAt
    have h2 : ContinuousAt (fun e : ℝ => e ^ 2) 0 := by fun_prop
    exact ContinuousAt.comp_of_eq (g := g66k2_R c n nu kk uk) (f := fun e : ℝ => e ^ 2) h1 h2 (by simp)
  have h0 : 0 < g66k2_R c n nu kk uk ((0:ℝ) ^ 2) := by
    rw [zero_pow two_ne_zero, g66k2_R0]; positivity
  exact hcont.eventually (lt_mem_nhds h0)

theorem g66k2_V_comp (c n e : ℝ) (u k : V3) (j : Fin 3)
    (hR : 0 < g66k2_R c n (dot3 u u) (dot3 k k) (dot3 u k) (e ^ 2)) :
    rayVelocity c n (e • u) k j =
      g66k2_S c n (dot3 u u) (e ^ 2) * ((c ^ 2 * k j - g66k2_A c n (dot3 u u) (e ^ 2) *
        (e ^ 2 * (dot3 u k * u j))) / Real.sqrt (g66k2_R c n (dot3 u u) (dot3 k k) (dot3 u k) (e ^ 2))) +
      g66k2_A c n (dot3 u u) (e ^ 2) * (e * u j) := by
  have hA : 0 < c ^ 2 * dot3 k k -
      ((n ^ 2 * c ^ 2 - c ^ 2) / (n ^ 2 * c ^ 2 - dot3 (e • u) (e • u))) * (dot3 (e • u) k) ^ 2 := by
    convert hR using 1
    rw [g66k2_dss, g66k2_dsl, g66k2_R, g66k2_A]; ring
  rw [g65g_grad c n (e • u) k j hA, g66k2_dss, g66k2_dsl]
  simp only [g66k2_S, g66k2_R, g66k2_A, Pi.smul_apply, smul_eq_mul]
  rw [mul_pow]; ring_nf

theorem g66k2_V_jet (c n : ℝ) (u k : V3) (hc : 0 < c) (hn : 1 ≤ n) (hk : k ≠ 0) :
    rayVelocity c n ((0:ℝ) • u) k = (c / n) • ((1 / length3 k) • k) ∧
    HasDerivAt (fun e : ℝ => rayVelocity c n (e • u) k) ((1 - 1 / n ^ 2) • u) 0 := by
  have hkk := g66k2_kk k hk
  have hn0 : 0 < n := by linarith
  have hev := g66k2_R_ev c n (dot3 u u) (dot3 k k) (dot3 u k) hc hn hkk
  constructor
  · funext j
    rw [g66k2_V_comp c n 0 u k j (by simpa using hev.self_of_nhds)]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, mul_zero, sub_zero,
      add_zero, Pi.smul_apply, smul_eq_mul]
    rw [g66k2_S0 c n _ hc hn, g66k2_R0, Real.sqrt_mul (by positivity), Real.sqrt_sq hc.le, length3]
    have : 0 < Real.sqrt (dot3 k k) := Real.sqrt_pos.2 hkk
    field_simp
  · rw [hasDerivAt_pi]
    intro j
    have h := g66k2_evenodd (fun t => g66k2_S c n (dot3 u u) t * ((c ^ 2 * k j - g66k2_A c n (dot3 u u) t *
        (t * (dot3 u k * u j))) / Real.sqrt (g66k2_R c n (dot3 u u) (dot3 k k) (dot3 u k) t)))
      (g66k2_A c n (dot3 u u))
      ((g66k2_S_diff c n _ hc hn).mul (((differentiableAt_const _).sub
        ((g66k2_A_diff c n _ hc hn).mul (by fun_prop))).div (g66k2_sqrtR_diff c n _ _ _ hc hn hkk)
        (by rw [g66k2_R0]; positivity)))
      (g66k2_A_diff c n _ hc hn) (u j)
    rw [g66k2_A0 c n _ hc hn] at h
    simp only [Pi.smul_apply, smul_eq_mul]
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [hev] with e he
    exact g66k2_V_comp c n e u k j he

def g66k2_L (c nu : ℝ) (t : ℝ) : ℝ := 1 / Real.sqrt (1 - t * nu / c ^ 2)

theorem g66k2_L_diff (c nu : ℝ) : DifferentiableAt ℝ (g66k2_L c nu) 0 := by
  have h1 : (1 : ℝ) - 0 * nu / c ^ 2 ≠ 0 := by simp
  have h2 : Real.sqrt (1 - 0 * nu / c ^ 2) ≠ 0 := by simp
  unfold g66k2_L
  exact (differentiableAt_const _).div ((by fun_prop : DifferentiableAt ℝ
    (fun t : ℝ => 1 - t * nu / c ^ 2) 0).sqrt h1) h2

theorem g66k2_L0 (c nu : ℝ) : g66k2_L c nu 0 = 1 := by simp [g66k2_L]

theorem g66k2_L_eq (c e : ℝ) (u : V3) : lorentzFactor c (e • u) = g66k2_L c (dot3 u u) (e ^ 2) := by
  rw [lorentzFactor, g66k2_dss, g66k2_L]

theorem g66k2_D_jet (c n omega : ℝ) (u k : V3) (hc : 0 < c) :
    -rayDispersion c n ((0:ℝ) • u) k omega / c ^ 2 = dot3 k k - n ^ 2 * omega ^ 2 / c ^ 2 ∧
    HasDerivAt (fun e : ℝ => -rayDispersion c n (e • u) k omega / c ^ 2)
      (2 * omega * (n ^ 2 - 1) * dot3 u k / c ^ 2) 0 := by
  have hfun : ∀ e : ℝ, -rayDispersion c n (e • u) k omega / c ^ 2 =
      (-(omega ^ 2 - c ^ 2 * dot3 k k) - (n ^ 2 - 1) * g66k2_L c (dot3 u u) (e ^ 2) ^ 2 *
        (omega ^ 2 + e ^ 2 * dot3 u k ^ 2)) / c ^ 2 +
      ((n ^ 2 - 1) * g66k2_L c (dot3 u u) (e ^ 2) ^ 2 * (2 * omega) / c ^ 2) * (e * dot3 u k) := by
    intro e
    rw [rayDispersion, g66k2_L_eq, g66k2_dsl]
    ring
  constructor
  · rw [hfun]; simp [g66k2_L0]; field_simp; ring
  · have h := g66k2_evenodd (fun t => (-(omega ^ 2 - c ^ 2 * dot3 k k) - (n ^ 2 - 1) * g66k2_L c (dot3 u u) t ^ 2 *
        (omega ^ 2 + t * dot3 u k ^ 2)) / c ^ 2)
      (fun t => (n ^ 2 - 1) * g66k2_L c (dot3 u u) t ^ 2 * (2 * omega) / c ^ 2)
      (by have := g66k2_L_diff c (dot3 u u); fun_prop)
      (by have := g66k2_L_diff c (dot3 u u); fun_prop) (dot3 u k)
    simp only [g66k2_L0] at h
    convert h using 1
    · funext e; exact hfun e
    · ring

theorem g66k2_slowFlow (c n omega : ℝ) (u k : V3)
    (hc : 0 < c) (hn : 1 ≤ n) (hk : k ≠ 0) :
    FirstJetEq (fun eps => rayHamiltonian c n (eps • u) k)
      (fun eps => c * length3 k / n + eps * (1 - 1 / n ^ 2) * dot3 u k) ∧
    FirstJetEq (fun eps => rayVelocity c n (eps • u) k)
      (fun eps => (c / n) • ((1 / length3 k) • k) +
        (eps * (1 - 1 / n ^ 2)) • u) ∧
    FirstJetEq (fun eps => -rayDispersion c n (eps • u) k omega / c ^ 2)
      (fun eps => dot3 k k - n ^ 2 * omega ^ 2 / c ^ 2 +
        2 * omega * (n ^ 2 - 1) * eps * dot3 u k / c ^ 2) := by
  obtain ⟨h1, h1'⟩ := g66k2_H_jet c n u k hc hn hk
  obtain ⟨h2, h2'⟩ := g66k2_V_jet c n u k hc hn hk
  obtain ⟨h3, h3'⟩ := g66k2_D_jet c n omega u k hc
  refine ⟨⟨by simpa using h1, _, h1', ?_⟩, ⟨by simpa using h2, _, h2', ?_⟩, ⟨by simpa using h3, _, h3', ?_⟩⟩
  · have := (((hasDerivAt_id (0:ℝ)).mul_const (1 - 1 / n ^ 2)).mul_const (dot3 u k)).const_add
      (c * length3 k / n)
    simpa using this
  · have := (((hasDerivAt_id (0:ℝ)).mul_const (1 - 1 / n ^ 2)).smul_const u).const_add
      ((c / n) • ((1 / length3 k) • k))
    simpa using this
  · have := ((((hasDerivAt_id (0:ℝ)).const_mul (2 * omega * (n ^ 2 - 1))).mul_const (dot3 u k)).div_const
      (c ^ 2)).const_add (dot3 k k - n ^ 2 * omega ^ 2 / c ^ 2)
    exact this.congr_deriv (by ring)

theorem solution (c n omega : ℝ) (u k : V3)
    (hc : 0 < c) (hn : 1 ≤ n) (hk : k ≠ 0) :
    FirstJetEq (fun eps => rayHamiltonian c n (eps • u) k)
      (fun eps => c * length3 k / n + eps * (1 - 1 / n ^ 2) * dot3 u k) ∧
    FirstJetEq (fun eps => rayVelocity c n (eps • u) k)
      (fun eps => (c / n) • ((1 / length3 k) • k) +
        (eps * (1 - 1 / n ^ 2)) • u) ∧
    FirstJetEq (fun eps => -rayDispersion c n (eps • u) k omega / c ^ 2)
      (fun eps => dot3 k k - n ^ 2 * omega ^ 2 / c ^ 2 +
        2 * omega * (n ^ 2 - 1) * eps * dot3 u k / c ^ 2) :=
  g66k2_slowFlow c n omega u k hc hn hk
