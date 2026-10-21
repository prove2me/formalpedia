-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P42.slowMetric_firstJet
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T05:50:17.167093+00:00
-- url     : https://prove2.me/submissions/364b600f-d4a8-4437-aed3-fa0641c41838

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

def g66k2_dF (c : ℝ) (u : V3) : V4 := ![0, u 0 / c, u 1 / c, u 2 / c]
def g66k2_F0 : V4 := ![1, 0, 0, 0]

theorem g66k2_F_jet (c : ℝ) (u : V3) (i : Fin 4) :
    fourFlow c ((0:ℝ) • u) i = g66k2_F0 i ∧
    HasDerivAt (fun e : ℝ => fourFlow c (e • u) i) (g66k2_dF c u i) 0 := by
  have hL := g66k2_L_diff c (dot3 u u)
  have h0 := g66k2_even _ hL
  have hsp : ∀ m : Fin 3, HasDerivAt (fun e : ℝ => g66k2_L c (dot3 u u) (e ^ 2) * (e * u m) / c)
      (u m / c) 0 := by
    intro m
    have := (h0.mul ((hasDerivAt_id (0:ℝ)).mul_const (u m))).div_const c
    refine this.congr_deriv ?_
    simp [g66k2_L0]
  fin_cases i
  · refine ⟨by simp [fourFlow, g66k2_F0, lorentzFactor, dot3], ?_⟩
    simp only [fourFlow, g66k2_L_eq, g66k2_dF]
    simpa using h0
  · refine ⟨by simp [fourFlow, g66k2_F0], ?_⟩
    simp only [fourFlow, g66k2_L_eq, g66k2_dF, Pi.smul_apply, smul_eq_mul]
    simpa using hsp 0
  · refine ⟨by simp [fourFlow, g66k2_F0], ?_⟩
    simp only [fourFlow, g66k2_L_eq, g66k2_dF, Pi.smul_apply, smul_eq_mul]
    simpa using hsp 1
  · refine ⟨by simp [fourFlow, g66k2_F0], ?_⟩
    simp only [fourFlow, g66k2_L_eq, g66k2_dF, Pi.smul_apply, smul_eq_mul]
    simpa using hsp 2

theorem g66k2_eta (v : V4) (i : Fin 4) :
    apply4 minkowskiMetric v i = (if i = 0 then 1 else -1) * v i := by
  fin_cases i <;> simp [apply4, minkowskiMetric, Fin.sum_univ_four]

theorem g66k2_slowUp_aff (c n e : ℝ) (u : V3) (i j : Fin 4) :
    slowUp c n (e • u) i j = slowUp c n 0 i j + e * (slowUp c n u i j - slowUp c n 0 i j) := by
  fin_cases i <;> fin_cases j <;> simp [slowUp] <;> ring

theorem g66k2_slowDown_aff (c n e : ℝ) (u : V3) (i j : Fin 4) :
    slowDown c n (e • u) i j = slowDown c n 0 i j + e * (slowDown c n u i j - slowDown c n 0 i j) := by
  fin_cases i <;> fin_cases j <;> simp [slowDown] <;> ring

theorem g66k2_aff_jet (a b : ℝ) : HasDerivAt (fun e : ℝ => a + e * b) b 0 := by
  simpa using ((hasDerivAt_id (0:ℝ)).mul_const b).const_add a

theorem g66k2_up_entry (c n : ℝ) (u : V3) (hc : 0 < c) (i j : Fin 4) :
    FirstJetEq (fun eps => gUp c n (eps • u) i j) (fun eps => slowUp c n (eps • u) i j) := by
  obtain ⟨hi0, hi⟩ := g66k2_F_jet c u i
  obtain ⟨hj0, hj⟩ := g66k2_F_jet c u j
  have hd := ((hi.mul hj).const_mul (n ^ 2 - 1)).const_add (minkowskiMetric i j)
  have hfun : (fun eps : ℝ => gUp c n (eps • u) i j) = fun eps =>
      minkowskiMetric i j + (n ^ 2 - 1) * (fourFlow c (eps • u) i * fourFlow c (eps • u) j) := by
    funext eps; simp only [gUp]; ring
  rw [hfun]
  refine ⟨?_, _, hd, ?_⟩
  · simp only; rw [hi0, hj0, zero_smul]
    fin_cases i <;> fin_cases j <;> simp [g66k2_F0, slowUp, minkowskiMetric]
  · have h2 := g66k2_aff_jet (slowUp c n 0 i j) (slowUp c n u i j - slowUp c n 0 i j)
    simp only [← g66k2_slowUp_aff] at h2
    refine h2.congr_deriv ?_
    rw [hi0, hj0]
    fin_cases i <;> fin_cases j <;> simp [g66k2_F0, g66k2_dF, slowUp, minkowskiMetric] <;> field_simp <;> ring

theorem g66k2_down_entry (c n : ℝ) (u : V3) (hc : 0 < c) (hn : 1 ≤ n) (i j : Fin 4) :
    FirstJetEq (fun eps => gDown c n (eps • u) i j) (fun eps => slowDown c n (eps • u) i j) := by
  have hn0 : 0 < n := by linarith
  obtain ⟨hi0, hi⟩ := g66k2_F_jet c u i
  obtain ⟨hj0, hj⟩ := g66k2_F_jet c u j
  have hd := (((hi.const_mul (if i = 0 then (1:ℝ) else -1)).mul
    (hj.const_mul (if j = 0 then (1:ℝ) else -1))).const_mul (1 / n ^ 2 - 1)).const_add (minkowskiMetric i j)
  have hfun : (fun eps : ℝ => gDown c n (eps • u) i j) = fun eps =>
      minkowskiMetric i j + (1 / n ^ 2 - 1) * ((if i = 0 then (1:ℝ) else -1) * fourFlow c (eps • u) i *
        ((if j = 0 then (1:ℝ) else -1) * fourFlow c (eps • u) j)) := by
    funext eps; simp only [gDown, g66k2_eta]; ring
  rw [hfun]
  refine ⟨?_, _, hd, ?_⟩
  · simp only; rw [hi0, hj0, zero_smul]
    fin_cases i <;> fin_cases j <;> simp [g66k2_F0, slowDown, minkowskiMetric] <;> field_simp <;> ring
  · have h2 := g66k2_aff_jet (slowDown c n 0 i j) (slowDown c n u i j - slowDown c n 0 i j)
    simp only [← g66k2_slowDown_aff] at h2
    refine h2.congr_deriv ?_
    rw [hi0, hj0]
    fin_cases i <;> fin_cases j <;> simp [g66k2_F0, g66k2_dF, slowDown, minkowskiMetric] <;> field_simp <;> ring

theorem g66k2_Kcomp (c n omega e : ℝ) (u k : V3) (j : Fin 3) :
    spatial (apply4 (gUp c n (e • u)) (waveCovector c omega k)) j =
      k j + (n ^ 2 - 1) * g66k2_L c (dot3 u u) (e ^ 2) ^ 2 * (omega - e * dot3 u k) * (e * u j) / c ^ 2 := by
  have := (g65g_K c n omega (e • u) k).2 j
  rw [this, g66k2_L_eq, g66k2_dsl]
  try simp

theorem g66k2_conj3 (c n omega : ℝ) (u k : V3) :
    FirstJetEq (fun eps => spatial (apply4 (gUp c n (eps • u)) (waveCovector c omega k)))
      (fun eps => k + ((n ^ 2 - 1) * omega / c ^ 2) • (eps • u)) := by
  have hL := g66k2_even _ (g66k2_L_diff c (dot3 u u))
  refine ⟨?_, ((n ^ 2 - 1) * omega / c ^ 2) • u, ?_, ?_⟩
  · funext j; beta_reduce; rw [g66k2_Kcomp]; simp
  · rw [hasDerivAt_pi]; intro j
    have hd := (((((hL.pow 2).const_mul (n ^ 2 - 1)).mul (((hasDerivAt_id (0:ℝ)).mul_const
      (dot3 u k)).const_sub omega)).mul ((hasDerivAt_id (0:ℝ)).mul_const (u j))).div_const (c ^ 2)).const_add (k j)
    have hfun : (fun e : ℝ => spatial (apply4 (gUp c n (e • u)) (waveCovector c omega k)) j) =
        fun e => k j + (n ^ 2 - 1) * g66k2_L c (dot3 u u) (e ^ 2) ^ 2 * (omega - e * dot3 u k) * (e * u j) / c ^ 2 := by
      funext e; exact g66k2_Kcomp c n omega e u k j
    rw [hfun]
    refine hd.congr_deriv ?_
    simp [g66k2_L0]; ring
  · rw [hasDerivAt_pi]; intro j
    have := (((hasDerivAt_id (0:ℝ)).mul_const (u j)).const_mul ((n ^ 2 - 1) * omega / c ^ 2)).const_add (k j)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine this.congr_deriv ?_
    simp

theorem g66k2_conj4 (c n : ℝ) (u k : V3) (hc : 0 < c) (hn : 1 ≤ n) (hk : k ≠ 0) :
    FirstJetEq (fun eps => spatial (apply4 (gUp c n (eps • u))
        (waveCovector c (rayHamiltonian c n (eps • u) k) k)))
      (fun eps => (n / c) • modifiedVelocity c n (eps • u) k) := by
  have hn0 : 0 < n := by linarith
  have hkk := g66k2_kk k hk
  have hlk : 0 < length3 k := Real.sqrt_pos.2 hkk
  obtain ⟨h1, h1'⟩ := g66k2_H_jet c n u k hc hn hk
  obtain ⟨h2, h2'⟩ := g66k2_V_jet c n u k hc hn hk
  have hL := g66k2_even _ (g66k2_L_diff c (dot3 u u))
  refine ⟨?_, (n / c) • (length3 k • ((1 - 1 / n ^ 2) • u)), ?_, ?_⟩
  · funext j
    beta_reduce
    rw [g66k2_Kcomp]
    simp only [modifiedVelocity]
    rw [h2]
    simp only [Pi.smul_apply, smul_eq_mul]
    simp
    field_simp
  · rw [hasDerivAt_pi]; intro j
    have hd := (((((hL.pow 2).const_mul (n ^ 2 - 1)).mul (h1'.sub ((hasDerivAt_id (0:ℝ)).mul_const
      (dot3 u k)))).mul ((hasDerivAt_id (0:ℝ)).mul_const (u j))).div_const (c ^ 2)).const_add (k j)
    have hfun : (fun e : ℝ => spatial (apply4 (gUp c n (e • u))
        (waveCovector c (rayHamiltonian c n (e • u) k) k)) j) =
        fun e => k j + (n ^ 2 - 1) * g66k2_L c (dot3 u u) (e ^ 2) ^ 2 *
          (rayHamiltonian c n (e • u) k - e * dot3 u k) * (e * u j) / c ^ 2 := by
      funext e; exact g66k2_Kcomp c n _ e u k j
    rw [hfun]
    refine hd.congr_deriv ?_
    have h1z : rayHamiltonian c n 0 k = c * length3 k / n := by simpa using h1
    simp [g66k2_L0, h1z]
    field_simp
  · exact (h2'.const_smul (length3 k)).const_smul (n / c)

theorem solution (c n omega : ℝ) (u k : V3)
    (hc : 0 < c) (hn : 1 ≤ n) (hk : k ≠ 0) :
    (∀ i j : Fin 4,
      FirstJetEq (fun eps => gDown c n (eps • u) i j)
        (fun eps => slowDown c n (eps • u) i j)) ∧
    (∀ i j : Fin 4,
      FirstJetEq (fun eps => gUp c n (eps • u) i j)
        (fun eps => slowUp c n (eps • u) i j)) ∧
    FirstJetEq (fun eps => spatial (apply4 (gUp c n (eps • u)) (waveCovector c omega k)))
      (fun eps => k + ((n ^ 2 - 1) * omega / c ^ 2) • (eps • u)) ∧
    FirstJetEq (fun eps => spatial (apply4 (gUp c n (eps • u))
        (waveCovector c (rayHamiltonian c n (eps • u) k) k)))
      (fun eps => (n / c) • modifiedVelocity c n (eps • u) k) := by
  exact ⟨fun i j => g66k2_down_entry c n u hc hn i j,
    fun i j => g66k2_up_entry c n u hc i j, g66k2_conj3 c n omega u k, g66k2_conj4 c n u k hc hn hk⟩
