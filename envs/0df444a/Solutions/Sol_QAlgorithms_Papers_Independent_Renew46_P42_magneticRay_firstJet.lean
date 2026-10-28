-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P42.magneticRay_firstJet
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T17:27:20.65559+00:00
-- url     : https://prove2.me/submissions/4ae76dca-c691-4d4f-8ee8-0911a1ec4e34

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P42
import Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P42_slowFlow_firstJet
namespace QAlgorithms.Papers.Independent.Renew46.P42

noncomputable section

open scoped BigOperators

open Filter Set MeasureTheory

-- Reuse the pinned accepted real quadratic form (arbitrary finite real matrices).

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

open scoped Topology

theorem p42s204_cp {d : ℕ} (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) (i : Fin d)
    (hf : DifferentiableAt ℝ f x) :
    cartesianPartial f x i = fderiv ℝ f x (Pi.single i 1) := by
  have hL : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin d) => WithLp.ofLp y)
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ) : EuclideanSpace ℝ (Fin d) →L[ℝ] (Fin d → ℝ))
      (WithLp.toLp 2 x) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).toContinuousLinearMap.hasFDerivAt
  have hf' : HasFDerivAt f (fderiv ℝ f x) (WithLp.ofLp (WithLp.toLp 2 x)) := hf.hasFDerivAt
  have hc := hf'.comp (WithLp.toLp 2 x) hL
  rw [cartesianPartial, QAlgorithms.Papers.Independent.Dependency50.P20.coordinatePartial]
  simp only
  rw [show (fun y : EuclideanSpace ℝ (Fin d) => f (WithLp.ofLp y)) = f ∘ WithLp.ofLp from rfl, hc.fderiv]
  simp [EuclideanSpace.single]
  congr 1

def p42s204_al (c n : ℝ) (u : V3) : ℝ := (n ^ 2 * c ^ 2 - c ^ 2) / (n ^ 2 * c ^ 2 - dot3 u u)
def p42s204_s (c n : ℝ) (u : V3) : ℝ :=
  Real.sqrt ((c ^ 2 - dot3 u u) / (n ^ 2 * c ^ 2 - dot3 u u))
def p42s204_A (c n : ℝ) (p : V3 × V3) : ℝ :=
  c ^ 2 * dot3 p.2 p.2 - p42s204_al c n p.1 * (dot3 p.1 p.2) ^ 2
def p42s204_S (c n : ℝ) : Set (V3 × V3) :=
  {p | dot3 p.1 p.1 < c ^ 2 ∧ 0 < p42s204_A c n p ∧ p.2 ≠ 0}
def p42s204_V (c n : ℝ) (p : V3 × V3) : V3 := fun j =>
  p42s204_s c n p.1 * ((c ^ 2 * p.2 j - p42s204_al c n p.1 * dot3 p.1 p.2 * p.1 j) /
    Real.sqrt (p42s204_A c n p)) + p42s204_al c n p.1 * p.1 j
def p42s204_W (c n : ℝ) (p : V3 × V3) : V3 := length3 p.2 • p42s204_V c n p

theorem p42s204_dot_cd : ContDiff ℝ 1 (fun p : V3 × V3 => dot3 p.1 p.1) := by
  unfold dot3; simp only [Fin.sum_univ_three]; fun_prop
theorem p42s204_dot12_cd : ContDiff ℝ 1 (fun p : V3 × V3 => dot3 p.1 p.2) := by
  unfold dot3; simp only [Fin.sum_univ_three]; fun_prop
theorem p42s204_dot22_cd : ContDiff ℝ 1 (fun p : V3 × V3 => dot3 p.2 p.2) := by
  unfold dot3; simp only [Fin.sum_univ_three]; fun_prop

theorem p42s204_kk (k : V3) (hk : k ≠ 0) : 0 < dot3 k k := by
  have h : ∃ i, k i ≠ 0 := by
    by_contra h; push Not at h; exact hk (funext h)
  obtain ⟨i, hi⟩ := h
  unfold dot3; simp only [Fin.sum_univ_three]
  have := sq_nonneg (k 0); have := sq_nonneg (k 1); have := sq_nonneg (k 2)
  fin_cases i <;> simp at hi <;> nlinarith [sq_pos_of_ne_zero hi]

theorem p42s204_den (c n : ℝ) (u : V3) (hc : 0 < c) (hn : 1 ≤ n) (hu : dot3 u u < c ^ 2) :
    0 < n ^ 2 * c ^ 2 - dot3 u u := by
  have hn2 : 1 ≤ n ^ 2 := by nlinarith
  have : c ^ 2 ≤ n ^ 2 * c ^ 2 := by nlinarith [mul_le_mul_of_nonneg_right hn2 (sq_nonneg c)]
  linarith

theorem p42s204_al_cd (c n : ℝ) (p : V3 × V3) (hc : 0 < c) (hn : 1 ≤ n)
    (hp : dot3 p.1 p.1 < c ^ 2) : ContDiffAt ℝ 1 (fun q : V3 × V3 => p42s204_al c n q.1) p := by
  unfold p42s204_al
  exact contDiffAt_const.div (contDiffAt_const.sub p42s204_dot_cd.contDiffAt)
    (p42s204_den c n p.1 hc hn hp).ne'

theorem p42s204_s_cd (c n : ℝ) (p : V3 × V3) (hc : 0 < c) (hn : 1 ≤ n)
    (hp : dot3 p.1 p.1 < c ^ 2) : ContDiffAt ℝ 1 (fun q : V3 × V3 => p42s204_s c n q.1) p := by
  unfold p42s204_s
  have hd := p42s204_den c n p.1 hc hn hp
  refine ContDiffAt.sqrt ((contDiffAt_const.sub p42s204_dot_cd.contDiffAt).div
    (contDiffAt_const.sub p42s204_dot_cd.contDiffAt) hd.ne') ?_
  exact (div_pos (by linarith) hd).ne'

theorem p42s204_A_cd (c n : ℝ) (p : V3 × V3) (hc : 0 < c) (hn : 1 ≤ n)
    (hp : dot3 p.1 p.1 < c ^ 2) : ContDiffAt ℝ 1 (p42s204_A c n) p := by
  have h := ((contDiffAt_const (c := c ^ 2)).mul p42s204_dot22_cd.contDiffAt).sub
    ((p42s204_al_cd c n p hc hn hp).mul (p42s204_dot12_cd.contDiffAt.pow 2))
  exact h

theorem p42s204_S_open (c n : ℝ) (hc : 0 < c) (hn : 1 ≤ n) : IsOpen (p42s204_S c n) := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  obtain ⟨h1, h2, h3⟩ := hp
  have e1 : ∀ᶠ q in 𝓝 p, dot3 q.1 q.1 < c ^ 2 :=
    p42s204_dot_cd.continuous.continuousAt.eventually (gt_mem_nhds h1)
  have e2 : ∀ᶠ q in 𝓝 p, 0 < p42s204_A c n q :=
    (p42s204_A_cd c n p hc hn h1).continuousAt.eventually (lt_mem_nhds h2)
  have e3 : ∀ᶠ q in 𝓝 p, q.2 ≠ 0 :=
    continuous_snd.continuousAt.eventually (isOpen_ne.mem_nhds h3)
  filter_upwards [e1, e2, e3] with q a b d using ⟨a, b, d⟩

theorem p42s204_V_cd (c n : ℝ) (p : V3 × V3) (hc : 0 < c) (hn : 1 ≤ n)
    (hp : p ∈ p42s204_S c n) : ContDiffAt ℝ 1 (p42s204_V c n) p := by
  obtain ⟨h1, h2, h3⟩ := hp
  unfold p42s204_V
  rw [contDiffAt_pi]
  intro j
  have hq1 : ContDiff ℝ 1 (fun q : V3 × V3 => q.1 j) := by fun_prop
  have hq2 : ContDiff ℝ 1 (fun q : V3 × V3 => q.2 j) := by fun_prop
  have hsA : ContDiffAt ℝ 1 (fun q : V3 × V3 => Real.sqrt (p42s204_A c n q)) p :=
    (p42s204_A_cd c n p hc hn h1).sqrt h2.ne'
  have hal := p42s204_al_cd c n p hc hn h1
  have hs := p42s204_s_cd c n p hc hn h1
  exact (hs.mul ((((contDiffAt_const (c := c ^ 2)).mul hq2.contDiffAt).sub
    ((hal.mul p42s204_dot12_cd.contDiffAt).mul hq1.contDiffAt)).div hsA
      (Real.sqrt_pos.2 h2).ne')).add (hal.mul hq1.contDiffAt)

theorem p42s204_W_cd (c n : ℝ) (p : V3 × V3) (hc : 0 < c) (hn : 1 ≤ n)
    (hp : p ∈ p42s204_S c n) : ContDiffAt ℝ 1 (p42s204_W c n) p := by
  have hl : ContDiffAt ℝ 1 (fun q : V3 × V3 => length3 q.2) p := by
    unfold length3
    exact p42s204_dot22_cd.contDiffAt.sqrt (p42s204_kk _ hp.2.2).ne'
  exact hl.smul (p42s204_V_cd c n p hc hn hp)

theorem p42s204_H_cd (c n : ℝ) (p : V3 × V3) (hc : 0 < c) (hn : 1 ≤ n)
    (hp : p ∈ p42s204_S c n) :
    ContDiffAt ℝ 1 (fun q : V3 × V3 => rayHamiltonian c n q.1 q.2) p := by
  obtain ⟨h1, h2, h3⟩ := hp
  have : (fun q : V3 × V3 => rayHamiltonian c n q.1 q.2) = fun q =>
      p42s204_s c n q.1 * Real.sqrt (p42s204_A c n q) + p42s204_al c n q.1 * dot3 q.1 q.2 := rfl
  rw [this]
  exact ((p42s204_s_cd c n p hc hn h1).mul ((p42s204_A_cd c n p hc hn h1).sqrt h2.ne')).add
    ((p42s204_al_cd c n p hc hn h1).mul p42s204_dot12_cd.contDiffAt)

theorem p42s204_dot_line (v k : V3) (j : Fin 3) (t : ℝ) :
    dot3 v (k + t • Pi.single j 1) = dot3 v k + t * v j := by
  fin_cases j <;> simp [dot3, Fin.sum_univ_three] <;> ring

theorem p42s204_dot_line2 (k : V3) (j : Fin 3) (t : ℝ) :
    dot3 (k + t • Pi.single j 1) (k + t • Pi.single j 1) = dot3 k k + 2 * t * k j + t ^ 2 := by
  fin_cases j <;> simp [dot3, Fin.sum_univ_three] <;> ring

theorem p42s204_grad (c n : ℝ) (u k : V3) (j : Fin 3)
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
  rw [p42s204_cp _ _ _ hdiff]
  have hline : HasDerivAt (fun t : ℝ => k + t • Pi.single j (1:ℝ)) (Pi.single j 1) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (Pi.single j (1:ℝ))).const_add k
  have h2' := (by simpa using hdiff.hasFDerivAt :
    HasFDerivAt (rayHamiltonian c n u) (fderiv ℝ (rayHamiltonian c n u) k)
      (k + (0:ℝ) • Pi.single j 1)).comp_hasDerivAt (0:ℝ) hline
  rw [← h2'.deriv]
  have hfun : (rayHamiltonian c n u ∘ fun t : ℝ => k + t • Pi.single j 1) =
      fun t => s * Real.sqrt (c ^ 2 * (dot3 k k + (2 * k j * t + t ^ 2)) - α * (dot3 u k + u j * t) ^ 2) +
        α * (dot3 u k + u j * t) := by
    funext t
    simp only [Function.comp]
    rw [rayHamiltonian, p42s204_dot_line2, p42s204_dot_line]
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

theorem p42s204_rv_eq (c n : ℝ) (p : V3 × V3) (hp : p ∈ p42s204_S c n) :
    rayVelocity c n p.1 p.2 = p42s204_V c n p := by
  funext j
  exact p42s204_grad c n p.1 p.2 j hp.2.1

theorem p42s204_Phi_cd (c n : ℝ) (hc : 0 < c) (hn : 1 ≤ n) :
    ContDiffOn ℝ 1 (fun p : V3 × V3 => modifiedVelocity c n p.1 p.2) (p42s204_S c n) := by
  intro p hp
  have : ContDiffOn ℝ 1 (p42s204_W c n) (p42s204_S c n) :=
    fun q hq => (p42s204_W_cd c n q hc hn hq).contDiffWithinAt
  refine (this p hp).congr (fun q hq => ?_) ?_
  · simp only [modifiedVelocity, p42s204_W, p42s204_rv_eq c n q hq]
  · simp only [modifiedVelocity, p42s204_W, p42s204_rv_eq c n p hp]

theorem p42s204_Psi_cd (c n : ℝ) (hc : 0 < c) (hn : 1 ≤ n) :
    ContDiffOn ℝ 1 (fun p : V3 × V3 => rayHamiltonian c n p.1 p.2) (p42s204_S c n) :=
  fun q hq => (p42s204_H_cd c n q hc hn hq).contDiffWithinAt

theorem p42s204_mem0 (c n : ℝ) (k : V3) (hc : 0 < c) (hk : k ≠ 0) :
    ((0 : V3), k) ∈ p42s204_S c n := by
  refine ⟨?_, ?_, hk⟩
  · simp [dot3]; positivity
  · have := p42s204_kk k hk
    simp only [p42s204_A]
    have h0 : dot3 (0 : V3) k = 0 := by simp [dot3]
    rw [h0]; simp; positivity

theorem p42s204_evS (c n : ℝ) (w k : V3) (hc : 0 < c) (hn : 1 ≤ n) (hk : k ≠ 0) :
    ∀ᶠ e in 𝓝 (0 : ℝ), (e • w, k) ∈ p42s204_S c n := by
  have hcont : Continuous (fun e : ℝ => (e • w, k)) := by fun_prop
  have h := hcont.continuousAt (x := 0) |>.eventually
    ((p42s204_S_open c n hc hn).mem_nhds (by simpa using p42s204_mem0 c n k hc hk))
  exact h

theorem p42s204_slope {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ → E)
    (hR : ContinuousAt R 0) : HasDerivAt (fun e => e • R e) (R 0) 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have h1 : Tendsto R (𝓝[≠] 0) (𝓝 (R 0)) := hR.tendsto.mono_left nhdsWithin_le_nhds
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [zero_add, zero_smul, sub_zero, smul_smul]
  rw [inv_mul_cancel₀ ht, one_smul]

theorem p42s204_DPsi_u (c n : ℝ) (a k : V3) (hc : 0 < c) (hn : 1 ≤ n) (hk : k ≠ 0) :
    fderiv ℝ (fun p : V3 × V3 => rayHamiltonian c n p.1 p.2) ((0 : V3), k) (a, 0) =
      (1 - 1 / n ^ 2) * dot3 a k := by
  have hd : DifferentiableAt ℝ (fun p : V3 × V3 => rayHamiltonian c n p.1 p.2) ((0 : V3), k) :=
    (p42s204_H_cd c n _ hc hn (p42s204_mem0 c n k hc hk)).differentiableAt (by norm_num)
  have hline : HasDerivAt (fun t : ℝ => (t • a, k)) (a, (0 : V3)) 0 := by
    have := ((hasDerivAt_id (0:ℝ)).smul_const a).prodMk (hasDerivAt_const (0:ℝ) k)
    simpa using this
  have hD : HasFDerivAt (fun p : V3 × V3 => rayHamiltonian c n p.1 p.2)
      (fderiv ℝ (fun p : V3 × V3 => rayHamiltonian c n p.1 p.2) ((0 : V3), k))
      ((0 : ℝ) • a, k) := by simpa using hd.hasFDerivAt
  have hc1 := hD.comp_hasDerivAt (0 : ℝ) hline
  obtain ⟨_, a', hf, hg⟩ := (slowFlow_firstJet c n 0 a k hc hn hk).1
  have hg' : HasDerivAt (fun eps : ℝ => c * length3 k / n + eps * (1 - 1 / n ^ 2) * dot3 a k)
      ((1 - 1 / n ^ 2) * dot3 a k) 0 := by
    have := (((hasDerivAt_id (0:ℝ)).mul_const (1 - 1 / n ^ 2)).mul_const (dot3 a k)).const_add
      (c * length3 k / n)
    simpa using this
  rw [hg.unique hg'] at hf
  exact hc1.unique hf

theorem p42s204_DPhi_u (c n : ℝ) (a k : V3) (hc : 0 < c) (hn : 1 ≤ n) (hk : k ≠ 0) :
    fderiv ℝ (fun p : V3 × V3 => modifiedVelocity c n p.1 p.2) ((0 : V3), k) (a, 0) =
      length3 k • ((1 - 1 / n ^ 2) • a) := by
  have hd : DifferentiableAt ℝ (fun p : V3 × V3 => modifiedVelocity c n p.1 p.2) ((0 : V3), k) :=
    ((p42s204_Phi_cd c n hc hn).contDiffAt ((p42s204_S_open c n hc hn).mem_nhds
      (p42s204_mem0 c n k hc hk))).differentiableAt (by norm_num)
  have hline : HasDerivAt (fun t : ℝ => (t • a, k)) (a, (0 : V3)) 0 := by
    have := ((hasDerivAt_id (0:ℝ)).smul_const a).prodMk (hasDerivAt_const (0:ℝ) k)
    simpa using this
  have hD : HasFDerivAt (fun p : V3 × V3 => modifiedVelocity c n p.1 p.2)
      (fderiv ℝ (fun p : V3 × V3 => modifiedVelocity c n p.1 p.2) ((0 : V3), k))
      ((0 : ℝ) • a, k) := by simpa using hd.hasFDerivAt
  have hc1 := hD.comp_hasDerivAt (0 : ℝ) hline
  obtain ⟨_, a', hf, hg⟩ := (slowFlow_firstJet c n 0 a k hc hn hk).2.1
  have hg' : HasDerivAt (fun eps : ℝ => (c / n) • ((1 / length3 k) • k) +
        (eps * (1 - 1 / n ^ 2)) • a) ((1 - 1 / n ^ 2) • a) 0 := by
    have := (((hasDerivAt_id (0:ℝ)).mul_const (1 - 1 / n ^ 2)).smul_const a).const_add
      ((c / n) • ((1 / length3 k) • k))
    simpa using this
  rw [hg.unique hg'] at hf
  exact hc1.unique (hf.const_smul (length3 k))

theorem p42s204_Phi0 (c n : ℝ) (k : V3) (hc : 0 < c) (hn : 1 ≤ n) (hk : k ≠ 0) :
    modifiedVelocity c n 0 k = (c / n) • k := by
  have h := (slowFlow_firstJet c n 0 0 k hc hn hk).2.1.1
  simp only [zero_smul, zero_mul, add_zero] at h
  rw [modifiedVelocity, h, smul_smul, smul_smul]
  have hl : length3 k ≠ 0 := (Real.sqrt_pos.2 (p42s204_kk k hk)).ne'
  congr 1
  field_simp

theorem p42s204_DPhi_k (c n : ℝ) (b k : V3) (hc : 0 < c) (hn : 1 ≤ n) (hk : k ≠ 0) :
    fderiv ℝ (fun p : V3 × V3 => modifiedVelocity c n p.1 p.2) ((0 : V3), k) (0, b) =
      (c / n) • b := by
  have hd : DifferentiableAt ℝ (fun p : V3 × V3 => modifiedVelocity c n p.1 p.2) ((0 : V3), k) :=
    ((p42s204_Phi_cd c n hc hn).contDiffAt ((p42s204_S_open c n hc hn).mem_nhds
      (p42s204_mem0 c n k hc hk))).differentiableAt (by norm_num)
  have hline : HasDerivAt (fun t : ℝ => ((0 : V3), k + t • b)) ((0 : V3), b) 0 := by
    have := (hasDerivAt_const (0:ℝ) (0 : V3)).prodMk (((hasDerivAt_id (0:ℝ)).smul_const b).const_add k)
    simpa using this
  have hD : HasFDerivAt (fun p : V3 × V3 => modifiedVelocity c n p.1 p.2)
      (fderiv ℝ (fun p : V3 × V3 => modifiedVelocity c n p.1 p.2) ((0 : V3), k))
      ((0 : V3), k + (0 : ℝ) • b) := by simpa using hd.hasFDerivAt
  have hc1 := hD.comp_hasDerivAt (0 : ℝ) hline
  have hg : HasDerivAt (fun t : ℝ => (c / n) • (k + t • b)) ((c / n) • b) 0 := by
    have := (((hasDerivAt_id (0:ℝ)).smul_const b).const_add k).const_smul (c / n)
    convert this using 1 <;> first | rfl | simp
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), k + t • b ≠ 0 := by
    have hcont : Continuous (fun t : ℝ => k + t • b) := by fun_prop
    exact hcont.continuousAt (x := 0) |>.eventually (isOpen_ne.mem_nhds (by simpa using hk))
  have hg2 : HasDerivAt ((fun p : V3 × V3 => modifiedVelocity c n p.1 p.2) ∘
      fun t : ℝ => ((0 : V3), k + t • b)) ((c / n) • b) 0 := by
    refine hg.congr_of_eventuallyEq ?_
    filter_upwards [hev] with t ht
    simp only [Function.comp]
    exact p42s204_Phi0 c n _ hc hn ht
  exact hc1.unique hg2

theorem p42s204_rv_D (c n : ℝ) (p : V3 × V3) (hc : 0 < c) (hn : 1 ≤ n)
    (hp : p ∈ p42s204_S c n) (j : Fin 3) :
    rayVelocity c n p.1 p.2 j =
      fderiv ℝ (fun q : V3 × V3 => rayHamiltonian c n q.1 q.2) p (0, Pi.single j 1) := by
  have hd := ((p42s204_H_cd c n p hc hn hp).differentiableAt (by norm_num)).hasFDerivAt
  have hc1 := hd.comp (x := p.2) (g := fun q : V3 × V3 => rayHamiltonian c n q.1 q.2) (hasFDerivAt_prodMk_right (𝕜 := ℝ) p.1 p.2)
  have hdiff : DifferentiableAt ℝ (rayHamiltonian c n p.1) p.2 := hc1.differentiableAt
  rw [rayVelocity, gradient, p42s204_cp _ _ _ hdiff]
  have : fderiv ℝ (rayHamiltonian c n p.1) p.2 = _ := hc1.fderiv
  rw [this]
  rfl

theorem p42s204_along {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c n eps : ℝ) (u : V3 → V3) (x k : V3) (Du : V3 →L[ℝ] V3) (hu : HasFDerivAt u Du x)
    (Θ : V3 × V3 → E) (hΘ : DifferentiableAt ℝ Θ (eps • u x, k)) :
    alongField c n eps u (fun z => Θ (eps • u z.1, z.2)) (x, k) =
      fderiv ℝ Θ (eps • u x, k) (eps • Du (rayVelocity c n (eps • u x) k),
        -gradient (fun x' => rayHamiltonian c n (eps • u x') k) x) := by
  have hι : HasFDerivAt (fun z : V3 × V3 => (eps • u z.1, z.2))
      (((eps • Du).comp (ContinuousLinearMap.fst ℝ V3 V3)).prod (ContinuousLinearMap.snd ℝ V3 V3))
      (x, k) := by
    have h1 := (hu.comp (x, k) (hasFDerivAt_fst (𝕜 := ℝ) (p := (x, k)))).const_smul eps
    exact h1.prodMk hasFDerivAt_snd
  have hc := hΘ.hasFDerivAt.comp (x, k) hι
  unfold alongField
  rw [show (fun z : V3 × V3 => Θ (eps • u z.1, z.2)) = Θ ∘ (fun z : V3 × V3 => (eps • u z.1, z.2))
    from rfl, hc.fderiv]
  simp [stationaryField]

theorem p42s204_gradF (c n eps : ℝ) (u : V3 → V3) (x k : V3) (Du : V3 →L[ℝ] V3)
    (hu : HasFDerivAt u Du x) (hc : 0 < c) (hn : 1 ≤ n) (hp : (eps • u x, k) ∈ p42s204_S c n) :
    -gradient (fun x' => rayHamiltonian c n (eps • u x') k) x =
      eps • (fun j => -fderiv ℝ (fun q : V3 × V3 => rayHamiltonian c n q.1 q.2) (eps • u x, k)
        (Du (Pi.single j 1), 0)) := by
  have hd := ((p42s204_H_cd c n _ hc hn hp).differentiableAt (by norm_num)).hasFDerivAt
  have hi : HasFDerivAt (fun x' : V3 => (eps • u x', k))
      ((eps • Du).prod (0 : V3 →L[ℝ] V3)) x := (hu.const_smul eps).prodMk (hasFDerivAt_const k x)
  have hc1 := hd.comp x hi
  funext j
  simp only [Pi.neg_apply, Pi.smul_apply, gradient]
  have hdf : DifferentiableAt ℝ (fun x' : V3 => rayHamiltonian c n (eps • u x') k) x :=
    hc1.differentiableAt
  rw [p42s204_cp _ _ _ hdf]
  rw [show (fun x' : V3 => rayHamiltonian c n (eps • u x') k) =
    (fun q : V3 × V3 => rayHamiltonian c n q.1 q.2) ∘ (fun x' : V3 => (eps • u x', k)) from rfl,
    hc1.fderiv]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.zero_apply, smul_eq_mul]
  rw [show ((eps • Du (Pi.single j 1)), (0 : V3)) = eps • (Du (Pi.single j 1), (0 : V3)) by simp,
    map_smul, smul_eq_mul]
  ring

/-- core remainder -/
def p42s204_R (c n : ℝ) (u : V3 → V3) (x k : V3) (Du : V3 →L[ℝ] V3) (eps : ℝ) : V3 :=
  fderiv ℝ (fun p : V3 × V3 => modifiedVelocity c n p.1 p.2) (eps • u x, k)
    (Du (rayVelocity c n (eps • u x) k),
      fun j => -fderiv ℝ (fun q : V3 × V3 => rayHamiltonian c n q.1 q.2) (eps • u x, k)
        (Du (Pi.single j 1), 0))

theorem p42s204_Wcore (c n eps : ℝ) (u : V3 → V3) (x k : V3) (Du : V3 →L[ℝ] V3)
    (hu : HasFDerivAt u Du x) (hc : 0 < c) (hn : 1 ≤ n) (hp : (eps • u x, k) ∈ p42s204_S c n) :
    fderiv ℝ (fun p : V3 × V3 => modifiedVelocity c n p.1 p.2) (eps • u x, k)
      (eps • Du (rayVelocity c n (eps • u x) k),
        -gradient (fun x' => rayHamiltonian c n (eps • u x') k) x) =
      eps • p42s204_R c n u x k Du eps := by
  rw [p42s204_gradF c n eps u x k Du hu hc hn hp, ← Prod.smul_mk, map_smul]
  rfl

theorem p42s204_R_cont (c n : ℝ) (u : V3 → V3) (x k : V3) (Du : V3 →L[ℝ] V3)
    (hc : 0 < c) (hn : 1 ≤ n) (hk : k ≠ 0) :
    ContinuousAt (p42s204_R c n u x k Du) 0 := by
  have hS := (p42s204_S_open c n hc hn).mem_nhds (p42s204_mem0 c n k hc hk)
  have hp : ContinuousAt (fun e : ℝ => (e • u x, k)) 0 := by fun_prop
  have hp0 : (fun e : ℝ => (e • u x, k)) 0 = ((0 : V3), k) := by simp
  have hΦ : ContinuousAt (fun e : ℝ =>
      fderiv ℝ (fun p : V3 × V3 => modifiedVelocity c n p.1 p.2) (e • u x, k)) 0 :=
    ContinuousAt.comp_of_eq (((p42s204_Phi_cd c n hc hn).continuousOn_fderiv_of_isOpen
      (p42s204_S_open c n hc hn) le_rfl).continuousAt hS) hp hp0
  have hΨ : ContinuousAt (fun e : ℝ =>
      fderiv ℝ (fun p : V3 × V3 => rayHamiltonian c n p.1 p.2) (e • u x, k)) 0 :=
    ContinuousAt.comp_of_eq (((p42s204_Psi_cd c n hc hn).continuousOn_fderiv_of_isOpen
      (p42s204_S_open c n hc hn) le_rfl).continuousAt hS) hp hp0
  obtain ⟨_, a', hf, _⟩ := (slowFlow_firstJet c n 0 (u x) k hc hn hk).2.1
  have hV := hf.continuousAt
  have hG : ContinuousAt (fun e : ℝ => fun j : Fin 3 =>
      -fderiv ℝ (fun q : V3 × V3 => rayHamiltonian c n q.1 q.2) (e • u x, k)
        (Du (Pi.single j 1), (0 : V3))) 0 := by
    rw [continuousAt_pi]
    intro j
    exact (hΨ.clm_apply continuousAt_const).neg
  exact hΦ.clm_apply ((Du.continuous.continuousAt.comp hV).prodMk hG)

theorem p42s204_curl (u : V3 → V3) (x : V3) (Du : V3 →L[ℝ] V3) (hu : HasFDerivAt u Du x)
    (a b : Fin 3) : cartesianPartial (fun y => u y a) x b = Du (Pi.single b 1) a := by
  have h := hasFDerivAt_pi'.1 hu a
  rw [p42s204_cp _ _ _ h.differentiableAt, h.fderiv]
  rfl

theorem p42s204_R0 (c n : ℝ) (u : V3 → V3) (x k : V3) (Du : V3 →L[ℝ] V3)
    (hu : HasFDerivAt u Du x) (hc : 0 < c) (hn : 1 ≤ n) (hk : k ≠ 0) :
    p42s204_R c n u x k Du 0 = (1 - 1 / n ^ 2) • cross3 (curl3 u x) ((c / n) • k) := by
  have hV0 := (slowFlow_firstJet c n 0 (u x) k hc hn hk).2.1.1
  simp only [zero_smul, zero_mul, add_zero] at hV0
  unfold p42s204_R
  simp only [zero_smul]
  rw [hV0]
  rw [show (Du ((c / n) • (1 / length3 k) • k), fun j : Fin 3 =>
      -fderiv ℝ (fun q : V3 × V3 => rayHamiltonian c n q.1 q.2) ((0 : V3), k)
        (Du (Pi.single j 1), (0 : V3))) =
      (Du ((c / n) • (1 / length3 k) • k), (0 : V3)) + ((0 : V3), fun j : Fin 3 =>
      -fderiv ℝ (fun q : V3 × V3 => rayHamiltonian c n q.1 q.2) ((0 : V3), k)
        (Du (Pi.single j 1), (0 : V3))) by simp, map_add,
    p42s204_DPhi_u c n _ k hc hn hk, p42s204_DPhi_k c n _ k hc hn hk]
  simp only [p42s204_DPsi_u c n _ k hc hn hk]
  have hl : length3 k ≠ 0 := (Real.sqrt_pos.2 (p42s204_kk k hk)).ne'
  have hk3 : k = k 0 • Pi.single 0 1 + k 1 • Pi.single 1 1 + k 2 • Pi.single 2 1 := by
    funext i; fin_cases i <;> simp
  have hDk : Du k = k 0 • Du (Pi.single 0 1) + k 1 • Du (Pi.single 1 1) +
      k 2 • Du (Pi.single 2 1) := by
    conv_lhs => rw [hk3]
    simp only [map_add, map_smul]
  simp only [map_smul, hDk]
  have hc0 : curl3 u x = ![Du (Pi.single 1 1) 2 - Du (Pi.single 2 1) 1,
      Du (Pi.single 2 1) 0 - Du (Pi.single 0 1) 2, Du (Pi.single 0 1) 1 - Du (Pi.single 1 1) 0] := by
    simp only [curl3, p42s204_curl u x Du hu]
  rw [hc0]
  funext i
  fin_cases i <;> simp [cross3, dot3, Fin.sum_univ_three] <;> field_simp <;> ring

theorem p42s204_Phi_diff (c n : ℝ) (p : V3 × V3) (hc : 0 < c) (hn : 1 ≤ n)
    (hp : p ∈ p42s204_S c n) :
    DifferentiableAt ℝ (fun p : V3 × V3 => modifiedVelocity c n p.1 p.2) p :=
  ((p42s204_Phi_cd c n hc hn).contDiffAt ((p42s204_S_open c n hc hn).mem_nhds hp)).differentiableAt
    (by norm_num)

theorem p42s204_lin (ℓ : V3 →L[ℝ] ℝ) (v : V3) :
    ℓ v = v 0 * ℓ (Pi.single 0 1) + v 1 * ℓ (Pi.single 1 1) + v 2 * ℓ (Pi.single 2 1) := by
  have hv : v = v 0 • Pi.single 0 1 + v 1 • Pi.single 1 1 + v 2 • Pi.single 2 1 := by
    funext i; fin_cases i <;> simp
  conv_lhs => rw [hv]
  simp only [map_add, map_smul, smul_eq_mul]

theorem p42s204_Hzero (c n eps : ℝ) (u : V3 → V3) (x k : V3) (Du : V3 →L[ℝ] V3)
    (hu : HasFDerivAt u Du x) (hc : 0 < c) (hn : 1 ≤ n) (hp : (eps • u x, k) ∈ p42s204_S c n) :
    fderiv ℝ (fun q : V3 × V3 => rayHamiltonian c n q.1 q.2) (eps • u x, k)
      (eps • Du (rayVelocity c n (eps • u x) k),
        -gradient (fun x' => rayHamiltonian c n (eps • u x') k) x) = 0 := by
  rw [p42s204_gradF c n eps u x k Du hu hc hn hp, ← Prod.smul_mk, map_smul, smul_eq_mul]
  set T := fderiv ℝ (fun q : V3 × V3 => rayHamiltonian c n q.1 q.2) (eps • u x, k) with hT
  have hsplit : ∀ a b : V3, T (a, b) = (T.comp (ContinuousLinearMap.inl ℝ V3 V3)) a +
      (T.comp (ContinuousLinearMap.inr ℝ V3 V3)) b := by
    intro a b
    rw [show (a, b) = ((a, 0) : V3 × V3) + (0, b) by simp, map_add]; rfl
  have hV : ∀ j, rayVelocity c n (eps • u x) k j = (T.comp (ContinuousLinearMap.inr ℝ V3 V3))
      (Pi.single j 1) := fun j => p42s204_rv_D c n _ hc hn hp j
  have hG : ∀ j, T (Du (Pi.single j 1), 0) =
      ((T.comp (ContinuousLinearMap.inl ℝ V3 V3)).comp Du) (Pi.single j 1) := fun j => rfl
  rw [hsplit]
  rw [show (T.comp (ContinuousLinearMap.inl ℝ V3 V3)) (Du (rayVelocity c n (eps • u x) k)) =
    ((T.comp (ContinuousLinearMap.inl ℝ V3 V3)).comp Du) (rayVelocity c n (eps • u x) k) from rfl]
  rw [p42s204_lin ((T.comp (ContinuousLinearMap.inl ℝ V3 V3)).comp Du),
    p42s204_lin (T.comp (ContinuousLinearMap.inr ℝ V3 V3))]
  simp only [hV, hG]
  ring

theorem p42s204_cross_smul (e : ℝ) (a v : V3) : cross3 (e • a) v = e • cross3 a v := by
  funext i; fin_cases i <;> simp [cross3] <;> ring

theorem p42s204_dot_cont (f g : ℝ → V3) (hf : ContinuousAt f 0) (hg : ContinuousAt g 0) :
    ContinuousAt (fun e => dot3 (f e) (g e)) 0 := by
  unfold dot3; simp only [Fin.sum_univ_three]
  exact (((continuousAt_pi.1 hf 0).mul (continuousAt_pi.1 hg 0)).add
    ((continuousAt_pi.1 hf 1).mul (continuousAt_pi.1 hg 1))).add
    ((continuousAt_pi.1 hf 2).mul (continuousAt_pi.1 hg 2))

theorem p42s204_dot_hasDeriv (f : ℝ → V3) (f' : V3) (t : ℝ) (hf : HasDerivAt f f' t) :
    HasDerivAt (fun s => dot3 (f s) (f s)) (2 * dot3 (f t) f') t := by
  have h : ∀ i : Fin 3, HasDerivAt (fun s => f s i) (f' i) t := fun i =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).hasFDerivAt.comp_hasDerivAt t hf
  unfold dot3; simp only [Fin.sum_univ_three]
  have := (((h 0).mul (h 0)).add ((h 1).mul (h 1))).add ((h 2).mul (h 2))
  refine this.congr_deriv ?_
  ring

theorem p42s204_dot_fderiv (Φ : V3 × V3 → V3) (Φ' : V3 × V3 →L[ℝ] V3) (p v : V3 × V3)
    (hΦ : HasFDerivAt Φ Φ' p) :
    DifferentiableAt ℝ (fun q => dot3 (Φ q) (Φ q)) p ∧
    fderiv ℝ (fun q => dot3 (Φ q) (Φ q)) p v = 2 * dot3 (Φ p) (Φ' v) := by
  have h := fun i => hasFDerivAt_pi'.1 hΦ i
  have hs : HasFDerivAt (fun q => Φ q 0 * Φ q 0 + Φ q 1 * Φ q 1 + Φ q 2 * Φ q 2) _ p :=
    (((h 0).mul (h 0)).add ((h 1).mul (h 1))).add ((h 2).mul (h 2))
  have he : (fun q => dot3 (Φ q) (Φ q)) =
      fun q => Φ q 0 * Φ q 0 + Φ q 1 * Φ q 1 + Φ q 2 * Φ q 2 := by
    funext q; simp [dot3, Fin.sum_univ_three]
  rw [he]
  refine ⟨hs.differentiableAt, ?_⟩
  rw [hs.fderiv]
  simp [dot3, Fin.sum_univ_three]; ring

theorem p42s204_main (c n : ℝ) (u : V3 → V3) (x k : V3) (O : Set V3)
    (hc : 0 < c) (hn : 1 ≤ n) (hk : k ≠ 0)
    (hO : IsOpen O) (hx : x ∈ O) (hreg : ContDiffOn ℝ 2 u O) :
    FirstJetEq (fun eps => modifiedVelocity c n (eps • u x) k)
      (fun eps => (c / n) • (k +
        ((n ^ 2 - 1) * rayHamiltonian c n (eps • u x) k / c ^ 2) • (eps • u x))) ∧
    FirstJetEq (fun eps => alongField c n eps u
        (fun z => modifiedVelocity c n (eps • u z.1) z.2) (x, k))
      (fun eps => (1 - 1 / n ^ 2) •
        cross3 (eps • curl3 u x) (modifiedVelocity c n (eps • u x) k)) ∧
    FirstJetEq (fun eps => alongField c n eps u
        (fun z => dot3 (modifiedVelocity c n (eps • u z.1) z.2)
          (modifiedVelocity c n (eps • u z.1) z.2)) (x, k)) (fun _ => (0 : ℝ)) ∧
    FirstJetEq (fun eps => alongField c n eps u
        (fun z => rayHamiltonian c n (eps • u z.1) z.2) (x, k)) (fun _ => (0 : ℝ)) ∧
    FirstJetEq (fun eps => dot3 (modifiedVelocity c n (eps • u x) k)
        (modifiedVelocity c n (eps • u x) k))
      (fun eps => (rayHamiltonian c n (eps • u x) k) ^ 2) ∧
    FirstJetEq (fun _ => k)
      (fun eps => (n / c) • modifiedVelocity c n (eps • u x) k -
        ((n ^ 2 - 1) * rayHamiltonian c n (eps • u x) k / c ^ 2) • (eps • u x)) := by
  have hu : HasFDerivAt u (fderiv ℝ u x) x :=
    ((hreg.contDiffAt (hO.mem_nhds hx)).differentiableAt (by norm_num)).hasFDerivAt
  set Du := fderiv ℝ u x with hDu
  set w := u x with hw
  have hc0 : c ≠ 0 := hc.ne'
  have hn0 : n ≠ 0 := by intro h; rw [h] at hn; linarith
  have hl : length3 k ≠ 0 := (Real.sqrt_pos.2 (p42s204_kk k hk)).ne'
  have hlen2 : length3 k ^ 2 = dot3 k k := Real.sq_sqrt (p42s204_kk k hk).le
  obtain ⟨hH0, aH, hHf, hHg⟩ := (slowFlow_firstJet c n 0 w k hc hn hk).1
  obtain ⟨hV0, aV, hVf, hVg⟩ := (slowFlow_firstJet c n 0 w k hc hn hk).2.1
  have haH : aH = (1 - 1 / n ^ 2) * dot3 w k := by
    refine hHg.unique ?_
    have := (((hasDerivAt_id (0:ℝ)).mul_const (1 - 1 / n ^ 2)).mul_const (dot3 w k)).const_add
      (c * length3 k / n)
    simpa using this
  have haV : aV = (1 - 1 / n ^ 2) • w := by
    refine hVg.unique ?_
    have := (((hasDerivAt_id (0:ℝ)).mul_const (1 - 1 / n ^ 2)).smul_const w).const_add
      ((c / n) • ((1 / length3 k) • k))
    simpa using this
  rw [haH] at hHf
  rw [haV] at hVf
  simp only [zero_smul, zero_mul, add_zero] at hH0 hV0
  have hW : HasDerivAt (fun eps : ℝ => modifiedVelocity c n (eps • w) k)
      (length3 k • ((1 - 1 / n ^ 2) • w)) 0 := hVf.const_smul (length3 k)
  have hW0 : modifiedVelocity c n 0 k = (c / n) • k := p42s204_Phi0 c n k hc hn hk
  have hHc : ContinuousAt (fun eps : ℝ => rayHamiltonian c n (eps • w) k) 0 := hHf.continuousAt
  have hWc : ContinuousAt (fun eps : ℝ => modifiedVelocity c n (eps • w) k) 0 := hW.continuousAt
  have hev := p42s204_evS c n w k hc hn hk
  have hRc := p42s204_R_cont c n u x k Du hc hn hk
  have hR0 := p42s204_R0 c n u x k Du hu hc hn hk
  -- the alongField of the modified velocity
  have hAW : ∀ᶠ eps in 𝓝 (0 : ℝ), alongField c n eps u
      (fun z => modifiedVelocity c n (eps • u z.1) z.2) (x, k) =
        eps • p42s204_R c n u x k Du eps := by
    filter_upwards [hev] with eps hp
    rw [p42s204_along c n eps u x k Du hu (fun p : V3 × V3 => modifiedVelocity c n p.1 p.2)
      (p42s204_Phi_diff c n _ hc hn hp)]
    exact p42s204_Wcore c n eps u x k Du hu hc hn hp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- part 1
    refine ⟨?_, _, hW, ?_⟩
    · simp only [zero_smul, smul_zero, add_zero]; exact hW0
    · have hg : (fun eps : ℝ => (c / n) • (k +
          ((n ^ 2 - 1) * rayHamiltonian c n (eps • w) k / c ^ 2) • (eps • w))) =
          fun eps => (c / n) • k + eps • ((c / n) •
            (((n ^ 2 - 1) * rayHamiltonian c n (eps • w) k / c ^ 2) • w)) := by
        funext eps; module
      rw [hg]
      have hR : ContinuousAt (fun eps : ℝ => (c / n) •
          (((n ^ 2 - 1) * rayHamiltonian c n (eps • w) k / c ^ 2) • w)) 0 :=
        by fun_prop
      have := (p42s204_slope _ hR).const_add ((c / n) • k)
      convert this using 1
      simp only [zero_smul, hH0, smul_smul]
      congr 1
      field_simp
  · -- part 2
    refine ⟨?_, p42s204_R c n u x k Du 0, ?_, ?_⟩
    · have h0 := hAW.self_of_nhds
      simp only [zero_smul] at h0 ⊢
      rw [h0]; funext i; fin_cases i <;> simp [cross3]
    · exact (p42s204_slope _ hRc).congr_of_eventuallyEq hAW
    · have hg : (fun eps : ℝ => (1 - 1 / n ^ 2) •
          cross3 (eps • curl3 u x) (modifiedVelocity c n (eps • w) k)) =
          fun eps => eps • ((1 - 1 / n ^ 2) • cross3 (curl3 u x) (modifiedVelocity c n (eps • w) k)) := by
        funext eps; rw [p42s204_cross_smul, smul_comm]
      rw [hg]
      have hcr : ContinuousAt (fun eps : ℝ => cross3 (curl3 u x)
          (modifiedVelocity c n (eps • w) k)) 0 := by
        unfold cross3
        have h0 := continuousAt_pi.1 hWc 0
        have h1 := continuousAt_pi.1 hWc 1
        have h2 := continuousAt_pi.1 hWc 2
        refine continuousAt_pi.2 (fun i => ?_)
        fin_cases i
        · exact (continuousAt_const.mul h2).sub (continuousAt_const.mul h1)
        · exact (continuousAt_const.mul h0).sub (continuousAt_const.mul h2)
        · exact (continuousAt_const.mul h1).sub (continuousAt_const.mul h0)
      have hcr' : ContinuousAt (fun eps : ℝ => (1 - 1 / n ^ 2) •
          cross3 (curl3 u x) (modifiedVelocity c n (eps • w) k)) 0 := by fun_prop
      refine (p42s204_slope _ hcr').congr_deriv ?_
      simp only [zero_smul, hW0, hR0]
  · -- part 3
    have hA3 : ∀ᶠ eps in 𝓝 (0 : ℝ), alongField c n eps u
        (fun z => dot3 (modifiedVelocity c n (eps • u z.1) z.2)
          (modifiedVelocity c n (eps • u z.1) z.2)) (x, k) =
        eps • (2 * dot3 (modifiedVelocity c n (eps • w) k) (p42s204_R c n u x k Du eps)) := by
      filter_upwards [hev] with eps hp
      have hd := (p42s204_Phi_diff c n _ hc hn hp).hasFDerivAt
      obtain ⟨hdd, hval⟩ := p42s204_dot_fderiv _ _ _ (eps • Du (rayVelocity c n (eps • u x) k),
        -gradient (fun x' => rayHamiltonian c n (eps • u x') k) x) hd
      rw [p42s204_along c n eps u x k Du hu
        (fun q : V3 × V3 => dot3 (modifiedVelocity c n q.1 q.2) (modifiedVelocity c n q.1 q.2)) hdd]
      rw [hval, p42s204_Wcore c n eps u x k Du hu hc hn hp]
      simp only [dot3, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]
      ring
    have hcont : ContinuousAt (fun eps : ℝ =>
        2 * dot3 (modifiedVelocity c n (eps • w) k) (p42s204_R c n u x k Du eps)) 0 :=
      continuousAt_const.mul (p42s204_dot_cont _ _ hWc hRc)
    have hz : 2 * dot3 (modifiedVelocity c n ((0 : ℝ) • w) k) (p42s204_R c n u x k Du 0) = 0 := by
      rw [zero_smul, hW0, hR0]
      simp only [dot3, cross3, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]
      simp; ring
    refine ⟨?_, 0, ?_, hasDerivAt_const _ _⟩
    · have h0 := hA3.self_of_nhds
      simp only [zero_smul] at h0 ⊢
      exact h0
    · have := (p42s204_slope _ hcont).congr_of_eventuallyEq hA3
      rwa [hz] at this
  · -- part 4
    have hA4 : ∀ᶠ eps in 𝓝 (0 : ℝ), alongField c n eps u
        (fun z => rayHamiltonian c n (eps • u z.1) z.2) (x, k) = 0 := by
      filter_upwards [hev] with eps hp
      rw [p42s204_along c n eps u x k Du hu (fun q : V3 × V3 => rayHamiltonian c n q.1 q.2)
        ((p42s204_H_cd c n _ hc hn hp).differentiableAt (by norm_num))]
      exact p42s204_Hzero c n eps u x k Du hu hc hn hp
    refine ⟨hA4.self_of_nhds, 0, ?_, hasDerivAt_const _ _⟩
    exact (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hA4
  · -- part 5
    refine ⟨?_, _, p42s204_dot_hasDeriv _ _ _ hW, ?_⟩
    · simp only [zero_smul, hW0, hH0, dot3, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]
      rw [show (c * length3 k / n) ^ 2 = c ^ 2 * length3 k ^ 2 / n ^ 2 by ring, hlen2]
      simp only [dot3, Fin.sum_univ_three]; field_simp
    · have := hHf.fun_pow 2
      refine this.congr_deriv ?_
      simp only [zero_smul, hW0, hH0, dot3, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]
      push_cast
      ring
  · -- part 6
    refine ⟨?_, 0, hasDerivAt_const _ _, ?_⟩
    · simp only [zero_smul, smul_zero, sub_zero, hW0, smul_smul]
      rw [show n / c * (c / n) = 1 by field_simp, one_smul]
    · have hg : (fun eps : ℝ => (n / c) • modifiedVelocity c n (eps • w) k -
          ((n ^ 2 - 1) * rayHamiltonian c n (eps • w) k / c ^ 2) • (eps • w)) =
          fun eps => (n / c) • modifiedVelocity c n (eps • w) k -
            eps • (((n ^ 2 - 1) * rayHamiltonian c n (eps • w) k / c ^ 2) • w) := by
        funext eps; module
      rw [hg]
      have hR : ContinuousAt (fun eps : ℝ =>
          ((n ^ 2 - 1) * rayHamiltonian c n (eps • w) k / c ^ 2) • w) 0 :=
        by fun_prop
      have := (hW.const_smul (n / c)).sub (p42s204_slope _ hR)
      refine this.congr_deriv ?_
      rw [zero_smul, hH0, smul_smul, smul_smul, ← sub_smul]
      symm
      have h0 : n / c * length3 k * (1 - 1 / n ^ 2) - (n ^ 2 - 1) * (c * length3 k / n) / c ^ 2 = 0 := by
        field_simp; ring
      rw [h0, zero_smul]

end

end QAlgorithms.Papers.Independent.Renew46.P42

open QAlgorithms.Papers.Independent.Renew46.P42 in
theorem solution (c n : ℝ) (u : V3 → V3) (x k : V3) (O : Set V3)
    (hc : 0 < c) (hn : 1 ≤ n) (hk : k ≠ 0)
    (hO : IsOpen O) (hx : x ∈ O) (hreg : ContDiffOn ℝ 2 u O) :
    FirstJetEq (fun eps => modifiedVelocity c n (eps • u x) k)
      (fun eps => (c / n) • (k +
        ((n ^ 2 - 1) * rayHamiltonian c n (eps • u x) k / c ^ 2) • (eps • u x))) ∧
    FirstJetEq (fun eps => alongField c n eps u
        (fun z => modifiedVelocity c n (eps • u z.1) z.2) (x, k))
      (fun eps => (1 - 1 / n ^ 2) •
        cross3 (eps • curl3 u x) (modifiedVelocity c n (eps • u x) k)) ∧
    FirstJetEq (fun eps => alongField c n eps u
        (fun z => dot3 (modifiedVelocity c n (eps • u z.1) z.2)
          (modifiedVelocity c n (eps • u z.1) z.2)) (x, k)) (fun _ => (0 : ℝ)) ∧
    FirstJetEq (fun eps => alongField c n eps u
        (fun z => rayHamiltonian c n (eps • u z.1) z.2) (x, k)) (fun _ => (0 : ℝ)) ∧
    FirstJetEq (fun eps => dot3 (modifiedVelocity c n (eps • u x) k)
        (modifiedVelocity c n (eps • u x) k))
      (fun eps => (rayHamiltonian c n (eps • u x) k) ^ 2) ∧
    FirstJetEq (fun _ => k)
      (fun eps => (n / c) • modifiedVelocity c n (eps • u x) k -
        ((n ^ 2 - 1) * rayHamiltonian c n (eps • u x) k / c ^ 2) • (eps • u x)) :=
  p42s204_main c n u x k O hc hn hk hO hx hreg

