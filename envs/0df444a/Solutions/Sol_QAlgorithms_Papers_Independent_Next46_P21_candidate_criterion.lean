-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P21.candidate_criterion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T22:42:33.786401+00:00
-- url     : https://prove2.me/submissions/be45f7ce-a9b6-428a-8ba4-547b740b6cfb

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P21
noncomputable section
open QAlgorithms.Papers.Independent.Next46.P21
open Set
open scoped ComplexConjugate Matrix

theorem g64a_qr (a : Zsqrtd 2) : quadraticReal a = (a.re : ℝ) + (a.im : ℝ) * Real.sqrt 2 := by
  simp [quadraticReal, Zsqrtd.toReal_apply]

theorem g64a_inj : Function.Injective quadraticReal :=
  Zsqrtd.toReal_injective (by norm_num) (by
    intro n hn
    have h1 : n.natAbs * n.natAbs = 2 := by
      have := congrArg Int.natAbs hn; simpa [Int.natAbs_mul] using this.symm
    have : n.natAbs ≤ 2 := by nlinarith
    interval_cases (n.natAbs) <;> omega)

theorem g64a_omega : QAlgorithms.gateT true true =
    ((Real.sqrt 2 / 2 : ℝ) : ℂ) + ((Real.sqrt 2 / 2 : ℝ) : ℂ) * Complex.I := by
  have : QAlgorithms.gateT true true = Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I) := by
    simp [QAlgorithms.gateT]; ring_nf
  rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four,
    Real.sin_pi_div_four]

theorem g64a_cyc (alpha beta : Zsqrtd 2) : IsCyclotomicInteger (quadraticComplex alpha beta) := by
  refine ⟨beta.im - alpha.im, beta.re, alpha.im + beta.im, alpha.re, ?_⟩
  rw [g64a_omega, quadraticComplex, g64a_qr, g64a_qr]
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; simp
  push_cast
  set s : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)
  ring_nf
  rw [Complex.I_sq, Complex.I_pow_three]
  ring_nf
  have hs3 : s ^ 3 = 2 * s := by rw [pow_succ, hs]
  rw [hs3, hs]; ring

theorem g64a_two_pow (k : ℕ) : (2 : Zsqrtd 2) ^ k = ⟨2 ^ k, 0⟩ := by
  induction k with
  | zero => rfl
  | succ n ih => rw [pow_succ, ih]; ext <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul, pow_succ]

theorem g64a_def_re (k : ℕ) (alpha beta : Zsqrtd 2) :
    (candidateDefect k alpha beta).re = 2 ^ k - (alpha.re ^ 2 + 2 * alpha.im ^ 2) -
      (beta.re ^ 2 + 2 * beta.im ^ 2) := by
  simp [candidateDefect, g64a_two_pow, sq, Zsqrtd.re_mul]; ring

theorem g64a_def_im (k : ℕ) (alpha beta : Zsqrtd 2) :
    (candidateDefect k alpha beta).im = -(2 * alpha.re * alpha.im) - 2 * beta.re * beta.im := by
  simp [candidateDefect, g64a_two_pow, sq, Zsqrtd.im_mul]; ring

theorem g64a_starmul (alpha beta : Zsqrtd 2) :
    star (quadraticComplex alpha beta) * quadraticComplex alpha beta =
      ((quadraticReal alpha ^ 2 + quadraticReal beta ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_apply]
  simp [quadraticComplex]; ring

theorem g64a_normSq_div (w : ℂ) (k : ℕ) :
    Complex.normSq (w / (Real.sqrt ((2 : ℝ) ^ k) : ℂ)) = Complex.normSq w / 2 ^ k := by
  rw [Complex.normSq_div, Complex.normSq_ofReal, Real.mul_self_sqrt (by positivity)]

theorem g64a_criterion (eps theta : ℝ) (k : ℕ) (alpha beta : Zsqrtd 2)
    (hk : 1 ≤ k) :
    IsCandidate eps theta k (quadraticComplex alpha beta) ↔
      (quadraticComplex alpha beta / (Real.sqrt ((2 : ℝ) ^ k) : ℂ)) ∈ epsilonRegion eps theta ∧
      normalizedBullet k alpha beta ∈ unitDisk ∧ Odd (alpha.re + beta.re) := by
  set xi0 := candidateDefect k alpha beta with hxi0
  have hq0 : quadraticReal xi0 = 2 ^ k - (quadraticReal alpha ^ 2 + quadraticReal beta ^ 2) := by
    rw [hxi0, candidateDefect, map_sub, map_sub, map_pow, map_pow, map_pow, map_ofNat]; ring
  have hq0s : quadraticReal (star xi0) =
      2 ^ k - (quadraticReal (star alpha) ^ 2 + quadraticReal (star beta) ^ 2) := by
    rw [hxi0, candidateDefect, star_sub, star_sub, star_pow, star_pow, star_pow, star_ofNat,
      map_sub, map_sub, map_pow, map_pow, map_pow, map_ofNat]; ring
  have hxiC : ((quadraticReal xi0 : ℝ) : ℂ) = (2 : ℂ) ^ k -
      star (quadraticComplex alpha beta) * quadraticComplex alpha beta := by
    rw [g64a_starmul, hq0]; push_cast; ring
  have huniq : ∀ xi : Zsqrtd 2, ((quadraticReal xi : ℝ) : ℂ) = (2 : ℂ) ^ k -
      star (quadraticComplex alpha beta) * quadraticComplex alpha beta → xi = xi0 := by
    intro xi h
    apply g64a_inj
    exact_mod_cast h.trans hxiC.symm
  have hpar : Odd xi0.re ↔ Odd (alpha.re + beta.re) := by
    rw [hxi0, g64a_def_re]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [pow_succ]
    simp [parity_simps]
    have h2 : Even ((2:ℤ) ^ j * 2) := even_two.mul_left _
    rw [← Int.not_even_iff_odd, ← Int.not_even_iff_odd]
    simp [h2]
  have hev : Even xi0.im := by
    rw [hxi0, g64a_def_im]; exact ⟨-(alpha.re * alpha.im) - beta.re * beta.im, by ring⟩
  have hdisk : (quadraticComplex alpha beta / (Real.sqrt ((2 : ℝ) ^ k) : ℂ)) ∈ unitDisk ↔
      0 ≤ quadraticReal xi0 := by
    simp only [unitDisk, Set.mem_ofPred_eq]
    rw [g64a_normSq_div, div_le_one (by positivity), hq0, Complex.normSq_apply]
    simp [quadraticComplex]
    constructor <;> intro h <;> nlinarith
  have hbul : normalizedBullet k alpha beta ∈ unitDisk ↔ 0 ≤ quadraticReal (star xi0) := by
    simp only [unitDisk, Set.mem_ofPred_eq, normalizedBullet]
    rw [Complex.normSq_mul, map_pow, Complex.normSq_neg, map_one, one_pow, one_mul, g64a_normSq_div,
      div_le_one (by positivity), hq0s, Complex.normSq_apply]
    simp [quadraticComplex]
    constructor <;> intro h <;> nlinarith
  constructor
  · rintro ⟨-, hreg, xi, hxi, hodd, -, -, hs⟩
    have := huniq xi hxi
    subst this
    exact ⟨hreg, hbul.2 hs, hpar.1 hodd⟩
  · rintro ⟨hreg, hb, hodd⟩
    refine ⟨g64a_cyc alpha beta, hreg, xi0, hxiC, hpar.2 hodd, hev, hdisk.1 hreg.1, hbul.1 hb⟩

theorem solution (eps theta : ℝ) (k : ℕ) (alpha beta : Zsqrtd 2)
    (heps : 0 < eps) (hk : 1 ≤ k) :
    IsCandidate eps theta k (quadraticComplex alpha beta) ↔
      (quadraticComplex alpha beta / (Real.sqrt ((2 : ℝ) ^ k) : ℂ)) ∈ epsilonRegion eps theta ∧
      normalizedBullet k alpha beta ∈ unitDisk ∧ Odd (alpha.re + beta.re) :=
  g64a_criterion eps theta k alpha beta hk
