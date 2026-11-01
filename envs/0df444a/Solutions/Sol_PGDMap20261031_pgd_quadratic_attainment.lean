-- Prove2me | solution 1 for PGDMap20261031.pgd_quadratic_attainment
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-31T17:44:35.608986+00:00
-- url     : https://prove2.me/submissions/99c4f157-d28d-4bd3-bb2e-89ca08e9554c

import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_PGDMap20261031_PGD

open PGDMap20261031 Set Filter
open scoped Topology RealInnerProductSpace BigOperators
noncomputable section

private def e (t : ℝ) : Space 1 := EuclideanSpace.single 0 t
private def co (x : Space 1) : ℝ := x 0

private lemma co_e (t : ℝ) : co (e t) = t := by simp [co, e]

private lemma e_co (x : Space 1) : e (co x) = x := by
  ext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp [e, co]

private lemma norm_one (x : Space 1) : ‖x‖ = |co x| := by
  calc
    ‖x‖ = ‖e (co x)‖ := congrArg norm (e_co x).symm
    _ = |co x| := by rw [e, EuclideanSpace.norm_single, Real.norm_eq_abs]

private lemma normsq_one (x : Space 1) : ‖x‖ ^ 2 = co x ^ 2 := by rw [norm_one, sq_abs]

private lemma coordinate_sub (x y : Space 1) : co (x - y) = co x - co y := rfl

private lemma coordinate_smul (a : ℝ) (x : Space 1) : co (a • x) = a * co x := rfl

private lemma scalar_convex (φ ψ : ℝ → ℝ) (hder : ∀ t, HasDerivAt φ (ψ t) t)
    (hmono : Monotone ψ) : ConvexOn ℝ univ φ := by
  apply MonotoneOn.convexOn_of_deriv convex_univ
  · intro t _
    exact (hder t).continuousAt.continuousWithinAt
  · intro t _
    exact (hder t).differentiableAt.differentiableWithinAt
  · intro x _ y _ hxy
    rw [(hder x).deriv, (hder y).deriv]
    exact hmono hxy

private lemma scalar_smooth (φ ψ : ℝ → ℝ) (hder : ∀ t, HasDerivAt φ (ψ t) t)
    (hconv : ConvexOn ℝ univ φ) (hlip : ∀ x y, |ψ x - ψ y| ≤ |x - y|)
    (L : ℝ) (hL : 0 < L) :
    SmoothConvex (fun x : Space 1 => L * φ (co x)) (fun x => e (L * ψ (co x))) L := by
  refine ⟨⟨convex_univ, ?_⟩, ?_, ?_⟩
  · intro x _ y _ a b ha hb hab
    have h := mul_le_mul_of_nonneg_left (hconv.2 (mem_univ (co x)) (mem_univ (co y)) ha hb hab) hL.le
    convert h using 1 <;> try rfl
    ring
  · intro x
    apply hasGradientAt_iff_hasFDerivAt.mpr
    have hdual : (InnerProductSpace.toDual ℝ (Space 1)) (e (L * ψ (co x))) =
        (L * ψ (co x)) • (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)) := by
      ext v
      change inner ℝ (e (L * ψ (co x))) v = (L * ψ (co x)) * co v
      rw [e, EuclideanSpace.inner_single_left]
      rfl
    rw [hdual]
    convert ((hder (co x)).const_mul L).comp_hasFDerivAt x
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).hasFDerivAt using 1 <;> rfl
  · intro x y
    rw [norm_one, norm_one, coordinate_sub, co_e, co_e]
    rw [← mul_sub, abs_mul, abs_of_pos hL]
    exact mul_le_mul_of_nonneg_left (hlip (co x) (co y)) hL.le

private def hubF (t : ℝ) : ℝ := ∫ s in (1 : ℝ)..t, min s 1
private def hubG (t : ℝ) : ℝ := min t 1

private lemma hubG_cont : Continuous hubG := continuous_id.min continuous_const

private lemma hub_deriv (t : ℝ) : HasDerivAt hubF (hubG t) t :=
  intervalIntegral.integral_hasDerivAt_right (hubG_cont.intervalIntegrable 1 t)
    (hubG_cont.stronglyMeasurableAtFilter MeasureTheory.volume (𝓝 t)) hubG_cont.continuousAt

private lemma hub_convex : ConvexOn ℝ univ hubF :=
  scalar_convex hubF hubG hub_deriv (fun _ _ h => min_le_min h le_rfl)

private lemma hub_lip (x y : ℝ) : |hubG x - hubG y| ≤ |x - y| := by
  by_cases hx : x ≤ 1 <;> by_cases hy : y ≤ 1
  · simp only [hubG, min_eq_left hx, min_eq_left hy]
    exact le_rfl
  · have hy' : 1 < y := lt_of_not_ge hy
    rw [hubG, hubG, min_eq_left hx, min_eq_right hy'.le,
      abs_of_nonpos (by linarith : x - 1 ≤ 0), abs_of_nonpos (by linarith : x - y ≤ 0)]
    linarith
  · have hx' : 1 < x := lt_of_not_ge hx
    rw [hubG, hubG, min_eq_right hx'.le, min_eq_left hy,
      abs_of_nonneg (by linarith : 0 ≤ 1 - y), abs_of_nonneg (by linarith : 0 ≤ x - y)]
    linarith
  · simp only [hubG, min_eq_right (le_of_not_ge hx), min_eq_right (le_of_not_ge hy), sub_self,
      abs_zero]
    exact abs_nonneg _

private lemma hub_value_right (t : ℝ) (ht : 1 ≤ t) : hubF t = t - 1 := by
  unfold hubF
  have heq : (∫ s in (1 : ℝ)..t, min s 1) = ∫ s in (1 : ℝ)..t, (1 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht] at hs
    exact min_eq_right hs.1
  rw [heq, intervalIntegral.integral_const]
  simp only [smul_eq_mul, mul_one]

private lemma hub_value_left (t : ℝ) (ht : t ≤ 1) : hubF t = (t ^ 2 - 1) / 2 := by
  unfold hubF
  have heq : (∫ s in (1 : ℝ)..t, min s 1) = ∫ s in (1 : ℝ)..t, s := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_ge ht] at hs
    exact min_eq_left hs.2
  rw [heq, integral_id]
  norm_num

private lemma quadratic_min (μ γ v y : ℝ) (hμ : 0 ≤ μ) (hγ : 0 < γ)
    (hy : (1 + γ * μ) * y = v) (z : ℝ) :
    μ / 2 * y ^ 2 + (y - v) ^ 2 / (2 * γ) ≤ μ / 2 * z ^ 2 + (z - v) ^ 2 / (2 * γ) := by
  have hid : μ / 2 * z ^ 2 + (z - v) ^ 2 / (2 * γ) -
      (μ / 2 * y ^ 2 + (y - v) ^ 2 / (2 * γ)) =
        (1 + γ * μ) / (2 * γ) * (z - y) ^ 2 := by
    rw [← hy]
    field_simp [ne_of_gt hγ]
    <;> ring
  have hb : 0 < 1 + γ * μ := by nlinarith
  have hn := mul_nonneg (div_nonneg hb.le (by positivity : 0 ≤ 2 * γ)) (sq_nonneg (z - y))
  rw [← hid] at hn
  linarith

private lemma scalar_trajectory (ψ : ℝ → ℝ) (L μ h : ℝ) (N : ℕ) (t : ℕ → ℝ)
    (hL : 0 < L) (hμ : 0 ≤ μ) (hh : 0 < h)
    (hupdate : ∀ i < N, base h (μ / L) * t (i + 1) = t i - h * ψ (t i)) :
    IsPGDTrajectory (quadraticPenalty 1 μ) (fun x => e (L * ψ (co x))) (h / L) N
      (fun i => e (t i)) := by
  refine ⟨fun _ _ => mem_univ _, ?_⟩
  intro i hi z _
  have hbase : 1 + h / L * μ = base h (μ / L) := by unfold base; ring
  have hscale : h / L * (L * ψ (t i)) = h * ψ (t i) := by field_simp [ne_of_gt hL]
  have hmin := quadratic_min μ (h / L) (t i - h * ψ (t i)) (t (i + 1)) hμ (div_pos hh hL)
    (by rw [hbase]; exact hupdate i hi) (co z)
  change μ / 2 * ‖e (t (i + 1))‖ ^ 2 + _ ≤ μ / 2 * ‖z‖ ^ 2 + _
  simp only [normsq_one, coordinate_sub, coordinate_smul, co_e, hscale]
  exact hmin

private lemma scalar_decrease (φ : ℝ → ℝ) (L μ : ℝ) (N : ℕ) (t : ℕ → ℝ) (hL : L ≠ 0) :
    decrease (quadraticPenalty 1 μ) (fun x => L * φ (co x)) (fun i => e (t i)) N =
      L * (φ (t 0) - φ (t N) + (μ / L) / 2 * (t 0 ^ 2 - t N ^ 2)) := by
  unfold decrease totalValue quadraticPenalty
  simp only [normsq_one, co_e]
  field_simp [hL]
  <;> ring

private lemma scalar_member (φ ψ : ℝ → ℝ) (hder : ∀ t, HasDerivAt φ (ψ t) t)
    (hconv : ConvexOn ℝ univ φ) (hlip : ∀ x y, |ψ x - ψ y| ≤ |x - y|)
    (L μ h : ℝ) (N : ℕ) (t : ℕ → ℝ) (R : ℝ) (hL : 0 < L) (hμ : 0 ≤ μ) (hh : 0 < h)
    (hupdate : ∀ i < N, base h (μ / L) * t (i + 1) = t i - h * ψ (t i))
    (hD : 0 < φ (t 0) - φ (t N) + (μ / L) / 2 * (t 0 ^ 2 - t N ^ 2))
    (hmatch : R * h ^ 2 * (φ (t 0) - φ (t N) + (μ / L) / 2 * (t 0 ^ 2 - t N ^ 2)) =
      (t (N - 1) - t N) ^ 2) : R ∈ ratioSet (quadraticPenalty 1 μ) L h N := by
  refine ⟨(fun x => L * φ (co x)), (fun x => e (L * ψ (co x))), (fun i => e (t i)),
    scalar_smooth φ ψ hder hconv hlip L hL,
    scalar_trajectory ψ L μ h N t hL hμ hh hupdate, ?_, ?_⟩
  · rw [scalar_decrease φ L μ N t (ne_of_gt hL)]
    exact mul_pos hL hD
  · rw [scalar_decrease φ L μ N t (ne_of_gt hL)]
    unfold residualSquared
    simp only [normsq_one, coordinate_sub, co_e]
    let D := φ (t 0) - φ (t N) + (μ / L) / 2 * (t 0 ^ 2 - t N ^ 2)
    change R = ((t (N - 1) - t N) ^ 2 / (h / L) ^ 2) / (L * (L * D))
    rw [div_div]
    have hden : (h / L) ^ 2 * (L * (L * D)) = h ^ 2 * D := by
      field_simp [ne_of_gt hL]
    rw [hden]
    apply (eq_div_iff (ne_of_gt (mul_pos (sq_pos_of_pos hh) hD))).2
    nlinarith only [hmatch]

private lemma A_den_positive (N : ℕ) (h q : ℝ) (hN : 1 ≤ N) (hh : validStep h) (hq : 0 < q) :
    0 < base h q ^ (2 * N) - 1 - h ^ 2 * q := by
  have hb : 1 ≤ base h q := by dsimp [base]; nlinarith [hh.1]
  have hpow : base h q ^ 2 ≤ base h q ^ (2 * N) := pow_le_pow_right₀ hb (by omega)
  have hpos : 0 < h * q * (2 - h + h * q) := by
    exact mul_pos (mul_pos hh.1 hq) (by nlinarith [hh.2, hh.1])
  dsimp [base] at hpow ⊢
  nlinarith only [hpow, hpos]

private lemma B_den_positive (N : ℕ) (h q : ℝ) (hN : 1 ≤ N) (hh : validStep h) (hq : 0 ≤ q) :
    0 < base h q ^ (2 * N) - (1 - h) ^ (2 * N) := by
  have hb : 1 ≤ base h q := by dsimp [base]; nlinarith [hh.1]
  have hpow := one_le_pow₀ hb (n := 2 * N)
  have hsq : (1 - h) ^ 2 < 1 := by nlinarith [hh.1, hh.2]
  have ht := pow_lt_one₀ (sq_nonneg (1 - h)) hsq (by omega : N ≠ 0)
  rw [← pow_mul] at ht
  linarith

private lemma quadratic_instance (L μ h : ℝ) (N : ℕ) (hL : 0 < L) (hμ : 0 ≤ μ)
    (hh : validStep h) (hN : 1 ≤ N) : branchB N h (μ / L) ∈ ratioSet (quadraticPenalty 1 μ) L h N := by
  cases N with
  | zero => omega
  | succ k =>
    let q := μ / L
    let b := base h q
    let a := (1 - h) / b
    let t := fun i : ℕ => a ^ i
    have hq : 0 ≤ q := div_nonneg hμ hL.le
    have hb1 : 1 ≤ b := by dsimp [b, base]; nlinarith [hh.1]
    have hb : 0 < b := by linarith
    have ha2 : a ^ 2 < 1 := by
      dsimp [a]
      rw [div_pow]
      apply (div_lt_one (sq_pos_of_pos hb)).2
      nlinarith [sq_nonneg (b - 1), hh.1, hh.2]
    have hpow : (a ^ (k + 1)) ^ 2 < 1 := by
      have hp := pow_lt_one₀ (sq_nonneg a) ha2 (by omega : k + 1 ≠ 0)
      simpa only [← pow_mul, Nat.mul_comm 2 (k + 1)] using hp
    have hd (s : ℝ) : HasDerivAt (fun s : ℝ => s ^ 2 / 2) s s := by
      convert ((hasDerivAt_id s).pow 2).div_const 2 using 1 <;> try rfl
      simp
    have hconv := scalar_convex (fun s : ℝ => s ^ 2 / 2) id hd monotone_id
    have hup (i : ℕ) (_hi : i < k + 1) : b * t (i + 1) = t i - h * t i := by
      dsimp [t]
      rw [pow_succ]
      dsimp [a]
      field_simp [ne_of_gt hb]
      <;> ring
    have hD : 0 < t 0 ^ 2 / 2 - t (k + 1) ^ 2 / 2 + q / 2 * (t 0 ^ 2 - t (k + 1) ^ 2) := by
      have heq : t 0 ^ 2 / 2 - t (k + 1) ^ 2 / 2 + q / 2 * (t 0 ^ 2 - t (k + 1) ^ 2) =
          (1 + q) / 2 * (1 - (a ^ (k + 1)) ^ 2) := by dsimp [t]; simp only [pow_zero]; ring
      rw [heq]
      positivity
    apply scalar_member (fun s : ℝ => s ^ 2 / 2) id hd hconv (fun _ _ => le_rfl)
      L μ h (k + 1) t (branchB (k + 1) h q) hL hμ hh.1 hup hD
    change branchB (k + 1) h q * h ^ 2 *
      (t 0 ^ 2 / 2 - t (k + 1) ^ 2 / 2 + q / 2 * (t 0 ^ 2 - t (k + 1) ^ 2)) =
        (t ((k + 1) - 1) - t (k + 1)) ^ 2
    have hden := ne_of_gt (B_den_positive (k + 1) h q (by omega) hh hq)
    dsimp [t]
    simp only [pow_zero, one_pow, Nat.add_sub_cancel]
    unfold branchB
    rw [show 2 * (k + 1) - 2 = 2 * k by omega]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
    apply (div_eq_iff hden).2
    rw [show 2 * (k + 1) = 2 * k + 2 by omega]
    simp only [a, div_pow, pow_succ, pow_add]
    simp only [show 2 * k = k * 2 by omega, pow_mul]
    have hvne := pow_ne_zero k (ne_of_gt hb)
    generalize hU : (1 - h) ^ k = u at *
    generalize hV : b ^ k = v at *
    field_simp [ne_of_gt hb, hvne]
    dsimp [b, base]
    ring

private def affinePath (q h : ℝ) (k i : ℕ) : ℝ :=
  if i ≤ k then
    if q = 0 then 1 + ((k - i : ℕ) : ℝ) * h
    else ((1 + q) * base h q ^ (k - i) - 1) / q
  else (1 - h) / base h q

private lemma affine_on (q h : ℝ) (k i : ℕ) (hi : i ≤ k) : affinePath q h k i =
    if q = 0 then 1 + ((k - i : ℕ) : ℝ) * h else ((1 + q) * base h q ^ (k - i) - 1) / q := by
  rw [affinePath, if_pos hi]

private lemma affine_last (q h : ℝ) (k : ℕ) : affinePath q h k (k + 1) = (1 - h) / base h q := by
  rw [affinePath, if_neg (by omega)]

private lemma affine_penultimate (q h : ℝ) (k : ℕ) : affinePath q h k k = 1 := by
  rw [affine_on q h k k le_rfl]
  simp only [Nat.sub_self, Nat.cast_zero, zero_mul, add_zero, pow_zero, mul_one]
  split_ifs with hq
  · rfl
  · field_simp [hq]
    ring

private lemma affine_ge_one (q h : ℝ) (k i : ℕ) (hq : 0 ≤ q) (hh : 0 < h) (hi : i ≤ k) :
    1 ≤ affinePath q h k i := by
  rw [affine_on q h k i hi]
  split_ifs with hq0
  · nlinarith [(Nat.cast_nonneg (k - i) : (0 : ℝ) ≤ ((k - i : ℕ) : ℝ))]
  · have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
    apply (le_div_iff₀ hqpos).2
    have hb : 1 ≤ base h q := by unfold base; nlinarith
    have hp := one_le_pow₀ hb (n := k - i)
    nlinarith

private lemma affine_update (q h : ℝ) (k : ℕ) (hq : 0 ≤ q) (hh : 0 < h) :
    ∀ i < k + 1, base h q * affinePath q h k (i + 1) =
      affinePath q h k i - h * hubG (affinePath q h k i) := by
  intro i hi
  have hiK : i ≤ k := by omega
  have hg : hubG (affinePath q h k i) = 1 := min_eq_right (affine_ge_one q h k i hq hh hiK)
  rw [hg, mul_one]
  by_cases hik : i = k
  · subst i
    rw [affine_penultimate, affine_last]
    have hb : 0 < base h q := by unfold base; nlinarith
    field_simp [ne_of_gt hb]
  · have hiNext : i + 1 ≤ k := by omega
    have hexp : k - i = (k - (i + 1)) + 1 := by omega
    rw [affine_on q h k (i + 1) hiNext, affine_on q h k i hiK]
    split_ifs with hq0
    · have hcast : ((k - i : ℕ) : ℝ) = ((k - (i + 1) : ℕ) : ℝ) + 1 := by exact_mod_cast hexp
      simp only [hq0, base, mul_zero, add_zero, one_mul]
      rw [hcast]
      ring
    · rw [hexp, pow_succ]
      unfold base
      field_simp [hq0]
      <;> ring

private lemma hub_algebra (q h : ℝ) (k : ℕ) (hq : 0 ≤ q) (hh : validStep h) :
    let t := affinePath q h k
    let D := hubF (t 0) - hubF (t (k + 1)) + q / 2 * (t 0 ^ 2 - t (k + 1) ^ 2)
    0 < D ∧ branchA (k + 1) h q * h ^ 2 * D = (1 - (1 - h) / base h q) ^ 2 := by
  dsimp only
  let t := affinePath q h k
  let b := base h q
  let a := (1 - h) / b
  let D := hubF (t 0) - hubF (t (k + 1)) + q / 2 * (t 0 ^ 2 - t (k + 1) ^ 2)
  change 0 < D ∧ branchA (k + 1) h q * h ^ 2 * D = (1 - a) ^ 2
  have hb1 : 1 ≤ b := by dsimp [b, base]; nlinarith [hh.1]
  have hb : 0 < b := by linarith
  have ha1 : a < 1 := (div_lt_one hb).2 (by nlinarith [hh.1])
  have hDformula : D = t 0 - 1 - (a ^ 2 - 1) / 2 + q / 2 * (t 0 ^ 2 - a ^ 2) := by
    dsimp only [D, t]
    rw [hub_value_right _ (affine_ge_one q h k 0 hq hh.1 (by omega)), affine_last,
      hub_value_left _ ha1.le]
  by_cases hq0 : q = 0
  · have hDzero : D = h * (2 * ((k + 1 : ℕ) : ℝ) - h) / 2 := by
      rw [hDformula]
      dsimp [t]
      rw [affine_on q h k 0 (by omega), if_pos hq0]
      simp only [hq0, base, mul_zero, add_zero, Nat.sub_zero, div_one]
      dsimp [a, b, base]
      rw [hq0]
      push_cast
      ring
    have hd : 0 < h * (2 * ((k + 1 : ℕ) : ℝ) - h) :=
      mul_pos hh.1 (by push_cast; nlinarith [hh.2, (Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))])
    constructor
    · rw [hDzero]
      positivity
    · rw [hDzero]
      unfold branchA
      rw [if_pos hq0]
      dsimp [a, b, base]
      rw [hq0]
      have hinner : 2 * ((k + 1 : ℕ) : ℝ) - h ≠ 0 := (mul_ne_zero_iff.mp (ne_of_gt hd)).2
      field_simp [ne_of_gt hd, hinner]
      <;> ring
  · have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
    have hDA := A_den_positive (k + 1) h q (by omega) hh hqpos
    have hidentity : 2 * q * b ^ 2 * D =
        (1 + q) ^ 2 * (b ^ (2 * (k + 1)) - 1 - h ^ 2 * q) := by
      rw [hDformula]
      dsimp [t]
      rw [affine_on q h k 0 (by omega), if_neg hq0, Nat.sub_zero]
      change 2 * q * b ^ 2 * (((1 + q) * b ^ k - 1) / q - 1 - (a ^ 2 - 1) / 2 +
        q / 2 * ((((1 + q) * b ^ k - 1) / q) ^ 2 - a ^ 2)) = _
      rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add]
      rw [show 2 * k = k * 2 by omega, pow_mul]
      dsimp [a]
      generalize hU : b ^ k = u
      field_simp [hq0, ne_of_gt hb]
      dsimp [b, base]
      ring
    have hDpos : 0 < D := by
      have hrhs : 0 < (1 + q) ^ 2 * (b ^ (2 * (k + 1)) - 1 - h ^ 2 * q) :=
        mul_pos (sq_pos_of_pos (by linarith)) hDA
      have hprod : 0 < 2 * q * b ^ 2 * D := by rw [hidentity]; exact hrhs
      by_contra hn
      have hnonpos := mul_nonpos_of_nonneg_of_nonpos
        (by positivity : 0 ≤ 2 * q * b ^ 2) (le_of_not_gt hn)
      exact (not_lt_of_ge hnonpos) hprod
    refine ⟨hDpos, ?_⟩
    unfold branchA
    rw [if_neg hq0, div_mul_eq_mul_div, div_mul_eq_mul_div]
    apply (div_eq_iff (ne_of_gt hDA)).2
    have hgap : 1 - a = h * (1 + q) / b := by
      dsimp [a]
      field_simp [ne_of_gt hb]
      dsimp [b, base]
      ring
    rw [hgap]
    field_simp [ne_of_gt hb]
    have hid := congrArg (fun v : ℝ => h ^ 2 * v) hidentity
    nlinarith only [hid]

private lemma hub_instance (L μ h : ℝ) (N : ℕ) (hL : 0 < L) (hμ : 0 ≤ μ)
    (hh : validStep h) (hN : 1 ≤ N) : branchA N h (μ / L) ∈ ratioSet (quadraticPenalty 1 μ) L h N := by
  cases N with
  | zero => omega
  | succ k =>
    let q := μ / L
    let t := affinePath q h k
    have hq : 0 ≤ q := div_nonneg hμ hL.le
    obtain ⟨hD, hmatch⟩ := hub_algebra q h k hq hh
    apply scalar_member hubF hubG hub_deriv hub_convex hub_lip L μ h (k + 1) t
      (branchA (k + 1) h q) hL hμ hh.1 (affine_update q h k hq hh.1) hD
    simpa only [t, q, Nat.add_sub_cancel, affine_penultimate, affine_last] using hmatch

private lemma A_one (h q : ℝ) : branchA 1 h q = curveOne h q := by
  unfold branchA curveOne
  by_cases hq : q = 0
  · simp [hq]
  · rw [if_neg hq]
    change 2 * q / ((1 + h * q) ^ 2 - 1 - h ^ 2 * q) = 2 / (h * (2 - h + h * q))
    have heq : (1 + h * q) ^ 2 - 1 - h ^ 2 * q = q * (h * (2 - h + h * q)) := by ring
    rw [heq]
    field_simp [hq]

theorem solution : QuadraticAttainmentClaim := by
  intro L μ h N hL hμ hh hN
  by_cases hN1 : N = 1
  · subst N
    rw [curve, if_pos rfl, ← A_one]
    exact hub_instance L μ h 1 hL hμ hh (by omega)
  · rw [curve, if_neg hN1]
    by_cases hAB : branchA N h (μ / L) ≤ branchB N h (μ / L)
    · rw [max_eq_right hAB]
      exact quadratic_instance L μ h N hL hμ hh hN
    · rw [max_eq_left (le_of_not_ge hAB)]
      exact hub_instance L μ h N hL hμ hh hN

