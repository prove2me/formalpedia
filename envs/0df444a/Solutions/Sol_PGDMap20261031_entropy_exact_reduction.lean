-- Prove2me | solution 1 for PGDMap20261031.entropy_exact_reduction
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-31T16:24:45.634188+00:00
-- url     : https://prove2.me/submissions/c394e2b1-6335-4c0f-9790-62724089caed

import Mathlib.Tactic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Definitions.Def_PGDMap20261031_Entropy

open PGDMap20261031 Filter Set
open scoped Topology BigOperators
noncomputable section

private lemma basic_den {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]

private lemma scaled_den (M : EntropyMixture) (j : Fin M.m) {t : ℝ}
    (ht : t ∈ Ioo (-1 : ℝ) 1) : 0 < 1 - M.a j * t ^ 2 := by
  have := basic_den ht
  nlinarith [M.a_pos j, M.a_lt_one j, sq_nonneg t]

private lemma k_cont (c : ℝ) : ContinuousOn (powerCurvature c) (Ioo (-1 : ℝ) 1) := by
  intro t ht
  apply ContinuousAt.continuousWithinAt
  unfold powerCurvature
  exact (((continuousAt_const.add continuousAt_id).rpow_const
    (Or.inl (ne_of_gt (by change 0 < 1 + t; linarith [ht.1])))).add
    ((continuousAt_const.sub continuousAt_id).rpow_const
      (Or.inl (ne_of_gt (by change 0 < 1 - t; linarith [ht.2]))))).div_const 2

private lemma k_pos (c : ℝ) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    0 < powerCurvature c t := by
  unfold powerCurvature
  exact div_pos (add_pos (Real.rpow_pos_of_pos (by linarith [ht.1]) _)
    (Real.rpow_pos_of_pos (by linarith [ht.2]) _)) (by norm_num)

private lemma ab_cont (M : EntropyMixture) :
    ContinuousOn (mixtureCurvature M) (Ioo (-1 : ℝ) 1) ∧
    ContinuousOn (entropyCurvature M) (Ioo (-1 : ℝ) 1) := by
  constructor
  · intro t ht
    apply ContinuousAt.continuousWithinAt
    unfold mixtureCurvature
    have hterm (j : Fin M.m) : ContinuousAt
        (fun s : ℝ => M.weight j * M.a j / (1 - M.a j * s ^ 2)) t :=
      continuousAt_const.div
        (continuousAt_const.sub (continuousAt_const.mul (continuousAt_id.pow 2)))
        (ne_of_gt (scaled_den M j ht))
    generalize (Finset.univ : Finset (Fin M.m)) = s
    induction s using Finset.induction_on with
    | empty => simpa using (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) t)
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (hterm i).add ih
  · intro t ht
    exact (continuousAt_const.div (continuousAt_const.sub (continuousAt_id.pow 2))
      (ne_of_gt (basic_den ht))).continuousWithinAt

private lemma ab_pos (M : EntropyMixture) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    0 ≤ mixtureCurvature M t ∧ 0 < entropyCurvature M t := by
  constructor
  · unfold mixtureCurvature
    exact Finset.sum_nonneg fun j _ => le_of_lt
      (div_pos (mul_pos (M.weight_pos j) (M.a_pos j)) (scaled_den M j ht))
  · exact div_pos M.lambda_pos (basic_den ht)

private lemma atan_deriv {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt artanh (1 / (1 - t ^ 2)) t := by
  have hp := ((hasDerivAt_id t).const_add 1).log
    (ne_of_gt (by linarith [ht.1]) : 1 + t ≠ 0)
  have hm := ((hasDerivAt_id t).const_sub 1).log
    (ne_of_gt (by linarith [ht.2]) : 1 - t ≠ 0)
  convert (hp.sub hm).div_const 2 using 1 <;> try rfl
  simp only [id_eq]
  field_simp [ne_of_gt (basic_den ht),
    (ne_of_gt (by linarith [ht.1]) : 1 + t ≠ 0),
    (ne_of_gt (by linarith [ht.2]) : 1 - t ≠ 0)]
  <;> ring

private lemma mix_deriv (M : EntropyMixture) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (mixtureSlope M) (mixtureCurvature M t) t := by
  unfold mixtureSlope mixtureCurvature
  apply HasDerivAt.fun_sum
  intro j _
  have hs : 0 < Real.sqrt (M.a j) := Real.sqrt_pos.mpr (M.a_pos j)
  have hsq := Real.sq_sqrt (le_of_lt (M.a_pos j))
  have hlt : Real.sqrt (M.a j) < 1 := by nlinarith [M.a_lt_one j]
  have ht' : Real.sqrt (M.a j) * t ∈ Ioo (-1 : ℝ) 1 := by
    constructor <;> nlinarith [mul_lt_mul_of_pos_left ht.1 hs,
      mul_lt_mul_of_pos_left ht.2 hs]
  convert ((atan_deriv ht').comp t ((hasDerivAt_id t).const_mul
    (Real.sqrt (M.a j)))).const_mul (M.weight j * Real.sqrt (M.a j)) using 1
    <;> try rfl
  rw [mul_pow, hsq]
  ring_nf
  rw [hsq]
  ring

private lemma geo_deriv (c : ℝ) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (geometrySlope c) (powerCurvature c t) t := by
  have hsub : uIcc (0 : ℝ) t ⊆ Ioo (-1 : ℝ) 1 := by
    intro y hy
    rcases le_total 0 t with h | h
    · rw [uIcc_of_le h] at hy
      exact ⟨by linarith [hy.1], lt_of_le_of_lt hy.2 ht.2⟩
    · rw [uIcc_of_ge h] at hy
      exact ⟨lt_of_lt_of_le ht.1 hy.1, by linarith [hy.2]⟩
  exact intervalIntegral.integral_hasDerivAt_right
    ((k_cont c).mono hsub |>.intervalIntegrable)
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (k_cont c) t ht)
    ((k_cont c).continuousAt (isOpen_Ioo.mem_nhds ht))

private def P (M : EntropyMixture) (c p : ℝ) (t : ℝ) :=
  p * geometrySlope c t + M.lambda * artanh t

private def Q (M : EntropyMixture) (c p ell : ℝ) (t : ℝ) :=
  p * geometrySlope c t - mixtureSlope M t - ell

private def g (M : EntropyMixture) (ell t : ℝ) :=
  mixtureSlope M t + M.lambda * artanh t + ell

private lemma P_deriv (M : EntropyMixture) (c p : ℝ) {t : ℝ}
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (P M c p) (p * powerCurvature c t + entropyCurvature M t) t := by
  convert ((geo_deriv c ht).const_mul p).add ((atan_deriv ht).const_mul M.lambda)
    using 1 <;> try rfl
  unfold entropyCurvature
  ring

private lemma Q_deriv (M : EntropyMixture) (c p ell : ℝ) {t : ℝ}
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (Q M c p ell) (p * powerCurvature c t - mixtureCurvature M t) t :=
  (((geo_deriv c ht).const_mul p).sub (mix_deriv M ht)).sub_const ell

private lemma g_deriv (M : EntropyMixture) (ell : ℝ) {t : ℝ}
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (g M ell) (mixtureCurvature M t + entropyCurvature M t) t := by
  convert ((mix_deriv M ht).add ((atan_deriv ht).const_mul M.lambda)).add_const ell
    using 1 <;> try rfl
  unfold entropyCurvature
  ring

private lemma E_even (M : EntropyMixture) (c p t : ℝ) :
    curvatureError M c p (-t) = curvatureError M c p t := by
  unfold curvatureError mixtureCurvature entropyCurvature powerCurvature
  simp only [neg_sq, ← sub_eq_add_neg, sub_neg_eq_add]
  rw [add_comm (Real.rpow (1 - t) (-c))]

private lemma E_bound (hlub : ErrorProfileLUBClaim) (M : EntropyMixture) (c p : ℝ)
    (hv : validGeometry (c, p)) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    |curvatureError M c p t| ≤ contraction M c p := by
  by_cases h : 0 ≤ t
  · exact (hlub M c p hv).1 ⟨t, ⟨h, ht.2⟩, rfl⟩
  · have he := (hlub M c p hv).1
      ⟨-t, ⟨by linarith, by linarith [ht.1]⟩, rfl⟩
    rwa [E_even] at he

private lemma pair_ratio_ordered (M : EntropyMixture) (c p ell x y : ℝ) (hp : 0 < p)
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hy : y ∈ Ioo (-1 : ℝ) 1) (hxy : x < y) :
    ∃ t ∈ Ioo (-1 : ℝ) 1, (P M c p x - P M c p y) * curvatureError M c p t =
      Q M c p ell x - Q M c p ell y := by
  have hsub : Icc x y ⊆ Ioo (-1 : ℝ) 1 := fun t ht =>
    ⟨lt_of_lt_of_le hx.1 ht.1, lt_of_le_of_lt ht.2 hy.2⟩
  obtain ⟨t, ht, heq⟩ := exists_ratio_hasDerivAt_eq_ratio_slope
    (Q M c p ell) (fun t => p * powerCurvature c t - mixtureCurvature M t) hxy
    (fun t ht => (Q_deriv M c p ell (hsub ht)).continuousAt.continuousWithinAt)
    (fun t ht => Q_deriv M c p ell (hsub ⟨le_of_lt ht.1, le_of_lt ht.2⟩))
    (P M c p) (fun t => p * powerCurvature c t + entropyCurvature M t)
    (fun t ht => (P_deriv M c p (hsub ht)).continuousAt.continuousWithinAt)
    (fun t ht => P_deriv M c p (hsub ⟨le_of_lt ht.1, le_of_lt ht.2⟩))
  have htI := hsub ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have hd : 0 < p * powerCurvature c t + entropyCurvature M t :=
    add_pos (mul_pos hp (k_pos c htI)) (ab_pos M htI).2
  refine ⟨t, htI, ?_⟩
  unfold curvatureError
  rw [← mul_div_assoc]
  apply (div_eq_iff (ne_of_gt hd)).2
  linarith

private lemma one_step (hlub : ErrorProfileLUBClaim) (M : EntropyMixture)
    (c p ell x y : ℝ) (hv : validGeometry (c, p))
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hy : y ∈ Ioo (-1 : ℝ) 1)
    (hu : P M c p y = Q M c p ell x) :
    |g M ell y| ≤ contraction M c p * |g M ell x| := by
  have hp : 0 < p := hv.2.2
  have hrat : ∃ t ∈ Ioo (-1 : ℝ) 1,
      (P M c p x - P M c p y) * curvatureError M c p t =
        Q M c p ell x - Q M c p ell y := by
    rcases lt_trichotomy x y with hxy | hxy | hxy
    · exact pair_ratio_ordered M c p ell x y hp hx hy hxy
    · subst y
      exact ⟨0, ⟨by norm_num, by norm_num⟩, by ring⟩
    · obtain ⟨t, ht, heq⟩ := pair_ratio_ordered M c p ell y x hp hy hx hxy
      exact ⟨t, ht, by nlinarith [heq]⟩
  obtain ⟨t, ht, heq⟩ := hrat
  have hgx : g M ell x = P M c p x - P M c p y := by
    dsimp [P, Q, g] at *
    linarith
  have hgy : g M ell y = Q M c p ell x - Q M c p ell y := by
    dsimp [P, Q, g] at *
    linarith
  rw [hgy, ← heq, abs_mul, ← hgx, mul_comm]
  exact mul_le_mul_of_nonneg_right (E_bound hlub M c p hv ht) (abs_nonneg _)

private lemma upper_ratio (hder : EntropyDerivativeClaim) (hlub : ErrorProfileLUBClaim)
    (M : EntropyMixture) (c p : ℝ) (N : ℕ) (hv : validGeometry (c, p)) :
    contraction M c p ^ (2 * N) ∈ upperBounds (entropyPerformanceSet M c p N) := by
  have hr : 0 ≤ contraction M c p := le_trans (abs_nonneg _)
    ((hlub M c p hv).1 ⟨0, ⟨by norm_num, by norm_num⟩, rfl⟩)
  rintro v ⟨ell, x, htraj, hg0, rfl⟩
  have hg (i : ℕ) (hi : i ≤ N) : objectiveGradient M ell (x i) = g M ell (x i) :=
    hder M ell (x i) (htraj.1 i hi)
  have hbound (i : ℕ) (hi : i ≤ N) :
      |g M ell (x i)| ≤ contraction M c p ^ i * |g M ell (x 0)| := by
    induction i with
    | zero => simp
    | succ i ih =>
      have hiN : i < N := by omega
      have hstep := one_step hlub M c p ell (x i) (x (i + 1)) hv
        (htraj.1 i (by omega)) (htraj.1 (i + 1) hi) (htraj.2 i hiN)
      calc
        _ ≤ contraction M c p * |g M ell (x i)| := hstep
        _ ≤ contraction M c p * (contraction M c p ^ i * |g M ell (x 0)|) :=
          mul_le_mul_of_nonneg_left (ih (by omega)) hr
        _ = _ := by rw [pow_succ]; ring
  have hb := hbound N le_rfl
  have hgnz : g M ell (x 0) ≠ 0 := by rwa [hg 0 (by omega)] at hg0
  rw [hg N le_rfl, hg 0 (by omega)]
  apply (div_le_iff₀ (sq_pos_of_ne_zero (abs_ne_zero.mpr hgnz))).2
  have hs := pow_le_pow_left₀ (abs_nonneg (g M ell (x N))) hb 2
  simpa only [mul_pow, ← pow_mul, Nat.mul_comm N 2] using hs

private lemma lower_at_state (hder : EntropyDerivativeClaim)
    (M : EntropyMixture) (c p : ℝ) (N : ℕ) (hv : validGeometry (c, p))
    (u : ℝ) (hu : u ∈ Ioo (-1 : ℝ) 1) (b : ℝ)
    (hb : b ∈ upperBounds (entropyPerformanceSet M c p N)) :
    |curvatureError M c p u| ^ (2 * N) ≤ b := by
  let d := p * powerCurvature c u + entropyCurvature M u
  have hd : 0 < d := add_pos (mul_pos hv.2.2 (k_pos c hu)) (ab_pos M hu).2
  have hmem : ∀ᶠ t in 𝓝 u, t ∈ Ioo (-1 : ℝ) 1 := isOpen_Ioo.mem_nhds hu
  have hPs : HasStrictDerivAt (P M c p) d u := by
    apply hasStrictDerivAt_of_hasDerivAt_of_continuousAt
      (hmem.mono (fun t ht => P_deriv M c p ht))
    exact (continuousAt_const.mul ((k_cont c).continuousAt
      (isOpen_Ioo.mem_nhds hu))).add
        ((ab_cont M).2.continuousAt (isOpen_Ioo.mem_nhds hu))
  let ell := -mixtureSlope M u - M.lambda * artanh u
  let R := hPs.localInverse (P M c p) d u (ne_of_gt hd)
  let T := fun t => R (Q M c p ell t)
  have hQeq : Q M c p ell u = P M c p u := by dsimp [Q, P, ell]; ring
  have hRu : R (P M c p u) = u := (hPs.eventually_left_inverse (ne_of_gt hd)).self_of_nhds
  have hTu : T u = u := by dsimp [T]; rw [hQeq, hRu]
  have hTd : HasDerivAt T (curvatureError M c p u) u := by
    have hi := (hPs.to_localInverse (ne_of_gt hd)).hasDerivAt
    have hi' : HasDerivAt R d⁻¹ (Q M c p ell u) := by simpa only [hQeq] using hi
    convert hi'.comp u (Q_deriv M c p ell hu) using 1 <;> try rfl
    unfold curvatureError d
    ring
  have hiter (i : ℕ) : HasDerivAt T^[i] (curvatureError M c p u ^ i) u :=
    HasDerivAt.iterate u hTd hTu i
  have hitercont (i : ℕ) : Tendsto T^[i] (𝓝 u) (𝓝 u) := by
    have hc := (hiter i).continuousAt
    change Tendsto T^[i] (𝓝 u) (𝓝 (T^[i] u)) at hc
    simpa only [Function.iterate_fixed hTu i] using hc
  have hstep : ∀ᶠ t in 𝓝 u, P M c p (T t) = Q M c p ell t := by
    have hc : Tendsto (Q M c p ell) (𝓝 u) (𝓝 (P M c p u)) := by
      have hc' := (Q_deriv M c p ell hu).continuousAt
      change Tendsto (Q M c p ell) (𝓝 u) (𝓝 (Q M c p ell u)) at hc'
      simpa only [hQeq] using hc'
    exact hc.eventually (hPs.eventually_right_inverse (ne_of_gt hd))
  have htraj : ∀ᶠ t in 𝓝 u, entropyTrajectory M c p ell N (fun i => T^[i] t) := by
    have hfinite : ∀ᶠ t in 𝓝 u, ∀ i ∈ Finset.range (N + 1),
        T^[i] t ∈ Ioo (-1 : ℝ) 1 ∧ P M c p (T (T^[i] t)) = Q M c p ell (T^[i] t) := by
      apply (Filter.eventually_all_finset _).2
      intro i _
      exact ((hitercont i).eventually hmem).and ((hitercont i).eventually hstep)
    filter_upwards [hfinite] with t ht
    constructor
    · intro i hi
      exact (ht i (Finset.mem_range.mpr (by omega))).1
    · intro i hi
      simpa only [Function.iterate_succ_apply', P, Q] using
        (ht i (Finset.mem_range.mpr (by omega))).2
  have hgu : g M ell u = 0 := by dsimp [g, ell]; ring
  have hgd := g_deriv M ell hu
  have hgdpos : 0 < mixtureCurvature M u + entropyCurvature M u := by
    linarith [(ab_pos M hu).1, (ab_pos M hu).2]
  have hgnz : ∀ᶠ t in 𝓝[≠] u, g M ell t ≠ 0 :=
    hgd.eventually_ne (ne_of_gt hgdpos)
  have hnumd : HasDerivAt (fun t => g M ell (T^[N] t))
      ((mixtureCurvature M u + entropyCurvature M u) * curvatureError M c p u ^ N) u := by
    have hg' : HasDerivAt (g M ell) (mixtureCurvature M u + entropyCurvature M u)
        (T^[N] u) := by simpa only [Function.iterate_fixed hTu N] using hgd
    exact hg'.comp u (hiter N)
  have hnumzero : g M ell (T^[N] u) = 0 := by rw [Function.iterate_fixed hTu N, hgu]
  have hlim := (hnumd.tendsto_slope.div hgd.tendsto_slope (ne_of_gt hgdpos)).pow 2
  have hlimit : Tendsto (fun t => |g M ell (T^[N] t)| ^ 2 / |g M ell t| ^ 2)
      (𝓝[≠] u) (𝓝 (|curvatureError M c p u| ^ (2 * N))) := by
    have hlim' : Tendsto (fun t => (slope (fun v => g M ell (T^[N] v)) u t /
        slope (g M ell) u t) ^ 2) (𝓝[≠] u)
        (𝓝 (|curvatureError M c p u| ^ (2 * N))) := by
      simp only [Pi.div_apply] at hlim
      convert hlim using 1 <;> try rfl
      rw [mul_div_cancel_left₀ _ (ne_of_gt hgdpos), ← pow_mul, Nat.mul_comm N 2]
      rw [mul_comm 2 N, pow_mul, ← abs_pow, sq_abs, ← pow_mul]
    apply hlim'.congr'
    filter_upwards [self_mem_nhdsWithin, hgnz] with t ht hgt
    have htu : t - u ≠ 0 := sub_ne_zero.mpr (by simpa only [mem_compl_iff,
      mem_singleton_iff] using ht)
    rw [slope_def_field, slope_def_field, hnumzero, hgu]
    simp only [sub_zero, sq_abs]
    field_simp [htu, hgt]
  apply le_of_tendsto hlimit
  have htraj' : ∀ᶠ t in 𝓝[≠] u, entropyTrajectory M c p ell N (fun i => T^[i] t) :=
    htraj.filter_mono nhdsWithin_le_nhds
  filter_upwards [htraj', hgnz] with t ht hgt
  have hgrad (i : ℕ) (hi : i ≤ N) :
      objectiveGradient M ell (T^[i] t) = g M ell (T^[i] t) :=
    hder M ell _ (ht.1 i hi)
  apply hb
  refine ⟨ell, (fun i => T^[i] t), ht, ?_, ?_⟩
  · simpa only [Function.iterate_zero, id_eq] using
      ((hgrad 0 (by omega)).trans_ne (by simpa using hgt))
  · rw [hgrad N le_rfl, hgrad 0 (by omega)]
    rfl

theorem solution : EntropyDerivativeClaim → ErrorProfileLUBClaim → ExactEntropyPerformanceClaim := by
  intro hder hlub M c p N hv hN
  refine ⟨upper_ratio hder hlub M c p N hv, ?_⟩
  intro b hb
  have hb0 : 0 ≤ b := le_trans (pow_nonneg (abs_nonneg _) _)
    (lower_at_state hder M c p N hv 0 ⟨by norm_num, by norm_num⟩ b hb)
  let root := Real.rpow b ((2 * N : ℕ) : ℝ)⁻¹
  have hroot0 : 0 ≤ root := Real.rpow_nonneg hb0 _
  have hrootpow : root ^ (2 * N) = b := Real.rpow_inv_natCast_pow hb0 (by omega)
  have hrle : contraction M c p ≤ root := by
    apply (hlub M c p hv).2
    rintro v ⟨t, ht, rfl⟩
    by_contra hnot
    have hlt : root < |curvatureError M c p t| := lt_of_not_ge hnot
    have hpow := pow_lt_pow_left₀ hlt hroot0 (by omega : 2 * N ≠ 0)
    rw [hrootpow] at hpow
    have hstate := lower_at_state hder M c p N hv t ⟨by linarith [ht.1], ht.2⟩ b hb
    linarith
  have hr0 : 0 ≤ contraction M c p := le_trans (abs_nonneg _)
    ((hlub M c p hv).1 ⟨0, ⟨by norm_num, by norm_num⟩, rfl⟩)
  simpa only [hrootpow] using pow_le_pow_left₀ hr0 hrle (2 * N)
