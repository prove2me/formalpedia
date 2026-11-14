-- Prove2me | solution 1 for PGDRevision20261113.exact_profile_reduction
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-11-13T10:09:46.724515+00:00
-- url     : https://prove2.me/submissions/66c2bcae-2d75-40b7-80ee-85c3fb11f1af

import Definitions.Def_PGDRevision20261113_Profile
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow

set_option autoImplicit false
set_option maxHeartbeats 2000000
open PGDRevision20261113 Filter Set
open scoped Topology BigOperators ENNReal
noncomputable section

private def implicitSlope (S : ScalarProfile) (p t : ℝ) :=
  p * deriv S.phi t + deriv S.g t

private def forcing (S : ScalarProfile) (p ell t : ℝ) :=
  p * deriv S.phi t - deriv S.f t - ell

private def gradient (S : ScalarProfile) (ell t : ℝ) :=
  deriv S.f t + deriv S.g t + ell

private lemma first_smooth (S : ScalarProfile) (p : ℝ) (hS : AdmissibleProfile S p) :
    ContDiffOn ℝ 1 (deriv S.f) S.domain ∧
    ContDiffOn ℝ 1 (deriv S.g) S.domain ∧
    ContDiffOn ℝ 1 (deriv S.phi) S.domain := by
  rcases hS with ⟨_, ho, _, hf, hg, hk, _⟩
  exact ⟨hf.deriv_of_isOpen ho (by norm_num), hg.deriv_of_isOpen ho (by norm_num),
    hk.deriv_of_isOpen ho (by norm_num)⟩

private lemma second_cont (S : ScalarProfile) (p : ℝ) (hS : AdmissibleProfile S p) :
    ContinuousOn (lossCurvature S) S.domain ∧
    ContinuousOn (penaltyCurvature S) S.domain ∧
    ContinuousOn (generatorCurvature S) S.domain := by
  obtain ⟨hf, hg, hk⟩ := first_smooth S p hS
  exact ⟨hf.continuousOn_deriv_of_isOpen hS.2.1 (by norm_num),
    hg.continuousOn_deriv_of_isOpen hS.2.1 (by norm_num),
    hk.continuousOn_deriv_of_isOpen hS.2.1 (by norm_num)⟩

private lemma derivative_data (S : ScalarProfile) (p : ℝ) (hS : AdmissibleProfile S p)
    (t : ℝ) (ht : t ∈ S.domain) :
    HasDerivAt (deriv S.f) (lossCurvature S t) t ∧
    HasDerivAt (deriv S.g) (penaltyCurvature S t) t ∧
    HasDerivAt (deriv S.phi) (generatorCurvature S t) t := by
  obtain ⟨hf, hg, hk⟩ := first_smooth S p hS
  exact ⟨((hf.differentiableOn (by norm_num)).differentiableAt
    (hS.2.1.mem_nhds ht)).hasDerivAt,
    ((hg.differentiableOn (by norm_num)).differentiableAt (hS.2.1.mem_nhds ht)).hasDerivAt,
    ((hk.differentiableOn (by norm_num)).differentiableAt (hS.2.1.mem_nhds ht)).hasDerivAt⟩

private lemma implicit_deriv (S : ScalarProfile) (p : ℝ) (hS : AdmissibleProfile S p)
    {t : ℝ} (ht : t ∈ S.domain) :
    HasDerivAt (implicitSlope S p)
      (p * generatorCurvature S t + penaltyCurvature S t) t := by
  obtain ⟨_, hg, hk⟩ := derivative_data S p hS t ht
  exact (hk.const_mul p).add hg

private lemma forcing_deriv (S : ScalarProfile) (p ell : ℝ) (hS : AdmissibleProfile S p)
    {t : ℝ} (ht : t ∈ S.domain) :
    HasDerivAt (forcing S p ell)
      (p * generatorCurvature S t - lossCurvature S t) t := by
  obtain ⟨hf, _, hk⟩ := derivative_data S p hS t ht
  exact ((hk.const_mul p).sub hf).sub_const ell

private lemma gradient_deriv (S : ScalarProfile) (p ell : ℝ) (hS : AdmissibleProfile S p)
    {t : ℝ} (ht : t ∈ S.domain) :
    HasDerivAt (gradient S ell) (lossCurvature S t + penaltyCurvature S t) t := by
  obtain ⟨hf, hg, _⟩ := derivative_data S p hS t ht
  exact (hf.add hg).add_const ell

private lemma objective_deriv (S : ScalarProfile) (p ell : ℝ) (hS : AdmissibleProfile S p)
    {t : ℝ} (ht : t ∈ S.domain) : objectiveDerivative S ell t = gradient S ell t := by
  rcases hS with ⟨_, ho, _, hf, hg, _⟩
  have hfd := (hf.differentiableOn (by norm_num)).differentiableAt (ho.mem_nhds ht)
  have hgd := (hg.differentiableOn (by norm_num)).differentiableAt (ho.mem_nhds ht)
  have hd : HasDerivAt (PGDRevision20261113.objective S ell)
      (deriv S.f t + deriv S.g t + ell) t := by
    convert (hfd.hasDerivAt.add hgd.hasDerivAt).add
      ((hasDerivAt_id t).const_mul ell) using 1 <;> first | rfl | simp [PGDRevision20261113.objective]
  exact hd.deriv

private lemma implicit_pos (S : ScalarProfile) (p : ℝ) (hS : AdmissibleProfile S p)
    {t : ℝ} (ht : t ∈ S.domain) : 0 < p * generatorCurvature S t + penaltyCurvature S t := by
  rcases hS with ⟨_, _, _, _, _, _, hp, hcurv, _⟩
  exact add_pos_of_pos_of_nonneg (mul_pos hp (hcurv t ht).2.2.2) (hcurv t ht).2.1

private lemma pair_ratio_ordered (S : ScalarProfile) (p ell x y : ℝ)
    (hS : AdmissibleProfile S p) (hx : x ∈ S.domain) (hy : y ∈ S.domain) (hxy : x < y) :
    ∃ t ∈ S.domain, (implicitSlope S p x - implicitSlope S p y) * profileError S p t =
      forcing S p ell x - forcing S p ell y := by
  have hsub : Icc x y ⊆ S.domain := hS.2.2.1.out hx hy
  obtain ⟨t, ht, heq⟩ := exists_ratio_hasDerivAt_eq_ratio_slope
    (forcing S p ell) (fun t => p * generatorCurvature S t - lossCurvature S t) hxy
    (fun t ht => (forcing_deriv S p ell hS (hsub ht)).continuousAt.continuousWithinAt)
    (fun t ht => forcing_deriv S p ell hS (hsub ⟨ht.1.le, ht.2.le⟩))
    (implicitSlope S p) (fun t => p * generatorCurvature S t + penaltyCurvature S t)
    (fun t ht => (implicit_deriv S p hS (hsub ht)).continuousAt.continuousWithinAt)
    (fun t ht => implicit_deriv S p hS (hsub ⟨ht.1.le, ht.2.le⟩))
  have htS := hsub ⟨ht.1.le, ht.2.le⟩
  refine ⟨t, htS, ?_⟩
  unfold profileError
  rw [← mul_div_assoc]
  apply (div_eq_iff (ne_of_gt (implicit_pos S p hS htS))).2
  linarith

private lemma one_step (S : ScalarProfile) (p ell x y R : ℝ)
    (hS : AdmissibleProfile S p) (hR : ∀ t ∈ S.domain, |profileError S p t| ≤ R)
    (hx : x ∈ S.domain) (hy : y ∈ S.domain)
    (hu : implicitSlope S p y = forcing S p ell x) :
    |gradient S ell y| ≤ R * |gradient S ell x| := by
  have hrat : ∃ t ∈ S.domain,
      (implicitSlope S p x - implicitSlope S p y) * profileError S p t =
        forcing S p ell x - forcing S p ell y := by
    rcases lt_trichotomy x y with hxy | hxy | hxy
    · exact pair_ratio_ordered S p ell x y hS hx hy hxy
    · subst y
      exact ⟨x, hx, by ring⟩
    · obtain ⟨t, ht, heq⟩ := pair_ratio_ordered S p ell y x hS hy hx hxy
      exact ⟨t, ht, by nlinarith [heq]⟩
  obtain ⟨t, ht, heq⟩ := hrat
  have hgx : gradient S ell x = implicitSlope S p x - implicitSlope S p y := by
    dsimp [implicitSlope, forcing, gradient] at *
    linarith
  have hgy : gradient S ell y = forcing S p ell x - forcing S p ell y := by
    dsimp [implicitSlope, forcing, gradient] at *
    linarith
  rw [hgy, ← heq, abs_mul, ← hgx, mul_comm]
  exact mul_le_mul_of_nonneg_right (hR t ht) (abs_nonneg _)

private lemma upper_ratio (S : ScalarProfile) (p R : ℝ) (N : ℕ)
    (hS : AdmissibleProfile S p) (hR0 : 0 ≤ R)
    (hR : ∀ t ∈ S.domain, |profileError S p t| ≤ R)
    (ell : ℝ) (x : ℕ → ℝ) (htraj : ProfileTrajectory S p ell N x)
    (hg0 : objectiveDerivative S ell (x 0) ≠ 0) :
    |objectiveDerivative S ell (x N)| ^ 2 / |objectiveDerivative S ell (x 0)| ^ 2 ≤
      R ^ (2 * N) := by
  have hg (i : ℕ) (hi : i ≤ N) : objectiveDerivative S ell (x i) = gradient S ell (x i) :=
    objective_deriv S p ell hS (htraj.1 i hi)
  have hbound (i : ℕ) (hi : i ≤ N) :
      |gradient S ell (x i)| ≤ R ^ i * |gradient S ell (x 0)| := by
    induction i with
    | zero => simp
    | succ i ih =>
      have hiN : i < N := by omega
      have hstep := one_step S p ell (x i) (x (i + 1)) R hS hR
        (htraj.1 i (by omega)) (htraj.1 (i + 1) hi) (htraj.2 i hiN)
      calc
        _ ≤ R * |gradient S ell (x i)| := hstep
        _ ≤ R * (R ^ i * |gradient S ell (x 0)|) :=
          mul_le_mul_of_nonneg_left (ih (by omega)) hR0
        _ = _ := by rw [pow_succ]; ring
  have hb := hbound N le_rfl
  have hgnz : gradient S ell (x 0) ≠ 0 := by rwa [hg 0 (by omega)] at hg0
  rw [hg N le_rfl, hg 0 (by omega)]
  apply (div_le_iff₀ (sq_pos_of_ne_zero (abs_ne_zero.mpr hgnz))).2
  have hs := pow_le_pow_left₀ (abs_nonneg (gradient S ell (x N))) hb 2
  simpa only [mul_pow, ← pow_mul, Nat.mul_comm N 2] using hs

private lemma lower_at_state (S : ScalarProfile) (p : ℝ) (N : ℕ)
    (hS : AdmissibleProfile S p) (u : ℝ) (hu : u ∈ S.domain) (b : ℝ)
    (hb : ∀ (ell : ℝ) (x : ℕ → ℝ), ProfileTrajectory S p ell N x →
      objectiveDerivative S ell (x 0) ≠ 0 →
      |objectiveDerivative S ell (x N)| ^ 2 / |objectiveDerivative S ell (x 0)| ^ 2 ≤ b) :
    |profileError S p u| ^ (2 * N) ≤ b := by
  let d := p * generatorCurvature S u + penaltyCurvature S u
  have hd : 0 < d := implicit_pos S p hS hu
  have hmem : ∀ᶠ t in 𝓝 u, t ∈ S.domain := hS.2.1.mem_nhds hu
  have hPs : HasStrictDerivAt (implicitSlope S p) d u := by
    apply hasStrictDerivAt_of_hasDerivAt_of_continuousAt
      (hmem.mono (fun t ht => implicit_deriv S p hS ht))
    exact (continuousAt_const.mul ((second_cont S p hS).2.2.continuousAt
      (hS.2.1.mem_nhds hu))).add
        ((second_cont S p hS).2.1.continuousAt (hS.2.1.mem_nhds hu))
  let ell := -deriv S.f u - deriv S.g u
  let R := hPs.localInverse (implicitSlope S p) d u (ne_of_gt hd)
  let T := fun t => R (forcing S p ell t)
  have hQeq : forcing S p ell u = implicitSlope S p u := by
    dsimp [forcing, implicitSlope, ell]; ring
  have hRu : R (implicitSlope S p u) = u := (hPs.eventually_left_inverse (ne_of_gt hd)).self_of_nhds
  have hTu : T u = u := by dsimp [T]; rw [hQeq, hRu]
  have hTd : HasDerivAt T (profileError S p u) u := by
    have hi := (hPs.to_localInverse (ne_of_gt hd)).hasDerivAt
    have hi' : HasDerivAt R d⁻¹ (forcing S p ell u) := by simpa only [hQeq] using hi
    convert hi'.comp u (forcing_deriv S p ell hS hu) using 1 <;> try rfl
    unfold profileError d
    ring
  have hiter (i : ℕ) : HasDerivAt T^[i] (profileError S p u ^ i) u :=
    HasDerivAt.iterate u hTd hTu i
  have hitercont (i : ℕ) : Tendsto T^[i] (𝓝 u) (𝓝 u) := by
    have hc := (hiter i).continuousAt
    change Tendsto T^[i] (𝓝 u) (𝓝 (T^[i] u)) at hc
    simpa only [Function.iterate_fixed hTu i] using hc
  have hstep : ∀ᶠ t in 𝓝 u, implicitSlope S p (T t) = forcing S p ell t := by
    have hc : Tendsto (forcing S p ell) (𝓝 u) (𝓝 (implicitSlope S p u)) := by
      have hc' := (forcing_deriv S p ell hS hu).continuousAt
      change Tendsto (forcing S p ell) (𝓝 u) (𝓝 (forcing S p ell u)) at hc'
      simpa only [hQeq] using hc'
    exact hc.eventually (hPs.eventually_right_inverse (ne_of_gt hd))
  have htraj : ∀ᶠ t in 𝓝 u, ProfileTrajectory S p ell N (fun i => T^[i] t) := by
    have hfinite : ∀ᶠ t in 𝓝 u, ∀ i ∈ Finset.range (N + 1),
        T^[i] t ∈ S.domain ∧ implicitSlope S p (T (T^[i] t)) = forcing S p ell (T^[i] t) := by
      apply (Filter.eventually_all_finset _).2
      intro i _
      exact ((hitercont i).eventually hmem).and ((hitercont i).eventually hstep)
    filter_upwards [hfinite] with t ht
    constructor
    · intro i hi
      exact (ht i (Finset.mem_range.mpr (by omega))).1
    · intro i hi
      simpa only [Function.iterate_succ_apply', implicitSlope, forcing] using
        (ht i (Finset.mem_range.mpr (by omega))).2
  have hgu : gradient S ell u = 0 := by dsimp [gradient, ell]; ring
  have hgd := gradient_deriv S p ell hS hu
  have hgdpos : 0 < lossCurvature S u + penaltyCurvature S u :=
    (hS.2.2.2.2.2.2.2.1 u hu).2.2.1
  have hgnz : ∀ᶠ t in 𝓝[≠] u, gradient S ell t ≠ 0 :=
    hgd.eventually_ne (ne_of_gt hgdpos)
  have hnumd : HasDerivAt (fun t => gradient S ell (T^[N] t))
      ((lossCurvature S u + penaltyCurvature S u) * profileError S p u ^ N) u := by
    have hg' : HasDerivAt (gradient S ell) (lossCurvature S u + penaltyCurvature S u)
        (T^[N] u) := by simpa only [Function.iterate_fixed hTu N] using hgd
    exact hg'.comp u (hiter N)
  have hnumzero : gradient S ell (T^[N] u) = 0 := by rw [Function.iterate_fixed hTu N, hgu]
  have hlim := (hnumd.tendsto_slope.div hgd.tendsto_slope (ne_of_gt hgdpos)).pow 2
  have hlimit : Tendsto (fun t => |gradient S ell (T^[N] t)| ^ 2 / |gradient S ell t| ^ 2)
      (𝓝[≠] u) (𝓝 (|profileError S p u| ^ (2 * N))) := by
    have hlim' : Tendsto (fun t => (slope (fun v => gradient S ell (T^[N] v)) u t /
        slope (gradient S ell) u t) ^ 2) (𝓝[≠] u)
        (𝓝 (|profileError S p u| ^ (2 * N))) := by
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
  have htraj' : ∀ᶠ t in 𝓝[≠] u, ProfileTrajectory S p ell N (fun i => T^[i] t) :=
    htraj.filter_mono nhdsWithin_le_nhds
  filter_upwards [htraj', hgnz] with t ht hgt
  have hgrad (i : ℕ) (hi : i ≤ N) :
      objectiveDerivative S ell (T^[i] t) = gradient S ell (T^[i] t) :=
    objective_deriv S p ell hS (ht.1 i hi)
  have hnz : objectiveDerivative S ell (T^[0] t) ≠ 0 := by
    simpa only [Function.iterate_zero, id_eq] using
      ((hgrad 0 (by omega)).trans_ne (by simpa using hgt))
  have hbound := hb ell (fun i => T^[i] t) ht hnz
  rwa [hgrad N le_rfl, hgrad 0 (by omega)] at hbound

theorem solution : ExactProfileReductionClaim := by
  intro S p hS N hN
  apply le_antisymm
  · by_cases hrho : profileRho S p = ⊤
    · rw [hrho, ENNReal.top_pow (by omega : 2 * N ≠ 0)]
      exact le_top
    have hR (t : ℝ) (ht : t ∈ S.domain) : |profileError S p t| ≤ (profileRho S p).toReal :=
      (ENNReal.ofReal_le_iff_le_toReal hrho).mp
        (le_iSup_of_le t (le_iSup_of_le ht le_rfl))
    apply sSup_le
    rintro v ⟨ell, x, htraj, hg0, rfl⟩
    have hu := upper_ratio S p (profileRho S p).toReal N hS ENNReal.toReal_nonneg hR ell x htraj hg0
    calc
      _ ≤ ENNReal.ofReal ((profileRho S p).toReal ^ (2 * N)) := ENNReal.ofReal_le_ofReal hu
      _ = _ := by rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hrho]
  · by_cases homega : profileOmega S p N = ⊤
    · rw [homega]
      exact le_top
    let b := (profileOmega S p N).toReal
    have hb0 : 0 ≤ b := ENNReal.toReal_nonneg
    have hb (ell : ℝ) (x : ℕ → ℝ) (htraj : ProfileTrajectory S p ell N x)
        (hg0 : objectiveDerivative S ell (x 0) ≠ 0) :
        |objectiveDerivative S ell (x N)| ^ 2 / |objectiveDerivative S ell (x 0)| ^ 2 ≤ b := by
      apply (ENNReal.ofReal_le_iff_le_toReal homega).mp
      exact le_sSup ⟨ell, x, htraj, hg0, rfl⟩
    let root := Real.rpow b ((2 * N : ℕ) : ℝ)⁻¹
    have hroot0 : 0 ≤ root := Real.rpow_nonneg hb0 _
    have hrootpow : root ^ (2 * N) = b := Real.rpow_inv_natCast_pow hb0 (by omega)
    have hrle : profileRho S p ≤ ENNReal.ofReal root := by
      refine iSup_le fun u => iSup_le fun hu => ENNReal.ofReal_le_ofReal ?_
      by_contra hn
      have hpow := pow_lt_pow_left₀ (lt_of_not_ge hn) hroot0 (by omega : 2 * N ≠ 0)
      rw [hrootpow] at hpow
      have hstate := lower_at_state S p N hS u hu b hb
      linarith
    calc
      _ ≤ ENNReal.ofReal root ^ (2 * N) := by gcongr
      _ = ENNReal.ofReal b := by rw [← ENNReal.ofReal_pow hroot0, hrootpow]
      _ = _ := ENNReal.ofReal_toReal homega
