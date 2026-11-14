-- Prove2me | solution 1 for PGDRevision20261113.polynomial_matched_geometry_examples
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-11-13T11:03:14.037274+00:00
-- url     : https://prove2.me/submissions/7f2df80c-6945-4e3b-8295-18c59d0b784d

import Theorems.Thm_PGDRevision20261113_polynomial_penalty_models
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_PGDRevision20261113_Examples
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
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

private def LocalProfile (P : ScalarProfile) (p : ℝ) : Prop :=
  P.domain.Nonempty ∧ IsOpen P.domain ∧ Set.OrdConnected P.domain ∧
  ContDiffOn ℝ 2 P.f P.domain ∧ ContDiffOn ℝ 2 P.g P.domain ∧
  ContDiffOn ℝ 2 P.phi P.domain ∧ 0 < p ∧
  (∀ t ∈ P.domain, 0 ≤ lossCurvature P t ∧ 0 ≤ penaltyCurvature P t ∧
    0 < lossCurvature P t + penaltyCurvature P t ∧ 0 < generatorCurvature P t) ∧
  True

private def implicitSlope (S : ScalarProfile) (p t : ℝ) :=
  p * deriv S.phi t + deriv S.g t

private def forcing (S : ScalarProfile) (p ell t : ℝ) :=
  p * deriv S.phi t - deriv S.f t - ell

private def gradient (S : ScalarProfile) (ell t : ℝ) :=
  deriv S.f t + deriv S.g t + ell

private lemma first_smooth (S : ScalarProfile) (p : ℝ) (hS : LocalProfile S p) :
    ContDiffOn ℝ 1 (deriv S.f) S.domain ∧
    ContDiffOn ℝ 1 (deriv S.g) S.domain ∧
    ContDiffOn ℝ 1 (deriv S.phi) S.domain := by
  rcases hS with ⟨_, ho, _, hf, hg, hk, _⟩
  exact ⟨hf.deriv_of_isOpen ho (by norm_num), hg.deriv_of_isOpen ho (by norm_num),
    hk.deriv_of_isOpen ho (by norm_num)⟩

private lemma second_cont (S : ScalarProfile) (p : ℝ) (hS : LocalProfile S p) :
    ContinuousOn (lossCurvature S) S.domain ∧
    ContinuousOn (penaltyCurvature S) S.domain ∧
    ContinuousOn (generatorCurvature S) S.domain := by
  obtain ⟨hf, hg, hk⟩ := first_smooth S p hS
  exact ⟨hf.continuousOn_deriv_of_isOpen hS.2.1 (by norm_num),
    hg.continuousOn_deriv_of_isOpen hS.2.1 (by norm_num),
    hk.continuousOn_deriv_of_isOpen hS.2.1 (by norm_num)⟩

private lemma derivative_data (S : ScalarProfile) (p : ℝ) (hS : LocalProfile S p)
    (t : ℝ) (ht : t ∈ S.domain) :
    HasDerivAt (deriv S.f) (lossCurvature S t) t ∧
    HasDerivAt (deriv S.g) (penaltyCurvature S t) t ∧
    HasDerivAt (deriv S.phi) (generatorCurvature S t) t := by
  obtain ⟨hf, hg, hk⟩ := first_smooth S p hS
  exact ⟨((hf.differentiableOn (by norm_num)).differentiableAt
    (hS.2.1.mem_nhds ht)).hasDerivAt,
    ((hg.differentiableOn (by norm_num)).differentiableAt (hS.2.1.mem_nhds ht)).hasDerivAt,
    ((hk.differentiableOn (by norm_num)).differentiableAt (hS.2.1.mem_nhds ht)).hasDerivAt⟩

private lemma implicit_deriv (S : ScalarProfile) (p : ℝ) (hS : LocalProfile S p)
    {t : ℝ} (ht : t ∈ S.domain) :
    HasDerivAt (implicitSlope S p)
      (p * generatorCurvature S t + penaltyCurvature S t) t := by
  obtain ⟨_, hg, hk⟩ := derivative_data S p hS t ht
  exact (hk.const_mul p).add hg

private lemma forcing_deriv (S : ScalarProfile) (p ell : ℝ) (hS : LocalProfile S p)
    {t : ℝ} (ht : t ∈ S.domain) :
    HasDerivAt (forcing S p ell)
      (p * generatorCurvature S t - lossCurvature S t) t := by
  obtain ⟨hf, _, hk⟩ := derivative_data S p hS t ht
  exact ((hk.const_mul p).sub hf).sub_const ell

private lemma gradient_deriv (S : ScalarProfile) (p ell : ℝ) (hS : LocalProfile S p)
    {t : ℝ} (ht : t ∈ S.domain) :
    HasDerivAt (gradient S ell) (lossCurvature S t + penaltyCurvature S t) t := by
  obtain ⟨hf, hg, _⟩ := derivative_data S p hS t ht
  exact (hf.add hg).add_const ell

private lemma objective_deriv (S : ScalarProfile) (p ell : ℝ) (hS : LocalProfile S p)
    {t : ℝ} (ht : t ∈ S.domain) : objectiveDerivative S ell t = gradient S ell t := by
  rcases hS with ⟨_, ho, _, hf, hg, _⟩
  have hfd := (hf.differentiableOn (by norm_num)).differentiableAt (ho.mem_nhds ht)
  have hgd := (hg.differentiableOn (by norm_num)).differentiableAt (ho.mem_nhds ht)
  have hd : HasDerivAt (PGDRevision20261113.objective S ell)
      (deriv S.f t + deriv S.g t + ell) t := by
    convert (hfd.hasDerivAt.add hgd.hasDerivAt).add
      ((hasDerivAt_id t).const_mul ell) using 1 <;> first | rfl | simp [PGDRevision20261113.objective]
  exact hd.deriv

private lemma implicit_pos (S : ScalarProfile) (p : ℝ) (hS : LocalProfile S p)
    {t : ℝ} (ht : t ∈ S.domain) : 0 < p * generatorCurvature S t + penaltyCurvature S t := by
  rcases hS with ⟨_, _, _, _, _, _, hp, hcurv, _⟩
  exact add_pos_of_pos_of_nonneg (mul_pos hp (hcurv t ht).2.2.2) (hcurv t ht).2.1

private lemma pair_ratio_ordered (S : ScalarProfile) (p ell x y : ℝ)
    (hS : LocalProfile S p) (hx : x ∈ S.domain) (hy : y ∈ S.domain) (hxy : x < y) :
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
    (hS : LocalProfile S p) (hR : ∀ t ∈ S.domain, |profileError S p t| ≤ R)
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
    (hS : LocalProfile S p) (hR0 : 0 ≤ R)
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
    (hS : LocalProfile S p) (u : ℝ) (hu : u ∈ S.domain) (b : ℝ)
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

private lemma exact_local_profile (S : ScalarProfile) (p : Real) (hS : LocalProfile S p)
    (N : Nat) (hN : 1 ≤ N) : profileOmega S p N = profileRho S p ^ (2 * N) := by
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

private lemma local_primitive (I : Set ℝ) (ho : IsOpen I) (hc : I.OrdConnected)
    (h0 : (0 : ℝ) ∈ I) (a : ℝ → ℝ) (ha : ContinuousOn a I) (x : ℝ) (hx : x ∈ I) :
    HasDerivAt (primitive a) (a x) x := by
  have hsub : Set.uIcc (0 : ℝ) x ⊆ I := hc.uIcc_subset h0 hx
  exact intervalIntegral.integral_hasDerivAt_right ((ha.mono hsub).intervalIntegrable)
    (ContinuousOn.stronglyMeasurableAtFilter ho ha x hx) (ha.continuousAt (ho.mem_nhds hx))

private lemma local_double (I : Set ℝ) (ho : IsOpen I) (hc : I.OrdConnected)
    (h0 : (0 : ℝ) ∈ I) (a : ℝ → ℝ) (ha : ContinuousOn a I) :
    ContDiffOn ℝ 2 (doublePrimitive a) I ∧
    ∀ x ∈ I, deriv (deriv (doublePrimitive a)) x = a x := by
  have hpd : DifferentiableOn ℝ (primitive a) I :=
    fun x hx => (local_primitive I ho hc h0 a ha x hx).differentiableAt.differentiableWithinAt
  have hpc : ContinuousOn (primitive a) I := hpd.continuousOn
  have hpe : ∀ x ∈ I, deriv (primitive a) x = a x := fun x hx => (local_primitive I ho hc h0 a ha x hx).deriv
  have hpc1 : ContDiffOn ℝ 1 (primitive a) I := by
    change ContDiffOn ℝ (0 + 1) (primitive a) I
    apply (contDiffOn_succ_iff_deriv_of_isOpen ho).mpr
    refine ⟨hpd, by norm_num, ?_⟩
    rw [contDiffOn_zero]
    exact ha.congr (fun x hx => hpe x hx)
  have hdd : DifferentiableOn ℝ (doublePrimitive a) I :=
    fun x hx => (local_primitive I ho hc h0 _ hpc x hx).differentiableAt.differentiableWithinAt
  have hde : ∀ x ∈ I, deriv (doublePrimitive a) x = primitive a x :=
    fun x hx => (local_primitive I ho hc h0 _ hpc x hx).deriv
  constructor
  · change ContDiffOn ℝ (1 + 1) (doublePrimitive a) I
    apply (contDiffOn_succ_iff_deriv_of_isOpen ho).mpr
    exact ⟨hdd, by norm_num, hpc1.congr (fun x hx => hde x hx)⟩
  · intro x hx
    have hmem : ∀ᶠ t in nhds x, t ∈ I := ho.mem_nhds hx
    have he : deriv (doublePrimitive a) =ᶠ[nhds x] primitive a :=
      hmem.mono fun t ht => hde t ht
    exact he.deriv_eq.trans (hpe x hx)

private lemma geometry_kernel_cont (G : GeometryData) (hG : AdmissibleGeometry G) (c : ℝ) :
    ContinuousOn (geometryKernel G c) (geometryDomain G) ∧
    ∀ t ∈ geometryDomain G, 0 < geometryKernel G c t := by
  cases hf : G.family with
  | interval beta =>
    constructor
    · intro t ht
      have htd : t ∈ Set.Ioo (-1 : ℝ) 1 := by simpa [geometryDomain, hf] using ht
      have hp := (continuousAt_const.add continuousAt_id).rpow_const
        (Or.inl (ne_of_gt (by linarith [htd.1]) : 1 + t ≠ 0) : 1 + t ≠ 0 ∨ 0 ≤ -c)
      have hm := (continuousAt_const.sub continuousAt_id).rpow_const
        (Or.inl (ne_of_gt (by linarith [htd.2]) : 1 - t ≠ 0) : 1 - t ≠ 0 ∨ 0 ≤ -c)
      have heq : geometryKernel G c = fun t => ((1 + t) ^ (-c) + (1 - t) ^ (-c)) / 2 := by
        funext t; simp only [geometryKernel, hf, powerCurvature, Real.rpow_eq_pow]
      rw [heq]
      exact ((hp.add hm).div_const 2).continuousWithinAt
    · intro t ht
      have htd : t ∈ Set.Ioo (-1 : ℝ) 1 := by simpa [geometryDomain, hf] using ht
      simp only [geometryKernel, hf, powerCurvature]
      exact div_pos (add_pos (Real.rpow_pos_of_pos (by linarith [htd.1]) _)
        (Real.rpow_pos_of_pos (by linarith [htd.2]) _)) (by norm_num)
  | realLine =>
    have hgf := hG.2.2.2.2
    simp only [hf] at hgf
    have hb (t : ℝ) : 0 < G.b t := by
      by_cases ht : t = 0
      · subst t; rw [hgf.2.2.1]; norm_num
      · linarith [hgf.2.2.2.1 t ht]
    constructor
    · intro t _
      have heq : geometryKernel G c = fun t => (G.b t) ^ c := by
        funext t; simp only [geometryKernel, hf, Real.rpow_eq_pow]
      rw [heq]
      exact (hgf.2.1.continuous.continuousAt.rpow_const
        (Or.inl (hb t).ne' : G.b t ≠ 0 ∨ 0 ≤ c)).continuousWithinAt
    · intro t _
      simpa [geometryKernel, hf] using Real.rpow_pos_of_pos (hb t) c

private lemma geometry_local_data (G : GeometryData) (hG : AdmissibleGeometry G) (c p : ℝ)
    (hp : 0 < p) : LocalProfile (geometryProfile G c) p ∧
    profileRho (geometryProfile G c) p = geometryRho G c p := by
  have h0 : (0 : ℝ) ∈ geometryDomain G := by
    cases hf : G.family <;> norm_num [geometryDomain, hf]
  have ho : IsOpen (geometryDomain G) := by
    cases hf : G.family with
    | interval beta => simpa only [geometryDomain, hf] using (isOpen_Ioo : IsOpen (Set.Ioo (-1 : ℝ) 1))
    | realLine => simpa only [geometryDomain, hf] using (isOpen_univ : IsOpen (Set.univ : Set ℝ))
  have hc : (geometryDomain G).OrdConnected := by
    cases hf : G.family with
    | interval beta => simpa only [geometryDomain, hf] using (Set.ordConnected_Ioo : (Set.Ioo (-1 : ℝ) 1).OrdConnected)
    | realLine => simpa only [geometryDomain, hf] using (Set.ordConnected_univ : (Set.univ : Set ℝ).OrdConnected)
  have hA : ContinuousOn G.A (geometryDomain G) := by
    have hgf := hG.2.2.2.2
    cases hf : G.family with
    | interval beta =>
      simp only [hf] at hgf
      apply hgf.2.2.1.mono
      simpa only [geometryDomain, hf] using (Set.Ioo_subset_Icc_self : Set.Ioo (-1 : ℝ) 1 ⊆ Set.Icc (-1 : ℝ) 1)
    | realLine =>
      simp only [hf] at hgf
      exact hgf.1.continuous.continuousOn
  have hb : ContinuousOn G.b (geometryDomain G) := by
    have hk := (geometry_kernel_cont G hG (matchedExponent G)).1
    have he : ∀ t ∈ geometryDomain G, geometryKernel G (matchedExponent G) t = G.b t := by
      intro t ht
      have hgf := hG.2.2.2.2
      cases hf : G.family with
      | interval beta =>
        simp only [hf] at hgf
        simpa only [geometryKernel, matchedExponent, hf] using (hgf.2.1 t ht).symm
      | realLine => simp [geometryKernel, matchedExponent, hf, Real.rpow_eq_pow]
    exact hk.congr (fun t ht => (he t ht).symm)
  obtain ⟨hfd, hfc⟩ := local_double _ ho hc h0 _ hA
  obtain ⟨hgd, hgc⟩ := local_double _ ho hc h0 (fun t => G.lambda * G.b t) (continuousOn_const.mul hb)
  obtain ⟨hkd, hkc⟩ := local_double _ ho hc h0 _ (geometry_kernel_cont G hG c).1
  have hB (t : ℝ) (ht : t ∈ geometryDomain G) : 0 < G.lambda * G.b t := by
    have hpos := (geometry_kernel_cont G hG (matchedExponent G)).2 t ht
    have hgf := hG.2.2.2.2
    cases hf : G.family with
    | interval beta =>
      simp only [hf] at hgf
      rw [hgf.2.1 t ht]
      exact mul_pos hG.1 (by simpa only [geometryKernel, matchedExponent, hf] using hpos)
    | realLine =>
      have hbpos : 0 < G.b t := by simpa [geometryKernel, matchedExponent, hf, Real.rpow_eq_pow] using hpos
      exact mul_pos hG.1 hbpos
  have hcurvs (t : ℝ) (ht : t ∈ geometryDomain G) :
      lossCurvature (geometryProfile G c) t = G.A t ∧
      penaltyCurvature (geometryProfile G c) t = G.lambda * G.b t ∧
      generatorCurvature (geometryProfile G c) t = geometryKernel G c t :=
    ⟨hfc t ht, hgc t ht, hkc t ht⟩
  constructor
  · refine ⟨⟨0, h0⟩, ho, hc, hfd, hgd, hkd, hp, ?_, trivial⟩
    intro t ht
    obtain ⟨hfa, hga, hka⟩ := hcurvs t ht
    rw [hfa, hga, hka]
    exact ⟨hG.2.1 t ht, (hB t ht).le,
      add_pos_of_nonneg_of_pos (hG.2.1 t ht) (hB t ht), (geometry_kernel_cont G hG c).2 t ht⟩
  · apply iSup_congr
    intro t
    apply iSup_congr
    intro ht
    obtain ⟨hfa, hga, hka⟩ := hcurvs t ht
    simp only [profileError, geometryError, hfa, hga, hka]

private lemma geometry_exact (G : GeometryData) (hG : AdmissibleGeometry G) (c p : ℝ)
    (hp : 0 < p) (N : ℕ) (hN : 1 ≤ N) :
    geometryOmega G (c, p) N = geometryRho G c p ^ (2 * N) := by
  obtain ⟨hlocal, hrho⟩ := geometry_local_data G hG c p hp
  exact (exact_local_profile _ p hlocal N hN).trans (by rw [hrho])

private lemma exact_example (G : GeometryData) (hG : AdmissibleGeometry G) (c p r : ℝ)
    (henv : UniformGeometryEnvelope G (c, p) r)
    (hrho : geometryRho G c p = ENNReal.ofReal r) (hopt : GeometryOptimum G (c, p))
    (huniq : ∀ z, GeometryOptimum G z → z = (c, p)) : ExactGeometryExample G c p r := by
  refine ⟨hG, henv, hrho, hopt, huniq, ?_⟩
  intro N hN
  refine ⟨by rw [geometry_exact G hG c p hopt.1.2 N hN, hrho], ?_⟩
  intro z hz
  have hez := geometry_exact G hG z.1 z.2 hz.2 N hN
  have hec := geometry_exact G hG c p hopt.1.2 N hN
  rw [hez, hec]
  refine ⟨by gcongr; exact hopt.2 z hz, ?_⟩
  intro he
  have hcf : geometryRho G c p ≠ ⊤ := by rw [hrho]; exact ENNReal.ofReal_ne_top
  have hzf : geometryRho G z.1 z.2 ≠ ⊤ := by
    intro ht
    have hfinite := ENNReal.pow_ne_top (n := 2 * N) hcf
    rw [ht, ENNReal.top_pow (by omega : 2 * N ≠ 0)] at he
    exact hfinite he.symm
  have her := congrArg ENNReal.toReal he
  simp only [ENNReal.toReal_pow] at her
  have hreal : (geometryRho G z.1 z.2).toReal = (geometryRho G c p).toReal :=
    (pow_left_inj₀ ENNReal.toReal_nonneg ENNReal.toReal_nonneg (by omega : 2 * N ≠ 0)).mp her
  have hr : geometryRho G z.1 z.2 = geometryRho G c p := by
    rw [← ENNReal.ofReal_toReal hzf, ← ENNReal.ofReal_toReal hcf, hreal]
  apply huniq z
  refine ⟨hz, fun w hw => ?_⟩
  rw [hr]
  exact hopt.2 w hw
private lemma penalty_range (G : GeometryData) (hG : AdmissibleGeometry G)
    (hf : G.family = .realLine) :
    (∀ x : ℝ, 1 ≤ G.b x) ∧ (∀ s : ℝ, 1 ≤ s → ∃ x : ℝ, G.b x = s) := by
  rcases hG with ⟨_, _, _, _, hG⟩
  simp only [hf] at hG
  rcases hG with ⟨_, hb, hb0, hb1, _, _, htail⟩
  constructor
  · intro x
    by_cases hx : x = 0
    · subst x
      exact hb0.ge
    · exact (hb1 x hx).le
  · intro s hs
    obtain ⟨R, hR, hbound⟩ := htail s
    have hbR : s ≤ G.b R := hbound R (by rw [abs_of_pos hR])
    have hbs : s ∈ Set.Icc (G.b 0) (G.b R) := ⟨by rwa [hb0], hbR⟩
    obtain ⟨x, _, hx⟩ := intermediate_value_Icc hR.le hb.continuous.continuousOn hbs
    exact ⟨x, hx⟩

private lemma error_bound (G : GeometryData) (w : ℝ × ℝ) (r : ℝ) (hr : 0 ≤ r)
    (hw : geometryRho G w.1 w.2 ≤ ENNReal.ofReal r)
    (t : ℝ) (ht : t ∈ geometryDomain G) : |geometryError G w.1 w.2 t| ≤ r := by
  have hs : ENNReal.ofReal |geometryError G w.1 w.2 t| ≤ geometryRho G w.1 w.2 :=
    le_iSup_of_le t (le_iSup_of_le ht le_rfl)
  exact (ENNReal.ofReal_le_ofReal_iff hr).mp (hs.trans hw)

private lemma poly_matched_model (b : ℝ → ℝ) (hb : b ∈ ({polynomialB1, polynomialB2} : Set (ℝ → ℝ))) :
    AdmissibleGeometry (realLineExample b (fun s => 1 - 1 / s) 1) := by
  have hbase := (PGDRevision20261113.polynomial_penalty_models 1 (by norm_num)).2.2.2.2 b hb
  obtain ⟨hbge, hsurj⟩ := penalty_range _ hbase rfl
  change ∀ x : ℝ, 1 ≤ b x at hbge
  obtain ⟨q, hq⟩ := hsurj 2 (by norm_num)
  have hq2 : b q = 2 := hq
  have hfam := hbase.2.2.2.2
  simp only [realLineExample] at hfam
  have hbp (x : ℝ) : 0 < b x := lt_of_lt_of_le (by norm_num) (hbge x)
  refine ⟨by norm_num [realLineExample], ?_, ?_, ?_, ?_⟩
  · intro t _
    change 0 ≤ 1 - 1 / b t
    have hh : 1 / b t ≤ 1 := (div_le_iff₀ (hbp t)).mpr (by simpa using hbge t)
    linarith
  · refine ⟨1, ?_⟩
    rintro v ⟨t, _, rfl⟩
    change 1 - 1 / b t ≤ 1
    have hh : 0 ≤ 1 / b t := (one_div_pos.mpr (hbp t)).le
    linarith
  · exact ⟨q, Set.mem_univ _, by norm_num [realLineExample, hq2]⟩
  · refine ⟨?_, hfam.2⟩
    exact contDiff_const.sub (contDiff_const.div hfam.2.1 (fun x => (hbp x).ne'))

private lemma poly_matched_error (b : ℝ → ℝ) (x : ℝ) (hb : 1 ≤ b x) :
    geometryError (realLineExample b (fun s => 1 - 1 / s) 1) 1 (1 / 8) x =
      (b x ^ 2 - 8 * b x + 8) / (9 * b x ^ 2) := by
  have hbp : 0 < b x := by linarith
  simp only [geometryError, geometryKernel, realLineExample, Real.rpow_eq_pow, Real.rpow_one, one_mul]
  field_simp
  <;> ring

theorem solution : PolynomialMatchedExamplesClaim := by
  intro b hb
  let G := realLineExample b (fun s => 1 - 1 / s) 1
  have hG : AdmissibleGeometry G := poly_matched_model b hb
  obtain ⟨hbge, hsurj⟩ := penalty_range G hG rfl
  change ∀ x : ℝ, 1 ≤ b x at hbge
  obtain ⟨q, hq⟩ := hsurj 2 (by norm_num)
  have hq2 : b q = 2 := hq
  have hfam := hG.2.2.2.2
  simp only [G, realLineExample] at hfam
  have hb0 : b 0 = 1 := hfam.2.2.1
  have henv : UniformGeometryEnvelope G (1, 1 / 8) (1 / 9) := by
    intro t ht
    rw [poly_matched_error b t (hbge t)]
    have hp : 0 < b t := by linarith [hbge t]
    have hd : 0 < 9 * b t ^ 2 := by positivity
    rw [abs_le]
    constructor
    · apply (le_div_iff₀ hd).mpr
      nlinarith [sq_nonneg (b t - 2)]
    · apply (div_le_iff₀ hd).mpr
      nlinarith [hbge t]
  have he0 : geometryError G 1 (1 / 8) 0 = 1 / 9 := by
    rw [poly_matched_error b 0 (hbge 0), hb0]; norm_num
  have heq : geometryError G 1 (1 / 8) q = -(1 / 9) := by
    rw [poly_matched_error b q (hbge q), hq2]; norm_num
  have hrho : geometryRho G 1 (1 / 8) = ENNReal.ofReal (1 / 9) := by
    apply le_antisymm
    · exact iSup_le fun t => iSup_le fun ht => ENNReal.ofReal_le_ofReal (henv t ht)
    · have habs : |geometryError G 1 (1 / 8) 0| = 1 / 9 := by rw [he0]; norm_num
      rw [← habs]
      exact le_iSup_of_le 0 (le_iSup_of_le (Set.mem_univ _) le_rfl)
  have hcompetitor (w : ℝ × ℝ) (hw : FeasiblePair w)
      (hwr : geometryRho G w.1 w.2 ≤ ENNReal.ofReal (1 / 9)) : w = (1, 1 / 8) := by
    have hpw : 0 < w.2 := hw.2
    have h0 := (abs_le.mp (error_bound G w (1 / 9) (by norm_num) hwr 0 (Set.mem_univ _))).2
    have h00 : geometryError G w.1 w.2 0 = w.2 / (w.2 + 1) := by
      norm_num [geometryError, geometryKernel, G, realLineExample, hb0, Real.rpow_eq_pow]
    rw [h00] at h0
    have hpu : w.2 ≤ 1 / 8 := by
      have hd : 0 < w.2 + 1 := by linarith [hw.2]
      have hh := (div_le_iff₀ hd).mp h0
      linarith
    have hk : 0 < geometryKernel G w.1 q := (geometry_kernel_cont G hG w.1).2 q (Set.mem_univ _)
    have hqerr : geometryError G w.1 w.2 q =
        (w.2 * geometryKernel G w.1 q - 1 / 2) / (w.2 * geometryKernel G w.1 q + 2) := by
      unfold geometryError
      change (w.2 * geometryKernel G w.1 q - (1 - 1 / b q)) /
        (w.2 * geometryKernel G w.1 q + 1 * b q) = _
      rw [hq2]; norm_num
    have hql := (abs_le.mp (error_bound G w (1 / 9) (by norm_num) hwr q (Set.mem_univ _))).1
    rw [hqerr] at hql
    have hv : 1 / 4 ≤ w.2 * geometryKernel G w.1 q := by
      have hd : 0 < w.2 * geometryKernel G w.1 q + 2 := by positivity
      have hh := (le_div_iff₀ hd).mp hql
      linarith
    have hcge : 1 ≤ w.1 := by
      by_contra hn
      have hcw : w.1 < 1 := lt_of_not_ge hn
      have hm := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : 1 < (2 : ℝ)) hcw
      have hk2 : geometryKernel G w.1 q < 2 := by
        simpa [geometryKernel, G, realLineExample, hq2, Real.rpow_eq_pow] using hm
      have hh := mul_lt_mul_of_pos_left hk2 hw.2
      nlinarith
    have hcle : w.1 ≤ 1 := by
      by_contra hn
      have hcw : 1 < w.1 := lt_of_not_ge hn
      let alpha := w.1 - 1
      let K := 100 / w.2 + 1
      let M := Real.rpow K alpha⁻¹
      have ha : 0 < alpha := by dsimp [alpha]; linarith
      have hK : 0 < K := by dsimp [K]; positivity
      have hM : 0 < M := Real.rpow_pos_of_pos hK _
      have hMpow : Real.rpow M alpha = K := by
        simp only [M, Real.rpow_eq_pow]
        exact Real.rpow_inv_rpow hK.le ha.ne'
      obtain ⟨t, ht⟩ := hsurj (M + 1) (by linarith)
      have hbt : b t = M + 1 := ht
      have hbtp : 0 < b t := by linarith [hbge t]
      have hraise : K ≤ Real.rpow (b t) alpha := by
        rw [← hMpow]
        simp only [Real.rpow_eq_pow]
        exact Real.rpow_le_rpow hM.le (by rw [hbt]; linarith) ha.le
      have hkt : 0 < geometryKernel G w.1 t := (geometry_kernel_cont G hG w.1).2 t (Set.mem_univ _)
      have het := (abs_le.mp (error_bound G w (1 / 9) (by norm_num) hwr t (Set.mem_univ _))).2
      change (w.2 * Real.rpow (b t) w.1 - (1 - 1 / b t)) /
        (w.2 * Real.rpow (b t) w.1 + 1 * b t) ≤ 1 / 9 at het
      have hden : 0 < w.2 * Real.rpow (b t) w.1 + 1 * b t := by
        have hkpos := Real.rpow_pos_of_pos hbtp w.1
        positivity
      have hh := (div_le_iff₀ hden).mp het
      have hinv : 0 ≤ 1 / b t := (one_div_pos.mpr hbtp).le
      have hbound : 8 * w.2 * Real.rpow (b t) w.1 ≤ 10 * b t := by
        nlinarith [hbge t]
      have hdisc : 8 * w.2 * Real.rpow (b t) alpha ≤ 10 := by
        have hid : 8 * w.2 * Real.rpow (b t) alpha =
            (8 * w.2 * Real.rpow (b t) w.1) / b t := by
          simp only [alpha, Real.rpow_eq_pow]
          rw [Real.rpow_sub_one hbtp.ne']
          ring
        rw [hid]
        exact (div_le_iff₀ hbtp).mpr hbound
      have hpk : w.2 * K = 100 + w.2 := by dsimp [K]; field_simp [hpw.ne'] <;> ring
      have hm := mul_le_mul_of_nonneg_left hraise (by linarith [hw.2] : 0 ≤ 8 * w.2)
      nlinarith [hw.2]
    have hc : w.1 = 1 := le_antisymm hcle hcge
    have hp : w.2 = 1 / 8 := by
      rw [hc] at hv
      have hk1 : geometryKernel G 1 q = 2 := by
        simp [geometryKernel, G, realLineExample, hq2, Real.rpow_eq_pow]
      rw [hk1] at hv
      linarith
    exact Prod.ext hc hp
  have hopt : GeometryOptimum G (1, 1 / 8) := by
    refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
    intro w hw
    by_contra hn
    have hh := (lt_of_not_ge hn).le
    rw [hrho] at hh
    have hwz := hcompetitor w hw hh
    subst w
    exact hn le_rfl
  apply exact_example G hG 1 (1 / 8) (1 / 9) henv hrho hopt
  intro w hw
  apply hcompetitor w hw.1
  exact (hw.2 (1, 1 / 8) hopt.1).trans_eq hrho

