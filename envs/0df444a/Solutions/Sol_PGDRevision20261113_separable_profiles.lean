-- Prove2me | solution 1 for PGDRevision20261113.separable_profiles
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-11-13T10:12:06.351851+00:00
-- url     : https://prove2.me/submissions/d98923ea-5fbe-4fed-a539-a556d653ff57

import Theorems.Thm_PGDRevision20261113_exact_profile_reduction
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

private lemma implicit_injective (S : ScalarProfile) (p : ℝ) (hS : AdmissibleProfile S p) :
    Set.InjOn (implicitSlope S p) S.domain := by
  apply StrictMonoOn.injOn
  apply strictMonoOn_of_deriv_pos hS.2.2.1.convex
  · intro t ht
    exact (implicit_deriv S p hS ht).continuousAt.continuousWithinAt
  · intro t ht
    have htd : t ∈ S.domain := interior_subset ht
    rw [(implicit_deriv S p hS htd).deriv]
    exact implicit_pos S p hS htd

private lemma zero_preserved (S : ScalarProfile) (p ell : ℝ) (N : ℕ)
    (hS : AdmissibleProfile S p) (x : ℕ → ℝ) (hx : ProfileTrajectory S p ell N x)
    (hz : objectiveDerivative S ell (x 0) = 0) : objectiveDerivative S ell (x N) = 0 := by
  have hfixed (i : ℕ) (hi : i ≤ N) : x i = x 0 := by
    induction i with
    | zero => rfl
    | succ i ih =>
      have hiN : i < N := by omega
      have heq := ih (by omega)
      have hzero : gradient S ell (x i) = 0 := by
        rw [heq, ← objective_deriv S p ell hS (hx.1 0 (by omega))]
        exact hz
      have hstep := hx.2 i hiN
      have hp : implicitSlope S p (x (i + 1)) = implicitSlope S p (x i) := by
        dsimp [implicitSlope, gradient] at *
        linarith
      exact (implicit_injective S p hS (hx.1 (i + 1) hi) (hx.1 i (by omega)) hp).trans heq
  rw [hfixed N le_rfl]
  exact hz

private lemma stationary_trajectory (S : ScalarProfile) (p : ℝ) (hS : AdmissibleProfile S p)
    (u : ℝ) (hu : u ∈ S.domain) (N : ℕ) :
    ProfileTrajectory S p (-deriv S.f u - deriv S.g u) N (fun _ => u) ∧
      objectiveDerivative S (-deriv S.f u - deriv S.g u) u = 0 := by
  constructor
  · exact ⟨fun _ _ => hu, fun _ _ => by ring⟩
  · rw [objective_deriv S p _ hS hu]
    unfold gradient
    ring

theorem solution : SeparableProfilesClaim := by
  classical
  intro d hd S p hS N hN
  let Q : ℝ≥0∞ := ⨆ j, profileRho (S j) p ^ (2 * N)
  apply le_antisymm
  · by_cases hQ : Q = ⊤
    · change _ ≤ Q
      rw [hQ]
      exact le_top
    apply sSup_le
    rintro v ⟨ell, x, hx, hnz, rfl⟩
    have hcoord (j : Fin d) :
        |objectiveDerivative (S j) (ell j) (x N j)| ^ 2 ≤
          Q.toReal * |objectiveDerivative (S j) (ell j) (x 0 j)| ^ 2 := by
      by_cases hz : objectiveDerivative (S j) (ell j) (x 0 j) = 0
      · have hlast := zero_preserved (S j) p (ell j) N (hS j) (fun i => x i j) (hx j) hz
        rw [hz, hlast]
        simp
      · have hperf : ENNReal.ofReal
            (|objectiveDerivative (S j) (ell j) (x N j)| ^ 2 /
              |objectiveDerivative (S j) (ell j) (x 0 j)| ^ 2) ≤ Q := by
          calc
            _ ≤ profileOmega (S j) p N := le_sSup ⟨ell j, (fun i => x i j), hx j, hz, rfl⟩
            _ = profileRho (S j) p ^ (2 * N) :=
              PGDRevision20261113.exact_profile_reduction (S j) p (hS j) N hN
            _ ≤ Q := le_iSup (fun j => profileRho (S j) p ^ (2 * N)) j
        exact (div_le_iff₀ (sq_pos_of_ne_zero (abs_ne_zero.mpr hz))).mp
          ((ENNReal.ofReal_le_iff_le_toReal hQ).mp hperf)
    have hsum : separableGradientSquared S ell (x N) ≤ Q.toReal * separableGradientSquared S ell (x 0) := by
      unfold separableGradientSquared
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ => hcoord j
    have hden : 0 < separableGradientSquared S ell (x 0) := by
      apply lt_of_le_of_ne
      · exact Finset.sum_nonneg fun j _ => sq_nonneg _
      · exact Ne.symm hnz
    exact (ENNReal.ofReal_le_iff_le_toReal hQ).mpr ((div_le_iff₀ hden).mpr hsum)
  · apply iSup_le
    intro j
    rw [← PGDRevision20261113.exact_profile_reduction (S j) p (hS j) N hN]
    apply sSup_le
    rintro v ⟨ell, x, hx, hnz, rfl⟩
    choose u hu using fun k => (hS k).1
    let ell0 : Fin d → ℝ := fun k => -deriv (S k).f (u k) - deriv (S k).g (u k)
    let tilt : Fin d → ℝ := Function.update ell0 j ell
    let traj : ℕ → Fin d → ℝ := fun i => Function.update u j (x i)
    have htraj : SeparableTrajectory S p tilt N traj := by
      intro k
      by_cases hk : k = j
      · subst k
        simpa [tilt, traj] using hx
      · simpa [tilt, traj, ell0, Function.update_of_ne hk] using
          (stationary_trajectory (S k) p (hS k) (u k) (hu k) N).1
    have hsum (i : ℕ) : separableGradientSquared S tilt (traj i) =
        |objectiveDerivative (S j) ell (x i)| ^ 2 := by
      unfold separableGradientSquared
      rw [Finset.sum_eq_single j]
      · simp [tilt, traj]
      · intro k _ hkj
        have hz := (stationary_trajectory (S k) p (hS k) (u k) (hu k) N).2
        simpa [tilt, traj, ell0, Function.update_of_ne hkj] using hz
      · simp
    have hinit : separableGradientSquared S tilt (traj 0) ≠ 0 := by
      rw [hsum 0]
      exact pow_ne_zero _ (abs_ne_zero.mpr hnz)
    apply le_sSup
    refine ⟨tilt, traj, htraj, hinit, ?_⟩
    rw [hsum N, hsum 0]

