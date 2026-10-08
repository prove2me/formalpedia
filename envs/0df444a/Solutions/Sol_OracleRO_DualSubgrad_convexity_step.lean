-- Prove2me | solution 1 for OracleRO.DualSubgrad.convexity_step
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T12:45:24.783302+00:00
-- url     : https://prove2.me/submissions/036651bd-efaf-4af2-8c1c-23beefaac25b

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_OracleRO_DualSubgrad_Problem
import Definitions.Def_OracleRO_DualSubgrad_Algorithm1

open OracleRO.DualSubgrad in
theorem OracleRO_DualSubgrad_convexity_step_iter_mem
    {m n d : ℕ} (Dom : Set (EuclideanSpace ℝ (Fin n))) (U : Set (EuclideanSpace ℝ (Fin d)))
    (f : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d) → ℝ)
    (gradU : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (O : (Fin m → EuclideanSpace ℝ (Fin d)) → Option (EuclideanSpace ℝ (Fin n)))
    (ε D G : ℝ) (u0 : Fin m → EuclideanSpace ℝ (Fin d)) (x0 : EuclideanSpace ℝ (Fin n))
    (hP : SpectralProjGrad.Shared.IsProjOnto U P)
    (hx0 : x0 ∈ Dom)
    (hO : IsApproxOracle Dom U f ε O) (t : ℕ) :
    alg1X gradU P O G D ε u0 x0 t ∈ Dom := by
  cases t with
  | zero => simpa [alg1X, alg1State] using hx0
  | succ k =>
    simp only [alg1X, alg1State]
    set u' : Fin m → EuclideanSpace ℝ (Fin d) := fun i =>
      P ((alg1State gradU P O (alg1Eta G D ε) u0 x0 k).1 i + alg1Eta G D ε •
        gradU i (alg1State gradU P O (alg1Eta G D ε) u0 x0 k).2
          ((alg1State gradU P O (alg1Eta G D ε) u0 x0 k).1 i)) with hu'
    have hU : ∀ i, u' i ∈ U := fun i => (hP _).1
    rcases h : O u' with _ | x
    · simpa using hx0
    · simpa using ((hO u' hU).1 x h).1

open OracleRO.DualSubgrad in
theorem solution
    {m n d : ℕ} (Dom : Set (EuclideanSpace ℝ (Fin n))) (U : Set (EuclideanSpace ℝ (Fin d)))
    (f : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d) → ℝ)
    (gradU : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (O : (Fin m → EuclideanSpace ℝ (Fin d)) → Option (EuclideanSpace ℝ (Fin n)))
    (ε D G : ℝ) (u0 : Fin m → EuclideanSpace ℝ (Fin d)) (x0 : EuclideanSpace ℝ (Fin n))
    (hDom : Convex ℝ Dom) (hP : SpectralProjGrad.Shared.IsProjOnto U P)
    (hconv : ∀ i, ∀ u ∈ U, ConvexOn ℝ Dom (fun x => f i x u))
    (hε : 0 < ε) (hD : 0 < D) (hG : 0 < G)
    (hx0 : x0 ∈ Dom)
    (hO : IsApproxOracle Dom U f ε O)
    (xbar : EuclideanSpace ℝ (Fin n))
    (hout : alg1Output gradU P O G D ε u0 x0 = some xbar) :
    ∀ i, ∀ u ∈ U, f i xbar u ≤ (1 / (alg1T G D ε : ℝ)) *
      ∑ t ∈ Finset.Icc 1 (alg1T G D ε), f i (alg1X gradU P O G D ε u0 x0 t) u := by
  intro i u hu
  have hT : 0 < (alg1T G D ε : ℝ) := by
    have : 0 < G ^ 2 * D ^ 2 / ε ^ 2 := by positivity
    have h1 : 0 < alg1T G D ε := by
      unfold alg1T
      exact Nat.ceil_pos.mpr this
    exact_mod_cast h1
  have hxbar : xbar = (1 / (alg1T G D ε : ℝ)) •
      ∑ t ∈ Finset.Icc 1 (alg1T G D ε), alg1X gradU P O G D ε u0 x0 t := by
    unfold alg1Output at hout
    split_ifs at hout
    exact (Option.some.inj hout).symm
  have hcard : ((Finset.Icc 1 (alg1T G D ε)).card : ℝ) = (alg1T G D ε : ℝ) := by
    simp
  have key := (hconv i u hu).map_sum_le (t := Finset.Icc 1 (alg1T G D ε))
    (w := fun _ => 1 / (alg1T G D ε : ℝ)) (p := fun t => alg1X gradU P O G D ε u0 x0 t)
    (fun _ _ => by positivity)
    (by rw [Finset.sum_const, nsmul_eq_mul, hcard]; field_simp)
    (fun t _ => OracleRO_DualSubgrad_convexity_step_iter_mem Dom U f gradU P O ε D G u0 x0
      hP hx0 hO t)
  rw [hxbar, Finset.smul_sum]
  refine key.trans (le_of_eq ?_)
  rw [Finset.mul_sum]
  simp [smul_eq_mul]
