-- Prove2me | solution 1 for OracleRO.DualSubgrad.eq_6
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T05:56:00.873225+00:00
-- url     : https://prove2.me/submissions/2b762a53-fe3e-4f03-a225-44713d4e6008

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_OracleRO_DualSubgrad_Problem
import Definitions.Def_OracleRO_DualSubgrad_Algorithm1

set_option autoImplicit false

open OracleRO.DualSubgrad in
theorem solution
    {m n d : ℕ} (Dom : Set (EuclideanSpace ℝ (Fin n))) (U : Set (EuclideanSpace ℝ (Fin d)))
    (f : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d) → ℝ)
    (gradU : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (O : (Fin m → EuclideanSpace ℝ (Fin d)) → Option (EuclideanSpace ℝ (Fin n)))
    (ε D G : ℝ) (u0 : Fin m → EuclideanSpace ℝ (Fin d)) (x0 : EuclideanSpace ℝ (Fin n))
    (hP : SpectralProjGrad.Shared.IsProjOnto U P) (hε : 0 < ε) (hD : 0 < D) (hG : 0 < G)
    (hO : IsApproxOracle Dom U f ε O)
    (xbar : EuclideanSpace ℝ (Fin n))
    (hout : alg1Output gradU P O G D ε u0 x0 = some xbar) :
    ∀ i, (1 / (alg1T G D ε : ℝ)) * ∑ t ∈ Finset.Icc 1 (alg1T G D ε),
      f i (alg1X gradU P O G D ε u0 x0 t) (alg1U gradU P O G D ε u0 x0 t i) ≤ ε := by
  intro i
  set T := alg1T G D ε with hT
  have hnone : ∀ t ∈ Finset.Icc 1 T, O (alg1U gradU P O G D ε u0 x0 t) ≠ none := by
    intro t ht hc
    unfold alg1Output at hout
    rw [if_pos ⟨t, ht, hc⟩] at hout
    cases hout
  have hbound : ∀ t ∈ Finset.Icc 1 T,
      f i (alg1X gradU P O G D ε u0 x0 t) (alg1U gradU P O G D ε u0 x0 t i) ≤ ε := by
    intro t ht
    have ht1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    have hU : ∀ j, alg1U gradU P O G D ε u0 x0 (s + 1) j ∈ U := by
      intro j
      simp only [alg1U, alg1State]
      exact (hP _).1
    obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp (hnone _ ht)
    have hX : alg1X gradU P O G D ε u0 x0 (s + 1) = x := by
      have : alg1X gradU P O G D ε u0 x0 (s + 1)
          = (O (alg1U gradU P O G D ε u0 x0 (s + 1))).getD x0 := by
        simp only [alg1X, alg1U, alg1State]
      rw [this, hx]; rfl
    rw [hX]
    exact ((hO _ hU).1 x hx).2 i
  have hsum : ∑ t ∈ Finset.Icc 1 T,
      f i (alg1X gradU P O G D ε u0 x0 t) (alg1U gradU P O G D ε u0 x0 t i) ≤ (T : ℝ) * ε := by
    calc _ ≤ ∑ t ∈ Finset.Icc 1 T, ε := Finset.sum_le_sum hbound
      _ = (T : ℝ) * ε := by simp
  rcases Nat.eq_zero_or_pos T with h0 | hpos
  · rw [h0]; simp; exact hε.le
  · have hTpos : (0 : ℝ) < T := by exact_mod_cast hpos
    rw [one_div, inv_mul_le_iff₀ hTpos]
    exact hsum
