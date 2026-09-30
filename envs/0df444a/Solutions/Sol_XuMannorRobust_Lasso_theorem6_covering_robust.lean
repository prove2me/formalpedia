-- Prove2me | solution 1 for XuMannorRobust.Lasso.theorem6_covering_robust
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:42:08.453116+00:00
-- url     : https://prove2.me/submissions/237a99de-df99-49b5-9bcc-30eb330f4d7b

import Mathlib
import Definitions.Def_XuMannorRobust_Lasso_IsRobustOn
open XuMannorRobust.Lasso

theorem solution {α H : Type*} [MetricSpace α] {n : ℕ} (Z : Set α)
    (l : H → α → ℝ) (A : (Fin n → α) → H) (ε : (Fin n → α) → ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hA : ∀ s : Fin n → α, (∀ j, s j ∈ Z) → ∀ j : Fin n, ∀ z ∈ Z,
      dist (s j) z ≤ γ → |l (A s) (s j) - l (A s) z| ≤ ε s)
    (hN : Metric.coveringNumber (Real.toNNReal (γ / 2)) Z < ⊤) :
    IsRobustOn Z l A (Metric.coveringNumber (Real.toNNReal (γ / 2)) Z).toNat ε := by
  classical
  obtain ⟨N, hNZ, hNfin, hcov, hcard⟩ := Metric.exists_set_encard_eq_coveringNumber hN.ne
  letI : Fintype N := hNfin.fintype
  have hcard' : Fintype.card N = (Metric.coveringNumber (Real.toNNReal (γ / 2)) Z).toNat := by
    rw [Set.fintypeCard_eq_ncard, Set.ncard_def, hcard]
  let e : N ≃ Fin ((Metric.coveringNumber (Real.toNNReal (γ / 2)) Z).toNat) :=
    Fintype.equivFinOfCardEq hcard'
  have hcent : ∀ z : Z, ∃ c : N, dist (z : α) (c : α) ≤ γ / 2 := by
    intro z
    have hz := Metric.isCover_iff_subset_iUnion_closedBall.mp hcov z.property
    simp only [Set.mem_iUnion, Metric.mem_closedBall, exists_prop] at hz
    obtain ⟨c, hc, hzc⟩ := hz
    refine ⟨⟨c, hc⟩, ?_⟩
    simpa [Real.toNNReal_of_nonneg (show 0 ≤ γ / 2 by linarith)] using hzc
  choose f hf using hcent
  let cells : Fin ((Metric.coveringNumber (Real.toNNReal (γ / 2)) Z).toNat) → Set α :=
    fun i => {z | ∃ hz : z ∈ Z, e (f ⟨z, hz⟩) = i}
  refine ⟨cells, ?_, ?_, ?_, ?_⟩
  · intro i z hz
    exact hz.choose
  · intro z hz
    exact Set.mem_iUnion.mpr ⟨e (f ⟨z, hz⟩), hz, rfl⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro z hzi hzj
    obtain ⟨hz, hi⟩ := hzi
    obtain ⟨hz', hj⟩ := hzj
    exact hij (hi.symm.trans hj)
  · intro s hs j z hz i hsj hzi
    obtain ⟨hsjZ, hsj⟩ := hsj
    obtain ⟨hzZ, hzi⟩ := hzi
    have heq : f ⟨s j, hsjZ⟩ = f ⟨z, hzZ⟩ := e.injective (hsj.trans hzi.symm)
    apply hA s hs j z hz
    have h1 := hf ⟨s j, hsjZ⟩
    have h2 := hf ⟨z, hzZ⟩
    rw [heq] at h1
    have ht := dist_triangle (s j) (f ⟨z, hzZ⟩ : α) z
    rw [dist_comm (f ⟨z, hzZ⟩ : α) z] at ht
    linarith
