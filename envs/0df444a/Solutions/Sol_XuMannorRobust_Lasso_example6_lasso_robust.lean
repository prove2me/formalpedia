-- Prove2me | solution 1 for XuMannorRobust.Lasso.example6_lasso_robust
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:43:29.515985+00:00
-- url     : https://prove2.me/submissions/59271778-4e98-431c-8703-11cbfcf2d645

import Mathlib
import Definitions.Def_XuMannorRobust_Lasso_IsRobustOn
import Definitions.Def_XuMannorRobust_Lasso_LassoLoss
import Definitions.Def_XuMannorRobust_Lasso_LassoFormulation
open XuMannorRobust.Lasso

private theorem lasso_bound {m n : ℕ} (c : ℝ) (hc : 0 < c)
    (s : Fin n → ℝ × (Fin m → ℝ)) (w : Fin m → ℝ) (hw : IsLassoSolution c s w) :
    lassoObjective c s w ≤ lassoObjective c s 0 ∧
    lassoObjective c s 0 = (1 / (n : ℝ)) * ∑ i, (s i).1 ^ 2 ∧
    l1norm w ≤ (1 / ((n : ℝ) * c)) * ∑ i, (s i).1 ^ 2 := by
  have hzero : lassoObjective c s 0 = (1 / (n : ℝ)) * ∑ i, (s i).1 ^ 2 := by
    simp [lassoObjective, l1norm]
  refine ⟨hw 0, hzero, ?_⟩
  have hnonneg : 0 ≤ (1 / (n : ℝ)) * ∑ i, ((s i).1 - dotProduct w (s i).2) ^ 2 := by
    positivity
  have hbound : c * l1norm w ≤ (1 / (n : ℝ)) * ∑ i, (s i).1 ^ 2 := by
    have := hw 0
    rw [hzero] at this
    unfold lassoObjective at this
    linarith
  calc
    l1norm w ≤ ((1 / (n : ℝ)) * ∑ i, (s i).1 ^ 2) / c :=
      (le_div_iff₀ hc).mpr (by simpa [mul_comm] using hbound)
    _ = (1 / ((n : ℝ) * c)) * ∑ i, (s i).1 ^ 2 := by simp [div_eq_mul_inv]; ring

private theorem loss_lipschitz {m n : ℕ} (c : ℝ) (hc : 0 < c)
    (s : Fin n → ℝ × (Fin m → ℝ)) (w : Fin m → ℝ) (hw : IsLassoSolution c s w)
    (za zb : ℝ × (Fin m → ℝ)) :
    |lassoLoss w za - lassoLoss w zb| ≤
      ((1 / ((n : ℝ) * c)) * ∑ i, (s i).1 ^ 2 + 1) * ‖za - zb‖ := by
  have hcoord (i : Fin m) : |za.2 i - zb.2 i| ≤ ‖za - zb‖ := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply, Prod.snd_sub] using
      (norm_le_pi_norm ((za - zb).2) i).trans (norm_snd_le (za - zb))
  have hresp : |za.1 - zb.1| ≤ ‖za - zb‖ := by
    simpa only [Real.norm_eq_abs, Prod.fst_sub] using norm_fst_le (za - zb)
  have hdot : |dotProduct w (za.2 - zb.2)| ≤ l1norm w * ‖za - zb‖ := by
    calc
      |dotProduct w (za.2 - zb.2)| ≤ ∑ i, |w i * (za.2 i - zb.2 i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |w i| * ‖za - zb‖ := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hcoord i) (abs_nonneg _)
      _ = l1norm w * ‖za - zb‖ := by rw [← Finset.sum_mul]; rfl
  have hb := (lasso_bound c hc s w hw).2.2
  calc
    |lassoLoss w za - lassoLoss w zb| ≤
        |(za.1 - dotProduct w za.2) - (zb.1 - dotProduct w zb.2)| :=
      abs_abs_sub_abs_le_abs_sub _ _
    _ = |(za.1 - zb.1) - dotProduct w (za.2 - zb.2)| := by
      rw [dotProduct_sub]
      congr 1
      ring
    _ ≤ |za.1 - zb.1| + |dotProduct w (za.2 - zb.2)| := abs_sub _ _
    _ ≤ ‖za - zb‖ + l1norm w * ‖za - zb‖ := add_le_add hresp hdot
    _ ≤ ‖za - zb‖ + ((1 / ((n : ℝ) * c)) * ∑ i, (s i).1 ^ 2) * ‖za - zb‖ :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
    _ = _ := by ring

private theorem covering_robust {α H : Type*} [MetricSpace α] {n : ℕ} (Z : Set α)
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

theorem solution {m n : ℕ} (Z : Set (ℝ × (Fin m → ℝ))) (hZ : IsCompact Z)
    (c : ℝ) (hc : 0 < c) (A : (Fin n → ℝ × (Fin m → ℝ)) → (Fin m → ℝ))
    (hA : ∀ s, IsLassoSolution c s (A s)) (γ : ℝ) (hγ : 0 < γ) :
    IsRobustOn Z lassoLoss A (Metric.coveringNumber (Real.toNNReal (γ / 2)) Z).toNat
      (fun s => (meanSqResponse s / c + 1) * γ) := by
  apply covering_robust Z lassoLoss A _ γ hγ
  · intro s hs j z hz hd
    have hloss := loss_lipschitz c hc s (A s) (hA s) (s j) z
    have he : (1 / ((n : ℝ) * c)) * ∑ i, (s i).1 ^ 2 + 1 = meanSqResponse s / c + 1 := by
      unfold meanSqResponse
      simp [div_eq_mul_inv]
      <;> ring
    rw [he] at hloss
    have hcoef : 0 ≤ meanSqResponse s / c + 1 := by
      unfold meanSqResponse
      positivity
    exact hloss.trans (mul_le_mul_of_nonneg_left (by simpa [dist_eq_norm] using hd) hcoef)
  · have hrad : Real.toNNReal (γ / 2) ≠ 0 := ne_of_gt (Real.toNNReal_pos.mpr (by linarith))
    obtain ⟨N, hNZ, hNfin, hcov⟩ := Metric.exists_finite_isCover_of_isCompact hrad hZ
    exact lt_of_le_of_lt (Metric.IsCover.coveringNumber_le_encard hNZ hcov) hNfin.encard_lt_top
