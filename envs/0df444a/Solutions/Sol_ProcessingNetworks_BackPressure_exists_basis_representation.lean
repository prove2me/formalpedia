-- Prove2me | solution 1 for ProcessingNetworks.BackPressure.exists_basis_representation
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T19:47:58.488669+00:00
-- url     : https://prove2.me/submissions/9e2667f5-1b25-4d5a-857d-c59351345fb6

import Mathlib
import Definitions.Def_ProcessingNetworks_BackPressure_SPNPlanningData
import Definitions.Def_ProcessingNetworks_BackPressure_LeontiefNetwork

open ProcessingNetworks.BackPressure in
theorem solution
    {I J K : ℕ} (dat : SPNPlanningData I J K) (h91 : SatisfiesAssumption91 dat)
    (y : Fin I → ℝ) (hy : ∀ i, 0 < y i)
    (x : Fin J → ℝ) (hx : ∀ j, 0 ≤ x j) (hRx : dat.R.mulVec x = y) :
    ∃ (basis : ActivityBasis dat) (xhat : Fin I → ℝ),
      (∀ i, 0 ≤ xhat i) ∧ (basisMatrix basis).mulVec xhat = y := by
  classical
  set R := dat.R with hRdef
  let supp : (Fin J → ℝ) → Finset (Fin J) := fun z => Finset.univ.filter (fun j => z j ≠ 0)
  have hex : ∃ n, ∃ z : Fin J → ℝ, (∀ j, 0 ≤ z j) ∧ R.mulVec z = y ∧ (supp z).card = n :=
    ⟨_, x, hx, hRx, rfl⟩
  obtain ⟨z, hz0, hRz, hcard⟩ := Nat.find_spec hex
  have hmin : ∀ z' : Fin J → ℝ, (∀ j, 0 ≤ z' j) → R.mulVec z' = y →
      (supp z).card ≤ (supp z').card := by
    intro z' h1 h2
    rw [hcard]
    exact Nat.find_min' hex ⟨z', h1, h2, rfl⟩
  -- the columns in the support are linearly independent
  have hind : ∀ c : Fin J → ℝ, (∀ j, z j = 0 → c j = 0) → R.mulVec c = 0 → c = 0 := by
    intro c hcs hRc
    by_contra hne
    obtain ⟨c', hc's, hRc', j1, hj1⟩ : ∃ c' : Fin J → ℝ, (∀ j, z j = 0 → c' j = 0) ∧
        R.mulVec c' = 0 ∧ ∃ j, 0 < c' j := by
      obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
        by_contra h; push Not at h; exact hne (funext h)
      rcases hj.lt_or_gt with hneg | hpos
      · refine ⟨-c, fun j h => by simp [hcs j h], by rw [Matrix.mulVec_neg, hRc, neg_zero], j, ?_⟩
        simp only [Pi.neg_apply]; linarith
      · exact ⟨c, hcs, hRc, j, hpos⟩
    set T := Finset.univ.filter (fun j => 0 < c' j) with hT
    have hTne : T.Nonempty := ⟨j1, by simp [hT, hj1]⟩
    obtain ⟨j0, hj0T, hj0min⟩ := T.exists_min_image (fun j => z j / c' j) hTne
    have hc'j0 : 0 < c' j0 := (Finset.mem_filter.mp hj0T).2
    have hzj0 : z j0 ≠ 0 := fun h => by have := hc's j0 h; linarith
    set τ := z j0 / c' j0 with hτ
    have hτ0 : 0 ≤ τ := div_nonneg (hz0 j0) hc'j0.le
    set z' : Fin J → ℝ := z - τ • c' with hz'
    have hz'0 : ∀ j, 0 ≤ z' j := by
      intro j
      simp only [hz', Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      by_cases hj : 0 < c' j
      · have := hj0min j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
        rw [le_div_iff₀ hj] at this
        linarith
      · push Not at hj
        nlinarith [hz0 j]
    have hRz' : R.mulVec z' = y := by
      rw [hz', Matrix.mulVec_sub, Matrix.mulVec_smul, hRc', smul_zero, sub_zero, hRz]
    have hsub : supp z' ⊂ supp z := by
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨j0, by simp [supp, hzj0], ?_⟩
        simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, not_not, hz', Pi.sub_apply,
          Pi.smul_apply, smul_eq_mul, hτ]
        field_simp
        ring
      · intro j hj
        simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        intro hzj
        apply hj
        simp [hz', hzj, hc's j hzj]
    have h1 := hmin z' hz'0 hRz'
    have h2 := Finset.card_lt_card hsub
    omega
  -- the support has at most `I` elements
  have hcardle : (supp z).card ≤ I := by
    let v : supp z → (Fin I → ℝ) := fun j => fun k => R k j
    have hli : LinearIndependent ℝ v := by
      rw [Fintype.linearIndependent_iff]
      intro g hg j
      set c : Fin J → ℝ := fun j' => if h : j' ∈ supp z then g ⟨j', h⟩ else 0 with hc
      have hcs : ∀ j', z j' = 0 → c j' = 0 := by
        intro j' hj'
        have : j' ∉ supp z := by simp [supp, hj']
        simp [hc, this]
      have hRc : R.mulVec c = 0 := by
        funext k
        have hk := congrFun hg k
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, v] at hk
        simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
        rw [← Finset.sum_subset (Finset.subset_univ (supp z)) (fun j' _ hj' => by simp [hc, hj'])]
        rw [← Finset.sum_coe_sort (supp z)]
        rw [← hk]
        refine Finset.sum_congr rfl fun j' _ => ?_
        simp [hc, j'.2, mul_comm]
      have := congrFun (hind c hcs hRc) j
      simpa [hc, j.2] using this
    have := hli.fintype_card_le_finrank
    simpa [Module.finrank_fin_fun] using this
  -- one serving activity in the support for each buffer
  have hpick : ∀ i, ∃ j, 0 < z j ∧ 0 < R i j := by
    intro i
    by_contra hcon
    push Not at hcon
    have h := hy i
    rw [← hRz] at h
    simp only [Matrix.mulVec, dotProduct] at h
    have : ∑ j, R i j * z j ≤ 0 := Finset.sum_nonpos fun j _ => by
      rcases (hz0 j).lt_or_eq with hp | he
      · nlinarith [hcon j hp]
      · rw [← he, mul_zero]
    linarith
  choose jf hjz hjR using hpick
  have hinj : Function.Injective jf := by
    intro i i' h
    obtain ⟨i0, -, huniq⟩ := h91 (jf i)
    have a := huniq i (hjR i)
    have b := huniq i' (by rw [h]; exact hjR i')
    rw [a, b]
  let basis : ActivityBasis dat := ⟨jf, hinj, hjR⟩
  refine ⟨basis, fun i => z (jf i), fun i => hz0 _, ?_⟩
  -- the support is exactly the image of `jf`
  have himg : Finset.univ.image jf ⊆ supp z := by
    intro j hj
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hj
    simp [supp, (hjz i).ne']
  have hcardimg : (Finset.univ.image jf).card = I := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have heq : Finset.univ.image jf = supp z :=
    Finset.eq_of_subset_of_card_le himg (by rw [hcardimg]; exact hcardle)
  funext k
  rw [← hRz]
  simp only [basisMatrix, Matrix.mulVec, dotProduct]
  rw [← Finset.sum_subset (Finset.subset_univ (supp z)) (fun j _ hj => by
    simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hj
    rw [hj, mul_zero])]
  rw [← heq, Finset.sum_image (fun a _ b _ h => hinj h)]


