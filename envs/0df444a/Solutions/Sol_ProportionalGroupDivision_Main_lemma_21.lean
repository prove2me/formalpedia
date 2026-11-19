-- Prove2me | solution 1 for ProportionalGroupDivision.Main.lemma_21
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-18T16:16:02.029224+00:00
-- url     : https://prove2.me/submissions/b195a8ba-5f30-4a4f-9906-9f6879d1ce40

import Mathlib

set_option maxHeartbeats 1200000

open scoped BigOperators

theorem solution (N m : ℕ) (hN : 0 < N) (hNm : N < m) (A : Matrix (Fin N) (Fin m) ℝ)
    (hA : ∀ i g, A i g ∈ Set.Icc (0 : ℝ) 1) (x : Fin m → ℝ) (hx : ∀ g, x g ∈ Set.Icc (0 : ℝ) 1) :
    ∃ x' : Fin m → ℝ, (∀ g, x' g ∈ Set.Icc (0 : ℝ) 1) ∧ A.mulVec x = A.mulVec x' ∧
      (Finset.univ.filter (fun g => x' g ≠ 0 ∧ x' g ≠ 1)).card ≤ N := by
  classical
  let cell : (Fin m → ℝ) → Finset (Fin m) :=
    fun y => Finset.univ.filter (fun g => y g ≠ 0 ∧ y g ≠ 1)
  let Feas : (Fin m → ℝ) → Prop :=
    fun y => (∀ g, y g ∈ Set.Icc (0 : ℝ) 1) ∧ A.mulVec x = A.mulVec y
  let S : Set ℕ := {n | ∃ y : Fin m → ℝ, Feas y ∧ (cell y).card = n}
  have hS : S.Nonempty := ⟨(cell x).card, x, ⟨hx, rfl⟩, rfl⟩
  let n : ℕ := Nat.find (show ∃ n, n ∈ S from hS)
  have hnS : n ∈ S := Nat.find_spec (show ∃ n, n ∈ S from hS)
  have hmin : ∀ z : Fin m → ℝ, Feas z → n ≤ (cell z).card := by
    intro z hz
    exact Nat.find_min' (show ∃ n, n ∈ S from hS) ⟨z, hz, rfl⟩
  obtain ⟨y, hyFeas, hycard⟩ := hnS
  have hy01 : ∀ g, y g ∈ Set.Icc (0 : ℝ) 1 := hyFeas.1
  have hyAx : A.mulVec x = A.mulVec y := hyFeas.2
  by_contra hcon
  have hNn : N < n := by
    by_contra h
    have hnN : n ≤ N := by omega
    have hcardle : (cell y).card ≤ N := by omega
    exact hcon ⟨y, hy01, hyAx, hcardle⟩
  let F : Finset (Fin m) := cell y
  have hFcard : F.card = n := hycard
  have hFN : N < F.card := by omega
  let v : F → (Fin N → ℝ) := fun j i => A i j.1
  have hdep : ¬ LinearIndependent ℝ v := by
    intro hind
    have hle := hind.fintype_card_le_finrank
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hle
    have hcard : Fintype.card F = F.card := by simp
    rw [hcard] at hle
    omega
  rw [Fintype.not_linearIndependent_iff] at hdep
  obtain ⟨g, hgsum, j0, hgj0⟩ := hdep
  let c : Fin m → ℝ := fun j => if h : j ∈ F then g ⟨j, h⟩ else 0
  have hc_mem : ∀ j : F, c j.1 = g j := by
    intro j
    simp [c, j.2]
  have hAc : A.mulVec c = 0 := by
    funext i
    have h := congrFun hgsum i
    simp only [Pi.zero_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, v, Matrix.row] at h
    rw [Matrix.mulVec_apply]
    simp only [dotProduct, Pi.zero_apply]
    have hzero : ∀ j ∈ (Finset.univ : Finset (Fin m)), j ∉ F → A.row i j * c j = 0 := by
      intro j _ hj
      simp [c, hj]
    rw [← Finset.sum_subset (Finset.subset_univ F) hzero]
    rw [← Finset.sum_coe_sort F (fun j => A.row i j * c j)]
    simpa [hc_mem, mul_comm] using h
  have hc_ne : c ≠ 0 := by
    intro hc0
    have := hc_mem j0
    rw [hc0, Pi.zero_apply] at this
    exact hgj0 this.symm
  -- fractional coordinates of y on which c is nonzero
  let Fpos : Finset (Fin m) := F.filter (fun j => c j ≠ 0)
  have hFpos : Fpos.Nonempty := by
    refine ⟨j0.1, ?_⟩
    simp [Fpos, j0.2, hc_mem j0, hgj0]
  have hy_pos : ∀ j ∈ F, 0 < y j := by
    intro j hj
    have hmem := Finset.mem_filter.mp hj
    have h01 := hy01 j
    exact lt_of_le_of_ne h01.1 (Ne.symm hmem.2.1)
  have hy_lt_one : ∀ j ∈ F, y j < 1 := by
    intro j hj
    have hmem := Finset.mem_filter.mp hj
    have h01 := hy01 j
    exact lt_of_le_of_ne h01.2 hmem.2.2
  have hFposF : ∀ j ∈ Fpos, j ∈ F := by
    intro j hj
    exact (Finset.mem_filter.mp hj).1
  have hcFpos : ∀ j ∈ Fpos, c j ≠ 0 := by
    intro j hj
    exact (Finset.mem_filter.mp hj).2
  -- candidate signed perturbations that hit a boundary
  let T : Finset ℝ := Fpos.attach.biUnion
    (fun j => ({- y j.1 / c j.1, (1 - y j.1) / c j.1} : Finset ℝ))
  have hTne : T.Nonempty := by
    obtain ⟨j, hj⟩ := hFpos
    refine ⟨- y j / c j, ?_⟩
    exact Finset.mem_biUnion.mpr ⟨⟨j, hj⟩, by simp, by simp⟩
  have hT_ne : ∀ r ∈ T, r ≠ 0 := by
    intro r hr
    rw [Finset.mem_biUnion] at hr
    obtain ⟨j, hj, hrj⟩ := hr
    have hjF : j.1 ∈ F := hFposF j.1 j.2
    have hcj : c j.1 ≠ 0 := hcFpos j.1 j.2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hrj
    rcases hrj with rfl | rfl
    · exact div_ne_zero (neg_ne_zero.mpr (ne_of_gt (hy_pos j.1 hjF))) hcj
    · exact div_ne_zero (ne_of_gt (sub_pos.mpr (hy_lt_one j.1 hjF))) hcj
  let D : Finset ℝ := T.image (fun r => |r|)
  have hDne : D.Nonempty := hTne.image _
  let d : ℝ := D.min' hDne
  have hdmem : d ∈ D := D.min'_mem hDne
  obtain ⟨eps, hepsT, heps_abs⟩ := Finset.mem_image.mp hdmem
  have heps_abs' : |eps| = d := heps_abs
  have heps_le : ∀ r ∈ T, |eps| ≤ |r| := by
    intro r hr
    rw [heps_abs']
    exact D.min'_le _ (Finset.mem_image.mpr ⟨r, hr, rfl⟩)
  have heps_ne : eps ≠ 0 := by
    intro h0
    have hzero : (0 : ℝ) ∈ T := by simpa [h0] using hepsT
    exact hT_ne 0 hzero rfl
  have hcand_mem : ∀ j ∈ Fpos, (- y j / c j) ∈ T ∧ ((1 - y j) / c j) ∈ T := by
    intro j hj
    constructor
    · exact Finset.mem_biUnion.mpr ⟨⟨j, hj⟩, by simp, by simp⟩
    · exact Finset.mem_biUnion.mpr ⟨⟨j, hj⟩, by simp, by simp⟩
  have hbound : ∀ j ∈ Fpos, |eps * c j| ≤ y j ∧ |eps * c j| ≤ 1 - y j := by
    intro j hj
    have hjF : j ∈ F := hFposF j hj
    have hcj : c j ≠ 0 := hcFpos j hj
    have hcjpos : 0 < |c j| := abs_pos.mpr hcj
    have h1 := heps_le _ (hcand_mem j hj).1
    have h2 := heps_le _ (hcand_mem j hj).2
    have h1' : |eps| ≤ y j / |c j| := by
      simpa [abs_div, abs_neg, abs_of_pos (hy_pos j hjF)] using h1
    have h2' : |eps| ≤ (1 - y j) / |c j| := by
      simpa [abs_div, abs_of_pos (sub_pos.mpr (hy_lt_one j hjF))] using h2
    constructor
    · calc |eps * c j| = |eps| * |c j| := abs_mul _ _
        _ ≤ (y j / |c j|) * |c j| := mul_le_mul_of_nonneg_right h1' hcjpos.le
        _ = y j := div_mul_cancel₀ _ hcjpos.ne'
    · calc |eps * c j| = |eps| * |c j| := abs_mul _ _
        _ ≤ ((1 - y j) / |c j|) * |c j| := mul_le_mul_of_nonneg_right h2' hcjpos.le
        _ = 1 - y j := div_mul_cancel₀ _ hcjpos.ne'
  let z : Fin m → ℝ := y + eps • c
  have hz_apply : ∀ j, z j = y j + eps * c j := by
    intro j
    simp [z]
  have hz01 : ∀ g, z g ∈ Set.Icc (0 : ℝ) 1 := by
    intro j
    by_cases hj : j ∈ Fpos
    · have hb := hbound j hj
      have hy := hy01 j
      have hle1 := abs_le.mp hb.1
      have hle2 := abs_le.mp hb.2
      rw [hz_apply j]
      constructor <;> linarith [hle1.1, hle1.2, hle2.1, hle2.2, hy.1, hy.2]
    · have hc0 : c j = 0 := by
        by_cases hjF : j ∈ F
        · by_contra hcne
          exact hj (by simp [Fpos, hjF, hcne])
        · simp [c, hjF]
      rw [hz_apply j, hc0, mul_zero, add_zero]
      exact hy01 j
  have hboundary : ∃ j ∈ Fpos, z j = 0 ∨ z j = 1 := by
    rw [Finset.mem_biUnion] at hepsT
    obtain ⟨j, hj, hrj⟩ := hepsT
    have hjF : j.1 ∈ F := hFposF j.1 j.2
    have hcj : c j.1 ≠ 0 := hcFpos j.1 j.2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hrj
    refine ⟨j.1, j.2, ?_⟩
    rcases hrj with h | h
    · left
      rw [hz_apply j.1, h]
      field_simp [hcj]
      ring
    · right
      rw [hz_apply j.1, h]
      field_simp [hcj]
      ring
  have hzAx : A.mulVec x = A.mulVec z := by
    have hz : z = y + eps • c := rfl
    rw [hyAx, hz, Matrix.mulVec_add, Matrix.mulVec_smul, hAc, smul_zero, add_zero]
  have hsubset : cell z ⊆ F := by
    intro j hj
    have hzj := Finset.mem_filter.mp hj
    simp only [Finset.mem_univ, true_and] at hzj
    by_contra hjF
    have hc0 : c j = 0 := by
      by_cases h : j ∈ F
      · exact absurd h hjF
      · simp [c, h]
    have hzy : z j = y j := by rw [hz_apply j, hc0, mul_zero, add_zero]
    have hyne : y j = 0 ∨ y j = 1 := by
      by_cases h0 : y j = 0
      · exact Or.inl h0
      · by_cases h1 : y j = 1
        · exact Or.inr h1
        · have : j ∈ cell y := by
            simp only [cell, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨h0, h1⟩
          exact absurd this hjF
    rw [hzy] at hzj
    rcases hyne with h0 | h1
    · exact hzj.1 h0
    · exact hzj.2 h1
  have hne : cell z ≠ F := by
    obtain ⟨j, hjFpos, hzj⟩ := hboundary
    have hjF : j ∈ F := hFposF j hjFpos
    intro heq
    have : j ∈ cell z := by rw [heq]; exact hjF
    have hmem := Finset.mem_filter.mp this
    simp only [Finset.mem_univ, true_and] at hmem
    rcases hzj with h | h
    · exact hmem.1 h
    · exact hmem.2 h
  have hssub : cell z ⊂ F := Finset.ssubset_iff_subset_ne.mpr ⟨hsubset, hne⟩
  have hlt : (cell z).card < n := by
    have := Finset.card_lt_card hssub
    simpa [hFcard] using this
  have hge : n ≤ (cell z).card := hmin z ⟨hz01, hzAx⟩
  omega

