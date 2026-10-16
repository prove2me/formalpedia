-- Prove2me | solution 1 for TaitTobin.Planar.lemma_12
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-15T12:48:54.834995+00:00
-- url     : https://prove2.me/submissions/09336d9c-bb60-4e1f-a8aa-a45657e44a9d

import Mathlib
import Definitions.Def_TaitTobin_Planar_Setting
import Theorems.Thm_TaitTobin_Planar_eq_7
import Theorems.Thm_TaitTobin_Planar_lemma_9
import Theorems.Thm_TaitTobin_Planar_planar_facts

set_option autoImplicit false

section L12

open Classical WangKangXue.SpectralTuran RobertsonSeymour1986.GM5 TaitTobin.Planar

/-- At most two vertices are adjacent to all of `u`, `x`, `w` (`K₃,₃`-freeness). -/
theorem l12_k33 {n : ℕ} (hn3 : 3 ≤ n) (G : SimpleGraph (Fin n)) (hG : IsPlanar G)
    (u x w : Fin n) (hux : u ≠ x) (huw : u ≠ w) (hxw : x ≠ w) :
    ((Finset.univ.filter (fun y => G.Adj u y ∧ G.Adj y x ∧ G.Adj y w)).card) ≤ 2 := by
  by_contra hcon
  have h3 : 2 < (Finset.univ.filter (fun y => G.Adj u y ∧ G.Adj y x ∧ G.Adj y w)).card :=
    not_le.1 hcon
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.1 h3
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb hc
  have hfree := (TaitTobin.Planar.planar_facts hn3 G hG).1
  apply hfree
  let f : Fin 3 ⊕ Fin 3 → Fin n := Sum.elim ![u, x, w] ![a, b, c]
  have hadj : ∀ (i : Fin 3) (j : Fin 3), G.Adj (![u, x, w] i) (![a, b, c] j) := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [ha.1, hb.1, hc.1, ha.2.1.symm, hb.2.1.symm, hc.2.1.symm,
      ha.2.2.symm, hb.2.2.symm, hc.2.2.symm]
  refine ⟨⟨⟨f, ?_⟩, ?_⟩⟩
  · rintro (i | i) (j | j) h
    · simp [completeBipartiteGraph_adj] at h
    · exact hadj i j
    · exact (hadj j i).symm
    · simp [completeBipartiteGraph_adj] at h
  · have hne : ∀ (i : Fin 3) (j : Fin 3), ![u, x, w] i ≠ ![a, b, c] j := fun i j =>
      (hadj i j).ne
    rintro (i | i) (j | j) h
    · congr 1
      fin_cases i <;> fin_cases j <;> simp_all [f]
    · exact absurd h (by simpa [f] using hne i j)
    · exact absurd h.symm (by simpa [f] using hne j i)
    · congr 1
      fin_cases i <;> fin_cases j <;> simp_all [f]

/-- Inclusion-exclusion for weighted common neighbours inside `S`. -/
theorem l12_incl {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n → ℝ) (hpos : ∀ i, 0 < v i)
    (T : Finset (Fin n)) (x w u : Fin n) :
    (∑ y ∈ T.filter (fun y => G.Adj x y), v y) + (∑ y ∈ T.filter (fun y => G.Adj w y), v y)
      + (∑ y ∈ T.filter (fun y => G.Adj u y), v y) - 2 * ∑ y ∈ T, v y ≤
    ∑ y ∈ T.filter (fun y => G.Adj u y ∧ G.Adj x y ∧ G.Adj w y), v y := by
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
    Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum (fun y _ => ?_)
  have := hpos y
  split_ifs <;> first | linarith | (exfalso; tauto)

end L12

open Classical WangKangXue.SpectralTuran RobertsonSeymour1986.GM5 TaitTobin.Planar in
theorem solution : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
    ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n), TaitTobin.Outerplanar.IsSpecMax IsPlanar G →
    ∀ v : Fin n → ℝ, (G.adjMatrix ℝ).mulVec v = specRad G • v →
      (∀ i, 0 < v i) → (∀ i, v i ≤ 1) → ∀ x : Fin n, v x = 1 →
        ∀ w : Fin n, IsSecondHub G ε v x w →
          ∀ u : Fin n, u ≠ x → u ≠ w → v u < 1 / 10 := by
  refine ⟨1 / 400, by norm_num, fun ε hε hε1 => ?_⟩
  obtain ⟨N7, h7⟩ := TaitTobin.Planar.eq_7 ε hε
  obtain ⟨N9, h9⟩ := TaitTobin.Planar.lemma_9 ε hε
  refine ⟨max (max N7 N9) (max 4 ⌈(4000 / ε) ^ 2⌉₊), fun n hn G hG v hv hpos hle x hx w hw u hux huw => ?_⟩
  by_contra hcon
  have hu10 : 1 / 10 ≤ v u := not_lt.1 hcon
  have hn7 : n ≥ N7 := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn9 : n ≥ N9 := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn4 : 4 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hnc : ⌈(4000 / ε) ^ 2⌉₊ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hnr : (4000 / ε) ^ 2 ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hnc)
  have hn4r : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hs : 4000 / ε ≤ Real.sqrt (2 * (n : ℝ) - 4) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hs0 : 0 ≤ Real.sqrt (2 * (n : ℝ) - 4) := Real.sqrt_nonneg _
  set s := Real.sqrt (2 * (n : ℝ) - 4) with hsdef
  have hxL : x ∈ Lset ε v := by
    unfold Lset
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hx]; linarith
  have huL : u ∈ Lset ε v := by
    unfold Lset
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    linarith
  obtain ⟨hwL, hwx, hwv, -⟩ := hw
  have hx7 := h7 n hn7 G hG v hv hpos hle x hx x hxL
  have hw7 := h7 n hn7 G hG v hv hpos hle x hx w hwL
  have hu7 := h7 n hn7 G hG v hv hpos hle x hx u huL
  have hS9 := (h9 n hn9 G hG v hv hpos hle x hx).2
  have hinc := l12_incl G v hpos (Sset ε v) x w u
  have hw' : (1 - 25 * ε) * s ≤ (v w - ε) * s :=
    mul_le_mul_of_nonneg_right (by linarith) hs0
  have hu' : (1 / 10 - ε) * s ≤ (v u - ε) * s :=
    mul_le_mul_of_nonneg_right (by linarith) hs0
  rw [hx] at hx7
  have hεs : ε * s ≤ s / 400 := by nlinarith
  have ht : 400 < 1 / ε := by
    rw [lt_div_iff₀ hε]; linarith
  have h18 : 18 / ε = 18 * (1 / ε) := by ring
  have h4000 : 4000 / ε = 4000 * (1 / ε) := by ring
  rw [h18] at hx7 hw7 hu7
  rw [h4000] at hs
  -- the common neighbourhood in S
  set C := (Sset ε v).filter (fun y => G.Adj u y ∧ G.Adj x y ∧ G.Adj w y) with hC
  have hCle : ∑ y ∈ C, v y ≤ ε * (C.card : ℝ) := by
    have : ∑ y ∈ C, v y ≤ C.card • ε := by
      apply Finset.sum_le_card_nsmul
      intro y hy
      have := (Finset.mem_filter.1 hy).1
      unfold Sset at this
      simpa using this
    simpa [mul_comm] using this
  have hCcard : C.card ≤ 2 := by
    have hsub : C ⊆ Finset.univ.filter (fun y => G.Adj u y ∧ G.Adj y x ∧ G.Adj y w) := by
      intro y hy
      have := (Finset.mem_filter.1 hy).2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨this.1, this.2.1.symm, this.2.2.symm⟩
    exact (Finset.card_le_card hsub).trans
      (l12_k33 (by omega) G hG.1 u x w hux huw (Ne.symm hwx))
  have hcr : (C.card : ℝ) ≤ 2 := by exact_mod_cast hCcard
  have hεC : ε * (C.card : ℝ) ≤ 2 * ε := by nlinarith
  nlinarith
