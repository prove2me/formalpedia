-- Prove2me | solution 1 for TaitTobin.Planar.eq_7
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-15T12:18:25.505221+00:00
-- url     : https://prove2.me/submissions/268a6fdd-1cab-4e1e-be5f-4680a965318f

import Mathlib
import Definitions.Def_TaitTobin_Planar_Setting
import Theorems.Thm_TaitTobin_Planar_lemma_8
import Theorems.Thm_TaitTobin_Planar_lemma_9

set_option autoImplicit false

section E7

open Classical WangKangXue.SpectralTuran RobertsonSeymour1986.GM5 TaitTobin.Planar

/-! Reduction of TaitTobin.Planar.eq_7 to Lemma 8 (lambda > sqrt(2n-4)) and Lemma 9 (5)
(sum over L of v <= eps sqrt(2n-4) + 18/eps). -/

theorem e7_row {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n → ℝ) (l : ℝ)
    (h : (G.adjMatrix ℝ).mulVec v = l • v) (i : Fin n) :
    ∑ j, (if G.Adj i j then v j else 0) = l * v i := by
  have := congrFun h i
  simpa [Matrix.mulVec, dotProduct, SimpleGraph.adjMatrix_apply, ite_mul] using this

theorem e7_split {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n → ℝ) (ε : ℝ) (u : Fin n)
    (hpos : ∀ i, 0 < v i) (l : ℝ)
    (hrow : ∑ j, (if G.Adj u j then v j else 0) = l * v u) :
    l * v u ≤ (∑ z ∈ Lset ε v, v z) + ∑ y ∈ (Sset ε v).filter (fun y => G.Adj u y), v y := by
  have h1 : ∑ j, (if G.Adj u j then v j else 0) =
      (∑ j ∈ Finset.univ.filter (fun j => ε < v j), (if G.Adj u j then v j else 0)) +
      ∑ j ∈ Finset.univ.filter (fun j => ¬ ε < v j), (if G.Adj u j then v j else 0) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have h2 : ∑ j ∈ Finset.univ.filter (fun j => ε < v j), (if G.Adj u j then v j else 0)
      ≤ ∑ z ∈ Lset ε v, v z := by
    unfold Lset
    refine Finset.sum_le_sum (fun j _ => ?_)
    split_ifs
    · exact le_rfl
    · exact (hpos j).le
  have h3 : ∑ j ∈ Finset.univ.filter (fun j => ¬ ε < v j), (if G.Adj u j then v j else 0)
      = ∑ y ∈ (Sset ε v).filter (fun y => G.Adj u y), v y := by
    unfold Sset
    rw [Finset.filter_filter, Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [not_lt]
    by_cases h : v j ≤ ε <;> by_cases h' : G.Adj u j <;> simp [h, h']
  linarith

end E7

open Classical WangKangXue.SpectralTuran RobertsonSeymour1986.GM5 TaitTobin.Planar in
theorem solution : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n),
    TaitTobin.Outerplanar.IsSpecMax IsPlanar G →
    ∀ v : Fin n → ℝ, (G.adjMatrix ℝ).mulVec v = specRad G • v →
      (∀ i, 0 < v i) → (∀ i, v i ≤ 1) → ∀ x : Fin n, v x = 1 →
        ∀ u ∈ Lset ε v,
          (v u - ε) * Real.sqrt (2 * (n : ℝ) - 4) - 18 / ε ≤
            ∑ y ∈ (Sset ε v).filter (fun y => G.Adj u y), v y := by
  intro ε hε
  obtain ⟨N9, h9⟩ := TaitTobin.Planar.lemma_9 ε hε
  refine ⟨max N9 3, fun n hn G hG v hv hpos hle x hx u hu => ?_⟩
  have hn9 : n ≥ N9 := le_trans (le_max_left _ _) hn
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn
  have hlam := (TaitTobin.Planar.lemma_8 hn3 G hG).1
  have h5 := (h9 n hn9 G hG v hv hpos hle x hx).1
  have hrow := e7_row G v (specRad G) (by simpa using hv) u
  have hsp := e7_split G v ε u hpos (specRad G) hrow
  have hvu := hpos u
  have hmul : Real.sqrt (2 * (n : ℝ) - 4) * v u ≤ specRad G * v u :=
    mul_le_mul_of_nonneg_right hlam.le hvu.le
  nlinarith
