-- Prove2me | solution 1 for TaitTobin.Planar.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-15T12:10:35.242422+00:00
-- url     : https://prove2.me/submissions/58fbcf7a-e3f9-4f8d-a488-cc5ffceab2a4

import Mathlib
import Definitions.Def_TaitTobin_Planar_Setting
import Theorems.Thm_TaitTobin_Planar_lemma_8
import Theorems.Thm_TaitTobin_Planar_LS_counts

set_option autoImplicit false

section L9

open Classical WangKangXue.SpectralTuran RobertsonSeymour1986.GM5 TaitTobin.Planar

/-! Reduction of TaitTobin.Planar.lemma_9 to Lemma 8 (lambda > sqrt(2n-4)) and the edge counts
of LS_counts. Idea: lambda * sum_Z v = sum_u v_u d_Z(u); split u over S (v <= eps) and L (v <= 1). -/

theorem l9_between {n : ℕ} (G : SimpleGraph (Fin n)) (X Y : Finset (Fin n))
    (hd : Disjoint X Y) :
    ∑ i ∈ X, ∑ j ∈ Y, (if G.Adj i j then (1:ℝ) else 0) ≤
      (TaitTobin.Outerplanar.eBetween G X Y : ℝ) := by
  rw [← Finset.sum_product' (f := fun i j => if G.Adj i j then (1:ℝ) else 0), Finset.sum_boole]
  have key : ((X ×ˢ Y).filter (fun p : Fin n × Fin n => G.Adj p.1 p.2)).card ≤
      TaitTobin.Outerplanar.eBetween G X Y := by
    unfold TaitTobin.Outerplanar.eBetween
    refine Finset.card_le_card_of_injOn (fun p => s(p.1, p.2)) ?_ ?_
    · intro p hp
      simp only [Finset.coe_filter, Finset.mem_product, Set.mem_setOf_eq] at hp
      simp only [Finset.coe_filter, SimpleGraph.mem_edgeFinset, Set.mem_setOf_eq,
        SimpleGraph.mem_edgeSet]
      exact ⟨hp.2, p.1, hp.1.1, p.2, hp.1.2, rfl⟩
    · intro p hp q hq hpq
      simp only [Finset.coe_filter, Finset.mem_product, Set.mem_setOf_eq] at hp hq
      rcases Sym2.eq_iff.1 hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Prod.ext h1 h2
      · exact absurd (h1 ▸ hp.1.1) (Finset.disjoint_left.1 hd |>.mt (not_not.2 hq.1.2))
  exact_mod_cast key

theorem l9_within {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n)) :
    ∑ i ∈ X, ∑ j ∈ X, (if G.Adj i j then (1:ℝ) else 0) ≤
      2 * (TaitTobin.Outerplanar.eIn G X : ℝ) := by
  rw [← Finset.sum_product' (f := fun i j => if G.Adj i j then (1:ℝ) else 0), Finset.sum_boole]
  have gen : ∀ E : Finset (Sym2 (Fin n)),
      (∀ e, e ∈ E ↔ (e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ X)) →
      ((X ×ˢ X).filter (fun p : Fin n × Fin n => G.Adj p.1 p.2)).card ≤ 2 * E.card := by
    intro E hE
    calc ((X ×ˢ X).filter (fun p : Fin n × Fin n => G.Adj p.1 p.2)).card
        ≤ (E ×ˢ (Finset.univ : Finset Bool)).card := by
          refine Finset.card_le_card_of_injOn (fun p => (s(p.1, p.2), decide (p.1 < p.2))) ?_ ?_
          · intro p hp
            simp only [Finset.coe_filter, Finset.mem_product, Set.mem_setOf_eq] at hp
            simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, hE, Finset.coe_univ,
              Set.mem_univ, and_true]
            refine ⟨hp.2, ?_⟩
            intro v hv
            rcases Sym2.mem_iff.1 hv with rfl | rfl
            · exact hp.1.1
            · exact hp.1.2
          · intro p hp q hq hpq
            simp only [Finset.coe_filter, Finset.mem_product, Set.mem_setOf_eq] at hp hq
            have hpq' := Prod.mk.inj hpq
            rcases Sym2.eq_iff.1 hpq'.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact Prod.ext h1 h2
            · exfalso
              have hne : p.1 ≠ p.2 := hp.2.ne
              have h3 := hpq'.2
              rw [← h1, ← h2] at h3
              rcases lt_or_gt_of_ne hne with hlt | hgt
              · simp [hlt, not_lt.2 hlt.le] at h3
              · simp [hgt, not_lt.2 hgt.le] at h3
      _ = 2 * E.card := by rw [Finset.card_product]; simp [mul_comm]
  have key : ((X ×ˢ X).filter (fun p : Fin n × Fin n => G.Adj p.1 p.2)).card ≤
      2 * TaitTobin.Outerplanar.eIn G X := by
    unfold TaitTobin.Outerplanar.eIn
    exact gen _ (fun e => by simp)
  have := (Nat.cast_le (α := ℝ)).2 key
  push_cast at this
  exact this

theorem l9_eig {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n → ℝ) (l : ℝ)
    (h : (G.adjMatrix ℝ).mulVec v = l • v) (Z : Finset (Fin n)) :
    l * ∑ z ∈ Z, v z = ∑ u, (∑ z ∈ Z, if G.Adj u z then (1:ℝ) else 0) * v u := by
  have hrow : ∀ i, ∑ j, (if G.Adj i j then v j else 0) = l * v i := by
    intro i
    have := congrFun h i
    simpa [Matrix.mulVec, dotProduct, SimpleGraph.adjMatrix_apply, ite_mul] using this
  rw [Finset.mul_sum]
  calc ∑ z ∈ Z, l * v z = ∑ z ∈ Z, ∑ j, (if G.Adj z j then v j else 0) :=
        Finset.sum_congr rfl (fun z _ => (hrow z).symm)
    _ = ∑ j, ∑ z ∈ Z, (if G.Adj z j then v j else 0) := Finset.sum_comm
    _ = ∑ u, (∑ z ∈ Z, if G.Adj u z then (1:ℝ) else 0) * v u := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun z _ => ?_)
        by_cases hz : G.Adj z j
        · have hz' : G.Adj j z := hz.symm
          simp [hz, hz']
        · have hz' : ¬ G.Adj j z := fun h' => hz h'.symm
          simp [hz, hz']

/-- the split of the weighted degree sum over `S` (entries `≤ ε`) and `L` (entries `≤ 1`). -/
theorem l9_split {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n → ℝ) (ε : ℝ)
    (hle : ∀ i, v i ≤ 1) (hpos : ∀ i, 0 < v i) (hε : 0 < ε) (Z : Finset (Fin n)) :
    ∑ u, (∑ z ∈ Z, if G.Adj u z then (1:ℝ) else 0) * v u ≤
      ε * ∑ u ∈ Sset ε v, (∑ z ∈ Z, if G.Adj u z then (1:ℝ) else 0) +
        ∑ u ∈ Lset ε v, (∑ z ∈ Z, if G.Adj u z then (1:ℝ) else 0) := by
  set D : Fin n → ℝ := fun u => ∑ z ∈ Z, if G.Adj u z then (1:ℝ) else 0 with hD
  have hD0 : ∀ u, 0 ≤ D u := fun u =>
    Finset.sum_nonneg (fun z _ => by split_ifs <;> norm_num)
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin n))
    (fun z => v z ≤ ε) (fun u => D u * v u)
  have hL : (Finset.univ.filter (fun z => ¬ v z ≤ ε)) = Lset ε v := by
    ext z; simp [Lset]
  rw [hL] at hsplit
  have hS : (Finset.univ.filter (fun z => v z ≤ ε)) = Sset ε v := rfl
  rw [hS] at hsplit
  show ∑ u, D u * v u ≤ ε * ∑ u ∈ Sset ε v, D u + ∑ u ∈ Lset ε v, D u
  rw [← hsplit, Finset.mul_sum]
  refine add_le_add (Finset.sum_le_sum (fun u hu => ?_)) (Finset.sum_le_sum (fun u hu => ?_))
  · have : v u ≤ ε := by simpa [Sset] using hu
    nlinarith [hD0 u]
  · have := hle u
    nlinarith [hD0 u]

theorem l9_core {n : ℕ} (ε : ℝ) (hε : 0 < ε) (hn : 3 ≤ n) (G : SimpleGraph (Fin n))
    (v : Fin n → ℝ) (l : ℝ) (hl : (G.adjMatrix ℝ).mulVec v = l • v)
    (hlam : Real.sqrt (2 * (n : ℝ) - 4) < l)
    (hpos : ∀ i, 0 < v i) (hle : ∀ i, v i ≤ 1)
    (hSL : TaitTobin.Outerplanar.eBetween G (Sset ε v) (Lset ε v) ≤ 2 * n - 4)
    (hS : TaitTobin.Outerplanar.eIn G (Sset ε v) ≤ 3 * n - 6)
    (hL : (TaitTobin.Outerplanar.eIn G (Lset ε v) : ℝ) ≤ 9 * Real.sqrt (2 * (n : ℝ) - 4) / ε) :
    (∑ z ∈ Lset ε v, v z) ≤ ε * Real.sqrt (2 * (n : ℝ) - 4) + 18 / ε ∧
      (∑ z ∈ Sset ε v, v z) ≤ (1 + 3 * ε) * Real.sqrt (2 * (n : ℝ) - 4) := by
  set s := Real.sqrt (2 * (n : ℝ) - 4) with hs
  have hn3 : (3:ℝ) ≤ n := by exact_mod_cast hn
  have hpos2 : 0 < 2 * (n:ℝ) - 4 := by linarith
  have hs0 : 0 < s := Real.sqrt_pos.2 hpos2
  have hss : s * s = 2 * (n:ℝ) - 4 := Real.mul_self_sqrt hpos2.le
  have hl0 : 0 < l := hs0.trans hlam
  have hdisj : Disjoint (Sset ε v) (Lset ε v) := by
    unfold Sset Lset
    rw [Finset.disjoint_filter]
    intro z _ h1 h2; linarith
  have hSLr : (TaitTobin.Outerplanar.eBetween G (Sset ε v) (Lset ε v) : ℝ) ≤ 2 * (n:ℝ) - 4 := by
    have : ((2 * n - 4 : ℕ) : ℝ) = 2 * (n:ℝ) - 4 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [← this]; exact_mod_cast hSL
  have hSr : (TaitTobin.Outerplanar.eIn G (Sset ε v) : ℝ) ≤ 3 * (n:ℝ) - 6 := by
    have : ((3 * n - 6 : ℕ) : ℝ) = 3 * (n:ℝ) - 6 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [← this]; exact_mod_cast hS
  have hLL := l9_within G (Lset ε v)
  have hSS := l9_within G (Sset ε v)
  have hSLb := l9_between G (Sset ε v) (Lset ε v) hdisj
  -- the reversed sum
  have hLS : ∑ u ∈ Lset ε v, ∑ z ∈ Sset ε v, (if G.Adj u z then (1:ℝ) else 0) ≤
      (TaitTobin.Outerplanar.eBetween G (Sset ε v) (Lset ε v) : ℝ) := by
    refine le_trans (le_of_eq ?_) hSLb
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    by_cases h : G.Adj b a
    · have h' : G.Adj a b := h.symm
      simp [h, h']
    · have h' : ¬ G.Adj a b := fun h'' => h h''.symm
      simp [h, h']
  have hε' : 0 ≤ ε := hε.le
  have hsL : 0 ≤ ∑ z ∈ Lset ε v, v z := Finset.sum_nonneg (fun z _ => (hpos z).le)
  have hsS : 0 ≤ ∑ z ∈ Sset ε v, v z := Finset.sum_nonneg (fun z _ => (hpos z).le)
  constructor
  · have h1 := l9_eig G v l hl (Lset ε v)
    have h2 := l9_split G v ε hle hpos hε (Lset ε v)
    have h3 : l * ∑ z ∈ Lset ε v, v z ≤ s * (ε * s + 18 / ε) := by
      have e1 : 9 * s / ε * 2 = 18 * s / ε := by field_simp; ring
      have e2 : s * (ε * s + 18 / ε) = ε * (s * s) + 18 * s / ε := by field_simp
      rw [e2, hss]
      have : 2 * (TaitTobin.Outerplanar.eIn G (Lset ε v) : ℝ) ≤ 18 * s / ε := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hSLb hε']
    have h4 : s * ∑ z ∈ Lset ε v, v z ≤ l * ∑ z ∈ Lset ε v, v z :=
      mul_le_mul_of_nonneg_right hlam.le hsL
    exact le_of_mul_le_mul_left (h4.trans h3) hs0
  · have h1 := l9_eig G v l hl (Sset ε v)
    have h2 := l9_split G v ε hle hpos hε (Sset ε v)
    have h3 : l * ∑ z ∈ Sset ε v, v z ≤ s * ((1 + 3 * ε) * s) := by
      have : s * ((1 + 3 * ε) * s) = (s * s) + 3 * ε * (s * s) := by ring
      rw [this, hss]
      nlinarith [mul_le_mul_of_nonneg_left hSS hε']
    have h4 : s * ∑ z ∈ Sset ε v, v z ≤ l * ∑ z ∈ Sset ε v, v z :=
      mul_le_mul_of_nonneg_right hlam.le hsS
    exact le_of_mul_le_mul_left (h4.trans h3) hs0

end L9

open Classical WangKangXue.SpectralTuran RobertsonSeymour1986.GM5 TaitTobin.Planar in
theorem solution : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n),
    TaitTobin.Outerplanar.IsSpecMax IsPlanar G →
    ∀ v : Fin n → ℝ, (G.adjMatrix ℝ).mulVec v = specRad G • v →
      (∀ i, 0 < v i) → (∀ i, v i ≤ 1) → ∀ x : Fin n, v x = 1 →
        (∑ z ∈ Lset ε v, v z) ≤ ε * Real.sqrt (2 * (n : ℝ) - 4) + 18 / ε ∧
          (∑ z ∈ Sset ε v, v z) ≤ (1 + 3 * ε) * Real.sqrt (2 * (n : ℝ) - 4) := by
  intro ε hε
  obtain ⟨NL, hL⟩ := TaitTobin.Planar.LS_counts ε hε
  refine ⟨max NL 3, fun n hn G hG v hv hpos hle x hx => ?_⟩
  have hn' := hn
  simp only [ge_iff_le, max_le_iff] at hn'
  obtain ⟨hnL, hn3⟩ := hn'
  have hlam := (TaitTobin.Planar.lemma_8 hn3 G hG).1
  have hLc := hL n hnL G hG v hv hpos hle x hx
  exact l9_core ε hε hn3 G v _ hv hlam hpos hle hLc.2.1 hLc.2.2.1 hLc.2.2.2
