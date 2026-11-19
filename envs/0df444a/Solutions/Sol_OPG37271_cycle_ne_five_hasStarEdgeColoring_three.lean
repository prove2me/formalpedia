-- Prove2me | solution 1 for OPG37271.cycle_ne_five_hasStarEdgeColoring_three
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T05:21:21.300336+00:00
-- url     : https://prove2.me/submissions/3d6321f4-2b69-4e30-8483-2036a7efb78b

import Definitions.Def_opg37271_star_edge_coloring
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

set_option autoImplicit false

open OPG37271

private def nextIdx (n i : ℕ) : ℕ :=
  if i + 1 = n then 0 else i + 1

private lemma nextIdx_eq_iff {n i j : ℕ} :
    nextIdx n i = j ↔ (i + 1 = n ∧ j = 0) ∨ (i + 1 ≠ n ∧ j = i + 1) := by
  unfold nextIdx
  split_ifs with h <;> omega

private lemma add_one_mod_eq_nextIdx {n i : ℕ} (hi : i < n) :
    (i + 1) % n = nextIdx n i := by
  unfold nextIdx
  split_ifs with h
  · rw [h, Nat.mod_self]
  · exact Nat.mod_eq_of_lt (by omega)

private def cycleColorNat (n i : ℕ) : ℕ :=
  if n % 3 = 0 then i % 3
  else if n % 3 = 1 then
    match i with
    | 0 => 0
    | 1 => 1
    | 2 => 2
    | 3 => 1
    | k + 4 => k % 3
  else
    match i with
    | 0 => 0
    | 1 => 1
    | 2 => 0
    | 3 => 2
    | 4 => 1
    | k + 5 => k % 3

private lemma cycleColorNat_ge_five (n k : ℕ) :
    cycleColorNat n (k + 5) =
      if n % 3 = 0 then (k + 5) % 3
      else if n % 3 = 1 then (k + 1) % 3
      else k % 3 := rfl

private lemma cycleColorNat_lt_three (n i : ℕ) : cycleColorNat n i < 3 := by
  by_cases hi : i < 5
  · have hic : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases hic with rfl | rfl | rfl | rfl | rfl <;>
      (dsimp only [cycleColorNat]; split_ifs <;> omega)
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 5 := ⟨i - 5, by omega⟩
    rw [cycleColorNat_ge_five]
    split_ifs <;> omega

private def cycleColor (n i : ℕ) : Fin 3 :=
  ⟨cycleColorNat n i, cycleColorNat_lt_three n i⟩

private lemma cycleColorNat_proper {n i : ℕ} (hn3 : 3 ≤ n) (hn5 : n ≠ 5) (hi : i < n) :
    cycleColorNat n i ≠ cycleColorNat n (nextIdx n i) := by
  by_cases hn8 : n < 8
  · have hcases : n = 3 ∨ n = 4 ∨ n = 6 ∨ n = 7 := by omega
    rcases hcases with rfl | rfl | rfl | rfl <;> decide +revert
  · by_cases hi5 : i < 5
    · have hnext : nextIdx n i = i + 1 := by unfold nextIdx; split_ifs <;> omega
      rw [hnext]
      have hic : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
      rcases hic with rfl | rfl | rfl | rfl | rfl <;>
        (dsimp only [cycleColorNat]; split_ifs <;> omega)
    · by_cases hlast : i + 1 = n
      · have hnext : nextIdx n i = 0 := by unfold nextIdx; rw [if_pos hlast]
        have h0 : cycleColorNat n 0 = 0 := by dsimp only [cycleColorNat]; split_ifs <;> omega
        obtain ⟨k, rfl⟩ : ∃ k, i = k + 5 := ⟨i - 5, by omega⟩
        rw [hnext, h0, cycleColorNat_ge_five]
        split_ifs <;> omega
      · have hnext : nextIdx n i = i + 1 := by unfold nextIdx; rw [if_neg hlast]
        obtain ⟨k, rfl⟩ : ∃ k, i = k + 5 := ⟨i - 5, by omega⟩
        have hkp1 : k + 5 + 1 = (k + 1) + 5 := by omega
        rw [hnext, hkp1, cycleColorNat_ge_five, cycleColorNat_ge_five]
        split_ifs <;> omega

private lemma cycleColorNat_no_p4 {n i₀ : ℕ} (hn6 : 6 ≤ n) (hi₀ : i₀ < n) :
    ¬ (cycleColorNat n i₀ = cycleColorNat n (nextIdx n (nextIdx n i₀)) ∧
       cycleColorNat n (nextIdx n i₀) = cycleColorNat n (nextIdx n (nextIdx n (nextIdx n i₀)))) := by
  by_cases hn8 : n < 8
  · have hcases : n = 6 ∨ n = 7 := by omega
    rcases hcases with rfl | rfl <;> decide +revert
  · by_cases hi5 : i₀ < 5
    · have s1 : nextIdx n i₀ = i₀ + 1 := by unfold nextIdx; split_ifs <;> omega
      have s2 : nextIdx n (i₀ + 1) = i₀ + 2 := by unfold nextIdx; split_ifs <;> omega
      have s3 : nextIdx n (i₀ + 2) = i₀ + 3 := by unfold nextIdx; split_ifs <;> omega
      rw [s1, s2, s3]
      have hic : i₀ = 0 ∨ i₀ = 1 ∨ i₀ = 2 ∨ i₀ = 3 ∨ i₀ = 4 := by omega
      rcases hic with rfl | rfl | rfl | rfl | rfl <;>
        (simp only [cycleColorNat]; split_ifs <;> simp)
    · by_cases hwrap : i₀ + 2 < n
      · have s1 : nextIdx n i₀ = i₀ + 1 := by unfold nextIdx; split_ifs <;> omega
        have s2 : nextIdx n (i₀ + 1) = i₀ + 2 := by unfold nextIdx; split_ifs <;> omega
        obtain ⟨k, rfl⟩ : ∃ k, i₀ = k + 5 := ⟨i₀ - 5, by omega⟩
        have hkp2 : k + 5 + 2 = (k + 2) + 5 := by omega
        rw [s1, s2, hkp2, cycleColorNat_ge_five, cycleColorNat_ge_five]
        rintro ⟨h1, _⟩
        revert h1
        split_ifs <;> omega
      · have hend : i₀ = n - 2 ∨ i₀ = n - 1 := by omega
        rcases hend with rfl | rfl
        · have s1 : nextIdx n (n - 2) = n - 1 := by unfold nextIdx; split_ifs <;> omega
          have s2 : nextIdx n (n - 1) = 0 := by unfold nextIdx; split_ifs <;> omega
          have s3 : nextIdx n 0 = 1 := by unfold nextIdx; split_ifs <;> omega
          have c0 : cycleColorNat n 0 = 0 := by dsimp only [cycleColorNat]; split_ifs <;> omega
          have c1 : cycleColorNat n 1 = 1 := by dsimp only [cycleColorNat]; split_ifs <;> omega
          obtain ⟨k, hk⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
          subst hk
          have heq1 : k + 7 - 2 = k + 5 := by omega
          have heq2 : k + 7 - 1 = (k + 1) + 5 := by omega
          rw [s1, s2, s3, c0, c1, heq1, heq2, cycleColorNat_ge_five, cycleColorNat_ge_five]
          split_ifs <;> omega
        · have s1 : nextIdx n (n - 1) = 0 := by unfold nextIdx; split_ifs <;> omega
          have s2 : nextIdx n 0 = 1 := by unfold nextIdx; split_ifs <;> omega
          have s3 : nextIdx n 1 = 2 := by unfold nextIdx; split_ifs <;> omega
          have c0 : cycleColorNat n 0 = 0 := by dsimp only [cycleColorNat]; split_ifs <;> omega
          have c1 : cycleColorNat n 1 = 1 := by dsimp only [cycleColorNat]; split_ifs <;> omega
          obtain ⟨k, hk⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
          subst hk
          have heq1 : k + 6 - 1 = k + 5 := by omega
          rw [s1, s2, s3, c0, c1, heq1, cycleColorNat_ge_five]
          rintro ⟨h1, h2⟩
          revert h1 h2
          dsimp only [cycleColorNat]
          split_ifs <;> omega

private lemma cycleColorNat_no_c4 {i₀ : ℕ} (hi₀ : i₀ < 4) :
    ¬ (cycleColorNat 4 i₀ = cycleColorNat 4 (nextIdx 4 (nextIdx 4 i₀)) ∧
       cycleColorNat 4 (nextIdx 4 i₀) = cycleColorNat 4 (nextIdx 4 (nextIdx 4 (nextIdx 4 i₀)))) := by
  decide +revert

private def cyclePairColor (n : ℕ) (x y : Fin n) : Fin 3 :=
  if (x.val + 1) % n = y.val then cycleColor n x.val
  else if (y.val + 1) % n = x.val then cycleColor n y.val
  else 0

private lemma cyclePairColor_symm {n : ℕ} (hn3 : 3 ≤ n) (x y : Fin n) :
    cyclePairColor n x y = cyclePairColor n y x := by
  unfold cyclePairColor
  rw [add_one_mod_eq_nextIdx x.isLt, add_one_mod_eq_nextIdx y.isLt]
  have hx := x.isLt
  have hy := y.isLt
  by_cases hxy : nextIdx n x.val = y.val
  · have hyx : nextIdx n y.val ≠ x.val := by
      intro hyx
      rw [nextIdx_eq_iff] at hxy hyx
      omega
    rw [if_pos hxy, if_neg hyx, if_pos hxy]
  · by_cases hyx : nextIdx n y.val = x.val
    · rw [if_neg hxy, if_pos hyx, if_pos hyx]
    · rw [if_neg hxy, if_neg hyx, if_neg hyx, if_neg hxy]

/-- The standard undirected cycle graph on `Fin n`, where `i` and `(i + 1) % n` are adjacent. -/
private abbrev cycleGraph (n : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun i j : Fin n => (i.val + 1) % n = j.val)

/-- Every cycle of length `n ≥ 3` with `n ≠ 5` admits a star 3-edge-coloring. -/
theorem solution (n : ℕ) (hn3 : 3 ≤ n) (hn5 : n ≠ 5) :
    HasStarEdgeColoring (SimpleGraph.fromRel (fun i j : Fin n => (i.val + 1) % n = j.val)) 3 := by
  let G := SimpleGraph.fromRel (fun i j : Fin n => (i.val + 1) % n = j.val)
  let c : EdgeColoring G (Fin 3) :=
    fun e => Sym2.lift ⟨cyclePairColor n, cyclePairColor_symm hn3⟩ e.1
  have hadj_iff : ∀ x y : Fin n, G.Adj x y ↔ nextIdx n x.val = y.val ∨ nextIdx n y.val = x.val := by
    intro x y
    rw [SimpleGraph.fromRel_adj, add_one_mod_eq_nextIdx x.isLt, add_one_mod_eq_nextIdx y.isLt]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      intro hxy
      subst hxy
      have hx := x.isLt
      rw [nextIdx_eq_iff] at h
      omega
  have hc_fwd : ∀ (x y : Fin n) (hxy : G.Adj x y),
      nextIdx n x.val = y.val → c.get x y hxy = cycleColor n x.val := by
    intro x y hxy hnext
    change cyclePairColor n x y = cycleColor n x.val
    unfold cyclePairColor
    rw [add_one_mod_eq_nextIdx x.isLt, if_pos hnext]
  have hc_bwd : ∀ (x y : Fin n) (hxy : G.Adj x y),
      nextIdx n y.val = x.val → c.get x y hxy = cycleColor n y.val := by
    intro x y hxy hnext
    have hsym : c.get x y hxy = c.get y x hxy.symm :=
      congrArg (fun e : G.edgeSet => c e) (Subtype.ext Sym2.eq_swap)
    rw [hsym]
    exact hc_fwd y x hxy.symm hnext
  have hstep_fwd : ∀ {a b d : Fin n}, G.Adj b d → a ≠ d →
      nextIdx n a.val = b.val → nextIdx n b.val = d.val := by
    intro a b d hbd had hab
    rcases (hadj_iff b d).mp hbd with h | h
    · exact h
    · exfalso
      apply had
      ext
      have ha := a.isLt
      have hb := b.isLt
      have hd := d.isLt
      rw [nextIdx_eq_iff] at hab h
      omega
  have hstep_bwd : ∀ {a b d : Fin n}, G.Adj b d → a ≠ d →
      nextIdx n b.val = a.val → nextIdx n d.val = b.val := by
    intro a b d hbd had hab
    rcases (hadj_iff b d).mp hbd with h | h
    · exfalso
      apply had
      ext
      have ha := a.isLt
      have hb := b.isLt
      have hd := d.isLt
      rw [nextIdx_eq_iff] at hab h
      omega
    · exact h
  refine ⟨c, ?_, ?_, ?_⟩
  · intro v u w hvu hvw huw heq
    have hv := v.isLt
    have hu := u.isLt
    have hw := w.isLt
    have huw_val : u.val ≠ w.val := fun h => huw (Fin.ext h)
    rcases (hadj_iff v u).mp hvu with hvu' | hvu' <;>
      rcases (hadj_iff v w).mp hvw with hvw' | hvw'
    · rw [nextIdx_eq_iff] at hvu' hvw'
      omega
    · rw [hc_fwd v u hvu hvu', hc_bwd v w hvw hvw', Fin.ext_iff] at heq
      exact cycleColorNat_proper hn3 hn5 w.isLt (hvw' ▸ heq.symm)
    · rw [hc_bwd v u hvu hvu', hc_fwd v w hvw hvw', Fin.ext_iff] at heq
      exact cycleColorNat_proper hn3 hn5 u.isLt (hvu' ▸ heq)
    · rw [nextIdx_eq_iff] at hvu' hvw'
      omega
  · rintro ⟨v₀, v₁, v₂, v₃, v₄, hnd, h01, h12, h23, h34, hc1, hc2⟩
    have hnd' := hnd
    simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, or_false,
      List.nodup_nil, and_true] at hnd'
    rcases hnd' with ⟨⟨_, n02, n03, n04⟩, ⟨_, n13, _⟩, ⟨_, n24⟩, _⟩
    have hn6 : 6 ≤ n := by
      have h0 := v₀.isLt; have h1 := v₁.isLt; have h2 := v₂.isLt
      have h3 := v₃.isLt; have h4 := v₄.isLt
      have n03v : v₀.val ≠ v₃.val := fun h => n03 (Fin.ext h)
      have n04v : v₀.val ≠ v₄.val := fun h => n04 (Fin.ext h)
      rcases (hadj_iff v₀ v₁).mp h01 with s01 | s01
      · have s12 := hstep_fwd h12 n02 s01
        have s23 := hstep_fwd h23 n13 s12
        have s34 := hstep_fwd h34 n24 s23
        rw [nextIdx_eq_iff] at s01 s12 s23 s34
        omega
      · have s12 := hstep_bwd h12 n02 s01
        have s23 := hstep_bwd h23 n13 s12
        have s34 := hstep_bwd h34 n24 s23
        rw [nextIdx_eq_iff] at s01 s12 s23 s34
        omega
    rcases (hadj_iff v₀ v₁).mp h01 with s01 | s01
    · have s12 := hstep_fwd h12 n02 s01
      have s23 := hstep_fwd h23 n13 s12
      have s34 := hstep_fwd h34 n24 s23
      rw [hc_fwd v₀ v₁ h01 s01, hc_fwd v₂ v₃ h23 s23, Fin.ext_iff] at hc1
      rw [hc_fwd v₁ v₂ h12 s12, hc_fwd v₃ v₄ h34 s34, Fin.ext_iff] at hc2
      change cycleColorNat n v₀.val = cycleColorNat n v₂.val at hc1
      change cycleColorNat n v₁.val = cycleColorNat n v₃.val at hc2
      rw [← s01] at s12 hc2
      rw [← s12] at s23 hc1
      rw [← s23] at hc2
      exact cycleColorNat_no_p4 hn6 v₀.isLt ⟨hc1, hc2⟩
    · have s12 := hstep_bwd h12 n02 s01
      have s23 := hstep_bwd h23 n13 s12
      have s34 := hstep_bwd h34 n24 s23
      rw [hc_bwd v₀ v₁ h01 s01, hc_bwd v₂ v₃ h23 s23, Fin.ext_iff] at hc1
      rw [hc_bwd v₁ v₂ h12 s12, hc_bwd v₃ v₄ h34 s34, Fin.ext_iff] at hc2
      change cycleColorNat n v₁.val = cycleColorNat n v₃.val at hc1
      change cycleColorNat n v₂.val = cycleColorNat n v₄.val at hc2
      rw [← s34] at s23 hc1
      rw [← s23] at s12 hc2
      rw [← s12] at hc1
      exact cycleColorNat_no_p4 hn6 v₄.isLt ⟨hc2.symm, hc1.symm⟩
  · rintro ⟨v₀, v₁, v₂, v₃, hnd, h01, h12, h23, h30, hc1, hc2⟩
    have hnd' := hnd
    simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, or_false,
      List.nodup_nil, and_true] at hnd'
    rcases hnd' with ⟨⟨_, n02, n03⟩, ⟨_, n13⟩, _⟩
    have n20 : v₂ ≠ v₀ := fun h => n02 h.symm
    rcases (hadj_iff v₀ v₁).mp h01 with s01 | s01
    · have s12 := hstep_fwd h12 n02 s01
      have s23 := hstep_fwd h23 n13 s12
      have s30 := hstep_fwd h30 n20 s23
      have hn4 : n = 4 := by
        have h0 := v₀.isLt; have h1 := v₁.isLt; have h2 := v₂.isLt; have h3 := v₃.isLt
        have n02v : v₀.val ≠ v₂.val := fun h => n02 (Fin.ext h)
        rw [nextIdx_eq_iff] at s01 s12 s23 s30
        omega
      rw [hc_fwd v₀ v₁ h01 s01, hc_fwd v₂ v₃ h23 s23, Fin.ext_iff] at hc1
      rw [hc_fwd v₁ v₂ h12 s12, hc_fwd v₃ v₀ h30 s30, Fin.ext_iff] at hc2
      change cycleColorNat n v₀.val = cycleColorNat n v₂.val at hc1
      change cycleColorNat n v₁.val = cycleColorNat n v₃.val at hc2
      rw [← s01] at s12 hc2
      rw [← s12] at s23 hc1
      rw [← s23] at hc2
      have hv0 : v₀.val < 4 := hn4 ▸ v₀.isLt
      subst hn4
      exact cycleColorNat_no_c4 hv0 ⟨hc1, hc2⟩
    · have s12 := hstep_bwd h12 n02 s01
      have s23 := hstep_bwd h23 n13 s12
      have s30 := hstep_bwd h30 n20 s23
      have hn4 : n = 4 := by
        have h0 := v₀.isLt; have h1 := v₁.isLt; have h2 := v₂.isLt; have h3 := v₃.isLt
        have n02v : v₀.val ≠ v₂.val := fun h => n02 (Fin.ext h)
        rw [nextIdx_eq_iff] at s01 s12 s23 s30
        omega
      rw [hc_bwd v₀ v₁ h01 s01, hc_bwd v₂ v₃ h23 s23, Fin.ext_iff] at hc1
      rw [hc_bwd v₁ v₂ h12 s12, hc_bwd v₃ v₀ h30 s30, Fin.ext_iff] at hc2
      change cycleColorNat n v₁.val = cycleColorNat n v₃.val at hc1
      change cycleColorNat n v₂.val = cycleColorNat n v₀.val at hc2
      rw [← s30] at s23 hc1
      rw [← s23] at s12 hc2
      rw [← s12] at hc1
      have hv0 : v₀.val < 4 := hn4 ▸ v₀.isLt
      subst hn4
      exact cycleColorNat_no_c4 hv0 ⟨hc2.symm, hc1.symm⟩
