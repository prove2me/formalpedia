-- Prove2me | solution 1 for OPG37271.subcubic_ten_canonical_23
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T07:41:07.912486+00:00
-- url     : https://prove2.me/submissions/fb049fc7-36a2-4d43-b817-664415689a03

import Definitions.Def_opg37271_star_edge_coloring
import Mathlib.Data.Finset.Card

set_option autoImplicit false

open OPG37271

private structure Three (α : Type) where (v0 v1 v2 : α)
private def Three.get {α : Type} (t : Three α) : ℕ → α
  | 0 => t.v0 | 1 => t.v1 | _ => t.v2

private structure Five (α : Type) where (v0 v1 v2 v3 v4 : α)
private def Five.get {α : Type} (t : Five α) : ℕ → α
  | 0 => t.v0 | 1 => t.v1 | 2 => t.v2 | 3 => t.v3 | _ => t.v4

private structure Seven (α : Type) where (v0 v1 v2 v3 v4 v5 v6 : α)
private def Seven.get {α : Type} (t : Seven α) : ℕ → α
  | 0 => t.v0 | 1 => t.v1 | 2 => t.v2 | 3 => t.v3
  | 4 => t.v4 | 5 => t.v5 | _ => t.v6

private structure Nine (α : Type) where (v0 v1 v2 v3 v4 v5 v6 v7 v8 : α)
private def Nine.get {α : Type} (t : Nine α) : ℕ → α
  | 0 => t.v0 | 1 => t.v1 | 2 => t.v2 | 3 => t.v3 | 4 => t.v4
  | 5 => t.v5 | 6 => t.v6 | 7 => t.v7 | _ => t.v8

private structure Ten (α : Type) where (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 : α)
private def Ten.get {α : Type} (t : Ten α) : ℕ → α
  | 0 => t.v0 | 1 => t.v1 | 2 => t.v2 | 3 => t.v3 | 4 => t.v4
  | 5 => t.v5 | 6 => t.v6 | 7 => t.v7 | 8 => t.v8 | _ => t.v9

private def Ten.getFin {α : Type} (t : Ten α) (x : Fin 10) : α :=
  t.get x.val

private def fin10List : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
private def dig10 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

private lemma mem_fin10List (x : Fin 10) : x ∈ fin10List := by
  revert x; decide

private lemma mem_dig10 {d : ℕ} (hd : d < 10) : d ∈ dig10 := by
  revert hd; decide +revert

private lemma fin10_cases (x : Fin 10) :
    x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨
    x = 5 ∨ x = 6 ∨ x = 7 ∨ x = 8 ∨ x = 9 := by
  revert x; decide

private def checkPermTen (g : Ten (Fin 10)) : Bool :=
  fin10List.all fun x => fin10List.all fun y => x == y || g.getFin x != g.getFin y

private lemma injective_of_checkPermTen {g : Ten (Fin 10)} (hg : checkPermTen g = true) :
    Function.Injective g.getFin := by
  intro x y hxy
  by_contra hne
  have h1 := List.all_eq_true.mp hg x (mem_fin10List x)
  have h2 := List.all_eq_true.mp h1 y (mem_fin10List y)
  simp [hne, hxy] at h2


private lemma dig10_cases {d : ℕ} (hd : d < 10) :
    d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨
    d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨ d = 9 := by
  revert hd; decide +revert

private lemma lt_of_mem_dig10 {a : ℕ} (h : a ∈ dig10) : a < 10 := by
  revert a h; decide +revert

private lemma nat_beq_false_of_ne {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.beq_eq.mp hb) h

private lemma nat_ble_succ_iff {a b : ℕ} : Nat.ble a.succ b = true ↔ a < b := by
  rw [Nat.ble_eq]; omega

private def memNat (x : ℕ) : List ℕ → Bool
  | [] => false
  | h :: t => Nat.beq x h || memNat x t

private lemma memNat_iff {x : ℕ} {l : List ℕ} : memNat x l = true ↔ x ∈ l := by
  induction l with
  | nil => simp [memNat]
  | cons h t ih => simp [memNat, Nat.beq_eq, ih]

private lemma memNat_eq_false_of_notMem {x : ℕ} {l : List ℕ} (h : x ∉ l) :
    memNat x l = false := by
  cases hm : memNat x l
  · rfl
  · exact absurd (memNat_iff.mp hm) h

private def memPairNat (x y : ℕ) : List (ℕ × ℕ) → Bool
  | [] => false
  | (a, b) :: t => (Nat.beq x a && Nat.beq y b) || memPairNat x y t

private lemma memPairNat_iff {x y : ℕ} {l : List (ℕ × ℕ)} :
    memPairNat x y l = true ↔ (x, y) ∈ l := by
  induction l with
  | nil => simp [memPairNat]
  | cons p t ih =>
    rcases p with ⟨a, b⟩
    simp [memPairNat, Nat.beq_eq, ih]

private def checkPermNat (g : Ten ℕ) : Bool :=
  dig10.all (fun x => Nat.ble (g.get x).succ 10) &&
  dig10.all (fun x => dig10.all (fun y => Nat.beq x y || !Nat.beq (g.get x) (g.get y)))

private lemma checkPermNat_spec {g : Ten ℕ} (hg : checkPermNat g = true) :
    (∀ x : ℕ, x < 10 → g.get x < 10) ∧
    (∀ x y : ℕ, x < 10 → y < 10 → g.get x = g.get y → x = y) := by
  unfold checkPermNat at hg
  rw [Bool.and_eq_true] at hg
  refine ⟨?_, ?_⟩
  · intro x hx
    exact nat_ble_succ_iff.mp (List.all_eq_true.mp hg.1 x (mem_dig10 hx))
  · intro x y hx hy heq
    by_contra hne
    have h1 := List.all_eq_true.mp hg.2 x (mem_dig10 hx)
    have h2 := List.all_eq_true.mp h1 y (mem_dig10 hy)
    rw [nat_beq_false_of_ne hne, Bool.false_or, heq, Nat.beq_refl] at h2
    contradiction

private def nbrsTenNat (adjMat : Ten (Ten Bool)) : Ten (List ℕ) :=
  let adj (x y : ℕ) : Bool := (adjMat.get x).get y
  ⟨dig10.filter (adj 0), dig10.filter (adj 1), dig10.filter (adj 2),
   dig10.filter (adj 3), dig10.filter (adj 4), dig10.filter (adj 5),
   dig10.filter (adj 6), dig10.filter (adj 7), dig10.filter (adj 8),
   dig10.filter (adj 9)⟩

private lemma mem_nbrsTenNat {adjMat : Ten (Ten Bool)} {x y : ℕ}
    (hx : x < 10) (hy : y < 10) (h : (adjMat.get x).get y = true) :
    y ∈ (nbrsTenNat adjMat).get x := by
  rcases dig10_cases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact List.mem_filter.mpr ⟨mem_dig10 hy, h⟩

private def checkStarMatNat (k : ℕ) (adjMat : Ten (Ten Bool)) (colMat : Ten (Ten ℕ)) : Bool :=
  let adj (x y : ℕ) : Bool := (adjMat.get x).get y
  let col (x y : ℕ) : ℕ := (colMat.get x).get y
  let ns := nbrsTenNat adjMat
  dig10.all (fun x => dig10.all (fun y =>
    (adj x y == adj y x) && Nat.ble (col x y).succ k && Nat.beq (col x y) (col y x))) &&
  dig10.all (fun v =>
    let nv := ns.get v
    nv.all (fun u => nv.all (fun w => Nat.beq u w || !Nat.beq (col v u) (col v w)))) &&
  dig10.all (fun v0 =>
    (ns.get v0).all (fun v1 =>
      (ns.get v1).all (fun v2 =>
        Nat.beq v2 v0 ||
        (ns.get v2).all (fun v3 =>
          Nat.beq v3 v0 || Nat.beq v3 v1 || !Nat.beq (col v0 v1) (col v2 v3) ||
          ((!adj v3 v0 || !Nat.beq (col v1 v2) (col v3 v0)) &&
           (ns.get v3).all (fun v4 =>
             Nat.beq v4 v0 || Nat.beq v4 v1 || Nat.beq v4 v2 || !Nat.beq (col v1 v2) (col v3 v4)))))))

private lemma adjMat_symm_of_checkStarMatNat {k : ℕ} {adjMat : Ten (Ten Bool)}
    {colMat : Ten (Ten ℕ)} (hstar : checkStarMatNat k adjMat colMat = true)
    {a b : ℕ} (ha : a < 10) (hb : b < 10) :
    (adjMat.get a).get b = (adjMat.get b).get a := by
  unfold checkStarMatNat at hstar
  dsimp only at hstar
  rw [Bool.and_eq_true, Bool.and_eq_true] at hstar
  have h1 := List.all_eq_true.mp hstar.1.1 a (mem_dig10 ha)
  have h2 := List.all_eq_true.mp h1 b (mem_dig10 hb)
  simp only [Bool.and_eq_true, beq_iff_eq] at h2
  exact h2.1.1

private lemma hasStarEdgeColoring_of_inj_certNat {G : SimpleGraph (Fin 10)} {k : ℕ}
    {φ : Fin 10 → ℕ} {adjMat : Ten (Ten Bool)} {colMat : Ten (Ten ℕ)}
    (hφ_lt : ∀ x : Fin 10, φ x < 10)
    (hφ_inj : Function.Injective φ)
    (hstar : checkStarMatNat k adjMat colMat = true)
    (hadj : ∀ x y : Fin 10, G.Adj x y → (adjMat.get (φ x)).get (φ y) = true) :
    HasStarEdgeColoring G k := by
  unfold checkStarMatNat at hstar
  dsimp only at hstar
  rw [Bool.and_eq_true, Bool.and_eq_true] at hstar
  rcases hstar with ⟨⟨hcol_ok, hprop_ok⟩, hp4c4_ok⟩
  have hcol_entry : ∀ x y : Fin 10,
      (colMat.get (φ x)).get (φ y) < k ∧
      (colMat.get (φ x)).get (φ y) = (colMat.get (φ y)).get (φ x) := by
    intro x y
    have h1 := List.all_eq_true.mp hcol_ok (φ x) (mem_dig10 (hφ_lt x))
    have h2 := List.all_eq_true.mp h1 (φ y) (mem_dig10 (hφ_lt y))
    simp only [Bool.and_eq_true, nat_ble_succ_iff, Nat.beq_eq] at h2
    exact ⟨h2.1.2, h2.2⟩
  let colPair (x y : Fin 10) : Fin k :=
    ⟨(colMat.get (φ x)).get (φ y), (hcol_entry x y).1⟩
  have hcolPair_symm : ∀ x y : Fin 10, colPair x y = colPair y x :=
    fun x y => Fin.ext (hcol_entry x y).2
  let c : EdgeColoring G (Fin k) := fun e => Sym2.lift ⟨colPair, hcolPair_symm⟩ e.1
  have hc_get : ∀ x y (hxy : G.Adj x y), c.get x y hxy = colPair x y := fun _ _ _ => rfl
  refine ⟨c, ?_, ?_, ?_⟩
  · intro v u w hvu hvw huw heq
    rw [hc_get, hc_get] at heq
    have hval : (colMat.get (φ v)).get (φ u) = (colMat.get (φ v)).get (φ w) :=
      congrArg Fin.val heq
    have hgu := mem_nbrsTenNat (hφ_lt v) (hφ_lt u) (hadj v u hvu)
    have hgw := mem_nbrsTenNat (hφ_lt v) (hφ_lt w) (hadj v w hvw)
    have hne : φ u ≠ φ w := fun h => huw (hφ_inj h)
    have p1 := List.all_eq_true.mp hprop_ok (φ v) (mem_dig10 (hφ_lt v))
    have p2 := List.all_eq_true.mp p1 (φ u) hgu
    have p3 := List.all_eq_true.mp p2 (φ w) hgw
    rw [nat_beq_false_of_ne hne, Bool.false_or, hval, Nat.beq_refl] at p3
    contradiction
  · rintro ⟨v₀, v₁, v₂, v₃, v₄, hnd, h01, h12, h23, h34, hc1, hc2⟩
    rw [hc_get, hc_get] at hc1 hc2
    have hv1 : (colMat.get (φ v₀)).get (φ v₁) = (colMat.get (φ v₂)).get (φ v₃) :=
      congrArg Fin.val hc1
    have hv2 : (colMat.get (φ v₁)).get (φ v₂) = (colMat.get (φ v₃)).get (φ v₄) :=
      congrArg Fin.val hc2
    simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, or_false,
      List.nodup_nil, and_true] at hnd
    rcases hnd with ⟨⟨_, n02, n03, n04⟩, ⟨_, n13, n14⟩, ⟨_, n24⟩, _⟩
    have q0 := List.all_eq_true.mp hp4c4_ok (φ v₀) (mem_dig10 (hφ_lt v₀))
    have q1 := List.all_eq_true.mp q0 (φ v₁) (mem_nbrsTenNat (hφ_lt v₀) (hφ_lt v₁) (hadj v₀ v₁ h01))
    have q2 := List.all_eq_true.mp q1 (φ v₂) (mem_nbrsTenNat (hφ_lt v₁) (hφ_lt v₂) (hadj v₁ v₂ h12))
    rw [nat_beq_false_of_ne (fun h => n02 (hφ_inj h.symm)), Bool.false_or] at q2
    have q3 := List.all_eq_true.mp q2 (φ v₃) (mem_nbrsTenNat (hφ_lt v₂) (hφ_lt v₃) (hadj v₂ v₃ h23))
    have gf1 : (!Nat.beq ((colMat.get (φ v₀)).get (φ v₁)) ((colMat.get (φ v₂)).get (φ v₃))) = false := by
      rw [hv1, Nat.beq_refl]; rfl
    rw [nat_beq_false_of_ne (fun h => n03 (hφ_inj h.symm)),
        nat_beq_false_of_ne (fun h => n13 (hφ_inj h.symm)),
        gf1, Bool.false_or, Bool.false_or, Bool.false_or, Bool.and_eq_true] at q3
    have q4 := List.all_eq_true.mp q3.2 (φ v₄) (mem_nbrsTenNat (hφ_lt v₃) (hφ_lt v₄) (hadj v₃ v₄ h34))
    have gf2 : (!Nat.beq ((colMat.get (φ v₁)).get (φ v₂)) ((colMat.get (φ v₃)).get (φ v₄))) = false := by
      rw [hv2, Nat.beq_refl]; rfl
    rw [nat_beq_false_of_ne (fun h => n04 (hφ_inj h.symm)),
        nat_beq_false_of_ne (fun h => n14 (hφ_inj h.symm)),
        nat_beq_false_of_ne (fun h => n24 (hφ_inj h.symm)),
        gf2] at q4
    contradiction
  · rintro ⟨v₀, v₁, v₂, v₃, hnd, h01, h12, h23, h30, hc1, hc2⟩
    rw [hc_get, hc_get] at hc1 hc2
    have hv1 : (colMat.get (φ v₀)).get (φ v₁) = (colMat.get (φ v₂)).get (φ v₃) :=
      congrArg Fin.val hc1
    have hv2 : (colMat.get (φ v₁)).get (φ v₂) = (colMat.get (φ v₃)).get (φ v₀) :=
      congrArg Fin.val hc2
    simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, or_false,
      List.nodup_nil, and_true] at hnd
    rcases hnd with ⟨⟨_, n02, n03⟩, ⟨_, n13⟩, _⟩
    have q0 := List.all_eq_true.mp hp4c4_ok (φ v₀) (mem_dig10 (hφ_lt v₀))
    have q1 := List.all_eq_true.mp q0 (φ v₁) (mem_nbrsTenNat (hφ_lt v₀) (hφ_lt v₁) (hadj v₀ v₁ h01))
    have q2 := List.all_eq_true.mp q1 (φ v₂) (mem_nbrsTenNat (hφ_lt v₁) (hφ_lt v₂) (hadj v₁ v₂ h12))
    rw [nat_beq_false_of_ne (fun h => n02 (hφ_inj h.symm)), Bool.false_or] at q2
    have q3 := List.all_eq_true.mp q2 (φ v₃) (mem_nbrsTenNat (hφ_lt v₂) (hφ_lt v₃) (hadj v₂ v₃ h23))
    have gf1 : (!Nat.beq ((colMat.get (φ v₀)).get (φ v₁)) ((colMat.get (φ v₂)).get (φ v₃))) = false := by
      rw [hv1, Nat.beq_refl]; rfl
    have gf2 : (!Nat.beq ((colMat.get (φ v₁)).get (φ v₂)) ((colMat.get (φ v₃)).get (φ v₀))) = false := by
      rw [hv2, Nat.beq_refl]; rfl
    rw [nat_beq_false_of_ne (fun h => n03 (hφ_inj h.symm)),
        nat_beq_false_of_ne (fun h => n13 (hφ_inj h.symm)),
        gf1, Bool.false_or, Bool.false_or, Bool.false_or, Bool.and_eq_true,
        hadj v₃ v₀ h30, gf2] at q3
    exact absurd q3.1 (by decide)

-- Subcubic and 2-regular Finset helpers

private lemma card_neighborFinset_le_three {G : SimpleGraph (Fin 10)} [DecidableRel G.Adj]
    (hsub : IsSubcubic G) (v : Fin 10) :
    (G.neighborFinset v).card ≤ 3 := by
  have h : ((G.neighborFinset v : Set (Fin 10))).encard ≤ 3 := by
    convert hsub v using 1
    congr 1; ext x; simp
  rw [Set.encard_coe_eq_coe_finsetCard] at h
  exact Nat.cast_le.mp h

private lemma card_neighborFinset_eq_two {T : SimpleGraph (Fin 10)} [DecidableRel T.Adj]
    (h2reg : ∀ v : Fin 10, (T.neighborSet v).encard = 2) (v : Fin 10) :
    (T.neighborFinset v).card = 2 := by
  have h : ((T.neighborFinset v : Set (Fin 10))).encard = 2 := by
    convert h2reg v using 1
    congr 1; ext x; simp
  rw [Set.encard_coe_eq_coe_finsetCard] at h
  exact Nat.cast_injective h

private lemma at_most_one_extra_adj {B G : SimpleGraph (Fin 10)} [DecidableRel G.Adj]
    (hBG : B ≤ G) (hdeg3 : ∀ v : Fin 10, (G.neighborFinset v).card ≤ 3)
    {x b₁ b₂ y₁ y₂ : Fin 10}
    (hb12 : b₁ ≠ b₂) (hb1 : B.Adj x b₁) (hb2 : B.Adj x b₂)
    (hy1 : G.Adj x y₁) (hny1 : ¬ B.Adj x y₁)
    (hy2 : G.Adj x y₂) (hny2 : ¬ B.Adj x y₂) :
    y₁ = y₂ := by
  by_contra hy12
  have hb1y1 : b₁ ≠ y₁ := fun h => hny1 (h ▸ hb1)
  have hb1y2 : b₁ ≠ y₂ := fun h => hny2 (h ▸ hb1)
  have hb2y1 : b₂ ≠ y₁ := fun h => hny1 (h ▸ hb2)
  have hb2y2 : b₂ ≠ y₂ := fun h => hny2 (h ▸ hb2)
  have hsub4 : ({b₁, b₂, y₁, y₂} : Finset (Fin 10)) ⊆ G.neighborFinset x := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rw [SimpleGraph.mem_neighborFinset]
    rcases hz with rfl | rfl | rfl | rfl
    · exact hBG hb1
    · exact hBG hb2
    · exact hy1
    · exact hy2
  have hle := le_trans (Finset.card_le_card hsub4) (hdeg3 x)
  have h4 : ({b₁, b₂, y₁, y₂} : Finset (Fin 10)).card = 4 := by
    simp [hb12, hb1y1, hb1y2, hb2y1, hb2y2, hy12]
  omega

private lemma exists_fpf_involution_on_finset (m : Fin 10 → Fin 10)
    (hinv : ∀ x, m (m x) = x) :
    ∀ (k : ℕ) (S : Finset (Fin 10)),
      S.card = 2 * k →
      (∀ x ∈ S, m x ∈ S) →
      ∃ m' : Fin 10 → Fin 10,
        (∀ x, m' (m' x) = x) ∧
        (∀ x ∈ S, m' x ∈ S ∧ m' x ≠ x) ∧
        (∀ x ∉ S, m' x = x) ∧
        (∀ x ∈ S, m x ≠ x → m' x = m x) := by
  intro k
  induction k with
  | zero =>
    intro S hcard _
    have hS : S = ∅ := Finset.card_eq_zero.mp hcard
    subst hS
    refine ⟨id, fun _ => rfl, ?_, fun _ _ => rfl, ?_⟩
    · intro x hx; exact absurd hx (Finset.notMem_empty x)
    · intro x hx; exact absurd hx (Finset.notMem_empty x)
  | succ k ih =>
    intro S hcard hclosed
    by_cases hmov : ∃ c ∈ S, m c ≠ c
    · rcases hmov with ⟨c, hcS, hmc_ne⟩
      let d := m c
      have hdS : d ∈ S := hclosed c hcS
      have hcd : c ≠ d := hmc_ne.symm
      let S' := (S.erase d).erase c
      have hc_mem_erd : c ∈ S.erase d := Finset.mem_erase.mpr ⟨hcd, hcS⟩
      have hcard' : S'.card = 2 * k := by
        dsimp only [S']
        rw [Finset.card_erase_of_mem hc_mem_erd, Finset.card_erase_of_mem hdS]
        omega
      have hclosed' : ∀ x ∈ S', m x ∈ S' := by
        intro x hx
        have hxc : x ≠ c := (Finset.mem_erase.mp hx).1
        have hxd : x ≠ d := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
        have hxS : x ∈ S := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).2
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, hclosed x hxS⟩⟩
        · intro hmx; exact hxd (by rw [← hinv x, hmx])
        · intro hmx; exact hxc (by rw [← hinv x, hmx, hinv c])
      rcases ih S' hcard' hclosed' with ⟨m₀, hm₀_inv, hm₀_S', hm₀_out, hm₀_ext⟩
      let m' (x : Fin 10) : Fin 10 := if x = c then d else if x = d then c else m₀ x
      refine ⟨m', ?_, ?_, ?_, ?_⟩
      · intro x
        by_cases hxc : x = c
        · subst hxc; simp [m', hcd.symm]
        · by_cases hxd : x = d
          · subst hxd; simp [m', hxc]
          · have hm₀_ne : m₀ x ≠ c ∧ m₀ x ≠ d := by
              by_cases hxS : x ∈ S
              · have hxS' : x ∈ S' := Finset.mem_erase.mpr ⟨hxc, Finset.mem_erase.mpr ⟨hxd, hxS⟩⟩
                have hmS' := (hm₀_S' x hxS').1
                exact ⟨(Finset.mem_erase.mp hmS').1,
                  (Finset.mem_erase.mp (Finset.mem_erase.mp hmS').2).1⟩
              · have hxS' : x ∉ S' :=
                  fun h => hxS (Finset.mem_erase.mp (Finset.mem_erase.mp h).2).2
                rw [hm₀_out x hxS']; exact ⟨hxc, hxd⟩
            simp [m', hxc, hxd, hm₀_ne.1, hm₀_ne.2, hm₀_inv x]
      · intro x hxS
        by_cases hxc : x = c
        · subst hxc; simp [m', hdS, hcd.symm]
        · by_cases hxd : x = d
          · subst hxd; simp [m', hxc, hcS, hcd]
          · have hxS' : x ∈ S' := Finset.mem_erase.mpr ⟨hxc, Finset.mem_erase.mpr ⟨hxd, hxS⟩⟩
            obtain ⟨hmS', hne'⟩ := hm₀_S' x hxS'
            have hmS : m₀ x ∈ S := (Finset.mem_erase.mp (Finset.mem_erase.mp hmS').2).2
            simp [m', hxc, hxd, hmS, hne']
      · intro x hxS
        have hxc : x ≠ c := fun h => hxS (h ▸ hcS)
        have hxd : x ≠ d := fun h => hxS (h ▸ hdS)
        have hxS' : x ∉ S' := fun h => hxS (Finset.mem_erase.mp (Finset.mem_erase.mp h).2).2
        simp [m', hxc, hxd, hm₀_out x hxS']
      · intro x hxS hmx
        by_cases hxc : x = c
        · subst hxc; simp [m', d]
        · by_cases hxd : x = d
          · subst hxd; simp [m', hxc, d, hinv c]
          · have hxS' : x ∈ S' := Finset.mem_erase.mpr ⟨hxc, Finset.mem_erase.mpr ⟨hxd, hxS⟩⟩
            simp [m', hxc, hxd, hm₀_ext x hxS' hmx]
    · push Not at hmov
      have hgt1 : 1 < S.card := by omega
      rcases Finset.one_lt_card.mp hgt1 with ⟨a, haS, b, hbS, hab⟩
      let S' := (S.erase b).erase a
      have ha_mem_erb : a ∈ S.erase b := Finset.mem_erase.mpr ⟨hab, haS⟩
      have hcard' : S'.card = 2 * k := by
        dsimp only [S']
        rw [Finset.card_erase_of_mem ha_mem_erb, Finset.card_erase_of_mem hbS]
        omega
      have hclosed' : ∀ x ∈ S', m x ∈ S' := by
        intro x hx
        have hxS : x ∈ S := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).2
        rw [hmov x hxS]
        exact hx
      rcases ih S' hcard' hclosed' with ⟨m₀, hm₀_inv, hm₀_S', hm₀_out, _⟩
      let m' (x : Fin 10) : Fin 10 := if x = a then b else if x = b then a else m₀ x
      refine ⟨m', ?_, ?_, ?_, ?_⟩
      · intro x
        by_cases hxa : x = a
        · subst hxa; simp [m', hab.symm]
        · by_cases hxb : x = b
          · subst hxb; simp [m', hxa]
          · have hm₀_ne : m₀ x ≠ a ∧ m₀ x ≠ b := by
              by_cases hxS : x ∈ S
              · have hxS' : x ∈ S' := Finset.mem_erase.mpr ⟨hxa, Finset.mem_erase.mpr ⟨hxb, hxS⟩⟩
                have hmS' := (hm₀_S' x hxS').1
                exact ⟨(Finset.mem_erase.mp hmS').1,
                  (Finset.mem_erase.mp (Finset.mem_erase.mp hmS').2).1⟩
              · have hxS' : x ∉ S' :=
                  fun h => hxS (Finset.mem_erase.mp (Finset.mem_erase.mp h).2).2
                rw [hm₀_out x hxS']; exact ⟨hxa, hxb⟩
            simp [m', hxa, hxb, hm₀_ne.1, hm₀_ne.2, hm₀_inv x]
      · intro x hxS
        by_cases hxa : x = a
        · subst hxa; simp [m', hbS, hab.symm]
        · by_cases hxb : x = b
          · subst hxb; simp [m', hxa, haS, hab]
          · have hxS' : x ∈ S' := Finset.mem_erase.mpr ⟨hxa, Finset.mem_erase.mpr ⟨hxb, hxS⟩⟩
            obtain ⟨hmS', hne'⟩ := hm₀_S' x hxS'
            have hmS : m₀ x ∈ S := (Finset.mem_erase.mp (Finset.mem_erase.mp hmS').2).2
            simp [m', hxa, hxb, hmS, hne']
      · intro x hxS
        have hxa : x ≠ a := fun h => hxS (h ▸ haS)
        have hxb : x ≠ b := fun h => hxS (h ▸ hbS)
        have hxS' : x ∉ S' := fun h => hxS (Finset.mem_erase.mp (Finset.mem_erase.mp h).2).2
        simp [m', hxa, hxb, hm₀_out x hxS']
      · intro x hxS hmx
        exact absurd (hmov x hxS) hmx

private lemma exists_fpf_extension_of_two_reg_base {B G : SimpleGraph (Fin 10)}
    [DecidableRel G.Adj]
    (hBG : B ≤ G) (hdeg3 : ∀ v : Fin 10, (G.neighborFinset v).card ≤ 3)
    (hb2 : ∀ x : Fin 10, ∃ b₁ b₂ : Fin 10, b₁ ≠ b₂ ∧ B.Adj x b₁ ∧ B.Adj x b₂) :
    ∃ m' : Fin 10 → Fin 10,
      (∀ x, m' (m' x) = x) ∧
      (∀ x, m' x ≠ x) ∧
      (∀ x y : Fin 10, G.Adj x y → B.Adj x y ∨ m' x = y) := by
  classical
  let m (x : Fin 10) : Fin 10 :=
    if h : ∃ y : Fin 10, G.Adj x y ∧ ¬ B.Adj x y then Classical.choose h else x
  have hm_spec : ∀ x y : Fin 10, G.Adj x y → ¬ B.Adj x y → m x = y := by
    intro x y hxy hnB
    have hex : ∃ z : Fin 10, G.Adj x z ∧ ¬ B.Adj x z := ⟨y, hxy, hnB⟩
    have hch := Classical.choose_spec hex
    rcases hb2 x with ⟨b₁, b₂, hb12, hb1, hb2'⟩
    have heq := at_most_one_extra_adj hBG hdeg3 hb12 hb1 hb2' hch.1 hch.2 hxy hnB
    simp only [m, dif_pos hex, heq]
  have hm_inv : ∀ x : Fin 10, m (m x) = x := by
    intro x
    by_cases hex : ∃ y : Fin 10, G.Adj x y ∧ ¬ B.Adj x y
    · have hch := Classical.choose_spec hex
      have hmx : m x = Classical.choose hex := by simp only [m, dif_pos hex]
      rw [hmx]
      exact hm_spec (Classical.choose hex) x hch.1.symm (fun hb => hch.2 hb.symm)
    · have hmx : m x = x := by simp only [m, dif_neg hex]
      rw [hmx, hmx]
  have hcard10 : (Finset.univ : Finset (Fin 10)).card = 2 * 5 := by decide
  rcases exists_fpf_involution_on_finset m hm_inv 5 Finset.univ hcard10
      (fun _ _ => Finset.mem_univ _) with ⟨m', hm'_inv, hm'_S, _, hm'_ext⟩
  refine ⟨m', hm'_inv, fun x => (hm'_S x (Finset.mem_univ x)).2, ?_⟩
  intro x y hxy
  by_cases hB : B.Adj x y
  · exact Or.inl hB
  · right
    have hmx : m x = y := hm_spec x y hxy hB
    have hne : m x ≠ x := by rw [hmx]; exact hxy.ne.symm
    rw [hm'_ext x (Finset.mem_univ x) hne, hmx]


private def baseEdges : ℕ → List (Fin 10 × Fin 10)
  | 0 => [(0, 1), (0, 9), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7), (7, 8), (8, 9)]
  | 1 => [(0, 1), (0, 4), (1, 2), (2, 3), (3, 4), (5, 6), (5, 9), (6, 7), (7, 8), (8, 9)]
  | 2 => [(0, 1), (0, 6), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (7, 8), (7, 9), (8, 9)]
  | 3 => [(0, 1), (0, 5), (1, 2), (2, 3), (3, 4), (4, 5), (6, 7), (6, 9), (7, 8), (8, 9)]
  | _ => [(0, 1), (0, 3), (1, 2), (2, 3), (4, 5), (4, 6), (5, 6), (7, 8), (7, 9), (8, 9)]

private def baseAdjSymBool (b : ℕ) (x y : Fin 10) : Bool :=
  (baseEdges b).contains (x, y) || (baseEdges b).contains (y, x)

private lemma baseAdjSymBool_symm (b : ℕ) (x y : Fin 10) :
    baseAdjSymBool b x y = baseAdjSymBool b y x := by
  unfold baseAdjSymBool; rw [Bool.or_comm]

private def baseGraph (b : ℕ) : SimpleGraph (Fin 10) where
  Adj x y := x ≠ y ∧ baseAdjSymBool b x y = true
  symm := ⟨fun _ _ h => ⟨h.1.symm, by rw [baseAdjSymBool_symm]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private instance baseGraph_decidableAdj (b : ℕ) : DecidableRel (baseGraph b).Adj :=
  fun _ _ => instDecidableAnd

private def baseEdgesNat : ℕ → List (ℕ × ℕ)
  | 0 => [(0, 1), (0, 9), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7), (7, 8), (8, 9)]
  | 1 => [(0, 1), (0, 4), (1, 2), (2, 3), (3, 4), (5, 6), (5, 9), (6, 7), (7, 8), (8, 9)]
  | 2 => [(0, 1), (0, 6), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (7, 8), (7, 9), (8, 9)]
  | 3 => [(0, 1), (0, 5), (1, 2), (2, 3), (3, 4), (4, 5), (6, 7), (6, 9), (7, 8), (8, 9)]
  | _ => [(0, 1), (0, 3), (1, 2), (2, 3), (4, 5), (4, 6), (5, 6), (7, 8), (7, 9), (8, 9)]

private def baseAdjSymNat (b x y : ℕ) : Bool :=
  memPairNat x y (baseEdgesNat b) || memPairNat y x (baseEdgesNat b)

private lemma baseAdjSymNat_symm (b x y : ℕ) :
    baseAdjSymNat b x y = baseAdjSymNat b y x := by
  unfold baseAdjSymNat; rw [Bool.or_comm]

private lemma baseAdjSymBool_eq_nat (b : ℕ) (hb : b < 5) (x y : Fin 10) :
    baseAdjSymBool b x y = baseAdjSymNat b x.val y.val := by
  revert x y
  have hbc : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 := by omega
  rcases hbc with rfl | rfl | rfl | rfl | rfl <;> decide


private def dAdjMat : Ten (Ten Bool) := ⟨⟨false, true, true, false, false, false, false, false, false, true⟩, ⟨true, false, true, true, false, false, false, false, false, false⟩, ⟨true, true, false, true, false, false, false, false, false, false⟩, ⟨false, true, true, false, true, false, false, false, false, false⟩, ⟨false, false, false, true, false, true, false, true, false, false⟩, ⟨false, false, false, false, true, false, true, false, false, true⟩, ⟨false, false, false, false, false, true, false, true, true, false⟩, ⟨false, false, false, false, true, false, true, false, true, false⟩, ⟨false, false, false, false, false, false, true, true, false, true⟩, ⟨true, false, false, false, false, true, false, false, true, false⟩⟩
private def dColMat : Ten (Ten ℕ) := ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 2⟩, ⟨0, 0, 2, 3, 0, 0, 0, 0, 0, 0⟩, ⟨1, 2, 0, 4, 0, 0, 0, 0, 0, 0⟩, ⟨0, 3, 4, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 2, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 3⟩, ⟨0, 0, 0, 0, 0, 0, 0, 3, 2, 0⟩, ⟨0, 0, 0, 0, 2, 0, 3, 0, 4, 0⟩, ⟨0, 0, 0, 0, 0, 0, 2, 4, 0, 5⟩, ⟨2, 0, 0, 0, 0, 3, 0, 0, 5, 0⟩⟩
private def dPerm : Ten ℕ := ⟨3, 1, 2, 0, 9, 5, 4, 7, 6, 8⟩

private structure TripleD where (b mHi mLo iHi iLo : ℕ)
private def dTr : TripleD := ⟨2, 0, 0, 0, 0⟩
private def dTrRow : Ten TripleD := ⟨dTr, dTr, dTr, dTr, dTr, dTr, dTr, dTr, dTr, dTr⟩
private def dTrBlk : Ten (Ten TripleD) := ⟨dTrRow, dTrRow, dTrRow, dTrRow, dTrRow, dTrRow, dTrRow, dTrRow, dTrRow, dTrRow⟩

private structure AutEntry where (b : ℕ) (g : Ten ℕ)
private def dAe : AutEntry := ⟨2, ⟨0, 1, 2, 3, 4, 5, 6, 7, 8, 9⟩⟩
private def dAeRow : Ten AutEntry := ⟨dAe, dAe, dAe, dAe, dAe, dAe, dAe, dAe, dAe, dAe⟩
private def dAeBlk : Ten (Ten AutEntry) := ⟨dAeRow, dAeRow, dAeRow, dAeRow, dAeRow, dAeRow, dAeRow, dAeRow, dAeRow, dAeRow⟩

private structure BaseRef where (tr2 tr1 tr0 a2 a1 a0 : ℕ)

private structure LeafWit where (r0 r1 : BaseRef)

private def mAdj_0 : Ten (Ten Bool) := ⟨⟨false, true, true, false, false, false, false, false, false, true⟩, ⟨true, false, true, true, false, false, false, false, false, false⟩, ⟨true, true, false, true, false, false, false, false, false, false⟩, ⟨false, true, true, false, true, false, false, false, false, false⟩, ⟨false, false, false, true, false, true, false, true, false, false⟩, ⟨false, false, false, false, true, false, true, false, false, true⟩, ⟨false, false, false, false, false, true, false, true, true, false⟩, ⟨false, false, false, false, true, false, true, false, true, false⟩, ⟨false, false, false, false, false, false, true, true, false, true⟩, ⟨true, false, false, false, false, true, false, false, true, false⟩⟩
private def mCol_0 : Ten (Ten ℕ) := ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 2⟩, ⟨0, 0, 2, 3, 0, 0, 0, 0, 0, 0⟩, ⟨1, 2, 0, 4, 0, 0, 0, 0, 0, 0⟩, ⟨0, 3, 4, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 2, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 3⟩, ⟨0, 0, 0, 0, 0, 0, 0, 3, 2, 0⟩, ⟨0, 0, 0, 0, 2, 0, 3, 0, 4, 0⟩, ⟨0, 0, 0, 0, 0, 0, 2, 4, 0, 5⟩, ⟨2, 0, 0, 0, 0, 3, 0, 0, 5, 0⟩⟩
private def mAdj_1 : Ten (Ten Bool) := ⟨⟨false, true, true, false, false, false, false, false, false, true⟩, ⟨true, false, true, true, false, false, false, false, false, false⟩, ⟨true, true, false, true, false, false, false, false, false, false⟩, ⟨false, true, true, false, true, false, false, false, false, false⟩, ⟨false, false, false, true, false, true, true, false, false, false⟩, ⟨false, false, false, false, true, false, true, false, true, false⟩, ⟨false, false, false, false, true, true, false, true, false, false⟩, ⟨false, false, false, false, false, false, true, false, true, true⟩, ⟨false, false, false, false, false, true, false, true, false, true⟩, ⟨true, false, false, false, false, false, false, true, true, false⟩⟩
private def mCol_1 : Ten (Ten ℕ) := ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 2⟩, ⟨0, 0, 2, 3, 0, 0, 0, 0, 0, 0⟩, ⟨1, 2, 0, 4, 0, 0, 0, 0, 0, 0⟩, ⟨0, 3, 4, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 2, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 0, 3, 0⟩, ⟨0, 0, 0, 0, 2, 0, 0, 3, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 3, 0, 4, 5⟩, ⟨0, 0, 0, 0, 0, 3, 0, 4, 0, 6⟩, ⟨2, 0, 0, 0, 0, 0, 0, 5, 6, 0⟩⟩
private def mAdj_2 : Ten (Ten Bool) := ⟨⟨false, true, true, false, false, true, false, false, false, false⟩, ⟨true, false, true, false, true, false, false, false, false, false⟩, ⟨true, true, false, true, false, false, false, false, false, false⟩, ⟨false, false, true, false, true, true, false, false, false, false⟩, ⟨false, true, false, true, false, true, false, false, false, false⟩, ⟨true, false, false, true, true, false, false, false, false, false⟩, ⟨false, false, false, false, false, false, false, true, true, true⟩, ⟨false, false, false, false, false, false, true, false, true, true⟩, ⟨false, false, false, false, false, false, true, true, false, true⟩, ⟨false, false, false, false, false, false, true, true, true, false⟩⟩
private def mCol_2 : Ten (Ten ℕ) := ⟨⟨0, 0, 1, 0, 0, 2, 0, 0, 0, 0⟩, ⟨0, 0, 2, 0, 3, 0, 0, 0, 0, 0⟩, ⟨1, 2, 0, 3, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 3, 0, 4, 5, 0, 0, 0, 0⟩, ⟨0, 3, 0, 4, 0, 6, 0, 0, 0, 0⟩, ⟨2, 0, 0, 5, 6, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 2⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 2, 3⟩, ⟨0, 0, 0, 0, 0, 0, 1, 2, 0, 4⟩, ⟨0, 0, 0, 0, 0, 0, 2, 3, 4, 0⟩⟩
private def mAdj_3 : Ten (Ten Bool) := ⟨⟨false, true, true, false, false, false, false, false, false, true⟩, ⟨true, false, true, false, true, false, false, false, false, false⟩, ⟨true, true, false, true, false, false, false, false, false, false⟩, ⟨false, false, true, false, true, false, true, false, false, false⟩, ⟨false, true, false, true, false, true, false, false, false, false⟩, ⟨false, false, false, false, true, false, true, false, true, false⟩, ⟨false, false, false, true, false, true, false, true, false, false⟩, ⟨false, false, false, false, false, false, true, false, true, true⟩, ⟨false, false, false, false, false, true, false, true, false, true⟩, ⟨true, false, false, false, false, false, false, true, true, false⟩⟩
private def mCol_3 : Ten (Ten ℕ) := ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 2⟩, ⟨0, 0, 2, 0, 3, 0, 0, 0, 0, 0⟩, ⟨1, 2, 0, 3, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 3, 0, 4, 0, 0, 0, 0, 0⟩, ⟨0, 3, 0, 4, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 2, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 2, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 2, 0, 3, 4⟩, ⟨0, 0, 0, 0, 0, 2, 0, 3, 0, 5⟩, ⟨2, 0, 0, 0, 0, 0, 0, 4, 5, 0⟩⟩
private def mAdj_4 : Ten (Ten Bool) := ⟨⟨false, true, true, false, false, false, false, false, false, true⟩, ⟨true, false, true, false, false, true, false, false, false, false⟩, ⟨true, true, false, true, false, false, false, false, false, false⟩, ⟨false, false, true, false, true, false, false, true, false, false⟩, ⟨false, false, false, true, false, true, false, false, true, false⟩, ⟨false, true, false, false, true, false, true, false, false, false⟩, ⟨false, false, false, false, false, true, false, true, false, true⟩, ⟨false, false, false, true, false, false, true, false, true, false⟩, ⟨false, false, false, false, true, false, false, true, false, true⟩, ⟨true, false, false, false, false, false, true, false, true, false⟩⟩
private def mCol_4 : Ten (Ten ℕ) := ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 2⟩, ⟨0, 0, 2, 0, 0, 3, 0, 0, 0, 0⟩, ⟨1, 2, 0, 3, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 3, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 2, 0⟩, ⟨0, 3, 0, 0, 1, 0, 4, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 4, 0, 2, 0, 3⟩, ⟨0, 0, 0, 1, 0, 0, 2, 0, 5, 0⟩, ⟨0, 0, 0, 0, 2, 0, 0, 5, 0, 6⟩, ⟨2, 0, 0, 0, 0, 0, 3, 0, 6, 0⟩⟩
private def mAdj_5 : Ten (Ten Bool) := ⟨⟨false, true, true, false, false, false, false, false, false, true⟩, ⟨true, false, true, true, false, false, false, false, false, false⟩, ⟨true, true, false, true, false, false, false, false, false, false⟩, ⟨false, true, true, false, true, false, false, false, false, false⟩, ⟨false, false, false, true, false, true, false, false, false, true⟩, ⟨false, false, false, false, true, false, true, true, false, false⟩, ⟨false, false, false, false, false, true, false, true, true, false⟩, ⟨false, false, false, false, false, true, true, false, true, false⟩, ⟨false, false, false, false, false, false, true, true, false, true⟩, ⟨true, false, false, false, true, false, false, false, true, false⟩⟩
private def mCol_5 : Ten (Ten ℕ) := ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 2⟩, ⟨0, 0, 2, 3, 0, 0, 0, 0, 0, 0⟩, ⟨1, 2, 0, 4, 0, 0, 0, 0, 0, 0⟩, ⟨0, 3, 4, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 4⟩, ⟨0, 0, 0, 0, 1, 0, 0, 2, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 3, 2, 0⟩, ⟨0, 0, 0, 0, 0, 2, 3, 0, 4, 0⟩, ⟨0, 0, 0, 0, 0, 0, 2, 4, 0, 5⟩, ⟨2, 0, 0, 0, 4, 0, 0, 0, 5, 0⟩⟩
private def mAdj_6 : Ten (Ten Bool) := ⟨⟨false, true, false, false, false, true, false, false, false, false⟩, ⟨true, false, true, false, false, false, false, false, false, false⟩, ⟨false, true, false, true, true, false, false, false, false, false⟩, ⟨false, false, true, false, true, true, false, false, false, false⟩, ⟨false, false, true, true, false, true, false, false, false, false⟩, ⟨true, false, false, true, true, false, false, false, false, false⟩, ⟨false, false, false, false, false, false, false, true, true, true⟩, ⟨false, false, false, false, false, false, true, false, true, true⟩, ⟨false, false, false, false, false, false, true, true, false, true⟩, ⟨false, false, false, false, false, false, true, true, true, false⟩⟩
private def mCol_6 : Ten (Ten ℕ) := ⟨⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩, ⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 0, 2, 3, 0, 0, 0, 0, 0⟩, ⟨0, 0, 2, 0, 0, 3, 0, 0, 0, 0⟩, ⟨0, 0, 3, 0, 0, 4, 0, 0, 0, 0⟩, ⟨1, 0, 0, 3, 4, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 2⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 2, 3⟩, ⟨0, 0, 0, 0, 0, 0, 1, 2, 0, 4⟩, ⟨0, 0, 0, 0, 0, 0, 2, 3, 4, 0⟩⟩
private def mAdj_7 : Ten (Ten Bool) := ⟨⟨false, true, true, false, false, false, false, false, false, true⟩, ⟨true, false, true, false, true, false, false, false, false, false⟩, ⟨true, true, false, true, false, false, false, false, false, false⟩, ⟨false, false, true, false, true, false, false, true, false, false⟩, ⟨false, true, false, true, false, true, false, false, false, false⟩, ⟨false, false, false, false, true, false, true, false, false, true⟩, ⟨false, false, false, false, false, true, false, true, true, false⟩, ⟨false, false, false, true, false, false, true, false, true, false⟩, ⟨false, false, false, false, false, false, true, true, false, true⟩, ⟨true, false, false, false, false, true, false, false, true, false⟩⟩
private def mCol_7 : Ten (Ten ℕ) := ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 2⟩, ⟨0, 0, 2, 0, 3, 0, 0, 0, 0, 0⟩, ⟨1, 2, 0, 3, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 3, 0, 4, 0, 0, 0, 0, 0⟩, ⟨0, 3, 0, 4, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 5⟩, ⟨0, 0, 0, 0, 0, 1, 0, 2, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 2, 0, 5, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 5, 0, 3⟩, ⟨2, 0, 0, 0, 0, 5, 0, 0, 3, 0⟩⟩
private def mAdj_8 : Ten (Ten Bool) := ⟨⟨false, true, false, false, false, false, false, false, false, true⟩, ⟨true, false, true, false, false, false, false, false, false, false⟩, ⟨false, true, false, true, true, false, false, false, false, false⟩, ⟨false, false, true, false, true, false, false, false, false, true⟩, ⟨false, false, true, true, false, true, false, false, false, false⟩, ⟨false, false, false, false, true, false, true, true, false, false⟩, ⟨false, false, false, false, false, true, false, true, true, false⟩, ⟨false, false, false, false, false, true, true, false, true, false⟩, ⟨false, false, false, false, false, false, true, true, false, true⟩, ⟨true, false, false, true, false, false, false, false, true, false⟩⟩
private def mCol_8 : Ten (Ten ℕ) := ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 0, 2, 3, 0, 0, 0, 0, 0⟩, ⟨0, 0, 2, 0, 0, 0, 0, 0, 0, 3⟩, ⟨0, 0, 3, 0, 0, 1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 2, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 3, 2, 0⟩, ⟨0, 0, 0, 0, 0, 2, 3, 0, 4, 0⟩, ⟨0, 0, 0, 0, 0, 0, 2, 4, 0, 5⟩, ⟨1, 0, 0, 3, 0, 0, 0, 0, 5, 0⟩⟩
private def mAdj_9 : Ten (Ten Bool) := ⟨⟨false, true, false, false, false, false, false, false, false, true⟩, ⟨true, false, true, false, false, false, false, false, false, false⟩, ⟨false, true, false, true, true, false, false, false, false, false⟩, ⟨false, false, true, false, true, false, false, true, false, false⟩, ⟨false, false, true, true, false, true, false, false, false, false⟩, ⟨false, false, false, false, true, false, true, false, false, true⟩, ⟨false, false, false, false, false, true, false, true, true, false⟩, ⟨false, false, false, true, false, false, true, false, true, false⟩, ⟨false, false, false, false, false, false, true, true, false, true⟩, ⟨true, false, false, false, false, true, false, false, true, false⟩⟩
private def mCol_9 : Ten (Ten ℕ) := ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 0, 2, 3, 0, 0, 0, 0, 0⟩, ⟨0, 0, 2, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 3, 0, 0, 1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 2, 0, 0, 4⟩, ⟨0, 0, 0, 0, 0, 2, 0, 3, 0, 0⟩, ⟨0, 0, 0, 1, 0, 0, 3, 0, 4, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 4, 0, 5⟩, ⟨1, 0, 0, 0, 0, 4, 0, 0, 5, 0⟩⟩
private def mAdj_10 : Ten (Ten Bool) := ⟨⟨false, true, true, false, false, false, false, false, false, true⟩, ⟨true, false, true, false, true, false, false, false, false, false⟩, ⟨true, true, false, true, false, false, false, false, false, false⟩, ⟨false, false, true, false, true, false, false, true, false, false⟩, ⟨false, true, false, true, false, true, false, false, false, false⟩, ⟨false, false, false, false, true, false, true, false, true, false⟩, ⟨false, false, false, false, false, true, false, true, false, true⟩, ⟨false, false, false, true, false, false, true, false, true, false⟩, ⟨false, false, false, false, false, true, false, true, false, true⟩, ⟨true, false, false, false, false, false, true, false, true, false⟩⟩
private def mCol_10 : Ten (Ten ℕ) := ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 2⟩, ⟨0, 0, 2, 0, 3, 0, 0, 0, 0, 0⟩, ⟨1, 2, 0, 3, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 3, 0, 4, 0, 0, 0, 0, 0⟩, ⟨0, 3, 0, 4, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 2, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 2, 0, 3⟩, ⟨0, 0, 0, 0, 0, 0, 2, 0, 5, 0⟩, ⟨0, 0, 0, 0, 0, 2, 0, 5, 0, 4⟩, ⟨2, 0, 0, 0, 0, 0, 3, 0, 4, 0⟩⟩
private def mAdj_11 : Ten (Ten Bool) := ⟨⟨false, true, true, false, false, false, false, false, false, true⟩, ⟨true, false, true, true, false, false, false, false, false, false⟩, ⟨true, true, false, true, false, false, false, false, false, false⟩, ⟨false, true, true, false, true, false, false, false, false, false⟩, ⟨false, false, false, true, false, true, false, true, false, false⟩, ⟨false, false, false, false, true, false, true, false, true, false⟩, ⟨false, false, false, false, false, true, false, true, false, true⟩, ⟨false, false, false, false, true, false, true, false, true, false⟩, ⟨false, false, false, false, false, true, false, true, false, true⟩, ⟨true, false, false, false, false, false, true, false, true, false⟩⟩
private def mCol_11 : Ten (Ten ℕ) := ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 2⟩, ⟨0, 0, 2, 3, 0, 0, 0, 0, 0, 0⟩, ⟨1, 2, 0, 4, 0, 0, 0, 0, 0, 0⟩, ⟨0, 3, 4, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 2, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 0, 0, 2, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 3, 0, 4⟩, ⟨0, 0, 0, 0, 2, 0, 3, 0, 4, 0⟩, ⟨0, 0, 0, 0, 0, 2, 0, 4, 0, 5⟩, ⟨2, 0, 0, 0, 0, 0, 4, 0, 5, 0⟩⟩
private def mAdj_12 : Ten (Ten Bool) := ⟨⟨false, true, false, true, false, false, false, false, false, true⟩, ⟨true, false, true, false, false, false, true, false, false, false⟩, ⟨false, true, false, true, false, false, false, true, false, false⟩, ⟨true, false, true, false, true, false, false, false, false, false⟩, ⟨false, false, false, true, false, true, false, false, false, true⟩, ⟨false, false, false, false, true, false, true, false, true, false⟩, ⟨false, true, false, false, false, true, false, true, false, false⟩, ⟨false, false, true, false, false, false, true, false, true, false⟩, ⟨false, false, false, false, false, true, false, true, false, true⟩, ⟨true, false, false, false, true, false, false, false, true, false⟩⟩
private def mCol_12 : Ten (Ten ℕ) := ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 2⟩, ⟨0, 0, 1, 0, 0, 0, 2, 0, 0, 0⟩, ⟨0, 1, 0, 3, 0, 0, 0, 2, 0, 0⟩, ⟨1, 0, 3, 0, 2, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 2, 0, 0, 0, 0, 0, 4⟩, ⟨0, 0, 0, 0, 0, 0, 3, 0, 1, 0⟩, ⟨0, 2, 0, 0, 0, 3, 0, 4, 0, 0⟩, ⟨0, 0, 2, 0, 0, 0, 4, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 3⟩, ⟨2, 0, 0, 0, 4, 0, 0, 0, 3, 0⟩⟩
private def mAdj_13 : Ten (Ten Bool) := ⟨⟨false, true, false, false, false, false, false, false, false, true⟩, ⟨true, false, true, false, false, false, false, false, false, false⟩, ⟨false, true, false, true, false, false, false, false, false, true⟩, ⟨false, false, true, false, true, false, false, false, true, false⟩, ⟨false, false, false, true, false, true, true, false, false, false⟩, ⟨false, false, false, false, true, false, true, true, false, false⟩, ⟨false, false, false, false, true, true, false, true, false, false⟩, ⟨false, false, false, false, false, true, true, false, true, false⟩, ⟨false, false, false, true, false, false, false, true, false, true⟩, ⟨true, false, true, false, false, false, false, false, true, false⟩⟩
private def mCol_13 : Ten (Ten ℕ) := ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 0, 2, 0, 0, 0, 0, 0, 3⟩, ⟨0, 0, 2, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 2, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 3, 2, 0, 0⟩, ⟨0, 0, 0, 0, 2, 3, 0, 4, 0, 0⟩, ⟨0, 0, 0, 0, 0, 2, 4, 0, 5, 0⟩, ⟨0, 0, 0, 1, 0, 0, 0, 5, 0, 4⟩, ⟨1, 0, 3, 0, 0, 0, 0, 0, 4, 0⟩⟩
private def mAdj_14 : Ten (Ten Bool) := ⟨⟨false, true, false, false, false, false, false, false, false, true⟩, ⟨true, false, true, false, false, false, false, false, false, false⟩, ⟨false, true, false, true, false, true, false, false, false, false⟩, ⟨false, false, true, false, true, false, false, false, false, true⟩, ⟨false, false, false, true, false, true, false, true, false, false⟩, ⟨false, false, true, false, true, false, true, false, false, false⟩, ⟨false, false, false, false, false, true, false, true, true, false⟩, ⟨false, false, false, false, true, false, true, false, true, false⟩, ⟨false, false, false, false, false, false, true, true, false, true⟩, ⟨true, false, false, true, false, false, false, false, true, false⟩⟩
private def mCol_14 : Ten (Ten ℕ) := ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 0, 2, 0, 3, 0, 0, 0, 0⟩, ⟨0, 0, 2, 0, 0, 0, 0, 0, 0, 3⟩, ⟨0, 0, 0, 0, 0, 1, 0, 2, 0, 0⟩, ⟨0, 0, 3, 0, 1, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 3, 2, 0⟩, ⟨0, 0, 0, 0, 2, 0, 3, 0, 4, 0⟩, ⟨0, 0, 0, 0, 0, 0, 2, 4, 0, 5⟩, ⟨1, 0, 0, 3, 0, 0, 0, 0, 5, 0⟩⟩
private def mAdj_15 : Ten (Ten Bool) := ⟨⟨false, true, false, false, false, false, false, false, false, true⟩, ⟨true, false, true, false, false, false, false, false, false, false⟩, ⟨false, true, false, true, false, false, false, false, false, true⟩, ⟨false, false, true, false, true, false, true, false, false, false⟩, ⟨false, false, false, true, false, true, false, false, true, false⟩, ⟨false, false, false, false, true, false, true, true, false, false⟩, ⟨false, false, false, true, false, true, false, true, false, false⟩, ⟨false, false, false, false, false, true, true, false, true, false⟩, ⟨false, false, false, false, true, false, false, true, false, true⟩, ⟨true, false, true, false, false, false, false, false, true, false⟩⟩
private def mCol_15 : Ten (Ten ℕ) := ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 0, 2, 0, 0, 0, 0, 0, 3⟩, ⟨0, 0, 2, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 2, 0⟩, ⟨0, 0, 0, 0, 1, 0, 3, 2, 0, 0⟩, ⟨0, 0, 0, 1, 0, 3, 0, 4, 0, 0⟩, ⟨0, 0, 0, 0, 0, 2, 4, 0, 5, 0⟩, ⟨0, 0, 0, 0, 2, 0, 0, 5, 0, 4⟩, ⟨1, 0, 3, 0, 0, 0, 0, 0, 4, 0⟩⟩
private def mAdj_16 : Ten (Ten Bool) := ⟨⟨false, true, false, false, false, false, false, false, false, true⟩, ⟨true, false, true, false, false, false, false, false, false, false⟩, ⟨false, true, false, true, false, true, false, false, false, false⟩, ⟨false, false, true, false, true, false, false, false, true, false⟩, ⟨false, false, false, true, false, true, false, true, false, false⟩, ⟨false, false, true, false, true, false, true, false, false, false⟩, ⟨false, false, false, false, false, true, false, true, false, true⟩, ⟨false, false, false, false, true, false, true, false, true, false⟩, ⟨false, false, false, true, false, false, false, true, false, true⟩, ⟨true, false, false, false, false, false, true, false, true, false⟩⟩
private def mCol_16 : Ten (Ten ℕ) := ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 0, 2, 0, 3, 0, 0, 0, 0⟩, ⟨0, 0, 2, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 2, 0, 0⟩, ⟨0, 0, 3, 0, 1, 0, 2, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 2, 0, 4, 0, 5⟩, ⟨0, 0, 0, 0, 2, 0, 4, 0, 3, 0⟩, ⟨0, 0, 0, 1, 0, 0, 0, 3, 0, 4⟩, ⟨1, 0, 0, 0, 0, 0, 5, 0, 4, 0⟩⟩
private def mAdj_17 : Ten (Ten Bool) := ⟨⟨false, true, false, false, false, false, false, false, false, true⟩, ⟨true, false, true, false, false, false, false, false, false, false⟩, ⟨false, true, false, true, false, true, false, false, false, false⟩, ⟨false, false, true, false, true, false, false, true, false, false⟩, ⟨false, false, false, true, false, true, false, false, true, false⟩, ⟨false, false, true, false, true, false, true, false, false, false⟩, ⟨false, false, false, false, false, true, false, true, false, true⟩, ⟨false, false, false, true, false, false, true, false, true, false⟩, ⟨false, false, false, false, true, false, false, true, false, true⟩, ⟨true, false, false, false, false, false, true, false, true, false⟩⟩
private def mCol_17 : Ten (Ten ℕ) := ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 0, 2, 0, 3, 0, 0, 0, 0⟩, ⟨0, 0, 2, 0, 0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 2, 0⟩, ⟨0, 0, 3, 0, 1, 0, 2, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 2, 0, 4, 0, 5⟩, ⟨0, 0, 0, 1, 0, 0, 4, 0, 3, 0⟩, ⟨0, 0, 0, 0, 2, 0, 0, 3, 0, 4⟩, ⟨1, 0, 0, 0, 0, 0, 5, 0, 4, 0⟩⟩
private def mAdj_18 : Ten (Ten Bool) := ⟨⟨false, true, false, false, false, false, false, false, false, true⟩, ⟨true, false, true, false, false, false, false, false, false, false⟩, ⟨false, true, false, true, false, false, true, false, false, false⟩, ⟨false, false, true, false, true, false, false, false, true, false⟩, ⟨false, false, false, true, false, true, false, true, false, false⟩, ⟨false, false, false, false, true, false, true, false, false, true⟩, ⟨false, false, true, false, false, true, false, true, false, false⟩, ⟨false, false, false, false, true, false, true, false, true, false⟩, ⟨false, false, false, true, false, false, false, true, false, true⟩, ⟨true, false, false, false, false, true, false, false, true, false⟩⟩
private def mCol_18 : Ten (Ten ℕ) := ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 0, 2, 0, 0, 3, 0, 0, 0⟩, ⟨0, 0, 2, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 2, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 2, 0, 0, 4⟩, ⟨0, 0, 3, 0, 0, 2, 0, 5, 0, 0⟩, ⟨0, 0, 0, 0, 2, 0, 5, 0, 3, 0⟩, ⟨0, 0, 0, 1, 0, 0, 0, 3, 0, 6⟩, ⟨1, 0, 0, 0, 0, 4, 0, 0, 6, 0⟩⟩
private def mAdj_19 : Ten (Ten Bool) := ⟨⟨false, true, false, false, false, false, false, false, false, true⟩, ⟨true, false, true, false, false, false, false, false, false, false⟩, ⟨false, true, false, true, false, false, false, true, false, false⟩, ⟨false, false, true, false, true, true, false, false, false, false⟩, ⟨false, false, false, true, false, true, false, false, false, true⟩, ⟨false, false, false, true, true, false, true, false, false, false⟩, ⟨false, false, false, false, false, true, false, true, true, false⟩, ⟨false, false, true, false, false, false, true, false, true, false⟩, ⟨false, false, false, false, false, false, true, true, false, true⟩, ⟨true, false, false, false, true, false, false, false, true, false⟩⟩
private def mCol_19 : Ten (Ten ℕ) := ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 0, 2, 0, 0, 0, 3, 0, 0⟩, ⟨0, 0, 2, 0, 0, 1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 3, 0, 0, 0, 2⟩, ⟨0, 0, 0, 1, 3, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 2, 4, 0⟩, ⟨0, 0, 3, 0, 0, 0, 2, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 4, 0, 0, 3⟩, ⟨1, 0, 0, 0, 2, 0, 0, 0, 3, 0⟩⟩
private def mAdj_20 : Ten (Ten Bool) := ⟨⟨false, true, true, false, false, false, true, false, false, false⟩, ⟨true, false, true, true, false, false, false, false, false, false⟩, ⟨true, true, false, true, false, false, false, false, false, false⟩, ⟨false, true, true, false, true, false, false, false, false, false⟩, ⟨false, false, false, true, false, true, true, false, false, false⟩, ⟨false, false, false, false, true, false, true, true, false, false⟩, ⟨true, false, false, false, true, true, false, false, false, false⟩, ⟨false, false, false, false, false, true, false, false, true, true⟩, ⟨false, false, false, false, false, false, false, true, false, true⟩, ⟨false, false, false, false, false, false, false, true, true, false⟩⟩
private def mCol_20 : Ten (Ten ℕ) := ⟨⟨0, 0, 1, 0, 0, 0, 2, 0, 0, 0⟩, ⟨0, 0, 2, 3, 0, 0, 0, 0, 0, 0⟩, ⟨1, 2, 0, 4, 0, 0, 0, 0, 0, 0⟩, ⟨0, 3, 4, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 4, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 3, 0, 0, 0⟩, ⟨2, 0, 0, 0, 4, 3, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 2, 3⟩, ⟨0, 0, 0, 0, 0, 0, 0, 2, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 3, 1, 0⟩⟩
private def mAdj_21 : Ten (Ten Bool) := ⟨⟨false, true, true, false, false, false, true, false, false, false⟩, ⟨true, false, true, false, true, false, false, false, false, false⟩, ⟨true, true, false, true, false, false, false, false, false, false⟩, ⟨false, false, true, false, true, true, false, false, false, false⟩, ⟨false, true, false, true, false, true, false, false, false, false⟩, ⟨false, false, false, true, true, false, true, false, false, false⟩, ⟨true, false, false, false, false, true, false, true, false, false⟩, ⟨false, false, false, false, false, false, true, false, true, true⟩, ⟨false, false, false, false, false, false, false, true, false, true⟩, ⟨false, false, false, false, false, false, false, true, true, false⟩⟩
private def mCol_21 : Ten (Ten ℕ) := ⟨⟨0, 0, 1, 0, 0, 0, 2, 0, 0, 0⟩, ⟨0, 0, 2, 0, 3, 0, 0, 0, 0, 0⟩, ⟨1, 2, 0, 3, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 3, 0, 4, 0, 0, 0, 0, 0⟩, ⟨0, 3, 0, 4, 0, 1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 3, 0, 0, 0⟩, ⟨2, 0, 0, 0, 0, 3, 0, 4, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 4, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 2⟩, ⟨0, 0, 0, 0, 0, 0, 0, 1, 2, 0⟩⟩
private def mAdj_22 : Ten (Ten Bool) := ⟨⟨false, true, true, false, false, false, true, false, false, false⟩, ⟨true, false, true, false, true, false, false, false, false, false⟩, ⟨true, true, false, true, false, false, false, false, false, false⟩, ⟨false, false, true, false, true, false, true, false, false, false⟩, ⟨false, true, false, true, false, true, false, false, false, false⟩, ⟨false, false, false, false, true, false, true, true, false, false⟩, ⟨true, false, false, true, false, true, false, false, false, false⟩, ⟨false, false, false, false, false, true, false, false, true, true⟩, ⟨false, false, false, false, false, false, false, true, false, true⟩, ⟨false, false, false, false, false, false, false, true, true, false⟩⟩
private def mCol_22 : Ten (Ten ℕ) := ⟨⟨0, 0, 1, 0, 0, 0, 2, 0, 0, 0⟩, ⟨0, 0, 2, 0, 3, 0, 0, 0, 0, 0⟩, ⟨1, 2, 0, 3, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 3, 0, 4, 0, 5, 0, 0, 0⟩, ⟨0, 3, 0, 4, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 4, 1, 0, 0⟩, ⟨2, 0, 0, 5, 0, 4, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 2⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 3⟩, ⟨0, 0, 0, 0, 0, 0, 0, 2, 3, 0⟩⟩
private def mAdj_23 : Ten (Ten Bool) := ⟨⟨false, true, false, false, false, false, false, false, false, true⟩, ⟨true, false, true, false, false, false, false, false, false, false⟩, ⟨false, true, false, true, false, false, false, false, false, true⟩, ⟨false, false, true, false, true, true, false, false, false, false⟩, ⟨false, false, false, true, false, true, false, true, false, false⟩, ⟨false, false, false, true, true, false, true, false, false, false⟩, ⟨false, false, false, false, false, true, false, true, true, false⟩, ⟨false, false, false, false, true, false, true, false, true, false⟩, ⟨false, false, false, false, false, false, true, true, false, true⟩, ⟨true, false, true, false, false, false, false, false, true, false⟩⟩
private def mCol_23 : Ten (Ten ℕ) := ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 0, 2, 0, 0, 0, 0, 0, 3⟩, ⟨0, 0, 2, 0, 0, 1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 3, 0, 1, 0, 0⟩, ⟨0, 0, 0, 1, 3, 0, 4, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 4, 0, 2, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 2, 0, 4, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 4, 0, 5⟩, ⟨1, 0, 3, 0, 0, 0, 0, 0, 5, 0⟩⟩
private def mAdj_24 : Ten (Ten Bool) := ⟨⟨false, true, true, false, false, false, false, false, false, true⟩, ⟨true, false, true, false, false, true, false, false, false, false⟩, ⟨true, true, false, true, false, false, false, false, false, false⟩, ⟨false, false, true, false, true, false, false, false, true, false⟩, ⟨false, false, false, true, false, true, false, true, false, false⟩, ⟨false, true, false, false, true, false, true, false, false, false⟩, ⟨false, false, false, false, false, true, false, true, false, true⟩, ⟨false, false, false, false, true, false, true, false, true, false⟩, ⟨false, false, false, true, false, false, false, true, false, true⟩, ⟨true, false, false, false, false, false, true, false, true, false⟩⟩
private def mCol_24 : Ten (Ten ℕ) := ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 2⟩, ⟨0, 0, 2, 0, 0, 3, 0, 0, 0, 0⟩, ⟨1, 2, 0, 3, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 3, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 2, 0, 0⟩, ⟨0, 3, 0, 0, 1, 0, 4, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 4, 0, 0, 0, 3⟩, ⟨0, 0, 0, 0, 2, 0, 0, 0, 4, 0⟩, ⟨0, 0, 0, 1, 0, 0, 0, 4, 0, 5⟩, ⟨2, 0, 0, 0, 0, 0, 3, 0, 5, 0⟩⟩
private def mAdj_25 : Ten (Ten Bool) := ⟨⟨false, true, true, false, false, false, false, false, false, true⟩, ⟨true, false, true, false, false, true, false, false, false, false⟩, ⟨true, true, false, true, false, false, false, false, false, false⟩, ⟨false, false, true, false, true, false, false, false, true, false⟩, ⟨false, false, false, true, false, true, true, false, false, false⟩, ⟨false, true, false, false, true, false, true, false, false, false⟩, ⟨false, false, false, false, true, true, false, true, false, false⟩, ⟨false, false, false, false, false, false, true, false, true, true⟩, ⟨false, false, false, true, false, false, false, true, false, true⟩, ⟨true, false, false, false, false, false, false, true, true, false⟩⟩
private def mCol_25 : Ten (Ten ℕ) := ⟨⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 2⟩, ⟨0, 0, 2, 0, 0, 3, 0, 0, 0, 0⟩, ⟨1, 2, 0, 3, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 3, 0, 0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 0, 1, 2, 0, 0, 0⟩, ⟨0, 3, 0, 0, 1, 0, 4, 0, 0, 0⟩, ⟨0, 0, 0, 0, 2, 4, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 4, 3⟩, ⟨0, 0, 0, 1, 0, 0, 0, 4, 0, 5⟩, ⟨2, 0, 0, 0, 0, 0, 0, 3, 5, 0⟩⟩
private def mAdj_26 : Ten (Ten Bool) := ⟨⟨false, true, false, true, false, false, true, false, false, false⟩, ⟨true, false, true, false, true, false, false, false, false, false⟩, ⟨false, true, false, true, false, true, false, false, false, false⟩, ⟨true, false, true, false, true, false, false, false, false, false⟩, ⟨false, true, false, true, false, true, false, false, false, false⟩, ⟨false, false, true, false, true, false, true, false, false, false⟩, ⟨true, false, false, false, false, true, false, true, false, false⟩, ⟨false, false, false, false, false, false, true, false, true, true⟩, ⟨false, false, false, false, false, false, false, true, false, true⟩, ⟨false, false, false, false, false, false, false, true, true, false⟩⟩
private def mCol_26 : Ten (Ten ℕ) := ⟨⟨0, 0, 0, 1, 0, 0, 2, 0, 0, 0⟩, ⟨0, 0, 1, 0, 2, 0, 0, 0, 0, 0⟩, ⟨0, 1, 0, 3, 0, 2, 0, 0, 0, 0⟩, ⟨1, 0, 3, 0, 4, 0, 0, 0, 0, 0⟩, ⟨0, 2, 0, 4, 0, 5, 0, 0, 0, 0⟩, ⟨0, 0, 2, 0, 5, 0, 4, 0, 0, 0⟩, ⟨2, 0, 0, 0, 0, 4, 0, 1, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 3⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 0, 0, 0, 0, 0, 3, 1, 0⟩⟩
private def mAdj_27 : Ten (Ten Bool) := ⟨⟨false, true, false, true, false, true, false, false, false, false⟩, ⟨true, false, true, false, true, false, false, false, false, false⟩, ⟨false, true, false, true, false, true, false, false, false, false⟩, ⟨true, false, true, false, true, false, false, false, false, false⟩, ⟨false, true, false, true, false, true, false, false, false, false⟩, ⟨true, false, true, false, true, false, false, false, false, false⟩, ⟨false, false, false, false, false, false, false, true, true, true⟩, ⟨false, false, false, false, false, false, true, false, true, true⟩, ⟨false, false, false, false, false, false, true, true, false, true⟩, ⟨false, false, false, false, false, false, true, true, true, false⟩⟩
private def mCol_27 : Ten (Ten ℕ) := ⟨⟨0, 0, 0, 1, 0, 2, 0, 0, 0, 0⟩, ⟨0, 0, 1, 0, 2, 0, 0, 0, 0, 0⟩, ⟨0, 1, 0, 3, 0, 4, 0, 0, 0, 0⟩, ⟨1, 0, 3, 0, 4, 0, 0, 0, 0, 0⟩, ⟨0, 2, 0, 4, 0, 5, 0, 0, 0, 0⟩, ⟨2, 0, 4, 0, 5, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 2⟩, ⟨0, 0, 0, 0, 0, 0, 0, 0, 2, 3⟩, ⟨0, 0, 0, 0, 0, 0, 1, 2, 0, 4⟩, ⟨0, 0, 0, 0, 0, 0, 2, 3, 4, 0⟩⟩
private def mAdj_28 : Ten (Ten Bool) := ⟨⟨false, true, false, false, false, false, false, false, false, true⟩, ⟨true, false, true, false, false, false, false, false, false, false⟩, ⟨false, true, false, true, false, false, false, false, false, true⟩, ⟨false, false, true, false, true, false, true, false, false, false⟩, ⟨false, false, false, true, false, true, false, true, false, false⟩, ⟨false, false, false, false, true, false, true, false, true, false⟩, ⟨false, false, false, true, false, true, false, true, false, false⟩, ⟨false, false, false, false, true, false, true, false, true, false⟩, ⟨false, false, false, false, false, true, false, true, false, true⟩, ⟨true, false, true, false, false, false, false, false, true, false⟩⟩
private def mCol_28 : Ten (Ten ℕ) := ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩, ⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩, ⟨0, 1, 0, 2, 0, 0, 0, 0, 0, 3⟩, ⟨0, 0, 2, 0, 0, 0, 1, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 2, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0, 3, 0, 2, 0⟩, ⟨0, 0, 0, 1, 0, 3, 0, 4, 0, 0⟩, ⟨0, 0, 0, 0, 2, 0, 4, 0, 5, 0⟩, ⟨0, 0, 0, 0, 0, 2, 0, 5, 0, 4⟩, ⟨1, 0, 3, 0, 0, 0, 0, 0, 4, 0⟩⟩
private def mAdj_29 : Ten (Ten Bool) := ⟨⟨false, true, false, true, false, false, false, false, false, true⟩, ⟨true, false, true, false, false, false, false, true, false, false⟩, ⟨false, true, false, true, false, false, true, false, false, false⟩, ⟨true, false, true, false, true, false, false, false, false, false⟩, ⟨false, false, false, true, false, true, false, false, false, true⟩, ⟨false, false, false, false, true, false, true, false, true, false⟩, ⟨false, false, true, false, false, true, false, true, false, false⟩, ⟨false, true, false, false, false, false, true, false, true, false⟩, ⟨false, false, false, false, false, true, false, true, false, true⟩, ⟨true, false, false, false, true, false, false, false, true, false⟩⟩
private def mCol_29 : Ten (Ten ℕ) := ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 2⟩, ⟨0, 0, 1, 0, 0, 0, 0, 2, 0, 0⟩, ⟨0, 1, 0, 3, 0, 0, 2, 0, 0, 0⟩, ⟨1, 0, 3, 0, 2, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 2, 0, 0, 0, 0, 0, 4⟩, ⟨0, 0, 0, 0, 0, 0, 4, 0, 1, 0⟩, ⟨0, 0, 2, 0, 0, 4, 0, 5, 0, 0⟩, ⟨0, 2, 0, 0, 0, 0, 5, 0, 3, 0⟩, ⟨0, 0, 0, 0, 0, 1, 0, 3, 0, 5⟩, ⟨2, 0, 0, 0, 4, 0, 0, 0, 5, 0⟩⟩
private def mAdj_30 : Ten (Ten Bool) := ⟨⟨false, true, false, true, false, false, false, false, false, true⟩, ⟨true, false, true, false, false, true, false, false, false, false⟩, ⟨false, true, false, true, false, false, false, false, true, false⟩, ⟨true, false, true, false, true, false, false, false, false, false⟩, ⟨false, false, false, true, false, true, false, true, false, false⟩, ⟨false, true, false, false, true, false, true, false, false, false⟩, ⟨false, false, false, false, false, true, false, true, false, true⟩, ⟨false, false, false, false, true, false, true, false, true, false⟩, ⟨false, false, true, false, false, false, false, true, false, true⟩, ⟨true, false, false, false, false, false, true, false, true, false⟩⟩
private def mCol_30 : Ten (Ten ℕ) := ⟨⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 2⟩, ⟨0, 0, 1, 0, 0, 2, 0, 0, 0, 0⟩, ⟨0, 1, 0, 3, 0, 0, 0, 0, 2, 0⟩, ⟨1, 0, 3, 0, 2, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 2, 0, 4, 0, 0, 0, 0⟩, ⟨0, 2, 0, 0, 4, 0, 3, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0, 3, 0, 1, 0, 4⟩, ⟨0, 0, 0, 0, 0, 0, 1, 0, 4, 0⟩, ⟨0, 0, 2, 0, 0, 0, 0, 4, 0, 5⟩, ⟨2, 0, 0, 0, 0, 0, 4, 0, 5, 0⟩⟩
private def mAdjRow_0 : Ten (Ten (Ten Bool)) := ⟨mAdj_0, mAdj_1, mAdj_2, mAdj_3, mAdj_4, mAdj_5, mAdj_6, mAdj_7, mAdj_8, mAdj_9⟩
private def mColRow_0 : Ten (Ten (Ten ℕ)) := ⟨mCol_0, mCol_1, mCol_2, mCol_3, mCol_4, mCol_5, mCol_6, mCol_7, mCol_8, mCol_9⟩
private def mAdjRow_1 : Ten (Ten (Ten Bool)) := ⟨mAdj_10, mAdj_11, mAdj_12, mAdj_13, mAdj_14, mAdj_15, mAdj_16, mAdj_17, mAdj_18, mAdj_19⟩
private def mColRow_1 : Ten (Ten (Ten ℕ)) := ⟨mCol_10, mCol_11, mCol_12, mCol_13, mCol_14, mCol_15, mCol_16, mCol_17, mCol_18, mCol_19⟩
private def mAdjRow_2 : Ten (Ten (Ten Bool)) := ⟨mAdj_20, mAdj_21, mAdj_22, mAdj_23, mAdj_24, mAdj_25, mAdj_26, mAdj_27, mAdj_28, mAdj_29⟩
private def mColRow_2 : Ten (Ten (Ten ℕ)) := ⟨mCol_20, mCol_21, mCol_22, mCol_23, mCol_24, mCol_25, mCol_26, mCol_27, mCol_28, mCol_29⟩
private def mAdjRow_3 : Ten (Ten (Ten Bool)) := ⟨mAdj_30, dAdjMat, dAdjMat, dAdjMat, dAdjMat, dAdjMat, dAdjMat, dAdjMat, dAdjMat, dAdjMat⟩
private def mColRow_3 : Ten (Ten (Ten ℕ)) := ⟨mCol_30, dColMat, dColMat, dColMat, dColMat, dColMat, dColMat, dColMat, dColMat, dColMat⟩
private def mAdjRow_4 : Ten (Ten (Ten Bool)) := ⟨dAdjMat, dAdjMat, dAdjMat, dAdjMat, dAdjMat, dAdjMat, dAdjMat, dAdjMat, dAdjMat, dAdjMat⟩
private def mColRow_4 : Ten (Ten (Ten ℕ)) := ⟨dColMat, dColMat, dColMat, dColMat, dColMat, dColMat, dColMat, dColMat, dColMat, dColMat⟩
private def masterAdjGrid : Five (Ten (Ten (Ten Bool))) := ⟨mAdjRow_0, mAdjRow_1, mAdjRow_2, mAdjRow_3, mAdjRow_4⟩
private def masterColGrid : Five (Ten (Ten (Ten ℕ))) := ⟨mColRow_0, mColRow_1, mColRow_2, mColRow_3, mColRow_4⟩
private def iso_0 : Ten ℕ := ⟨3, 1, 2, 0, 9, 5, 4, 7, 6, 8⟩
private def iso_1 : Ten ℕ := ⟨4, 5, 8, 9, 7, 6, 0, 1, 3, 2⟩
private def iso_2 : Ten ℕ := ⟨0, 1, 2, 3, 4, 5, 6, 7, 8, 9⟩
private def iso_3 : Ten ℕ := ⟨3, 6, 5, 4, 1, 0, 2, 9, 7, 8⟩
private def iso_4 : Ten ℕ := ⟨5, 1, 0, 2, 3, 4, 7, 8, 9, 6⟩
private def iso_5 : Ten ℕ := ⟨8, 6, 7, 5, 4, 9, 3, 1, 0, 2⟩
private def iso_6 : Ten ℕ := ⟨0, 1, 2, 3, 4, 5, 9, 7, 6, 8⟩
private def iso_7 : Ten ℕ := ⟨5, 9, 0, 1, 2, 3, 4, 7, 6, 8⟩
private def iso_8 : Ten ℕ := ⟨4, 9, 0, 1, 2, 3, 5, 6, 8, 7⟩
private def iso_9 : Ten ℕ := ⟨6, 9, 0, 2, 1, 5, 3, 4, 8, 7⟩
private def iso_10 : Ten ℕ := ⟨0, 1, 2, 4, 3, 9, 5, 6, 8, 7⟩
private def iso_11 : Ten ℕ := ⟨3, 7, 6, 9, 8, 5, 4, 1, 0, 2⟩
private def iso_12 : Ten ℕ := ⟨7, 4, 5, 8, 9, 6, 0, 1, 3, 2⟩
private def iso_13 : Ten ℕ := ⟨3, 2, 0, 1, 4, 5, 6, 7, 8, 9⟩
private def iso_14 : Ten ℕ := ⟨3, 4, 5, 6, 9, 8, 7, 0, 1, 2⟩
private def iso_15 : Ten ℕ := ⟨4, 9, 0, 1, 2, 3, 6, 7, 8, 5⟩
private def iso_16 : Ten ℕ := ⟨0, 1, 2, 3, 8, 9, 4, 5, 7, 6⟩
private def iso_17 : Ten ℕ := ⟨0, 1, 2, 5, 4, 3, 9, 6, 7, 8⟩
private def iso_18 : Ten ℕ := ⟨3, 2, 0, 1, 5, 4, 9, 8, 7, 6⟩
private def iso_19 : Ten ℕ := ⟨7, 6, 4, 5, 8, 9, 3, 1, 0, 2⟩
private def iso_20 : Ten ℕ := ⟨5, 6, 3, 2, 0, 1, 4, 9, 7, 8⟩
private def iso_21 : Ten ℕ := ⟨0, 1, 2, 3, 4, 8, 9, 6, 5, 7⟩
private def iso_22 : Ten ℕ := ⟨0, 1, 2, 3, 8, 9, 5, 4, 7, 6⟩
private def iso_23 : Ten ℕ := ⟨0, 1, 2, 5, 6, 9, 3, 4, 8, 7⟩
private def iso_24 : Ten ℕ := ⟨0, 1, 2, 3, 8, 9, 6, 7, 4, 5⟩
private def iso_25 : Ten ℕ := ⟨3, 2, 0, 1, 4, 5, 6, 9, 8, 7⟩
private def iso_26 : Ten ℕ := ⟨0, 1, 2, 3, 5, 4, 9, 7, 6, 8⟩
private def iso_27 : Ten ℕ := ⟨4, 5, 6, 7, 8, 3, 9, 2, 1, 0⟩
private def iso_28 : Ten ℕ := ⟨0, 1, 2, 3, 4, 9, 5, 6, 8, 7⟩
private def iso_29 : Ten ℕ := ⟨6, 5, 7, 8, 4, 3, 9, 2, 1, 0⟩
private def iso_30 : Ten ℕ := ⟨7, 6, 8, 9, 5, 4, 0, 1, 3, 2⟩
private def iso_31 : Ten ℕ := ⟨4, 3, 5, 6, 8, 7, 2, 9, 0, 1⟩
private def iso_32 : Ten ℕ := ⟨5, 4, 6, 7, 9, 8, 3, 1, 0, 2⟩
private def iso_33 : Ten ℕ := ⟨0, 2, 1, 5, 6, 9, 3, 4, 8, 7⟩
private def iso_34 : Ten ℕ := ⟨2, 0, 1, 5, 6, 4, 3, 9, 7, 8⟩
private def iso_35 : Ten ℕ := ⟨1, 0, 2, 3, 6, 5, 4, 9, 7, 8⟩
private def iso_36 : Ten ℕ := ⟨4, 5, 8, 7, 6, 3, 9, 2, 1, 0⟩
private def iso_37 : Ten ℕ := ⟨5, 6, 9, 8, 7, 4, 0, 1, 3, 2⟩
private def iso_38 : Ten ℕ := ⟨5, 6, 9, 8, 7, 3, 4, 0, 2, 1⟩
private def iso_39 : Ten ℕ := ⟨7, 8, 9, 6, 5, 4, 3, 0, 1, 2⟩
private def iso_40 : Ten ℕ := ⟨0, 1, 2, 3, 4, 9, 7, 6, 5, 8⟩
private def iso_41 : Ten ℕ := ⟨0, 1, 2, 3, 4, 9, 6, 7, 8, 5⟩
private def iso_42 : Ten ℕ := ⟨6, 5, 4, 7, 8, 9, 1, 2, 3, 0⟩
private def isoRow_0 : Ten (Ten ℕ) := ⟨iso_0, iso_1, iso_2, iso_3, iso_4, iso_5, iso_6, iso_7, iso_8, iso_9⟩
private def isoRow_1 : Ten (Ten ℕ) := ⟨iso_10, iso_11, iso_12, iso_13, iso_14, iso_15, iso_16, iso_17, iso_18, iso_19⟩
private def isoRow_2 : Ten (Ten ℕ) := ⟨iso_20, iso_21, iso_22, iso_23, iso_24, iso_25, iso_26, iso_27, iso_28, iso_29⟩
private def isoRow_3 : Ten (Ten ℕ) := ⟨iso_30, iso_31, iso_32, iso_33, iso_34, iso_35, iso_36, iso_37, iso_38, iso_39⟩
private def isoRow_4 : Ten (Ten ℕ) := ⟨iso_40, iso_41, iso_42, dPerm, dPerm, dPerm, dPerm, dPerm, dPerm, dPerm⟩
private def isoRow_5 : Ten (Ten ℕ) := ⟨dPerm, dPerm, dPerm, dPerm, dPerm, dPerm, dPerm, dPerm, dPerm, dPerm⟩
private def isoRow_6 : Ten (Ten ℕ) := ⟨dPerm, dPerm, dPerm, dPerm, dPerm, dPerm, dPerm, dPerm, dPerm, dPerm⟩
private def isoRow_7 : Ten (Ten ℕ) := ⟨dPerm, dPerm, dPerm, dPerm, dPerm, dPerm, dPerm, dPerm, dPerm, dPerm⟩
private def isoRow_8 : Ten (Ten ℕ) := ⟨dPerm, dPerm, dPerm, dPerm, dPerm, dPerm, dPerm, dPerm, dPerm, dPerm⟩
private def isoRow_9 : Ten (Ten ℕ) := ⟨dPerm, dPerm, dPerm, dPerm, dPerm, dPerm, dPerm, dPerm, dPerm, dPerm⟩
private def isoGrid : Ten (Ten (Ten ℕ)) := ⟨isoRow_0, isoRow_1, isoRow_2, isoRow_3, isoRow_4, isoRow_5, isoRow_6, isoRow_7, isoRow_8, isoRow_9⟩
private def trRow_0 : Ten TripleD := ⟨⟨2, 0, 0, 0, 0⟩, ⟨3, 0, 1, 0, 1⟩, ⟨3, 0, 2, 0, 2⟩, ⟨2, 0, 3, 0, 3⟩, ⟨3, 0, 4, 0, 4⟩, ⟨3, 0, 5, 0, 5⟩, ⟨2, 0, 0, 0, 6⟩, ⟨2, 0, 0, 0, 7⟩, ⟨3, 0, 5, 0, 8⟩, ⟨3, 0, 6, 0, 2⟩⟩
private def trRow_1 : Ten TripleD := ⟨⟨2, 0, 7, 0, 7⟩, ⟨3, 0, 4, 0, 9⟩, ⟨3, 0, 8, 1, 0⟩, ⟨2, 0, 9, 0, 6⟩, ⟨2, 1, 0, 1, 1⟩, ⟨3, 1, 1, 1, 2⟩, ⟨3, 0, 2, 1, 3⟩, ⟨2, 1, 0, 1, 4⟩, ⟨3, 1, 2, 1, 5⟩, ⟨3, 1, 3, 1, 6⟩⟩
private def trRow_2 : Ten TripleD := ⟨⟨2, 1, 4, 1, 7⟩, ⟨3, 0, 4, 1, 8⟩, ⟨3, 0, 1, 1, 9⟩, ⟨2, 0, 3, 2, 0⟩, ⟨2, 1, 5, 2, 1⟩, ⟨3, 1, 6, 2, 2⟩, ⟨3, 1, 7, 2, 3⟩, ⟨3, 1, 8, 2, 4⟩, ⟨2, 0, 3, 2, 5⟩, ⟨2, 1, 9, 2, 6⟩⟩
private def trRow_3 : Ten TripleD := ⟨⟨2, 2, 0, 0, 2⟩, ⟨3, 1, 3, 2, 7⟩, ⟨3, 0, 5, 2, 8⟩, ⟨2, 2, 1, 0, 2⟩, ⟨2, 2, 2, 0, 2⟩, ⟨3, 1, 5, 2, 9⟩, ⟨3, 0, 0, 3, 0⟩, ⟨2, 0, 7, 0, 6⟩, ⟨3, 2, 3, 3, 1⟩, ⟨3, 0, 1, 3, 2⟩⟩
private def trRow_4 : Ten TripleD := ⟨⟨3, 2, 4, 2, 2⟩, ⟨3, 0, 4, 3, 3⟩, ⟨2, 2, 5, 3, 4⟩, ⟨2, 0, 3, 3, 5⟩, ⟨2, 2, 6, 0, 2⟩, ⟨3, 2, 7, 0, 2⟩, ⟨3, 2, 8, 3, 6⟩, ⟨3, 1, 1, 3, 7⟩, ⟨2, 1, 0, 3, 8⟩, ⟨2, 0, 4, 3, 9⟩⟩
private def trRow_5 : Ten TripleD := ⟨⟨3, 2, 9, 4, 0⟩, ⟨3, 1, 2, 4, 1⟩, ⟨3, 3, 0, 4, 2⟩, dTr, dTr, dTr, dTr, dTr, dTr, dTr⟩
private def trBlk_0 : Ten (Ten TripleD) := ⟨trRow_0, trRow_1, trRow_2, trRow_3, trRow_4, trRow_5, dTrRow, dTrRow, dTrRow, dTrRow⟩
private def trGrid : Three (Ten (Ten TripleD)) := ⟨trBlk_0, dTrBlk, dTrBlk⟩
private def ae_0 : AutEntry := ⟨2, ⟨0, 1, 2, 3, 4, 5, 6, 7, 8, 9⟩⟩
private def ae_1 : AutEntry := ⟨3, ⟨0, 1, 2, 3, 4, 5, 6, 7, 8, 9⟩⟩
private def ae_2 : AutEntry := ⟨2, ⟨0, 1, 2, 3, 4, 5, 6, 9, 7, 8⟩⟩
private def ae_3 : AutEntry := ⟨2, ⟨0, 1, 2, 3, 4, 5, 6, 8, 9, 7⟩⟩
private def ae_4 : AutEntry := ⟨3, ⟨0, 1, 2, 3, 4, 5, 7, 8, 9, 6⟩⟩
private def ae_5 : AutEntry := ⟨3, ⟨0, 1, 2, 3, 4, 5, 6, 9, 8, 7⟩⟩
private def ae_6 : AutEntry := ⟨2, ⟨2, 3, 4, 5, 6, 0, 1, 7, 8, 9⟩⟩
private def ae_7 : AutEntry := ⟨3, ⟨0, 1, 2, 3, 4, 5, 7, 6, 9, 8⟩⟩
private def ae_8 : AutEntry := ⟨3, ⟨0, 1, 2, 3, 4, 5, 9, 6, 7, 8⟩⟩
private def ae_9 : AutEntry := ⟨2, ⟨0, 1, 2, 3, 4, 5, 6, 7, 9, 8⟩⟩
private def ae_10 : AutEntry := ⟨2, ⟨2, 3, 4, 5, 6, 0, 1, 9, 7, 8⟩⟩
private def ae_11 : AutEntry := ⟨3, ⟨0, 1, 2, 3, 4, 5, 8, 9, 6, 7⟩⟩
private def ae_12 : AutEntry := ⟨2, ⟨0, 1, 2, 3, 4, 5, 6, 8, 7, 9⟩⟩
private def ae_13 : AutEntry := ⟨3, ⟨0, 1, 2, 3, 4, 5, 8, 7, 6, 9⟩⟩
private def ae_14 : AutEntry := ⟨2, ⟨2, 3, 4, 5, 6, 0, 1, 8, 9, 7⟩⟩
private def ae_15 : AutEntry := ⟨2, ⟨0, 1, 2, 3, 4, 5, 6, 9, 8, 7⟩⟩
private def ae_16 : AutEntry := ⟨3, ⟨0, 1, 2, 3, 4, 5, 9, 8, 7, 6⟩⟩
private def ae_17 : AutEntry := ⟨2, ⟨1, 0, 6, 5, 4, 3, 2, 7, 8, 9⟩⟩
private def ae_18 : AutEntry := ⟨2, ⟨1, 0, 6, 5, 4, 3, 2, 9, 7, 8⟩⟩
private def ae_19 : AutEntry := ⟨2, ⟨1, 0, 6, 5, 4, 3, 2, 8, 9, 7⟩⟩
private def ae_20 : AutEntry := ⟨2, ⟨4, 3, 2, 1, 0, 6, 5, 7, 8, 9⟩⟩
private def ae_21 : AutEntry := ⟨2, ⟨4, 3, 2, 1, 0, 6, 5, 9, 7, 8⟩⟩
private def ae_22 : AutEntry := ⟨2, ⟨4, 3, 2, 1, 0, 6, 5, 8, 9, 7⟩⟩
private def ae_23 : AutEntry := ⟨3, ⟨1, 0, 5, 4, 3, 2, 7, 6, 9, 8⟩⟩
private def ae_24 : AutEntry := ⟨3, ⟨1, 0, 5, 4, 3, 2, 8, 9, 6, 7⟩⟩
private def ae_25 : AutEntry := ⟨3, ⟨1, 0, 5, 4, 3, 2, 7, 8, 9, 6⟩⟩
private def ae_26 : AutEntry := ⟨2, ⟨3, 4, 5, 6, 0, 1, 2, 7, 8, 9⟩⟩
private def ae_27 : AutEntry := ⟨3, ⟨2, 3, 4, 5, 0, 1, 6, 7, 8, 9⟩⟩
private def ae_28 : AutEntry := ⟨2, ⟨3, 4, 5, 6, 0, 1, 2, 9, 7, 8⟩⟩
private def ae_29 : AutEntry := ⟨2, ⟨3, 4, 5, 6, 0, 1, 2, 8, 9, 7⟩⟩
private def ae_30 : AutEntry := ⟨3, ⟨2, 3, 4, 5, 0, 1, 6, 9, 8, 7⟩⟩
private def ae_31 : AutEntry := ⟨2, ⟨4, 5, 6, 0, 1, 2, 3, 7, 8, 9⟩⟩
private def ae_32 : AutEntry := ⟨3, ⟨1, 0, 5, 4, 3, 2, 6, 7, 8, 9⟩⟩
private def ae_33 : AutEntry := ⟨3, ⟨1, 0, 5, 4, 3, 2, 8, 7, 6, 9⟩⟩
private def ae_34 : AutEntry := ⟨3, ⟨2, 3, 4, 5, 0, 1, 7, 6, 9, 8⟩⟩
private def ae_35 : AutEntry := ⟨2, ⟨1, 0, 6, 5, 4, 3, 2, 9, 8, 7⟩⟩
private def ae_36 : AutEntry := ⟨3, ⟨2, 3, 4, 5, 0, 1, 9, 6, 7, 8⟩⟩
private def ae_37 : AutEntry := ⟨2, ⟨3, 4, 5, 6, 0, 1, 2, 8, 7, 9⟩⟩
private def ae_38 : AutEntry := ⟨2, ⟨2, 3, 4, 5, 6, 0, 1, 7, 9, 8⟩⟩
private def ae_39 : AutEntry := ⟨2, ⟨4, 5, 6, 0, 1, 2, 3, 9, 7, 8⟩⟩
private def ae_40 : AutEntry := ⟨3, ⟨1, 0, 5, 4, 3, 2, 9, 6, 7, 8⟩⟩
private def ae_41 : AutEntry := ⟨3, ⟨1, 0, 5, 4, 3, 2, 9, 8, 7, 6⟩⟩
private def ae_42 : AutEntry := ⟨3, ⟨2, 3, 4, 5, 0, 1, 8, 9, 6, 7⟩⟩
private def ae_43 : AutEntry := ⟨2, ⟨1, 0, 6, 5, 4, 3, 2, 7, 9, 8⟩⟩
private def ae_44 : AutEntry := ⟨2, ⟨3, 4, 5, 6, 0, 1, 2, 9, 8, 7⟩⟩
private def ae_45 : AutEntry := ⟨3, ⟨2, 3, 4, 5, 0, 1, 8, 7, 6, 9⟩⟩
private def ae_46 : AutEntry := ⟨2, ⟨2, 3, 4, 5, 6, 0, 1, 8, 7, 9⟩⟩
private def ae_47 : AutEntry := ⟨2, ⟨4, 5, 6, 0, 1, 2, 3, 8, 9, 7⟩⟩
private def ae_48 : AutEntry := ⟨3, ⟨1, 0, 5, 4, 3, 2, 6, 9, 8, 7⟩⟩
private def ae_49 : AutEntry := ⟨3, ⟨2, 3, 4, 5, 0, 1, 7, 8, 9, 6⟩⟩
private def ae_50 : AutEntry := ⟨2, ⟨1, 0, 6, 5, 4, 3, 2, 8, 7, 9⟩⟩
private def ae_51 : AutEntry := ⟨2, ⟨3, 4, 5, 6, 0, 1, 2, 7, 9, 8⟩⟩
private def ae_52 : AutEntry := ⟨3, ⟨2, 3, 4, 5, 0, 1, 9, 8, 7, 6⟩⟩
private def ae_53 : AutEntry := ⟨2, ⟨2, 3, 4, 5, 6, 0, 1, 9, 8, 7⟩⟩
private def ae_54 : AutEntry := ⟨2, ⟨5, 4, 3, 2, 1, 0, 6, 7, 8, 9⟩⟩
private def ae_55 : AutEntry := ⟨2, ⟨5, 4, 3, 2, 1, 0, 6, 9, 7, 8⟩⟩
private def ae_56 : AutEntry := ⟨2, ⟨5, 4, 3, 2, 1, 0, 6, 8, 9, 7⟩⟩
private def ae_57 : AutEntry := ⟨3, ⟨3, 4, 5, 0, 1, 2, 6, 7, 8, 9⟩⟩
private def ae_58 : AutEntry := ⟨3, ⟨3, 4, 5, 0, 1, 2, 7, 8, 9, 6⟩⟩
private def ae_59 : AutEntry := ⟨2, ⟨2, 1, 0, 6, 5, 4, 3, 7, 8, 9⟩⟩
private def ae_60 : AutEntry := ⟨3, ⟨1, 2, 3, 4, 5, 0, 6, 7, 8, 9⟩⟩
private def ae_61 : AutEntry := ⟨2, ⟨2, 1, 0, 6, 5, 4, 3, 9, 7, 8⟩⟩
private def ae_62 : AutEntry := ⟨2, ⟨2, 1, 0, 6, 5, 4, 3, 8, 9, 7⟩⟩
private def ae_63 : AutEntry := ⟨3, ⟨1, 2, 3, 4, 5, 0, 6, 9, 8, 7⟩⟩
private def ae_64 : AutEntry := ⟨3, ⟨1, 2, 3, 4, 5, 0, 7, 6, 9, 8⟩⟩
private def ae_65 : AutEntry := ⟨2, ⟨2, 1, 0, 6, 5, 4, 3, 9, 8, 7⟩⟩
private def ae_66 : AutEntry := ⟨3, ⟨1, 2, 3, 4, 5, 0, 9, 6, 7, 8⟩⟩
private def ae_67 : AutEntry := ⟨3, ⟨1, 2, 3, 4, 5, 0, 8, 9, 6, 7⟩⟩
private def ae_68 : AutEntry := ⟨3, ⟨1, 2, 3, 4, 5, 0, 8, 7, 6, 9⟩⟩
private def ae_69 : AutEntry := ⟨2, ⟨2, 1, 0, 6, 5, 4, 3, 7, 9, 8⟩⟩
private def ae_70 : AutEntry := ⟨3, ⟨1, 2, 3, 4, 5, 0, 7, 8, 9, 6⟩⟩
private def ae_71 : AutEntry := ⟨2, ⟨2, 1, 0, 6, 5, 4, 3, 8, 7, 9⟩⟩
private def ae_72 : AutEntry := ⟨3, ⟨1, 2, 3, 4, 5, 0, 9, 8, 7, 6⟩⟩
private def ae_73 : AutEntry := ⟨3, ⟨4, 3, 2, 1, 0, 5, 6, 7, 8, 9⟩⟩
private def ae_74 : AutEntry := ⟨3, ⟨4, 3, 2, 1, 0, 5, 6, 9, 8, 7⟩⟩
private def ae_75 : AutEntry := ⟨2, ⟨1, 2, 3, 4, 5, 6, 0, 7, 8, 9⟩⟩
private def ae_76 : AutEntry := ⟨2, ⟨1, 2, 3, 4, 5, 6, 0, 9, 7, 8⟩⟩
private def ae_77 : AutEntry := ⟨2, ⟨1, 2, 3, 4, 5, 6, 0, 8, 9, 7⟩⟩
private def ae_78 : AutEntry := ⟨2, ⟨1, 2, 3, 4, 5, 6, 0, 7, 9, 8⟩⟩
private def ae_79 : AutEntry := ⟨2, ⟨1, 2, 3, 4, 5, 6, 0, 8, 7, 9⟩⟩
private def ae_80 : AutEntry := ⟨3, ⟨2, 1, 0, 5, 4, 3, 6, 9, 8, 7⟩⟩
private def ae_81 : AutEntry := ⟨3, ⟨2, 1, 0, 5, 4, 3, 6, 7, 8, 9⟩⟩
private def ae_82 : AutEntry := ⟨2, ⟨1, 2, 3, 4, 5, 6, 0, 9, 8, 7⟩⟩
private def ae_83 : AutEntry := ⟨3, ⟨4, 3, 2, 1, 0, 5, 7, 6, 9, 8⟩⟩
private def ae_84 : AutEntry := ⟨2, ⟨4, 3, 2, 1, 0, 6, 5, 7, 9, 8⟩⟩
private def ae_85 : AutEntry := ⟨3, ⟨4, 3, 2, 1, 0, 5, 9, 6, 7, 8⟩⟩
private def ae_86 : AutEntry := ⟨3, ⟨2, 1, 0, 5, 4, 3, 9, 6, 7, 8⟩⟩
private def ae_87 : AutEntry := ⟨3, ⟨2, 1, 0, 5, 4, 3, 7, 6, 9, 8⟩⟩
private def ae_88 : AutEntry := ⟨3, ⟨4, 3, 2, 1, 0, 5, 8, 9, 6, 7⟩⟩
private def ae_89 : AutEntry := ⟨3, ⟨4, 3, 2, 1, 0, 5, 8, 7, 6, 9⟩⟩
private def ae_90 : AutEntry := ⟨2, ⟨4, 3, 2, 1, 0, 6, 5, 8, 7, 9⟩⟩
private def ae_91 : AutEntry := ⟨3, ⟨2, 1, 0, 5, 4, 3, 8, 9, 6, 7⟩⟩
private def ae_92 : AutEntry := ⟨3, ⟨2, 1, 0, 5, 4, 3, 8, 7, 6, 9⟩⟩
private def ae_93 : AutEntry := ⟨3, ⟨4, 3, 2, 1, 0, 5, 7, 8, 9, 6⟩⟩
private def ae_94 : AutEntry := ⟨2, ⟨4, 3, 2, 1, 0, 6, 5, 9, 8, 7⟩⟩
private def ae_95 : AutEntry := ⟨3, ⟨4, 3, 2, 1, 0, 5, 9, 8, 7, 6⟩⟩
private def ae_96 : AutEntry := ⟨3, ⟨2, 1, 0, 5, 4, 3, 9, 8, 7, 6⟩⟩
private def ae_97 : AutEntry := ⟨3, ⟨2, 1, 0, 5, 4, 3, 7, 8, 9, 6⟩⟩
private def ae_98 : AutEntry := ⟨2, ⟨6, 0, 1, 2, 3, 4, 5, 7, 8, 9⟩⟩
private def ae_99 : AutEntry := ⟨3, ⟨5, 0, 1, 2, 3, 4, 6, 7, 8, 9⟩⟩
private def ae_100 : AutEntry := ⟨2, ⟨6, 0, 1, 2, 3, 4, 5, 9, 7, 8⟩⟩
private def ae_101 : AutEntry := ⟨2, ⟨6, 0, 1, 2, 3, 4, 5, 8, 9, 7⟩⟩
private def ae_102 : AutEntry := ⟨3, ⟨5, 0, 1, 2, 3, 4, 6, 9, 8, 7⟩⟩
private def ae_103 : AutEntry := ⟨3, ⟨5, 0, 1, 2, 3, 4, 7, 6, 9, 8⟩⟩
private def ae_104 : AutEntry := ⟨3, ⟨5, 0, 1, 2, 3, 4, 9, 6, 7, 8⟩⟩
private def ae_105 : AutEntry := ⟨2, ⟨6, 0, 1, 2, 3, 4, 5, 7, 9, 8⟩⟩
private def ae_106 : AutEntry := ⟨3, ⟨5, 0, 1, 2, 3, 4, 8, 9, 6, 7⟩⟩
private def ae_107 : AutEntry := ⟨2, ⟨6, 0, 1, 2, 3, 4, 5, 8, 7, 9⟩⟩
private def ae_108 : AutEntry := ⟨3, ⟨5, 0, 1, 2, 3, 4, 8, 7, 6, 9⟩⟩
private def ae_109 : AutEntry := ⟨3, ⟨5, 0, 1, 2, 3, 4, 7, 8, 9, 6⟩⟩
private def ae_110 : AutEntry := ⟨2, ⟨6, 0, 1, 2, 3, 4, 5, 9, 8, 7⟩⟩
private def ae_111 : AutEntry := ⟨3, ⟨5, 0, 1, 2, 3, 4, 9, 8, 7, 6⟩⟩
private def ae_112 : AutEntry := ⟨3, ⟨4, 5, 0, 1, 2, 3, 7, 6, 9, 8⟩⟩
private def ae_113 : AutEntry := ⟨3, ⟨4, 5, 0, 1, 2, 3, 8, 9, 6, 7⟩⟩
private def ae_114 : AutEntry := ⟨3, ⟨4, 5, 0, 1, 2, 3, 7, 8, 9, 6⟩⟩
private def ae_115 : AutEntry := ⟨2, ⟨6, 5, 4, 3, 2, 1, 0, 7, 8, 9⟩⟩
private def ae_116 : AutEntry := ⟨3, ⟨4, 5, 0, 1, 2, 3, 6, 7, 8, 9⟩⟩
private def ae_117 : AutEntry := ⟨3, ⟨4, 5, 0, 1, 2, 3, 8, 7, 6, 9⟩⟩
private def ae_118 : AutEntry := ⟨2, ⟨5, 6, 0, 1, 2, 3, 4, 9, 7, 8⟩⟩
private def ae_119 : AutEntry := ⟨2, ⟨5, 6, 0, 1, 2, 3, 4, 9, 8, 7⟩⟩
private def ae_120 : AutEntry := ⟨2, ⟨5, 4, 3, 2, 1, 0, 6, 8, 7, 9⟩⟩
private def ae_121 : AutEntry := ⟨2, ⟨6, 5, 4, 3, 2, 1, 0, 9, 7, 8⟩⟩
private def ae_122 : AutEntry := ⟨3, ⟨4, 5, 0, 1, 2, 3, 9, 6, 7, 8⟩⟩
private def ae_123 : AutEntry := ⟨3, ⟨4, 5, 0, 1, 2, 3, 9, 8, 7, 6⟩⟩
private def ae_124 : AutEntry := ⟨2, ⟨5, 6, 0, 1, 2, 3, 4, 7, 9, 8⟩⟩
private def ae_125 : AutEntry := ⟨2, ⟨5, 6, 0, 1, 2, 3, 4, 8, 9, 7⟩⟩
private def ae_126 : AutEntry := ⟨2, ⟨5, 4, 3, 2, 1, 0, 6, 9, 8, 7⟩⟩
private def ae_127 : AutEntry := ⟨2, ⟨6, 5, 4, 3, 2, 1, 0, 8, 9, 7⟩⟩
private def ae_128 : AutEntry := ⟨3, ⟨4, 5, 0, 1, 2, 3, 6, 9, 8, 7⟩⟩
private def ae_129 : AutEntry := ⟨2, ⟨5, 6, 0, 1, 2, 3, 4, 7, 8, 9⟩⟩
private def ae_130 : AutEntry := ⟨2, ⟨5, 6, 0, 1, 2, 3, 4, 8, 7, 9⟩⟩
private def ae_131 : AutEntry := ⟨2, ⟨5, 4, 3, 2, 1, 0, 6, 7, 9, 8⟩⟩
private def ae_132 : AutEntry := ⟨2, ⟨3, 2, 1, 0, 6, 5, 4, 7, 8, 9⟩⟩
private def ae_133 : AutEntry := ⟨2, ⟨3, 2, 1, 0, 6, 5, 4, 9, 7, 8⟩⟩
private def ae_134 : AutEntry := ⟨2, ⟨3, 2, 1, 0, 6, 5, 4, 8, 9, 7⟩⟩
private def ae_135 : AutEntry := ⟨3, ⟨0, 5, 4, 3, 2, 1, 8, 9, 6, 7⟩⟩
private def ae_136 : AutEntry := ⟨3, ⟨3, 4, 5, 0, 1, 2, 6, 9, 8, 7⟩⟩
private def ae_137 : AutEntry := ⟨3, ⟨0, 5, 4, 3, 2, 1, 8, 7, 6, 9⟩⟩
private def ae_138 : AutEntry := ⟨3, ⟨3, 4, 5, 0, 1, 2, 7, 6, 9, 8⟩⟩
private def ae_139 : AutEntry := ⟨3, ⟨0, 5, 4, 3, 2, 1, 9, 8, 7, 6⟩⟩
private def ae_140 : AutEntry := ⟨3, ⟨3, 4, 5, 0, 1, 2, 9, 6, 7, 8⟩⟩
private def ae_141 : AutEntry := ⟨3, ⟨0, 5, 4, 3, 2, 1, 7, 8, 9, 6⟩⟩
private def ae_142 : AutEntry := ⟨2, ⟨4, 5, 6, 0, 1, 2, 3, 8, 7, 9⟩⟩
private def ae_143 : AutEntry := ⟨3, ⟨3, 4, 5, 0, 1, 2, 8, 9, 6, 7⟩⟩
private def ae_144 : AutEntry := ⟨2, ⟨4, 5, 6, 0, 1, 2, 3, 9, 8, 7⟩⟩
private def ae_145 : AutEntry := ⟨3, ⟨3, 4, 5, 0, 1, 2, 8, 7, 6, 9⟩⟩
private def ae_146 : AutEntry := ⟨3, ⟨0, 5, 4, 3, 2, 1, 6, 9, 8, 7⟩⟩
private def ae_147 : AutEntry := ⟨3, ⟨0, 5, 4, 3, 2, 1, 6, 7, 8, 9⟩⟩
private def ae_148 : AutEntry := ⟨3, ⟨0, 5, 4, 3, 2, 1, 9, 6, 7, 8⟩⟩
private def ae_149 : AutEntry := ⟨2, ⟨4, 5, 6, 0, 1, 2, 3, 7, 9, 8⟩⟩
private def ae_150 : AutEntry := ⟨3, ⟨3, 4, 5, 0, 1, 2, 9, 8, 7, 6⟩⟩
private def ae_151 : AutEntry := ⟨3, ⟨0, 5, 4, 3, 2, 1, 7, 6, 9, 8⟩⟩
private def ae_152 : AutEntry := ⟨2, ⟨0, 6, 5, 4, 3, 2, 1, 7, 8, 9⟩⟩
private def ae_153 : AutEntry := ⟨2, ⟨0, 6, 5, 4, 3, 2, 1, 9, 7, 8⟩⟩
private def ae_154 : AutEntry := ⟨2, ⟨0, 6, 5, 4, 3, 2, 1, 8, 9, 7⟩⟩
private def ae_155 : AutEntry := ⟨2, ⟨0, 6, 5, 4, 3, 2, 1, 9, 8, 7⟩⟩
private def ae_156 : AutEntry := ⟨2, ⟨0, 6, 5, 4, 3, 2, 1, 7, 9, 8⟩⟩
private def ae_157 : AutEntry := ⟨2, ⟨0, 6, 5, 4, 3, 2, 1, 8, 7, 9⟩⟩
private def ae_158 : AutEntry := ⟨3, ⟨5, 4, 3, 2, 1, 0, 7, 6, 9, 8⟩⟩
private def ae_159 : AutEntry := ⟨3, ⟨3, 2, 1, 0, 5, 4, 7, 6, 9, 8⟩⟩
private def ae_160 : AutEntry := ⟨3, ⟨5, 4, 3, 2, 1, 0, 8, 9, 6, 7⟩⟩
private def ae_161 : AutEntry := ⟨3, ⟨5, 4, 3, 2, 1, 0, 7, 8, 9, 6⟩⟩
private def ae_162 : AutEntry := ⟨3, ⟨3, 2, 1, 0, 5, 4, 7, 8, 9, 6⟩⟩
private def ae_163 : AutEntry := ⟨3, ⟨3, 2, 1, 0, 5, 4, 6, 7, 8, 9⟩⟩
private def ae_164 : AutEntry := ⟨3, ⟨3, 2, 1, 0, 5, 4, 6, 9, 8, 7⟩⟩
private def ae_165 : AutEntry := ⟨3, ⟨5, 4, 3, 2, 1, 0, 8, 7, 6, 9⟩⟩
private def ae_166 : AutEntry := ⟨3, ⟨5, 4, 3, 2, 1, 0, 6, 7, 8, 9⟩⟩
private def ae_167 : AutEntry := ⟨2, ⟨3, 2, 1, 0, 6, 5, 4, 7, 9, 8⟩⟩
private def ae_168 : AutEntry := ⟨3, ⟨3, 2, 1, 0, 5, 4, 8, 7, 6, 9⟩⟩
private def ae_169 : AutEntry := ⟨2, ⟨6, 5, 4, 3, 2, 1, 0, 9, 8, 7⟩⟩
private def ae_170 : AutEntry := ⟨3, ⟨3, 2, 1, 0, 5, 4, 9, 6, 7, 8⟩⟩
private def ae_171 : AutEntry := ⟨3, ⟨5, 4, 3, 2, 1, 0, 9, 8, 7, 6⟩⟩
private def ae_172 : AutEntry := ⟨2, ⟨3, 2, 1, 0, 6, 5, 4, 8, 7, 9⟩⟩
private def ae_173 : AutEntry := ⟨3, ⟨5, 4, 3, 2, 1, 0, 9, 6, 7, 8⟩⟩
private def ae_174 : AutEntry := ⟨3, ⟨3, 2, 1, 0, 5, 4, 9, 8, 7, 6⟩⟩
private def ae_175 : AutEntry := ⟨2, ⟨6, 5, 4, 3, 2, 1, 0, 7, 9, 8⟩⟩
private def ae_176 : AutEntry := ⟨3, ⟨3, 2, 1, 0, 5, 4, 8, 9, 6, 7⟩⟩
private def ae_177 : AutEntry := ⟨3, ⟨5, 4, 3, 2, 1, 0, 6, 9, 8, 7⟩⟩
private def ae_178 : AutEntry := ⟨2, ⟨3, 2, 1, 0, 6, 5, 4, 9, 8, 7⟩⟩
private def ae_179 : AutEntry := ⟨2, ⟨6, 5, 4, 3, 2, 1, 0, 8, 7, 9⟩⟩
private def autRow_0 : Ten AutEntry := ⟨ae_0, ae_1, ae_2, ae_3, ae_4, ae_5, ae_6, ae_7, ae_8, ae_9⟩
private def autRow_1 : Ten AutEntry := ⟨ae_10, ae_11, ae_12, ae_13, ae_14, ae_15, ae_16, ae_17, ae_18, ae_19⟩
private def autRow_2 : Ten AutEntry := ⟨ae_20, ae_21, ae_22, ae_23, ae_24, ae_25, ae_26, ae_27, ae_28, ae_29⟩
private def autRow_3 : Ten AutEntry := ⟨ae_30, ae_31, ae_32, ae_33, ae_34, ae_35, ae_36, ae_37, ae_38, ae_39⟩
private def autRow_4 : Ten AutEntry := ⟨ae_40, ae_41, ae_42, ae_43, ae_44, ae_45, ae_46, ae_47, ae_48, ae_49⟩
private def autRow_5 : Ten AutEntry := ⟨ae_50, ae_51, ae_52, ae_53, ae_54, ae_55, ae_56, ae_57, ae_58, ae_59⟩
private def autRow_6 : Ten AutEntry := ⟨ae_60, ae_61, ae_62, ae_63, ae_64, ae_65, ae_66, ae_67, ae_68, ae_69⟩
private def autRow_7 : Ten AutEntry := ⟨ae_70, ae_71, ae_72, ae_73, ae_74, ae_75, ae_76, ae_77, ae_78, ae_79⟩
private def autRow_8 : Ten AutEntry := ⟨ae_80, ae_81, ae_82, ae_83, ae_84, ae_85, ae_86, ae_87, ae_88, ae_89⟩
private def autRow_9 : Ten AutEntry := ⟨ae_90, ae_91, ae_92, ae_93, ae_94, ae_95, ae_96, ae_97, ae_98, ae_99⟩
private def autRow_10 : Ten AutEntry := ⟨ae_100, ae_101, ae_102, ae_103, ae_104, ae_105, ae_106, ae_107, ae_108, ae_109⟩
private def autRow_11 : Ten AutEntry := ⟨ae_110, ae_111, ae_112, ae_113, ae_114, ae_115, ae_116, ae_117, ae_118, ae_119⟩
private def autRow_12 : Ten AutEntry := ⟨ae_120, ae_121, ae_122, ae_123, ae_124, ae_125, ae_126, ae_127, ae_128, ae_129⟩
private def autRow_13 : Ten AutEntry := ⟨ae_130, ae_131, ae_132, ae_133, ae_134, ae_135, ae_136, ae_137, ae_138, ae_139⟩
private def autRow_14 : Ten AutEntry := ⟨ae_140, ae_141, ae_142, ae_143, ae_144, ae_145, ae_146, ae_147, ae_148, ae_149⟩
private def autRow_15 : Ten AutEntry := ⟨ae_150, ae_151, ae_152, ae_153, ae_154, ae_155, ae_156, ae_157, ae_158, ae_159⟩
private def autRow_16 : Ten AutEntry := ⟨ae_160, ae_161, ae_162, ae_163, ae_164, ae_165, ae_166, ae_167, ae_168, ae_169⟩
private def autRow_17 : Ten AutEntry := ⟨ae_170, ae_171, ae_172, ae_173, ae_174, ae_175, ae_176, ae_177, ae_178, ae_179⟩
private def autBlk_0 : Ten (Ten AutEntry) := ⟨autRow_0, autRow_1, autRow_2, autRow_3, autRow_4, autRow_5, autRow_6, autRow_7, autRow_8, autRow_9⟩
private def autBlk_1 : Ten (Ten AutEntry) := ⟨autRow_10, autRow_11, autRow_12, autRow_13, autRow_14, autRow_15, autRow_16, autRow_17, dAeRow, dAeRow⟩
private def autGrid : Three (Ten (Ten AutEntry)) := ⟨autBlk_0, autBlk_1, dAeBlk⟩
private def lw53_0_0 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 1, 0, 0, 1⟩⟩, ⟨⟨0, 0, 0, 0, 0, 2⟩, ⟨0, 0, 2, 0, 0, 1⟩⟩, ⟨⟨0, 0, 0, 0, 0, 3⟩, ⟨0, 0, 1, 0, 0, 4⟩⟩⟩, ⟨⟨⟨0, 0, 3, 0, 0, 0⟩, ⟨0, 0, 4, 0, 0, 1⟩⟩, ⟨⟨0, 0, 3, 0, 0, 2⟩, ⟨0, 0, 5, 0, 0, 1⟩⟩, ⟨⟨0, 0, 3, 0, 0, 3⟩, ⟨0, 0, 4, 0, 0, 5⟩⟩⟩, ⟨⟨⟨0, 0, 0, 0, 0, 6⟩, ⟨0, 0, 4, 0, 0, 7⟩⟩, ⟨⟨0, 0, 6, 0, 0, 0⟩, ⟨0, 0, 4, 0, 0, 8⟩⟩, ⟨⟨0, 0, 6, 0, 0, 9⟩, ⟨0, 0, 5, 0, 0, 8⟩⟩⟩, ⟨⟨⟨0, 0, 0, 0, 1, 0⟩, ⟨0, 0, 5, 0, 1, 1⟩⟩, ⟨⟨0, 0, 6, 0, 1, 2⟩, ⟨0, 0, 4, 0, 1, 3⟩⟩, ⟨⟨0, 0, 6, 0, 0, 2⟩, ⟨0, 0, 4, 0, 1, 1⟩⟩⟩, ⟨⟨⟨0, 0, 0, 0, 1, 4⟩, ⟨0, 0, 4, 0, 0, 4⟩⟩, ⟨⟨0, 0, 6, 0, 0, 3⟩, ⟨0, 0, 5, 0, 0, 4⟩⟩, ⟨⟨0, 0, 6, 0, 1, 5⟩, ⟨0, 0, 4, 0, 1, 6⟩⟩⟩⟩
private def lw53_0_1 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 0, 7, 0, 0, 0⟩, ⟨0, 0, 8, 0, 0, 1⟩⟩, ⟨⟨0, 0, 7, 0, 0, 2⟩, ⟨0, 0, 9, 0, 0, 1⟩⟩, ⟨⟨0, 0, 7, 0, 0, 3⟩, ⟨0, 0, 8, 0, 0, 4⟩⟩⟩, ⟨⟨⟨0, 1, 0, 0, 0, 0⟩, ⟨0, 1, 1, 0, 0, 1⟩⟩, ⟨⟨0, 1, 0, 0, 0, 2⟩, ⟨0, 1, 2, 0, 0, 1⟩⟩, ⟨⟨0, 1, 0, 0, 0, 3⟩, ⟨0, 1, 1, 0, 0, 5⟩⟩⟩, ⟨⟨⟨0, 0, 3, 0, 0, 6⟩, ⟨0, 1, 1, 0, 0, 7⟩⟩, ⟨⟨0, 1, 3, 0, 0, 0⟩, ⟨0, 1, 1, 0, 0, 8⟩⟩, ⟨⟨0, 1, 3, 0, 0, 9⟩, ⟨0, 1, 2, 0, 0, 8⟩⟩⟩, ⟨⟨⟨0, 0, 3, 0, 1, 0⟩, ⟨0, 1, 2, 0, 1, 1⟩⟩, ⟨⟨0, 1, 3, 0, 1, 2⟩, ⟨0, 1, 1, 0, 1, 3⟩⟩, ⟨⟨0, 1, 3, 0, 0, 2⟩, ⟨0, 1, 1, 0, 1, 1⟩⟩⟩, ⟨⟨⟨0, 0, 3, 0, 1, 4⟩, ⟨0, 1, 1, 0, 0, 4⟩⟩, ⟨⟨0, 1, 3, 0, 0, 3⟩, ⟨0, 1, 2, 0, 0, 4⟩⟩, ⟨⟨0, 1, 3, 0, 1, 5⟩, ⟨0, 1, 1, 0, 1, 6⟩⟩⟩⟩
private def lw53_0_2 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 1, 4, 0, 0, 0⟩, ⟨0, 1, 5, 0, 0, 1⟩⟩, ⟨⟨0, 1, 4, 0, 0, 2⟩, ⟨0, 1, 6, 0, 0, 1⟩⟩, ⟨⟨0, 1, 4, 0, 0, 3⟩, ⟨0, 1, 5, 0, 0, 4⟩⟩⟩, ⟨⟨⟨0, 1, 7, 0, 0, 0⟩, ⟨0, 1, 8, 0, 0, 1⟩⟩, ⟨⟨0, 1, 7, 0, 0, 2⟩, ⟨0, 1, 9, 0, 0, 1⟩⟩, ⟨⟨0, 1, 7, 0, 0, 3⟩, ⟨0, 1, 8, 0, 0, 5⟩⟩⟩, ⟨⟨⟨0, 1, 0, 0, 1, 7⟩, ⟨0, 1, 8, 0, 0, 7⟩⟩, ⟨⟨0, 2, 0, 0, 0, 0⟩, ⟨0, 1, 8, 0, 0, 8⟩⟩, ⟨⟨0, 2, 0, 0, 0, 9⟩, ⟨0, 1, 9, 0, 0, 8⟩⟩⟩, ⟨⟨⟨0, 1, 0, 0, 1, 8⟩, ⟨0, 1, 9, 0, 1, 1⟩⟩, ⟨⟨0, 2, 0, 0, 1, 2⟩, ⟨0, 1, 8, 0, 1, 3⟩⟩, ⟨⟨0, 2, 0, 0, 0, 2⟩, ⟨0, 1, 8, 0, 1, 1⟩⟩⟩, ⟨⟨⟨0, 1, 0, 0, 1, 9⟩, ⟨0, 1, 8, 0, 0, 4⟩⟩, ⟨⟨0, 2, 0, 0, 0, 3⟩, ⟨0, 1, 9, 0, 0, 4⟩⟩, ⟨⟨0, 2, 0, 0, 1, 5⟩, ⟨0, 1, 8, 0, 1, 6⟩⟩⟩⟩
private def lw53_0_3 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 1, 4, 0, 2, 0⟩, ⟨0, 2, 1, 0, 0, 1⟩⟩, ⟨⟨0, 1, 4, 0, 2, 1⟩, ⟨0, 2, 2, 0, 0, 1⟩⟩, ⟨⟨0, 1, 4, 0, 2, 2⟩, ⟨0, 2, 1, 0, 0, 5⟩⟩⟩, ⟨⟨⟨0, 2, 3, 0, 0, 0⟩, ⟨0, 1, 1, 0, 2, 3⟩⟩, ⟨⟨0, 2, 3, 0, 0, 2⟩, ⟨0, 1, 2, 0, 2, 4⟩⟩, ⟨⟨0, 2, 3, 0, 0, 3⟩, ⟨0, 1, 1, 0, 2, 5⟩⟩⟩, ⟨⟨⟨0, 1, 4, 0, 2, 6⟩, ⟨0, 0, 4, 0, 2, 7⟩⟩, ⟨⟨0, 2, 4, 0, 0, 0⟩, ⟨0, 2, 5, 0, 0, 1⟩⟩, ⟨⟨0, 2, 4, 0, 0, 9⟩, ⟨0, 2, 6, 0, 0, 1⟩⟩⟩, ⟨⟨⟨0, 1, 4, 0, 2, 8⟩, ⟨0, 0, 5, 0, 2, 7⟩⟩, ⟨⟨0, 2, 4, 0, 1, 2⟩, ⟨0, 2, 7, 0, 0, 1⟩⟩, ⟨⟨0, 2, 4, 0, 0, 2⟩, ⟨0, 2, 7, 0, 0, 5⟩⟩⟩, ⟨⟨⟨0, 1, 4, 0, 2, 9⟩, ⟨0, 0, 4, 0, 3, 0⟩⟩, ⟨⟨0, 2, 4, 0, 0, 3⟩, ⟨0, 2, 6, 0, 0, 5⟩⟩, ⟨⟨0, 2, 4, 0, 1, 5⟩, ⟨0, 2, 5, 0, 0, 5⟩⟩⟩⟩
private def lw53_0_4 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 0, 0, 0, 3, 1⟩, ⟨0, 2, 1, 0, 0, 7⟩⟩, ⟨⟨0, 2, 8, 0, 0, 0⟩, ⟨0, 2, 1, 0, 0, 8⟩⟩, ⟨⟨0, 2, 8, 0, 0, 9⟩, ⟨0, 2, 2, 0, 0, 8⟩⟩⟩, ⟨⟨⟨0, 0, 7, 0, 1, 7⟩, ⟨0, 1, 1, 0, 3, 2⟩⟩, ⟨⟨0, 2, 9, 0, 0, 0⟩, ⟨0, 1, 1, 0, 3, 3⟩⟩, ⟨⟨0, 2, 9, 0, 0, 9⟩, ⟨0, 1, 2, 0, 2, 5⟩⟩⟩, ⟨⟨⟨0, 1, 4, 0, 1, 7⟩, ⟨0, 0, 4, 0, 3, 4⟩⟩, ⟨⟨0, 2, 0, 0, 3, 5⟩, ⟨0, 2, 6, 0, 0, 7⟩⟩, ⟨⟨0, 2, 0, 0, 1, 8⟩, ⟨0, 2, 5, 0, 0, 7⟩⟩⟩, ⟨⟨⟨0, 2, 8, 0, 2, 9⟩, ⟨0, 0, 4, 0, 3, 6⟩⟩, ⟨⟨0, 1, 3, 0, 3, 5⟩, ⟨0, 2, 6, 0, 0, 8⟩⟩, ⟨⟨0, 0, 6, 0, 0, 6⟩, ⟨0, 2, 5, 0, 0, 8⟩⟩⟩, ⟨⟨⟨0, 2, 8, 0, 3, 7⟩, ⟨0, 0, 5, 0, 3, 6⟩⟩, ⟨⟨0, 1, 3, 0, 1, 8⟩, ⟨0, 2, 7, 0, 0, 7⟩⟩, ⟨⟨0, 0, 6, 0, 3, 8⟩, ⟨0, 2, 7, 0, 0, 8⟩⟩⟩⟩
private def lw53_0_5 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 0, 0, 0, 3, 9⟩, ⟨0, 2, 2, 0, 1, 1⟩⟩, ⟨⟨0, 2, 8, 0, 1, 2⟩, ⟨0, 2, 1, 0, 1, 3⟩⟩, ⟨⟨0, 2, 8, 0, 0, 2⟩, ⟨0, 2, 1, 0, 1, 1⟩⟩⟩, ⟨⟨⟨0, 0, 7, 0, 1, 8⟩, ⟨0, 1, 2, 0, 3, 2⟩⟩, ⟨⟨0, 2, 9, 0, 1, 2⟩, ⟨0, 1, 1, 0, 4, 0⟩⟩, ⟨⟨0, 2, 9, 0, 0, 2⟩, ⟨0, 1, 1, 0, 4, 1⟩⟩⟩, ⟨⟨⟨0, 1, 4, 0, 1, 8⟩, ⟨0, 0, 5, 0, 4, 2⟩⟩, ⟨⟨0, 2, 0, 0, 1, 9⟩, ⟨0, 2, 7, 0, 1, 3⟩⟩, ⟨⟨0, 2, 0, 0, 4, 3⟩, ⟨0, 2, 7, 0, 1, 1⟩⟩⟩, ⟨⟨⟨0, 2, 8, 0, 4, 4⟩, ⟨0, 0, 4, 0, 4, 5⟩⟩, ⟨⟨0, 1, 3, 0, 1, 9⟩, ⟨0, 2, 5, 0, 1, 3⟩⟩, ⟨⟨0, 0, 6, 0, 4, 6⟩, ⟨0, 2, 6, 0, 1, 3⟩⟩⟩, ⟨⟨⟨0, 2, 8, 0, 2, 6⟩, ⟨0, 0, 4, 0, 4, 2⟩⟩, ⟨⟨0, 1, 3, 0, 4, 3⟩, ⟨0, 2, 5, 0, 1, 1⟩⟩, ⟨⟨0, 0, 6, 0, 1, 0⟩, ⟨0, 2, 6, 0, 1, 1⟩⟩⟩⟩
private def lw53_0_6 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 0, 0, 0, 4, 7⟩, ⟨0, 2, 1, 0, 0, 4⟩⟩, ⟨⟨0, 2, 8, 0, 0, 3⟩, ⟨0, 2, 2, 0, 0, 4⟩⟩, ⟨⟨0, 2, 8, 0, 1, 5⟩, ⟨0, 2, 1, 0, 1, 6⟩⟩⟩, ⟨⟨⟨0, 0, 7, 0, 1, 9⟩, ⟨0, 1, 1, 0, 4, 8⟩⟩, ⟨⟨0, 2, 9, 0, 0, 3⟩, ⟨0, 1, 2, 0, 4, 0⟩⟩, ⟨⟨0, 2, 9, 0, 1, 5⟩, ⟨0, 1, 1, 0, 2, 4⟩⟩⟩, ⟨⟨⟨0, 1, 4, 0, 1, 9⟩, ⟨0, 0, 4, 0, 4, 9⟩⟩, ⟨⟨0, 2, 0, 0, 5, 0⟩, ⟨0, 2, 5, 0, 0, 4⟩⟩, ⟨⟨0, 2, 0, 0, 1, 7⟩, ⟨0, 2, 6, 0, 0, 4⟩⟩⟩, ⟨⟨⟨0, 2, 8, 0, 2, 8⟩, ⟨0, 0, 5, 0, 4, 9⟩⟩, ⟨⟨0, 1, 3, 0, 5, 0⟩, ⟨0, 2, 7, 0, 0, 4⟩⟩, ⟨⟨0, 0, 6, 0, 1, 4⟩, ⟨0, 2, 7, 0, 1, 6⟩⟩⟩, ⟨⟨⟨0, 2, 8, 0, 5, 1⟩, ⟨0, 0, 4, 0, 5, 2⟩⟩, ⟨⟨0, 1, 3, 0, 1, 7⟩, ⟨0, 2, 6, 0, 1, 6⟩⟩, ⟨⟨0, 0, 6, 0, 5, 3⟩, ⟨0, 2, 5, 0, 1, 6⟩⟩⟩⟩
private def lwBlk_0 : Seven (Five (Three LeafWit)) := ⟨lw53_0_0, lw53_0_1, lw53_0_2, lw53_0_3, lw53_0_4, lw53_0_5, lw53_0_6⟩
private def lw53_1_0 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 0, 7, 0, 5, 4⟩, ⟨0, 0, 8, 0, 2, 7⟩⟩, ⟨⟨0, 0, 7, 0, 5, 5⟩, ⟨0, 0, 9, 0, 2, 7⟩⟩, ⟨⟨0, 0, 7, 0, 5, 6⟩, ⟨0, 0, 8, 0, 4, 9⟩⟩⟩, ⟨⟨⟨0, 3, 0, 0, 0, 0⟩, ⟨0, 3, 1, 0, 0, 1⟩⟩, ⟨⟨0, 3, 0, 0, 0, 2⟩, ⟨0, 3, 2, 0, 0, 1⟩⟩, ⟨⟨0, 3, 0, 0, 0, 3⟩, ⟨0, 3, 1, 0, 0, 5⟩⟩⟩, ⟨⟨⟨0, 0, 7, 0, 0, 6⟩, ⟨0, 3, 1, 0, 0, 7⟩⟩, ⟨⟨0, 0, 6, 0, 0, 0⟩, ⟨0, 3, 1, 0, 0, 8⟩⟩, ⟨⟨0, 0, 6, 0, 0, 9⟩, ⟨0, 3, 2, 0, 0, 8⟩⟩⟩, ⟨⟨⟨0, 0, 7, 0, 1, 0⟩, ⟨0, 3, 2, 0, 1, 1⟩⟩, ⟨⟨0, 0, 6, 0, 1, 2⟩, ⟨0, 3, 1, 0, 1, 3⟩⟩, ⟨⟨0, 0, 6, 0, 0, 2⟩, ⟨0, 3, 1, 0, 1, 1⟩⟩⟩, ⟨⟨⟨0, 0, 7, 0, 1, 4⟩, ⟨0, 3, 1, 0, 0, 4⟩⟩, ⟨⟨0, 0, 6, 0, 0, 3⟩, ⟨0, 3, 2, 0, 0, 4⟩⟩, ⟨⟨0, 0, 6, 0, 1, 5⟩, ⟨0, 3, 1, 0, 1, 6⟩⟩⟩⟩
private def lw53_1_1 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 3, 3, 0, 0, 0⟩, ⟨0, 0, 2, 0, 0, 1⟩⟩, ⟨⟨0, 3, 3, 0, 0, 2⟩, ⟨0, 0, 2, 0, 0, 1⟩⟩, ⟨⟨0, 3, 3, 0, 0, 3⟩, ⟨0, 0, 2, 0, 0, 4⟩⟩⟩, ⟨⟨⟨0, 3, 4, 0, 0, 0⟩, ⟨0, 3, 5, 0, 0, 1⟩⟩, ⟨⟨0, 3, 4, 0, 0, 2⟩, ⟨0, 3, 6, 0, 0, 1⟩⟩, ⟨⟨0, 3, 4, 0, 0, 3⟩, ⟨0, 3, 5, 0, 0, 5⟩⟩⟩, ⟨⟨⟨0, 1, 0, 0, 0, 6⟩, ⟨0, 3, 5, 0, 0, 7⟩⟩, ⟨⟨0, 3, 7, 0, 0, 0⟩, ⟨0, 3, 5, 0, 0, 8⟩⟩, ⟨⟨0, 3, 7, 0, 0, 9⟩, ⟨0, 3, 6, 0, 0, 8⟩⟩⟩, ⟨⟨⟨0, 1, 0, 0, 1, 0⟩, ⟨0, 3, 6, 0, 1, 1⟩⟩, ⟨⟨0, 3, 7, 0, 1, 2⟩, ⟨0, 3, 5, 0, 1, 3⟩⟩, ⟨⟨0, 3, 7, 0, 0, 2⟩, ⟨0, 3, 5, 0, 1, 1⟩⟩⟩, ⟨⟨⟨0, 1, 0, 0, 1, 4⟩, ⟨0, 3, 5, 0, 0, 4⟩⟩, ⟨⟨0, 3, 7, 0, 0, 3⟩, ⟨0, 3, 6, 0, 0, 4⟩⟩, ⟨⟨0, 3, 7, 0, 1, 5⟩, ⟨0, 3, 5, 0, 1, 6⟩⟩⟩⟩
private def lw53_1_2 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 1, 0, 0, 2, 0⟩, ⟨0, 0, 8, 0, 5, 7⟩⟩, ⟨⟨0, 1, 0, 0, 2, 1⟩, ⟨0, 0, 9, 0, 5, 7⟩⟩, ⟨⟨0, 1, 0, 0, 2, 2⟩, ⟨0, 0, 8, 0, 5, 8⟩⟩⟩, ⟨⟨⟨0, 3, 4, 0, 5, 9⟩, ⟨0, 3, 1, 0, 6, 0⟩⟩, ⟨⟨0, 3, 4, 0, 6, 1⟩, ⟨0, 3, 2, 0, 6, 0⟩⟩, ⟨⟨0, 3, 4, 0, 6, 2⟩, ⟨0, 3, 1, 0, 6, 3⟩⟩⟩, ⟨⟨⟨0, 3, 3, 0, 2, 6⟩, ⟨0, 3, 1, 0, 6, 4⟩⟩, ⟨⟨0, 3, 7, 0, 6, 5⟩, ⟨0, 3, 1, 0, 6, 6⟩⟩, ⟨⟨0, 3, 7, 0, 6, 1⟩, ⟨0, 3, 2, 0, 6, 6⟩⟩⟩, ⟨⟨⟨0, 3, 3, 0, 2, 8⟩, ⟨0, 3, 2, 0, 6, 7⟩⟩, ⟨⟨0, 3, 7, 0, 6, 2⟩, ⟨0, 3, 1, 0, 6, 8⟩⟩, ⟨⟨0, 3, 7, 0, 6, 9⟩, ⟨0, 3, 1, 0, 6, 7⟩⟩⟩, ⟨⟨⟨0, 3, 3, 0, 2, 9⟩, ⟨0, 3, 1, 0, 7, 0⟩⟩, ⟨⟨0, 3, 7, 0, 7, 1⟩, ⟨0, 3, 2, 0, 7, 0⟩⟩, ⟨⟨0, 3, 7, 0, 5, 9⟩, ⟨0, 3, 1, 0, 7, 2⟩⟩⟩⟩
private def lw53_1_3 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 0, 7, 0, 2, 0⟩, ⟨0, 1, 1, 0, 7, 3⟩⟩, ⟨⟨0, 0, 7, 0, 2, 1⟩, ⟨0, 1, 2, 0, 7, 3⟩⟩, ⟨⟨0, 0, 7, 0, 2, 2⟩, ⟨0, 1, 1, 0, 7, 4⟩⟩⟩, ⟨⟨⟨0, 3, 0, 0, 7, 5⟩, ⟨0, 3, 8, 0, 0, 1⟩⟩, ⟨⟨0, 3, 0, 0, 7, 6⟩, ⟨0, 3, 9, 0, 0, 1⟩⟩, ⟨⟨0, 3, 0, 0, 7, 7⟩, ⟨0, 3, 8, 0, 0, 5⟩⟩⟩, ⟨⟨⟨0, 0, 7, 0, 2, 6⟩, ⟨0, 1, 1, 0, 2, 7⟩⟩, ⟨⟨0, 0, 6, 0, 7, 5⟩, ⟨0, 4, 0, 0, 0, 1⟩⟩, ⟨⟨0, 0, 6, 0, 7, 8⟩, ⟨0, 4, 1, 0, 0, 1⟩⟩⟩, ⟨⟨⟨0, 0, 7, 0, 2, 8⟩, ⟨0, 1, 2, 0, 2, 7⟩⟩, ⟨⟨0, 0, 6, 0, 7, 9⟩, ⟨0, 4, 1, 0, 8, 0⟩⟩, ⟨⟨0, 0, 6, 0, 7, 6⟩, ⟨0, 4, 1, 0, 8, 1⟩⟩⟩, ⟨⟨⟨0, 0, 7, 0, 2, 9⟩, ⟨0, 1, 1, 0, 3, 0⟩⟩, ⟨⟨0, 0, 6, 0, 7, 7⟩, ⟨0, 4, 1, 0, 0, 5⟩⟩, ⟨⟨0, 0, 6, 0, 8, 2⟩, ⟨0, 4, 0, 0, 0, 5⟩⟩⟩⟩
private def lw53_1_4 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 0, 3, 0, 3, 1⟩, ⟨0, 1, 1, 0, 8, 3⟩⟩, ⟨⟨0, 1, 3, 0, 8, 4⟩, ⟨0, 1, 1, 0, 8, 5⟩⟩, ⟨⟨0, 1, 3, 0, 2, 0⟩, ⟨0, 1, 2, 0, 8, 5⟩⟩⟩, ⟨⟨⟨0, 3, 0, 0, 3, 1⟩, ⟨0, 3, 8, 0, 0, 7⟩⟩, ⟨⟨0, 4, 2, 0, 0, 0⟩, ⟨0, 3, 8, 0, 0, 8⟩⟩, ⟨⟨0, 4, 2, 0, 0, 9⟩, ⟨0, 3, 9, 0, 0, 8⟩⟩⟩, ⟨⟨⟨0, 2, 3, 0, 2, 6⟩, ⟨0, 1, 1, 0, 3, 4⟩⟩, ⟨⟨0, 4, 3, 0, 0, 0⟩, ⟨0, 4, 1, 0, 0, 7⟩⟩, ⟨⟨0, 4, 3, 0, 0, 9⟩, ⟨0, 4, 0, 0, 0, 7⟩⟩⟩, ⟨⟨⟨0, 2, 9, 0, 2, 9⟩, ⟨0, 1, 1, 0, 3, 6⟩⟩, ⟨⟨0, 4, 2, 0, 2, 9⟩, ⟨0, 4, 1, 0, 0, 8⟩⟩, ⟨⟨0, 1, 3, 0, 0, 6⟩, ⟨0, 4, 0, 0, 0, 8⟩⟩⟩, ⟨⟨⟨0, 2, 9, 0, 3, 7⟩, ⟨0, 1, 2, 0, 3, 6⟩⟩, ⟨⟨0, 4, 2, 0, 3, 7⟩, ⟨0, 4, 1, 0, 8, 6⟩⟩, ⟨⟨0, 1, 3, 0, 3, 8⟩, ⟨0, 4, 1, 0, 8, 7⟩⟩⟩⟩
private def lw53_1_5 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 0, 3, 0, 3, 9⟩, ⟨0, 1, 2, 0, 8, 8⟩⟩, ⟨⟨0, 1, 3, 0, 2, 1⟩, ⟨0, 1, 1, 0, 8, 9⟩⟩, ⟨⟨0, 1, 3, 0, 9, 0⟩, ⟨0, 1, 1, 0, 8, 8⟩⟩⟩, ⟨⟨⟨0, 3, 0, 0, 3, 9⟩, ⟨0, 3, 9, 0, 1, 1⟩⟩, ⟨⟨0, 4, 2, 0, 1, 2⟩, ⟨0, 3, 8, 0, 1, 3⟩⟩, ⟨⟨0, 4, 2, 0, 0, 2⟩, ⟨0, 3, 8, 0, 1, 1⟩⟩⟩, ⟨⟨⟨0, 2, 3, 0, 2, 8⟩, ⟨0, 1, 2, 0, 4, 2⟩⟩, ⟨⟨0, 4, 3, 0, 1, 2⟩, ⟨0, 4, 1, 0, 9, 1⟩⟩, ⟨⟨0, 4, 3, 0, 0, 2⟩, ⟨0, 4, 1, 0, 9, 2⟩⟩⟩, ⟨⟨⟨0, 2, 9, 0, 4, 4⟩, ⟨0, 1, 1, 0, 4, 5⟩⟩, ⟨⟨0, 4, 2, 0, 4, 4⟩, ⟨0, 4, 0, 0, 1, 3⟩⟩, ⟨⟨0, 1, 3, 0, 4, 6⟩, ⟨0, 4, 1, 0, 1, 3⟩⟩⟩, ⟨⟨⟨0, 2, 9, 0, 2, 6⟩, ⟨0, 1, 1, 0, 4, 2⟩⟩, ⟨⟨0, 4, 2, 0, 2, 6⟩, ⟨0, 4, 0, 0, 1, 1⟩⟩, ⟨⟨0, 1, 3, 0, 1, 0⟩, ⟨0, 4, 1, 0, 1, 1⟩⟩⟩⟩
private def lw53_1_6 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 0, 3, 0, 4, 7⟩, ⟨0, 1, 1, 0, 9, 3⟩⟩, ⟨⟨0, 1, 3, 0, 9, 4⟩, ⟨0, 1, 2, 0, 9, 3⟩⟩, ⟨⟨0, 1, 3, 0, 2, 2⟩, ⟨0, 1, 1, 0, 9, 5⟩⟩⟩, ⟨⟨⟨0, 3, 0, 0, 4, 7⟩, ⟨0, 3, 8, 0, 0, 4⟩⟩, ⟨⟨0, 4, 2, 0, 0, 3⟩, ⟨0, 3, 9, 0, 0, 4⟩⟩, ⟨⟨0, 4, 2, 0, 1, 5⟩, ⟨0, 3, 8, 0, 1, 6⟩⟩⟩, ⟨⟨⟨0, 2, 3, 0, 2, 9⟩, ⟨0, 1, 1, 0, 4, 9⟩⟩, ⟨⟨0, 4, 3, 0, 0, 3⟩, ⟨0, 4, 0, 0, 0, 4⟩⟩, ⟨⟨0, 4, 3, 0, 1, 5⟩, ⟨0, 4, 1, 0, 0, 4⟩⟩⟩, ⟨⟨⟨0, 2, 9, 0, 2, 8⟩, ⟨0, 1, 2, 0, 4, 9⟩⟩, ⟨⟨0, 4, 2, 0, 2, 8⟩, ⟨0, 4, 1, 0, 9, 6⟩⟩, ⟨⟨0, 1, 3, 0, 1, 4⟩, ⟨0, 4, 1, 0, 9, 7⟩⟩⟩, ⟨⟨⟨0, 2, 9, 0, 5, 1⟩, ⟨0, 1, 1, 0, 5, 2⟩⟩, ⟨⟨0, 4, 2, 0, 5, 1⟩, ⟨0, 4, 1, 0, 1, 6⟩⟩, ⟨⟨0, 1, 3, 0, 5, 3⟩, ⟨0, 4, 0, 0, 1, 6⟩⟩⟩⟩
private def lwBlk_1 : Seven (Five (Three LeafWit)) := ⟨lw53_1_0, lw53_1_1, lw53_1_2, lw53_1_3, lw53_1_4, lw53_1_5, lw53_1_6⟩
private def lw53_2_0 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 1, 4, 0, 5, 4⟩, ⟨0, 1, 5, 0, 2, 7⟩⟩, ⟨⟨0, 1, 4, 0, 5, 5⟩, ⟨0, 1, 6, 0, 2, 7⟩⟩, ⟨⟨0, 1, 4, 0, 5, 6⟩, ⟨0, 1, 5, 0, 4, 9⟩⟩⟩, ⟨⟨⟨0, 2, 3, 0, 9, 8⟩, ⟨0, 1, 8, 0, 9, 9⟩⟩, ⟨⟨0, 2, 3, 1, 0, 0⟩, ⟨0, 1, 9, 0, 9, 9⟩⟩, ⟨⟨0, 2, 3, 1, 0, 1⟩, ⟨0, 1, 8, 1, 0, 2⟩⟩⟩, ⟨⟨⟨0, 1, 4, 0, 0, 6⟩, ⟨0, 1, 8, 1, 0, 3⟩⟩, ⟨⟨0, 2, 4, 0, 9, 8⟩, ⟨0, 1, 8, 1, 0, 4⟩⟩, ⟨⟨0, 2, 4, 1, 0, 5⟩, ⟨0, 1, 9, 1, 0, 4⟩⟩⟩, ⟨⟨⟨0, 1, 4, 0, 1, 0⟩, ⟨0, 1, 9, 1, 0, 6⟩⟩, ⟨⟨0, 2, 4, 1, 0, 7⟩, ⟨0, 1, 8, 1, 0, 8⟩⟩, ⟨⟨0, 2, 4, 1, 0, 0⟩, ⟨0, 1, 8, 1, 0, 6⟩⟩⟩, ⟨⟨⟨0, 1, 4, 0, 1, 4⟩, ⟨0, 1, 8, 1, 0, 9⟩⟩, ⟨⟨0, 2, 4, 1, 0, 1⟩, ⟨0, 1, 9, 1, 0, 9⟩⟩, ⟨⟨0, 2, 4, 1, 1, 0⟩, ⟨0, 1, 8, 1, 1, 1⟩⟩⟩⟩
private def lw53_2_1 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 4, 4, 0, 0, 0⟩, ⟨0, 4, 5, 0, 0, 1⟩⟩, ⟨⟨0, 4, 4, 0, 0, 2⟩, ⟨0, 4, 5, 0, 0, 1⟩⟩, ⟨⟨0, 4, 4, 0, 0, 3⟩, ⟨0, 4, 5, 0, 0, 4⟩⟩⟩, ⟨⟨⟨0, 4, 4, 0, 7, 5⟩, ⟨0, 4, 6, 0, 0, 1⟩⟩, ⟨⟨0, 4, 4, 0, 7, 6⟩, ⟨0, 4, 7, 0, 0, 1⟩⟩, ⟨⟨0, 4, 4, 0, 7, 7⟩, ⟨0, 4, 6, 0, 0, 5⟩⟩⟩, ⟨⟨⟨0, 1, 7, 0, 0, 6⟩, ⟨0, 4, 6, 0, 0, 7⟩⟩, ⟨⟨0, 4, 8, 0, 0, 0⟩, ⟨0, 4, 6, 0, 0, 8⟩⟩, ⟨⟨0, 4, 8, 0, 0, 9⟩, ⟨0, 4, 7, 0, 0, 8⟩⟩⟩, ⟨⟨⟨0, 1, 7, 0, 1, 0⟩, ⟨0, 4, 7, 0, 1, 1⟩⟩, ⟨⟨0, 4, 8, 0, 1, 2⟩, ⟨0, 4, 6, 0, 1, 3⟩⟩, ⟨⟨0, 4, 8, 0, 0, 2⟩, ⟨0, 4, 6, 0, 1, 1⟩⟩⟩, ⟨⟨⟨0, 1, 7, 0, 1, 4⟩, ⟨0, 4, 6, 0, 0, 4⟩⟩, ⟨⟨0, 4, 8, 0, 0, 3⟩, ⟨0, 4, 7, 0, 0, 4⟩⟩, ⟨⟨0, 4, 8, 0, 1, 5⟩, ⟨0, 4, 6, 0, 1, 6⟩⟩⟩⟩
private def lw53_2_2 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 3, 4, 0, 2, 0⟩, ⟨0, 0, 2, 0, 6, 0⟩⟩, ⟨⟨0, 3, 4, 0, 2, 1⟩, ⟨0, 0, 2, 0, 6, 0⟩⟩, ⟨⟨0, 3, 4, 0, 2, 2⟩, ⟨0, 0, 2, 0, 7, 0⟩⟩⟩, ⟨⟨⟨0, 4, 4, 0, 0, 6⟩, ⟨0, 3, 5, 0, 6, 0⟩⟩, ⟨⟨0, 4, 4, 0, 1, 0⟩, ⟨0, 3, 6, 0, 6, 0⟩⟩, ⟨⟨0, 4, 4, 0, 1, 4⟩, ⟨0, 3, 5, 0, 6, 3⟩⟩⟩, ⟨⟨⟨0, 3, 4, 0, 2, 6⟩, ⟨0, 3, 5, 0, 6, 4⟩⟩, ⟨⟨0, 4, 9, 0, 0, 0⟩, ⟨0, 3, 5, 0, 6, 6⟩⟩, ⟨⟨0, 4, 9, 0, 0, 9⟩, ⟨0, 3, 6, 0, 6, 6⟩⟩⟩, ⟨⟨⟨0, 3, 4, 0, 2, 8⟩, ⟨0, 3, 6, 0, 6, 7⟩⟩, ⟨⟨0, 4, 9, 0, 1, 2⟩, ⟨0, 3, 5, 0, 6, 8⟩⟩, ⟨⟨0, 4, 9, 0, 0, 2⟩, ⟨0, 3, 5, 0, 6, 7⟩⟩⟩, ⟨⟨⟨0, 3, 4, 0, 2, 9⟩, ⟨0, 3, 5, 0, 7, 0⟩⟩, ⟨⟨0, 4, 9, 0, 0, 3⟩, ⟨0, 3, 6, 0, 7, 0⟩⟩, ⟨⟨0, 4, 9, 0, 1, 5⟩, ⟨0, 3, 5, 0, 7, 2⟩⟩⟩⟩
private def lw53_2_3 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 3, 3, 0, 7, 5⟩, ⟨0, 3, 5, 1, 1, 2⟩⟩, ⟨⟨0, 3, 3, 0, 7, 6⟩, ⟨0, 3, 6, 1, 1, 3⟩⟩, ⟨⟨0, 3, 3, 0, 7, 7⟩, ⟨0, 3, 5, 1, 1, 4⟩⟩⟩, ⟨⟨⟨0, 3, 4, 0, 7, 5⟩, ⟨0, 4, 6, 0, 6, 0⟩⟩, ⟨⟨0, 3, 4, 0, 7, 6⟩, ⟨0, 4, 7, 0, 6, 0⟩⟩, ⟨⟨0, 3, 4, 0, 7, 7⟩, ⟨0, 4, 6, 0, 6, 3⟩⟩⟩, ⟨⟨⟨0, 1, 0, 0, 2, 6⟩, ⟨0, 1, 8, 0, 2, 7⟩⟩, ⟨⟨0, 3, 7, 0, 7, 5⟩, ⟨0, 5, 0, 0, 0, 1⟩⟩, ⟨⟨0, 3, 7, 0, 7, 8⟩, ⟨0, 5, 1, 0, 0, 1⟩⟩⟩, ⟨⟨⟨0, 1, 0, 0, 2, 8⟩, ⟨0, 1, 9, 0, 2, 7⟩⟩, ⟨⟨0, 3, 7, 0, 7, 9⟩, ⟨0, 5, 2, 0, 0, 1⟩⟩, ⟨⟨0, 3, 7, 0, 7, 6⟩, ⟨0, 5, 2, 0, 0, 5⟩⟩⟩, ⟨⟨⟨0, 1, 0, 0, 2, 9⟩, ⟨0, 1, 8, 0, 3, 0⟩⟩, ⟨⟨0, 3, 7, 0, 7, 7⟩, ⟨0, 5, 1, 0, 0, 5⟩⟩, ⟨⟨0, 3, 7, 0, 8, 2⟩, ⟨0, 5, 0, 0, 0, 5⟩⟩⟩⟩
private def lw53_2_4 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 1, 0, 1, 1, 5⟩, ⟨0, 3, 5, 1, 1, 6⟩⟩, ⟨⟨0, 3, 7, 0, 8, 4⟩, ⟨0, 3, 5, 1, 1, 7⟩⟩, ⟨⟨0, 3, 7, 0, 2, 0⟩, ⟨0, 3, 6, 1, 1, 4⟩⟩⟩, ⟨⟨⟨0, 3, 4, 1, 1, 5⟩, ⟨0, 4, 6, 0, 6, 4⟩⟩, ⟨⟨0, 4, 9, 1, 1, 8⟩, ⟨0, 4, 6, 0, 6, 6⟩⟩, ⟨⟨0, 4, 9, 1, 1, 9⟩, ⟨0, 4, 7, 0, 6, 6⟩⟩⟩, ⟨⟨⟨0, 1, 7, 0, 2, 6⟩, ⟨0, 1, 8, 0, 3, 4⟩⟩, ⟨⟨0, 4, 8, 0, 7, 5⟩, ⟨0, 5, 1, 0, 0, 7⟩⟩, ⟨⟨0, 4, 8, 0, 7, 8⟩, ⟨0, 5, 0, 0, 0, 7⟩⟩⟩, ⟨⟨⟨0, 2, 0, 1, 2, 0⟩, ⟨0, 1, 8, 0, 3, 6⟩⟩, ⟨⟨0, 4, 3, 0, 2, 9⟩, ⟨0, 5, 1, 0, 0, 8⟩⟩, ⟨⟨0, 2, 0, 0, 0, 6⟩, ⟨0, 5, 0, 0, 0, 8⟩⟩⟩, ⟨⟨⟨0, 2, 0, 0, 5, 6⟩, ⟨0, 1, 9, 0, 3, 6⟩⟩, ⟨⟨0, 4, 3, 0, 3, 7⟩, ⟨0, 5, 2, 0, 0, 7⟩⟩, ⟨⟨0, 2, 0, 0, 3, 8⟩, ⟨0, 5, 2, 0, 0, 8⟩⟩⟩⟩
private def lw53_2_5 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 1, 0, 1, 2, 1⟩, ⟨0, 3, 6, 1, 1, 6⟩⟩, ⟨⟨0, 3, 7, 0, 2, 1⟩, ⟨0, 3, 5, 1, 2, 2⟩⟩, ⟨⟨0, 3, 7, 0, 9, 0⟩, ⟨0, 3, 5, 1, 2, 3⟩⟩⟩, ⟨⟨⟨0, 3, 4, 1, 2, 1⟩, ⟨0, 4, 7, 0, 6, 7⟩⟩, ⟨⟨0, 4, 9, 1, 2, 4⟩, ⟨0, 4, 6, 0, 6, 8⟩⟩, ⟨⟨0, 4, 9, 1, 2, 5⟩, ⟨0, 4, 6, 0, 6, 7⟩⟩⟩, ⟨⟨⟨0, 1, 7, 0, 2, 8⟩, ⟨0, 1, 9, 0, 4, 2⟩⟩, ⟨⟨0, 4, 8, 0, 7, 9⟩, ⟨0, 5, 2, 0, 1, 3⟩⟩, ⟨⟨0, 4, 8, 0, 7, 6⟩, ⟨0, 5, 2, 0, 1, 1⟩⟩⟩, ⟨⟨⟨0, 2, 0, 0, 5, 4⟩, ⟨0, 1, 8, 0, 4, 5⟩⟩, ⟨⟨0, 4, 3, 0, 4, 4⟩, ⟨0, 5, 0, 0, 1, 3⟩⟩, ⟨⟨0, 2, 0, 0, 4, 6⟩, ⟨0, 5, 1, 0, 1, 3⟩⟩⟩, ⟨⟨⟨0, 2, 0, 1, 2, 6⟩, ⟨0, 1, 8, 0, 4, 2⟩⟩, ⟨⟨0, 4, 3, 0, 2, 6⟩, ⟨0, 5, 0, 0, 1, 1⟩⟩, ⟨⟨0, 2, 0, 0, 1, 0⟩, ⟨0, 5, 1, 0, 1, 1⟩⟩⟩⟩
private def lw53_2_6 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 1, 0, 1, 2, 7⟩, ⟨0, 3, 5, 1, 2, 8⟩⟩, ⟨⟨0, 3, 7, 0, 9, 4⟩, ⟨0, 3, 6, 1, 2, 2⟩⟩, ⟨⟨0, 3, 7, 0, 2, 2⟩, ⟨0, 3, 5, 1, 1, 3⟩⟩⟩, ⟨⟨⟨0, 3, 4, 1, 2, 7⟩, ⟨0, 4, 6, 0, 7, 0⟩⟩, ⟨⟨0, 4, 9, 1, 2, 9⟩, ⟨0, 4, 7, 0, 7, 0⟩⟩, ⟨⟨0, 4, 9, 1, 3, 0⟩, ⟨0, 4, 6, 0, 7, 2⟩⟩⟩, ⟨⟨⟨0, 1, 7, 0, 2, 9⟩, ⟨0, 1, 8, 0, 4, 9⟩⟩, ⟨⟨0, 4, 8, 0, 7, 7⟩, ⟨0, 5, 0, 0, 0, 4⟩⟩, ⟨⟨0, 4, 8, 0, 8, 2⟩, ⟨0, 5, 1, 0, 0, 4⟩⟩⟩, ⟨⟨⟨0, 2, 0, 1, 3, 1⟩, ⟨0, 1, 9, 0, 4, 9⟩⟩, ⟨⟨0, 4, 3, 0, 2, 8⟩, ⟨0, 5, 2, 0, 0, 4⟩⟩, ⟨⟨0, 2, 0, 0, 1, 4⟩, ⟨0, 5, 2, 0, 1, 6⟩⟩⟩, ⟨⟨⟨0, 2, 0, 0, 5, 5⟩, ⟨0, 1, 8, 0, 5, 2⟩⟩, ⟨⟨0, 4, 3, 0, 5, 1⟩, ⟨0, 5, 1, 0, 1, 6⟩⟩, ⟨⟨0, 2, 0, 0, 5, 3⟩, ⟨0, 5, 0, 0, 1, 6⟩⟩⟩⟩
private def lwBlk_2 : Seven (Five (Three LeafWit)) := ⟨lw53_2_0, lw53_2_1, lw53_2_2, lw53_2_3, lw53_2_4, lw53_2_5, lw53_2_6⟩
private def lw53_3_0 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 1, 0, 0, 9, 8⟩, ⟨0, 0, 8, 0, 9, 9⟩⟩, ⟨⟨0, 1, 0, 1, 0, 0⟩, ⟨0, 0, 9, 0, 9, 9⟩⟩, ⟨⟨0, 1, 0, 1, 0, 1⟩, ⟨0, 0, 8, 1, 0, 9⟩⟩⟩, ⟨⟨⟨0, 1, 7, 0, 9, 8⟩, ⟨0, 1, 1, 0, 8, 7⟩⟩, ⟨⟨0, 1, 7, 1, 0, 0⟩, ⟨0, 1, 2, 0, 9, 1⟩⟩, ⟨⟨0, 1, 7, 1, 0, 1⟩, ⟨0, 1, 1, 0, 9, 7⟩⟩⟩, ⟨⟨⟨0, 1, 4, 0, 5, 9⟩, ⟨0, 1, 1, 0, 8, 1⟩⟩, ⟨⟨0, 2, 0, 0, 6, 5⟩, ⟨0, 1, 1, 0, 9, 2⟩⟩, ⟨⟨0, 2, 0, 0, 6, 1⟩, ⟨0, 1, 2, 0, 9, 7⟩⟩⟩, ⟨⟨⟨0, 1, 4, 0, 6, 1⟩, ⟨0, 1, 2, 0, 8, 1⟩⟩, ⟨⟨0, 2, 0, 0, 6, 2⟩, ⟨0, 1, 1, 0, 8, 6⟩⟩, ⟨⟨0, 2, 0, 0, 6, 9⟩, ⟨0, 1, 1, 0, 9, 6⟩⟩⟩, ⟨⟨⟨0, 1, 4, 0, 6, 2⟩, ⟨0, 1, 1, 0, 8, 0⟩⟩, ⟨⟨0, 2, 0, 0, 7, 1⟩, ⟨0, 1, 2, 0, 8, 6⟩⟩, ⟨⟨0, 2, 0, 0, 5, 9⟩, ⟨0, 1, 1, 0, 9, 1⟩⟩⟩⟩
private def lw53_3_1 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 3, 4, 0, 9, 8⟩, ⟨0, 0, 2, 0, 2, 7⟩⟩, ⟨⟨0, 3, 4, 1, 0, 0⟩, ⟨0, 0, 2, 0, 2, 7⟩⟩, ⟨⟨0, 3, 4, 1, 0, 1⟩, ⟨0, 0, 2, 0, 4, 9⟩⟩⟩, ⟨⟨⟨0, 3, 4, 1, 3, 2⟩, ⟨0, 3, 8, 0, 3, 4⟩⟩, ⟨⟨0, 3, 4, 1, 3, 3⟩, ⟨0, 3, 9, 0, 4, 2⟩⟩, ⟨⟨0, 3, 4, 1, 3, 4⟩, ⟨0, 3, 8, 0, 4, 9⟩⟩⟩, ⟨⟨⟨0, 2, 3, 0, 0, 6⟩, ⟨0, 3, 8, 0, 2, 7⟩⟩, ⟨⟨0, 4, 3, 0, 9, 8⟩, ⟨0, 3, 8, 0, 4, 5⟩⟩, ⟨⟨0, 4, 3, 1, 0, 5⟩, ⟨0, 3, 9, 0, 4, 9⟩⟩⟩, ⟨⟨⟨0, 2, 3, 0, 1, 0⟩, ⟨0, 3, 9, 0, 2, 7⟩⟩, ⟨⟨0, 4, 3, 1, 0, 7⟩, ⟨0, 3, 8, 0, 3, 6⟩⟩, ⟨⟨0, 4, 3, 1, 0, 0⟩, ⟨0, 3, 8, 0, 5, 2⟩⟩⟩, ⟨⟨⟨0, 2, 3, 0, 1, 4⟩, ⟨0, 3, 8, 0, 3, 0⟩⟩, ⟨⟨0, 4, 3, 1, 0, 1⟩, ⟨0, 3, 9, 0, 3, 6⟩⟩, ⟨⟨0, 4, 3, 1, 1, 0⟩, ⟨0, 3, 8, 0, 4, 2⟩⟩⟩⟩
private def lw53_3_2 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 1, 7, 1, 2, 9⟩, ⟨0, 0, 8, 1, 1, 6⟩⟩, ⟨⟨0, 1, 7, 1, 1, 8⟩, ⟨0, 0, 9, 1, 1, 6⟩⟩, ⟨⟨0, 1, 7, 1, 2, 5⟩, ⟨0, 0, 8, 1, 1, 4⟩⟩⟩, ⟨⟨⟨0, 4, 4, 0, 2, 6⟩, ⟨0, 3, 1, 0, 2, 7⟩⟩, ⟨⟨0, 4, 4, 0, 2, 8⟩, ⟨0, 3, 2, 0, 2, 7⟩⟩, ⟨⟨0, 4, 4, 0, 2, 9⟩, ⟨0, 3, 1, 0, 3, 0⟩⟩⟩, ⟨⟨⟨0, 4, 4, 0, 3, 1⟩, ⟨0, 3, 1, 0, 3, 4⟩⟩, ⟨⟨0, 4, 8, 0, 2, 9⟩, ⟨0, 3, 1, 0, 3, 6⟩⟩, ⟨⟨0, 4, 8, 0, 3, 7⟩, ⟨0, 3, 2, 0, 3, 6⟩⟩⟩, ⟨⟨⟨0, 4, 4, 0, 3, 9⟩, ⟨0, 3, 2, 0, 4, 2⟩⟩, ⟨⟨0, 4, 8, 0, 4, 4⟩, ⟨0, 3, 1, 0, 4, 5⟩⟩, ⟨⟨0, 4, 8, 0, 2, 6⟩, ⟨0, 3, 1, 0, 4, 2⟩⟩⟩, ⟨⟨⟨0, 4, 4, 0, 4, 7⟩, ⟨0, 3, 1, 0, 4, 9⟩⟩, ⟨⟨0, 4, 8, 0, 2, 8⟩, ⟨0, 3, 2, 0, 4, 9⟩⟩, ⟨⟨0, 4, 8, 0, 5, 1⟩, ⟨0, 3, 1, 0, 5, 2⟩⟩⟩⟩
private def lw53_3_3 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 1, 0, 1, 3, 2⟩, ⟨0, 1, 1, 1, 1, 2⟩⟩, ⟨⟨0, 1, 0, 1, 3, 3⟩, ⟨0, 1, 2, 1, 1, 3⟩⟩, ⟨⟨0, 1, 0, 1, 3, 4⟩, ⟨0, 1, 1, 1, 1, 4⟩⟩⟩, ⟨⟨⟨0, 3, 4, 0, 1, 7⟩, ⟨0, 3, 5, 0, 2, 7⟩⟩, ⟨⟨0, 3, 4, 0, 1, 8⟩, ⟨0, 3, 6, 0, 2, 7⟩⟩, ⟨⟨0, 3, 4, 0, 1, 9⟩, ⟨0, 3, 5, 0, 3, 0⟩⟩⟩, ⟨⟨⟨0, 3, 3, 0, 3, 1⟩, ⟨0, 3, 1, 0, 5, 7⟩⟩, ⟨⟨0, 3, 7, 0, 3, 5⟩, ⟨0, 4, 0, 0, 4, 9⟩⟩, ⟨⟨0, 3, 7, 0, 1, 8⟩, ⟨0, 4, 1, 1, 3, 5⟩⟩⟩, ⟨⟨⟨0, 3, 3, 0, 3, 9⟩, ⟨0, 3, 2, 0, 5, 7⟩⟩, ⟨⟨0, 3, 7, 0, 1, 9⟩, ⟨0, 4, 1, 0, 4, 9⟩⟩, ⟨⟨0, 3, 7, 0, 4, 3⟩, ⟨0, 4, 1, 0, 3, 4⟩⟩⟩, ⟨⟨⟨0, 3, 3, 0, 4, 7⟩, ⟨0, 3, 1, 1, 3, 6⟩⟩, ⟨⟨0, 3, 7, 0, 5, 0⟩, ⟨0, 4, 1, 1, 3, 7⟩⟩, ⟨⟨0, 3, 7, 0, 1, 7⟩, ⟨0, 4, 0, 0, 3, 4⟩⟩⟩⟩
private def lw53_3_4 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 1, 4, 1, 2, 9⟩, ⟨0, 1, 1, 1, 1, 6⟩⟩, ⟨⟨0, 2, 0, 1, 1, 8⟩, ⟨0, 1, 1, 1, 1, 7⟩⟩, ⟨⟨0, 2, 0, 1, 1, 9⟩, ⟨0, 1, 2, 1, 1, 4⟩⟩⟩, ⟨⟨⟨0, 4, 4, 1, 2, 9⟩, ⟨0, 3, 5, 0, 3, 4⟩⟩, ⟨⟨0, 4, 9, 0, 2, 9⟩, ⟨0, 3, 5, 0, 3, 6⟩⟩, ⟨⟨0, 4, 9, 0, 3, 7⟩, ⟨0, 3, 6, 0, 3, 6⟩⟩⟩, ⟨⟨⟨0, 3, 4, 0, 3, 1⟩, ⟨0, 3, 1, 1, 3, 8⟩⟩, ⟨⟨0, 4, 9, 0, 7, 5⟩, ⟨0, 4, 1, 1, 3, 9⟩⟩, ⟨⟨0, 4, 9, 0, 7, 8⟩, ⟨0, 4, 0, 0, 4, 5⟩⟩⟩, ⟨⟨⟨0, 3, 7, 0, 4, 7⟩, ⟨0, 3, 1, 1, 4, 0⟩⟩, ⟨⟨0, 4, 8, 0, 4, 7⟩, ⟨0, 4, 1, 1, 4, 1⟩⟩, ⟨⟨0, 2, 4, 0, 0, 6⟩, ⟨0, 4, 0, 0, 2, 7⟩⟩⟩, ⟨⟨⟨0, 3, 7, 1, 4, 2⟩, ⟨0, 3, 2, 1, 4, 0⟩⟩, ⟨⟨0, 4, 8, 1, 4, 2⟩, ⟨0, 4, 1, 0, 4, 5⟩⟩, ⟨⟨0, 2, 4, 0, 3, 8⟩, ⟨0, 4, 1, 0, 2, 7⟩⟩⟩⟩
private def lw53_3_5 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 1, 4, 1, 1, 8⟩, ⟨0, 1, 2, 1, 1, 6⟩⟩, ⟨⟨0, 2, 0, 1, 2, 4⟩, ⟨0, 1, 1, 1, 2, 2⟩⟩, ⟨⟨0, 2, 0, 1, 2, 5⟩, ⟨0, 1, 1, 1, 2, 3⟩⟩⟩, ⟨⟨⟨0, 4, 4, 1, 1, 8⟩, ⟨0, 3, 6, 0, 4, 2⟩⟩, ⟨⟨0, 4, 9, 0, 4, 4⟩, ⟨0, 3, 5, 0, 4, 5⟩⟩, ⟨⟨0, 4, 9, 0, 2, 6⟩, ⟨0, 3, 5, 0, 4, 2⟩⟩⟩, ⟨⟨⟨0, 3, 4, 0, 3, 9⟩, ⟨0, 3, 2, 1, 4, 3⟩⟩, ⟨⟨0, 4, 9, 0, 7, 9⟩, ⟨0, 4, 1, 0, 5, 2⟩⟩, ⟨⟨0, 4, 9, 0, 7, 6⟩, ⟨0, 4, 1, 0, 3, 6⟩⟩⟩, ⟨⟨⟨0, 3, 7, 1, 4, 4⟩, ⟨0, 3, 1, 1, 4, 5⟩⟩, ⟨⟨0, 4, 8, 1, 4, 4⟩, ⟨0, 4, 0, 0, 5, 2⟩⟩, ⟨⟨0, 2, 4, 0, 4, 6⟩, ⟨0, 4, 1, 1, 4, 6⟩⟩⟩, ⟨⟨⟨0, 3, 7, 0, 3, 1⟩, ⟨0, 3, 1, 1, 4, 3⟩⟩, ⟨⟨0, 4, 8, 0, 3, 1⟩, ⟨0, 4, 0, 0, 3, 6⟩⟩, ⟨⟨0, 2, 4, 0, 1, 0⟩, ⟨0, 4, 1, 1, 4, 7⟩⟩⟩⟩
private def lw53_3_6 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 1, 4, 1, 2, 5⟩, ⟨0, 1, 1, 1, 2, 8⟩⟩, ⟨⟨0, 2, 0, 1, 2, 9⟩, ⟨0, 1, 2, 1, 2, 2⟩⟩, ⟨⟨0, 2, 0, 1, 3, 0⟩, ⟨0, 1, 1, 1, 1, 3⟩⟩⟩, ⟨⟨⟨0, 4, 4, 1, 2, 5⟩, ⟨0, 3, 5, 0, 4, 9⟩⟩, ⟨⟨0, 4, 9, 0, 2, 8⟩, ⟨0, 3, 6, 0, 4, 9⟩⟩, ⟨⟨0, 4, 9, 0, 5, 1⟩, ⟨0, 3, 5, 0, 5, 2⟩⟩⟩, ⟨⟨⟨0, 3, 4, 0, 4, 7⟩, ⟨0, 3, 1, 0, 5, 8⟩⟩, ⟨⟨0, 4, 9, 0, 7, 7⟩, ⟨0, 4, 0, 0, 4, 2⟩⟩, ⟨⟨0, 4, 9, 0, 8, 2⟩, ⟨0, 4, 1, 1, 4, 8⟩⟩⟩, ⟨⟨⟨0, 3, 7, 0, 3, 9⟩, ⟨0, 3, 2, 0, 5, 8⟩⟩, ⟨⟨0, 4, 8, 0, 3, 9⟩, ⟨0, 4, 1, 0, 4, 2⟩⟩, ⟨⟨0, 2, 4, 0, 1, 4⟩, ⟨0, 4, 1, 0, 3, 0⟩⟩⟩, ⟨⟨⟨0, 3, 7, 1, 4, 9⟩, ⟨0, 3, 1, 1, 5, 0⟩⟩, ⟨⟨0, 4, 8, 1, 4, 9⟩, ⟨0, 4, 1, 1, 5, 1⟩⟩, ⟨⟨0, 2, 4, 0, 5, 3⟩, ⟨0, 4, 0, 0, 3, 0⟩⟩⟩⟩
private def lwBlk_3 : Seven (Five (Three LeafWit)) := ⟨lw53_3_0, lw53_3_1, lw53_3_2, lw53_3_3, lw53_3_4, lw53_3_5, lw53_3_6⟩
private def lw53_4_0 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 0, 3, 0, 9, 8⟩, ⟨0, 0, 1, 0, 6, 0⟩⟩, ⟨⟨0, 0, 3, 1, 0, 0⟩, ⟨0, 0, 2, 0, 6, 0⟩⟩, ⟨⟨0, 0, 3, 1, 0, 1⟩, ⟨0, 0, 1, 0, 7, 0⟩⟩⟩, ⟨⟨⟨0, 1, 0, 0, 5, 9⟩, ⟨0, 0, 4, 0, 6, 0⟩⟩, ⟨⟨0, 1, 0, 0, 6, 1⟩, ⟨0, 0, 5, 0, 6, 0⟩⟩, ⟨⟨0, 1, 0, 0, 6, 2⟩, ⟨0, 0, 4, 0, 6, 3⟩⟩⟩, ⟨⟨⟨0, 0, 7, 0, 5, 9⟩, ⟨0, 0, 4, 0, 6, 4⟩⟩, ⟨⟨0, 1, 3, 0, 6, 5⟩, ⟨0, 0, 4, 0, 6, 6⟩⟩, ⟨⟨0, 1, 3, 0, 6, 1⟩, ⟨0, 0, 5, 0, 6, 6⟩⟩⟩, ⟨⟨⟨0, 0, 7, 0, 6, 1⟩, ⟨0, 0, 5, 0, 6, 7⟩⟩, ⟨⟨0, 1, 3, 0, 6, 2⟩, ⟨0, 0, 4, 0, 6, 8⟩⟩, ⟨⟨0, 1, 3, 0, 6, 9⟩, ⟨0, 0, 4, 0, 6, 7⟩⟩⟩, ⟨⟨⟨0, 0, 7, 0, 6, 2⟩, ⟨0, 0, 4, 0, 7, 0⟩⟩, ⟨⟨0, 1, 3, 0, 7, 1⟩, ⟨0, 0, 5, 0, 7, 0⟩⟩, ⟨⟨0, 1, 3, 0, 5, 9⟩, ⟨0, 0, 4, 0, 7, 2⟩⟩⟩⟩
private def lw53_4_1 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 3, 0, 0, 9, 8⟩, ⟨0, 0, 8, 0, 6, 0⟩⟩, ⟨⟨0, 3, 0, 1, 0, 0⟩, ⟨0, 0, 9, 0, 6, 0⟩⟩, ⟨⟨0, 3, 0, 1, 0, 1⟩, ⟨0, 0, 8, 0, 7, 0⟩⟩⟩, ⟨⟨⟨0, 3, 3, 0, 0, 6⟩, ⟨0, 1, 1, 0, 6, 0⟩⟩, ⟨⟨0, 3, 3, 0, 1, 0⟩, ⟨0, 1, 2, 0, 6, 0⟩⟩, ⟨⟨0, 3, 3, 0, 1, 4⟩, ⟨0, 1, 1, 0, 6, 3⟩⟩⟩, ⟨⟨⟨0, 3, 0, 0, 2, 6⟩, ⟨0, 1, 1, 0, 6, 4⟩⟩, ⟨⟨0, 4, 2, 0, 1, 4⟩, ⟨0, 1, 1, 0, 6, 6⟩⟩, ⟨⟨0, 4, 2, 0, 4, 6⟩, ⟨0, 1, 2, 0, 6, 6⟩⟩⟩, ⟨⟨⟨0, 3, 0, 0, 2, 8⟩, ⟨0, 1, 2, 0, 6, 7⟩⟩, ⟨⟨0, 4, 2, 0, 5, 3⟩, ⟨0, 1, 1, 0, 6, 8⟩⟩, ⟨⟨0, 4, 2, 0, 0, 6⟩, ⟨0, 1, 1, 0, 6, 7⟩⟩⟩, ⟨⟨⟨0, 3, 0, 0, 2, 9⟩, ⟨0, 1, 1, 0, 7, 0⟩⟩, ⟨⟨0, 4, 2, 0, 1, 0⟩, ⟨0, 1, 2, 0, 7, 0⟩⟩, ⟨⟨0, 4, 2, 0, 3, 8⟩, ⟨0, 1, 1, 0, 7, 2⟩⟩⟩⟩
private def lw53_4_2 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 2, 3, 1, 2, 9⟩, ⟨0, 1, 5, 0, 6, 0⟩⟩, ⟨⟨0, 2, 3, 1, 1, 8⟩, ⟨0, 1, 6, 0, 6, 0⟩⟩, ⟨⟨0, 2, 3, 1, 2, 5⟩, ⟨0, 1, 5, 0, 7, 0⟩⟩⟩, ⟨⟨⟨0, 3, 4, 0, 0, 6⟩, ⟨0, 1, 8, 0, 6, 0⟩⟩, ⟨⟨0, 3, 4, 0, 1, 0⟩, ⟨0, 1, 9, 0, 6, 0⟩⟩, ⟨⟨0, 3, 4, 0, 1, 4⟩, ⟨0, 1, 8, 0, 6, 3⟩⟩⟩, ⟨⟨⟨0, 3, 4, 1, 5, 2⟩, ⟨0, 1, 8, 0, 6, 4⟩⟩, ⟨⟨0, 4, 3, 0, 1, 4⟩, ⟨0, 1, 8, 0, 6, 6⟩⟩, ⟨⟨0, 4, 3, 0, 4, 6⟩, ⟨0, 1, 9, 0, 6, 6⟩⟩⟩, ⟨⟨⟨0, 3, 4, 1, 5, 3⟩, ⟨0, 1, 9, 0, 6, 7⟩⟩, ⟨⟨0, 4, 3, 0, 5, 3⟩, ⟨0, 1, 8, 0, 6, 8⟩⟩, ⟨⟨0, 4, 3, 0, 0, 6⟩, ⟨0, 1, 8, 0, 6, 7⟩⟩⟩, ⟨⟨⟨0, 3, 4, 1, 5, 4⟩, ⟨0, 1, 8, 0, 7, 0⟩⟩, ⟨⟨0, 4, 3, 0, 1, 0⟩, ⟨0, 1, 9, 0, 7, 0⟩⟩, ⟨⟨0, 4, 3, 0, 3, 8⟩, ⟨0, 1, 8, 0, 7, 2⟩⟩⟩⟩
private def lw53_4_3 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 0, 7, 1, 3, 2⟩, ⟨0, 2, 1, 0, 6, 0⟩⟩, ⟨⟨0, 0, 7, 1, 3, 3⟩, ⟨0, 2, 2, 0, 6, 0⟩⟩, ⟨⟨0, 0, 7, 1, 3, 4⟩, ⟨0, 2, 1, 0, 6, 3⟩⟩⟩, ⟨⟨⟨0, 3, 0, 0, 0, 6⟩, ⟨0, 1, 1, 1, 5, 1⟩⟩, ⟨⟨0, 3, 0, 0, 1, 0⟩, ⟨0, 1, 2, 1, 3, 5⟩⟩, ⟨⟨0, 3, 0, 0, 1, 4⟩, ⟨0, 1, 1, 1, 4, 1⟩⟩⟩, ⟨⟨⟨0, 0, 7, 0, 3, 1⟩, ⟨0, 0, 4, 0, 5, 7⟩⟩, ⟨⟨0, 0, 6, 0, 0, 6⟩, ⟨0, 2, 5, 0, 6, 0⟩⟩, ⟨⟨0, 0, 6, 0, 3, 8⟩, ⟨0, 2, 6, 0, 6, 0⟩⟩⟩, ⟨⟨⟨0, 0, 7, 0, 3, 9⟩, ⟨0, 0, 5, 0, 5, 7⟩⟩, ⟨⟨0, 0, 6, 0, 4, 6⟩, ⟨0, 2, 7, 0, 6, 0⟩⟩, ⟨⟨0, 0, 6, 0, 1, 0⟩, ⟨0, 2, 7, 0, 6, 3⟩⟩⟩, ⟨⟨⟨0, 0, 7, 0, 4, 7⟩, ⟨0, 0, 4, 1, 3, 6⟩⟩, ⟨⟨0, 0, 6, 0, 1, 4⟩, ⟨0, 2, 6, 0, 6, 3⟩⟩, ⟨⟨0, 0, 6, 0, 5, 3⟩, ⟨0, 2, 5, 0, 6, 3⟩⟩⟩⟩
private def lw53_4_4 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 0, 7, 1, 2, 9⟩, ⟨0, 2, 1, 0, 6, 4⟩⟩, ⟨⟨0, 2, 9, 1, 1, 8⟩, ⟨0, 2, 1, 0, 6, 6⟩⟩, ⟨⟨0, 2, 9, 1, 1, 9⟩, ⟨0, 2, 2, 0, 6, 6⟩⟩⟩, ⟨⟨⟨0, 3, 3, 1, 2, 9⟩, ⟨0, 1, 1, 1, 4, 7⟩⟩, ⟨⟨0, 4, 2, 1, 1, 8⟩, ⟨0, 1, 1, 1, 3, 7⟩⟩, ⟨⟨0, 4, 2, 1, 1, 9⟩, ⟨0, 1, 2, 1, 4, 1⟩⟩⟩, ⟨⟨⟨0, 1, 0, 0, 3, 1⟩, ⟨0, 0, 4, 1, 3, 8⟩⟩, ⟨⟨0, 3, 7, 0, 0, 6⟩, ⟨0, 2, 6, 0, 6, 4⟩⟩, ⟨⟨0, 3, 7, 0, 3, 8⟩, ⟨0, 2, 5, 0, 6, 4⟩⟩⟩, ⟨⟨⟨0, 1, 3, 0, 4, 7⟩, ⟨0, 0, 4, 1, 4, 0⟩⟩, ⟨⟨0, 3, 7, 1, 5, 5⟩, ⟨0, 2, 6, 0, 6, 6⟩⟩, ⟨⟨0, 0, 6, 0, 2, 6⟩, ⟨0, 2, 5, 0, 6, 6⟩⟩⟩, ⟨⟨⟨0, 1, 3, 1, 4, 2⟩, ⟨0, 0, 5, 1, 4, 0⟩⟩, ⟨⟨0, 3, 7, 1, 5, 3⟩, ⟨0, 2, 7, 0, 6, 4⟩⟩, ⟨⟨0, 0, 6, 0, 5, 1⟩, ⟨0, 2, 7, 0, 6, 6⟩⟩⟩⟩
private def lw53_4_5 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 0, 7, 1, 1, 8⟩, ⟨0, 2, 2, 0, 6, 7⟩⟩, ⟨⟨0, 2, 9, 1, 2, 4⟩, ⟨0, 2, 1, 0, 6, 8⟩⟩, ⟨⟨0, 2, 9, 1, 2, 5⟩, ⟨0, 2, 1, 0, 6, 7⟩⟩⟩, ⟨⟨⟨0, 3, 3, 1, 1, 8⟩, ⟨0, 1, 2, 1, 4, 7⟩⟩, ⟨⟨0, 4, 2, 1, 2, 4⟩, ⟨0, 1, 1, 1, 4, 8⟩⟩, ⟨⟨0, 4, 2, 1, 2, 5⟩, ⟨0, 1, 1, 1, 3, 9⟩⟩⟩, ⟨⟨⟨0, 1, 0, 0, 3, 9⟩, ⟨0, 0, 5, 1, 4, 3⟩⟩, ⟨⟨0, 3, 7, 0, 4, 6⟩, ⟨0, 2, 7, 0, 6, 8⟩⟩, ⟨⟨0, 3, 7, 0, 1, 0⟩, ⟨0, 2, 7, 0, 6, 7⟩⟩⟩, ⟨⟨⟨0, 1, 3, 1, 4, 4⟩, ⟨0, 0, 4, 1, 4, 5⟩⟩, ⟨⟨0, 3, 7, 1, 5, 4⟩, ⟨0, 2, 5, 0, 6, 8⟩⟩, ⟨⟨0, 0, 6, 0, 3, 7⟩, ⟨0, 2, 6, 0, 6, 8⟩⟩⟩, ⟨⟨⟨0, 1, 3, 0, 3, 1⟩, ⟨0, 0, 4, 1, 4, 3⟩⟩, ⟨⟨0, 3, 7, 1, 5, 6⟩, ⟨0, 2, 5, 0, 6, 7⟩⟩, ⟨⟨0, 0, 6, 0, 2, 8⟩, ⟨0, 2, 6, 0, 6, 7⟩⟩⟩⟩
private def lw53_4_6 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 0, 7, 1, 2, 5⟩, ⟨0, 2, 1, 0, 7, 0⟩⟩, ⟨⟨0, 2, 9, 1, 2, 9⟩, ⟨0, 2, 2, 0, 7, 0⟩⟩, ⟨⟨0, 2, 9, 1, 3, 0⟩, ⟨0, 2, 1, 0, 7, 2⟩⟩⟩, ⟨⟨⟨0, 3, 3, 1, 2, 5⟩, ⟨0, 1, 1, 1, 4, 6⟩⟩, ⟨⟨0, 4, 2, 1, 2, 9⟩, ⟨0, 1, 2, 1, 4, 8⟩⟩, ⟨⟨0, 4, 2, 1, 3, 0⟩, ⟨0, 1, 1, 1, 3, 5⟩⟩⟩, ⟨⟨⟨0, 1, 0, 0, 4, 7⟩, ⟨0, 0, 4, 0, 5, 8⟩⟩, ⟨⟨0, 3, 7, 0, 1, 4⟩, ⟨0, 2, 5, 0, 7, 0⟩⟩, ⟨⟨0, 3, 7, 0, 5, 3⟩, ⟨0, 2, 6, 0, 7, 0⟩⟩⟩, ⟨⟨⟨0, 1, 3, 0, 3, 9⟩, ⟨0, 0, 5, 0, 5, 8⟩⟩, ⟨⟨0, 3, 7, 1, 5, 7⟩, ⟨0, 2, 7, 0, 7, 0⟩⟩, ⟨⟨0, 0, 6, 0, 2, 9⟩, ⟨0, 2, 7, 0, 7, 2⟩⟩⟩, ⟨⟨⟨0, 1, 3, 1, 4, 9⟩, ⟨0, 0, 4, 1, 5, 0⟩⟩, ⟨⟨0, 3, 7, 1, 5, 2⟩, ⟨0, 2, 6, 0, 7, 2⟩⟩, ⟨⟨0, 0, 6, 0, 4, 4⟩, ⟨0, 2, 5, 0, 7, 2⟩⟩⟩⟩
private def lwBlk_4 : Seven (Five (Three LeafWit)) := ⟨lw53_4_0, lw53_4_1, lw53_4_2, lw53_4_3, lw53_4_4, lw53_4_5, lw53_4_6⟩
private def lw53_5_0 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 0, 0, 0, 7, 5⟩, ⟨0, 0, 4, 1, 0, 3⟩⟩, ⟨⟨0, 0, 0, 0, 7, 6⟩, ⟨0, 0, 5, 1, 0, 6⟩⟩, ⟨⟨0, 0, 0, 0, 7, 7⟩, ⟨0, 0, 4, 1, 0, 9⟩⟩⟩, ⟨⟨⟨0, 0, 3, 0, 7, 5⟩, ⟨0, 1, 1, 1, 0, 3⟩⟩, ⟨⟨0, 0, 3, 0, 7, 6⟩, ⟨0, 1, 2, 1, 0, 6⟩⟩, ⟨⟨0, 0, 3, 0, 7, 7⟩, ⟨0, 1, 1, 1, 0, 9⟩⟩⟩, ⟨⟨⟨0, 0, 0, 0, 2, 6⟩, ⟨0, 2, 1, 0, 2, 7⟩⟩, ⟨⟨0, 0, 6, 0, 7, 5⟩, ⟨0, 2, 5, 1, 0, 4⟩⟩, ⟨⟨0, 0, 6, 0, 7, 8⟩, ⟨0, 2, 7, 1, 0, 4⟩⟩⟩, ⟨⟨⟨0, 0, 0, 0, 2, 8⟩, ⟨0, 2, 2, 0, 2, 7⟩⟩, ⟨⟨0, 0, 6, 0, 7, 9⟩, ⟨0, 2, 6, 1, 0, 8⟩⟩, ⟨⟨0, 0, 6, 0, 7, 6⟩, ⟨0, 2, 6, 1, 0, 6⟩⟩⟩, ⟨⟨⟨0, 0, 0, 0, 2, 9⟩, ⟨0, 2, 1, 0, 3, 0⟩⟩, ⟨⟨0, 0, 6, 0, 7, 7⟩, ⟨0, 2, 7, 1, 1, 1⟩⟩, ⟨⟨0, 0, 6, 0, 8, 2⟩, ⟨0, 2, 5, 1, 1, 1⟩⟩⟩⟩
private def lw53_5_1 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 0, 7, 0, 7, 5⟩, ⟨0, 3, 1, 1, 0, 3⟩⟩, ⟨⟨0, 0, 7, 0, 7, 6⟩, ⟨0, 3, 2, 1, 0, 6⟩⟩, ⟨⟨0, 0, 7, 0, 7, 7⟩, ⟨0, 3, 1, 1, 0, 9⟩⟩⟩, ⟨⟨⟨0, 1, 0, 0, 7, 5⟩, ⟨0, 3, 5, 1, 0, 3⟩⟩, ⟨⟨0, 1, 0, 0, 7, 6⟩, ⟨0, 3, 6, 1, 0, 6⟩⟩, ⟨⟨0, 1, 0, 0, 7, 7⟩, ⟨0, 3, 5, 1, 0, 9⟩⟩⟩, ⟨⟨⟨0, 0, 3, 0, 2, 6⟩, ⟨0, 1, 1, 1, 5, 8⟩⟩, ⟨⟨0, 1, 3, 0, 7, 5⟩, ⟨0, 4, 0, 1, 0, 4⟩⟩, ⟨⟨0, 1, 3, 0, 7, 8⟩, ⟨0, 4, 1, 1, 5, 9⟩⟩⟩, ⟨⟨⟨0, 0, 3, 0, 2, 8⟩, ⟨0, 1, 2, 1, 6, 0⟩⟩, ⟨⟨0, 1, 3, 0, 7, 9⟩, ⟨0, 4, 1, 1, 0, 8⟩⟩, ⟨⟨0, 1, 3, 0, 7, 6⟩, ⟨0, 4, 1, 1, 0, 6⟩⟩⟩, ⟨⟨⟨0, 0, 3, 0, 2, 9⟩, ⟨0, 1, 1, 1, 6, 1⟩⟩, ⟨⟨0, 1, 3, 0, 7, 7⟩, ⟨0, 4, 1, 1, 6, 2⟩⟩, ⟨⟨0, 1, 3, 0, 8, 2⟩, ⟨0, 4, 0, 1, 1, 1⟩⟩⟩⟩
private def lw53_5_2 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 1, 4, 0, 7, 5⟩, ⟨0, 1, 8, 1, 1, 2⟩⟩, ⟨⟨0, 1, 4, 0, 7, 6⟩, ⟨0, 1, 9, 1, 1, 3⟩⟩, ⟨⟨0, 1, 4, 0, 7, 7⟩, ⟨0, 1, 8, 1, 1, 4⟩⟩⟩, ⟨⟨⟨0, 1, 7, 0, 7, 5⟩, ⟨0, 4, 6, 0, 2, 7⟩⟩, ⟨⟨0, 1, 7, 0, 7, 6⟩, ⟨0, 4, 7, 0, 2, 7⟩⟩, ⟨⟨0, 1, 7, 0, 7, 7⟩, ⟨0, 4, 6, 0, 3, 0⟩⟩⟩, ⟨⟨⟨0, 1, 0, 1, 5, 2⟩, ⟨0, 3, 5, 0, 5, 7⟩⟩, ⟨⟨0, 2, 0, 0, 7, 5⟩, ⟨0, 5, 0, 0, 4, 9⟩⟩, ⟨⟨0, 2, 0, 0, 7, 8⟩, ⟨0, 5, 2, 0, 4, 5⟩⟩⟩, ⟨⟨⟨0, 1, 0, 1, 5, 3⟩, ⟨0, 3, 6, 0, 5, 7⟩⟩, ⟨⟨0, 2, 0, 0, 7, 9⟩, ⟨0, 5, 1, 0, 4, 9⟩⟩, ⟨⟨0, 2, 0, 0, 7, 6⟩, ⟨0, 5, 1, 0, 3, 4⟩⟩⟩, ⟨⟨⟨0, 1, 0, 1, 5, 4⟩, ⟨0, 3, 5, 1, 3, 6⟩⟩, ⟨⟨0, 2, 0, 0, 7, 7⟩, ⟨0, 5, 2, 0, 4, 2⟩⟩, ⟨⟨0, 2, 0, 0, 8, 2⟩, ⟨0, 5, 0, 0, 3, 4⟩⟩⟩⟩
private def lw53_5_3 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 1, 4, 1, 3, 2⟩, ⟨0, 1, 1, 1, 6, 3⟩⟩, ⟨⟨0, 1, 4, 1, 3, 3⟩, ⟨0, 1, 2, 1, 6, 3⟩⟩, ⟨⟨0, 1, 4, 1, 3, 4⟩, ⟨0, 1, 1, 1, 6, 4⟩⟩⟩, ⟨⟨⟨0, 2, 3, 0, 7, 5⟩, ⟨0, 3, 8, 0, 6, 0⟩⟩, ⟨⟨0, 2, 3, 0, 7, 6⟩, ⟨0, 3, 9, 0, 6, 0⟩⟩, ⟨⟨0, 2, 3, 0, 7, 7⟩, ⟨0, 3, 8, 0, 6, 3⟩⟩⟩, ⟨⟨⟨0, 1, 4, 0, 3, 1⟩, ⟨0, 1, 1, 0, 5, 7⟩⟩, ⟨⟨0, 2, 4, 0, 7, 5⟩, ⟨0, 4, 0, 0, 6, 0⟩⟩, ⟨⟨0, 2, 4, 0, 7, 8⟩, ⟨0, 4, 1, 0, 6, 0⟩⟩⟩, ⟨⟨⟨0, 1, 4, 0, 3, 9⟩, ⟨0, 1, 2, 0, 5, 7⟩⟩, ⟨⟨0, 2, 4, 0, 7, 9⟩, ⟨0, 4, 1, 0, 4, 8⟩⟩, ⟨⟨0, 2, 4, 0, 7, 6⟩, ⟨0, 4, 1, 0, 3, 2⟩⟩⟩, ⟨⟨⟨0, 1, 4, 0, 4, 7⟩, ⟨0, 1, 1, 1, 3, 6⟩⟩, ⟨⟨0, 2, 4, 0, 7, 7⟩, ⟨0, 4, 1, 0, 6, 3⟩⟩, ⟨⟨0, 2, 4, 0, 8, 2⟩, ⟨0, 4, 0, 0, 6, 3⟩⟩⟩⟩
private def lw53_5_4 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 0, 0, 1, 2, 9⟩, ⟨0, 0, 4, 1, 1, 6⟩⟩, ⟨⟨0, 2, 8, 0, 7, 5⟩, ⟨0, 2, 5, 1, 1, 3⟩⟩, ⟨⟨0, 2, 8, 0, 7, 8⟩, ⟨0, 2, 6, 1, 2, 3⟩⟩⟩, ⟨⟨⟨0, 0, 7, 1, 5, 2⟩, ⟨0, 3, 1, 1, 1, 6⟩⟩, ⟨⟨0, 2, 9, 0, 7, 5⟩, ⟨0, 4, 0, 1, 1, 3⟩⟩, ⟨⟨0, 2, 9, 0, 7, 8⟩, ⟨0, 4, 1, 1, 2, 3⟩⟩⟩, ⟨⟨⟨0, 1, 4, 1, 5, 2⟩, ⟨0, 1, 8, 0, 5, 7⟩⟩, ⟨⟨0, 2, 0, 1, 5, 5⟩, ⟨0, 5, 0, 0, 6, 0⟩⟩, ⟨⟨0, 2, 0, 1, 5, 3⟩, ⟨0, 5, 1, 0, 6, 0⟩⟩⟩, ⟨⟨⟨0, 2, 8, 0, 4, 7⟩, ⟨0, 2, 5, 0, 5, 8⟩⟩, ⟨⟨0, 1, 3, 1, 5, 5⟩, ⟨0, 4, 0, 0, 5, 8⟩⟩, ⟨⟨0, 0, 6, 0, 2, 6⟩, ⟨0, 2, 5, 0, 2, 7⟩⟩⟩, ⟨⟨⟨0, 2, 8, 1, 4, 2⟩, ⟨0, 2, 7, 1, 4, 5⟩⟩, ⟨⟨0, 1, 3, 1, 5, 3⟩, ⟨0, 4, 1, 1, 6, 0⟩⟩, ⟨⟨0, 0, 6, 0, 5, 1⟩, ⟨0, 2, 6, 0, 2, 7⟩⟩⟩⟩
private def lw53_5_5 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 0, 0, 1, 1, 8⟩, ⟨0, 0, 5, 1, 1, 6⟩⟩, ⟨⟨0, 2, 8, 0, 7, 9⟩, ⟨0, 2, 7, 1, 1, 2⟩⟩, ⟨⟨0, 2, 8, 0, 7, 6⟩, ⟨0, 2, 7, 1, 1, 4⟩⟩⟩, ⟨⟨⟨0, 0, 7, 1, 5, 3⟩, ⟨0, 3, 2, 1, 1, 6⟩⟩, ⟨⟨0, 2, 9, 0, 7, 9⟩, ⟨0, 4, 1, 0, 8, 5⟩⟩, ⟨⟨0, 2, 9, 0, 7, 6⟩, ⟨0, 4, 1, 0, 9, 5⟩⟩⟩, ⟨⟨⟨0, 1, 4, 1, 5, 3⟩, ⟨0, 1, 9, 0, 5, 7⟩⟩, ⟨⟨0, 2, 0, 1, 5, 4⟩, ⟨0, 5, 2, 0, 6, 0⟩⟩, ⟨⟨0, 2, 0, 1, 5, 6⟩, ⟨0, 5, 2, 0, 6, 3⟩⟩⟩, ⟨⟨⟨0, 2, 8, 1, 4, 4⟩, ⟨0, 2, 6, 0, 5, 8⟩⟩, ⟨⟨0, 1, 3, 1, 5, 4⟩, ⟨0, 4, 1, 0, 5, 8⟩⟩, ⟨⟨0, 0, 6, 0, 3, 7⟩, ⟨0, 2, 7, 0, 2, 7⟩⟩⟩, ⟨⟨⟨0, 2, 8, 0, 3, 1⟩, ⟨0, 2, 6, 1, 3, 8⟩⟩, ⟨⟨0, 1, 3, 1, 5, 6⟩, ⟨0, 4, 1, 1, 3, 8⟩⟩, ⟨⟨0, 0, 6, 0, 2, 8⟩, ⟨0, 2, 7, 0, 3, 0⟩⟩⟩⟩
private def lw53_5_6 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 0, 0, 1, 2, 5⟩, ⟨0, 0, 4, 1, 2, 8⟩⟩, ⟨⟨0, 2, 8, 0, 7, 7⟩, ⟨0, 2, 6, 1, 2, 2⟩⟩, ⟨⟨0, 2, 8, 0, 8, 2⟩, ⟨0, 2, 5, 1, 1, 7⟩⟩⟩, ⟨⟨⟨0, 0, 7, 1, 5, 4⟩, ⟨0, 3, 1, 1, 2, 8⟩⟩, ⟨⟨0, 2, 9, 0, 7, 7⟩, ⟨0, 4, 1, 1, 2, 2⟩⟩, ⟨⟨0, 2, 9, 0, 8, 2⟩, ⟨0, 4, 0, 1, 1, 7⟩⟩⟩, ⟨⟨⟨0, 1, 4, 1, 5, 4⟩, ⟨0, 1, 8, 1, 3, 6⟩⟩, ⟨⟨0, 2, 0, 1, 5, 7⟩, ⟨0, 5, 1, 0, 6, 3⟩⟩, ⟨⟨0, 2, 0, 1, 5, 2⟩, ⟨0, 5, 0, 0, 6, 3⟩⟩⟩, ⟨⟨⟨0, 2, 8, 0, 3, 9⟩, ⟨0, 2, 7, 1, 4, 3⟩⟩, ⟨⟨0, 1, 3, 1, 5, 7⟩, ⟨0, 4, 1, 1, 6, 5⟩⟩, ⟨⟨0, 0, 6, 0, 2, 9⟩, ⟨0, 2, 6, 0, 3, 0⟩⟩⟩, ⟨⟨⟨0, 2, 8, 1, 4, 9⟩, ⟨0, 2, 5, 1, 3, 8⟩⟩, ⟨⟨0, 1, 3, 1, 5, 2⟩, ⟨0, 4, 0, 1, 3, 8⟩⟩, ⟨⟨0, 0, 6, 0, 4, 4⟩, ⟨0, 2, 5, 0, 3, 0⟩⟩⟩⟩
private def lwBlk_5 : Seven (Five (Three LeafWit)) := ⟨lw53_5_0, lw53_5_1, lw53_5_2, lw53_5_3, lw53_5_4, lw53_5_5, lw53_5_6⟩
private def lw53_6_0 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 0, 0, 0, 9, 8⟩, ⟨0, 0, 4, 0, 9, 9⟩⟩, ⟨⟨0, 0, 6, 1, 0, 0⟩, ⟨0, 0, 4, 1, 0, 8⟩⟩, ⟨⟨0, 0, 6, 1, 1, 0⟩, ⟨0, 0, 5, 1, 0, 9⟩⟩⟩, ⟨⟨⟨0, 0, 7, 0, 9, 8⟩, ⟨0, 1, 1, 0, 9, 9⟩⟩, ⟨⟨0, 1, 3, 1, 0, 0⟩, ⟨0, 1, 1, 1, 0, 8⟩⟩, ⟨⟨0, 1, 3, 1, 1, 0⟩, ⟨0, 1, 2, 1, 0, 9⟩⟩⟩, ⟨⟨⟨0, 1, 4, 0, 9, 8⟩, ⟨0, 2, 1, 0, 3, 4⟩⟩, ⟨⟨0, 2, 0, 1, 0, 0⟩, ⟨0, 2, 7, 1, 0, 2⟩⟩, ⟨⟨0, 2, 0, 1, 1, 0⟩, ⟨0, 2, 5, 1, 0, 2⟩⟩⟩, ⟨⟨⟨0, 2, 8, 1, 0, 0⟩, ⟨0, 2, 1, 0, 3, 6⟩⟩, ⟨⟨0, 2, 9, 1, 0, 0⟩, ⟨0, 2, 7, 1, 0, 6⟩⟩, ⟨⟨0, 2, 8, 0, 0, 6⟩, ⟨0, 2, 5, 1, 0, 6⟩⟩⟩, ⟨⟨⟨0, 2, 8, 1, 1, 0⟩, ⟨0, 2, 2, 0, 3, 6⟩⟩, ⟨⟨0, 2, 9, 1, 1, 0⟩, ⟨0, 2, 6, 1, 0, 9⟩⟩, ⟨⟨0, 2, 8, 0, 3, 8⟩, ⟨0, 2, 6, 1, 1, 1⟩⟩⟩⟩
private def lw53_6_1 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 0, 7, 1, 1, 5⟩, ⟨0, 3, 1, 0, 9, 9⟩⟩, ⟨⟨0, 0, 6, 1, 0, 0⟩, ⟨0, 3, 1, 1, 0, 8⟩⟩, ⟨⟨0, 0, 6, 1, 1, 0⟩, ⟨0, 3, 2, 1, 0, 9⟩⟩⟩, ⟨⟨⟨0, 3, 3, 0, 9, 8⟩, ⟨0, 3, 5, 0, 9, 9⟩⟩, ⟨⟨0, 3, 7, 1, 0, 0⟩, ⟨0, 3, 5, 1, 0, 8⟩⟩, ⟨⟨0, 3, 7, 1, 1, 0⟩, ⟨0, 3, 6, 1, 0, 9⟩⟩⟩, ⟨⟨⟨0, 1, 0, 0, 5, 4⟩, ⟨0, 1, 1, 1, 6, 6⟩⟩, ⟨⟨0, 3, 7, 1, 6, 7⟩, ⟨0, 4, 1, 1, 6, 3⟩⟩, ⟨⟨0, 3, 7, 1, 3, 2⟩, ⟨0, 4, 0, 1, 0, 2⟩⟩⟩, ⟨⟨⟨0, 1, 3, 1, 2, 0⟩, ⟨0, 1, 1, 1, 6, 5⟩⟩, ⟨⟨0, 4, 2, 1, 0, 0⟩, ⟨0, 4, 1, 1, 6, 8⟩⟩, ⟨⟨0, 2, 9, 0, 0, 6⟩, ⟨0, 4, 0, 1, 0, 6⟩⟩⟩, ⟨⟨⟨0, 1, 3, 0, 5, 6⟩, ⟨0, 1, 2, 1, 6, 1⟩⟩, ⟨⟨0, 4, 2, 1, 1, 0⟩, ⟨0, 4, 1, 1, 0, 9⟩⟩, ⟨⟨0, 2, 9, 0, 3, 8⟩, ⟨0, 4, 1, 1, 1, 1⟩⟩⟩⟩
private def lw53_6_2 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 1, 4, 1, 1, 5⟩, ⟨0, 1, 8, 1, 1, 6⟩⟩, ⟨⟨0, 2, 4, 1, 1, 8⟩, ⟨0, 1, 8, 1, 1, 7⟩⟩, ⟨⟨0, 2, 4, 1, 1, 9⟩, ⟨0, 1, 9, 1, 1, 4⟩⟩⟩, ⟨⟨⟨0, 4, 4, 0, 9, 8⟩, ⟨0, 4, 6, 0, 3, 4⟩⟩, ⟨⟨0, 4, 8, 1, 0, 0⟩, ⟨0, 4, 6, 0, 3, 6⟩⟩, ⟨⟨0, 4, 8, 1, 1, 0⟩, ⟨0, 4, 7, 0, 3, 6⟩⟩⟩, ⟨⟨⟨0, 3, 4, 0, 5, 4⟩, ⟨0, 3, 5, 1, 3, 8⟩⟩, ⟨⟨0, 4, 9, 1, 0, 0⟩, ⟨0, 5, 2, 0, 4, 9⟩⟩, ⟨⟨0, 4, 9, 1, 1, 0⟩, ⟨0, 5, 0, 0, 4, 5⟩⟩⟩, ⟨⟨⟨0, 3, 7, 1, 2, 0⟩, ⟨0, 3, 5, 1, 4, 0⟩⟩, ⟨⟨0, 4, 9, 0, 4, 7⟩, ⟨0, 5, 2, 0, 5, 2⟩⟩, ⟨⟨0, 2, 0, 1, 6, 9⟩, ⟨0, 5, 0, 0, 2, 7⟩⟩⟩, ⟨⟨⟨0, 3, 7, 0, 5, 6⟩, ⟨0, 3, 6, 1, 4, 0⟩⟩, ⟨⟨0, 4, 9, 1, 4, 2⟩, ⟨0, 5, 1, 0, 4, 5⟩⟩, ⟨⟨0, 2, 0, 1, 2, 1⟩, ⟨0, 5, 1, 0, 2, 7⟩⟩⟩⟩
private def lw53_6_3 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 1, 0, 1, 2, 9⟩, ⟨0, 1, 1, 1, 5, 9⟩⟩, ⟨⟨0, 2, 0, 1, 6, 7⟩, ⟨0, 1, 1, 1, 7, 0⟩⟩, ⟨⟨0, 2, 0, 1, 3, 2⟩, ⟨0, 1, 2, 1, 7, 0⟩⟩⟩, ⟨⟨⟨0, 3, 4, 1, 2, 9⟩, ⟨0, 3, 8, 0, 6, 4⟩⟩, ⟨⟨0, 4, 3, 1, 1, 8⟩, ⟨0, 3, 8, 0, 6, 6⟩⟩, ⟨⟨0, 4, 3, 1, 1, 9⟩, ⟨0, 3, 9, 0, 6, 6⟩⟩⟩, ⟨⟨⟨0, 1, 7, 0, 3, 1⟩, ⟨0, 1, 1, 1, 3, 8⟩⟩, ⟨⟨0, 4, 8, 0, 0, 6⟩, ⟨0, 4, 1, 0, 6, 4⟩⟩, ⟨⟨0, 4, 8, 0, 3, 8⟩, ⟨0, 4, 0, 0, 6, 4⟩⟩⟩, ⟨⟨⟨0, 2, 0, 0, 4, 7⟩, ⟨0, 1, 1, 1, 4, 0⟩⟩, ⟨⟨0, 4, 9, 0, 0, 6⟩, ⟨0, 4, 1, 0, 6, 6⟩⟩, ⟨⟨0, 3, 7, 0, 2, 6⟩, ⟨0, 4, 0, 0, 6, 6⟩⟩⟩, ⟨⟨⟨0, 2, 0, 1, 4, 2⟩, ⟨0, 1, 2, 1, 4, 0⟩⟩, ⟨⟨0, 4, 9, 0, 3, 8⟩, ⟨0, 4, 1, 0, 4, 0⟩⟩, ⟨⟨0, 3, 7, 0, 5, 1⟩, ⟨0, 4, 1, 0, 2, 3⟩⟩⟩⟩
private def lw53_6_4 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 0, 3, 1, 2, 9⟩, ⟨0, 0, 4, 1, 1, 2⟩⟩, ⟨⟨0, 1, 3, 1, 6, 7⟩, ⟨0, 2, 6, 1, 1, 3⟩⟩, ⟨⟨0, 1, 3, 1, 3, 2⟩, ⟨0, 2, 5, 1, 2, 3⟩⟩⟩, ⟨⟨⟨0, 3, 0, 1, 2, 9⟩, ⟨0, 3, 1, 1, 1, 2⟩⟩, ⟨⟨0, 4, 2, 0, 7, 5⟩, ⟨0, 4, 1, 1, 1, 3⟩⟩, ⟨⟨0, 4, 2, 0, 7, 8⟩, ⟨0, 4, 0, 1, 2, 3⟩⟩⟩, ⟨⟨⟨0, 2, 3, 0, 3, 1⟩, ⟨0, 1, 8, 1, 3, 8⟩⟩, ⟨⟨0, 4, 3, 0, 7, 5⟩, ⟨0, 5, 1, 0, 6, 4⟩⟩, ⟨⟨0, 4, 3, 0, 7, 8⟩, ⟨0, 5, 0, 0, 6, 4⟩⟩⟩, ⟨⟨⟨0, 2, 9, 0, 4, 7⟩, ⟨0, 2, 7, 0, 5, 8⟩⟩, ⟨⟨0, 4, 2, 0, 4, 7⟩, ⟨0, 4, 1, 1, 7, 1⟩⟩, ⟨⟨0, 1, 3, 0, 2, 6⟩, ⟨0, 2, 6, 0, 3, 4⟩⟩⟩, ⟨⟨⟨0, 2, 9, 1, 4, 2⟩, ⟨0, 2, 5, 1, 4, 5⟩⟩, ⟨⟨0, 4, 2, 1, 4, 2⟩, ⟨0, 4, 0, 1, 4, 5⟩⟩, ⟨⟨0, 1, 3, 0, 5, 1⟩, ⟨0, 2, 5, 0, 3, 4⟩⟩⟩⟩
private def lw53_6_5 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 0, 6, 1, 2, 5⟩, ⟨0, 0, 4, 1, 2, 2⟩⟩, ⟨⟨0, 1, 3, 1, 2, 5⟩, ⟨0, 2, 6, 1, 2, 8⟩⟩, ⟨⟨0, 2, 8, 1, 2, 5⟩, ⟨0, 2, 5, 1, 1, 4⟩⟩⟩, ⟨⟨⟨0, 0, 6, 1, 2, 5⟩, ⟨0, 3, 1, 1, 2, 2⟩⟩, ⟨⟨0, 3, 7, 1, 2, 5⟩, ⟨0, 4, 1, 1, 2, 8⟩⟩, ⟨⟨0, 1, 3, 1, 6, 9⟩, ⟨0, 4, 0, 1, 1, 4⟩⟩⟩, ⟨⟨⟨0, 2, 4, 0, 4, 7⟩, ⟨0, 1, 8, 1, 4, 0⟩⟩, ⟨⟨0, 4, 8, 1, 2, 5⟩, ⟨0, 5, 1, 0, 6, 6⟩⟩, ⟨⟨0, 3, 7, 1, 6, 9⟩, ⟨0, 5, 0, 0, 6, 6⟩⟩⟩, ⟨⟨⟨0, 2, 0, 0, 9, 0⟩, ⟨0, 2, 7, 1, 5, 0⟩⟩, ⟨⟨0, 4, 3, 0, 4, 7⟩, ⟨0, 4, 1, 1, 6, 1⟩⟩, ⟨⟨0, 2, 0, 0, 2, 6⟩, ⟨0, 2, 6, 0, 3, 6⟩⟩⟩, ⟨⟨⟨0, 0, 6, 0, 3, 1⟩, ⟨0, 2, 5, 0, 5, 7⟩⟩, ⟨⟨0, 0, 6, 0, 3, 1⟩, ⟨0, 4, 0, 0, 5, 7⟩⟩, ⟨⟨0, 2, 4, 0, 2, 6⟩, ⟨0, 2, 5, 0, 3, 6⟩⟩⟩⟩
private def lw53_6_6 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 0, 6, 1, 3, 0⟩, ⟨0, 0, 5, 1, 2, 2⟩⟩, ⟨⟨0, 1, 3, 1, 3, 0⟩, ⟨0, 2, 7, 1, 1, 6⟩⟩, ⟨⟨0, 2, 8, 1, 3, 0⟩, ⟨0, 2, 7, 1, 1, 7⟩⟩⟩, ⟨⟨⟨0, 0, 6, 1, 3, 0⟩, ⟨0, 3, 2, 1, 2, 2⟩⟩, ⟨⟨0, 3, 7, 1, 3, 0⟩, ⟨0, 4, 1, 0, 7, 4⟩⟩, ⟨⟨0, 1, 3, 1, 2, 1⟩, ⟨0, 4, 1, 0, 8, 8⟩⟩⟩, ⟨⟨⟨0, 2, 4, 1, 4, 2⟩, ⟨0, 1, 9, 1, 4, 0⟩⟩, ⟨⟨0, 4, 8, 1, 3, 0⟩, ⟨0, 5, 2, 0, 6, 4⟩⟩, ⟨⟨0, 3, 7, 1, 2, 1⟩, ⟨0, 5, 2, 0, 6, 6⟩⟩⟩, ⟨⟨⟨0, 2, 0, 0, 2, 2⟩, ⟨0, 2, 6, 1, 4, 5⟩⟩, ⟨⟨0, 4, 3, 1, 4, 2⟩, ⟨0, 4, 1, 1, 4, 5⟩⟩, ⟨⟨0, 2, 0, 0, 5, 1⟩, ⟨0, 2, 7, 0, 3, 4⟩⟩⟩, ⟨⟨⟨0, 0, 6, 1, 4, 9⟩, ⟨0, 2, 6, 0, 5, 7⟩⟩, ⟨⟨0, 0, 6, 1, 4, 9⟩, ⟨0, 4, 1, 0, 5, 7⟩⟩, ⟨⟨0, 2, 4, 0, 5, 1⟩, ⟨0, 2, 7, 0, 3, 6⟩⟩⟩⟩
private def lwBlk_6 : Seven (Five (Three LeafWit)) := ⟨lw53_6_0, lw53_6_1, lw53_6_2, lw53_6_3, lw53_6_4, lw53_6_5, lw53_6_6⟩
private def lw53_7_0 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 0, 0, 1, 0, 0⟩, ⟨0, 0, 5, 0, 9, 9⟩⟩, ⟨⟨0, 0, 6, 1, 0, 5⟩, ⟨0, 0, 4, 1, 0, 4⟩⟩, ⟨⟨0, 0, 6, 1, 0, 1⟩, ⟨0, 0, 4, 1, 1, 1⟩⟩⟩, ⟨⟨⟨0, 0, 7, 1, 0, 0⟩, ⟨0, 1, 2, 0, 9, 9⟩⟩, ⟨⟨0, 1, 3, 1, 0, 5⟩, ⟨0, 1, 1, 1, 0, 4⟩⟩, ⟨⟨0, 1, 3, 1, 0, 1⟩, ⟨0, 1, 1, 1, 1, 1⟩⟩⟩, ⟨⟨⟨0, 1, 4, 1, 0, 0⟩, ⟨0, 2, 2, 0, 4, 2⟩⟩, ⟨⟨0, 2, 0, 1, 0, 5⟩, ⟨0, 2, 6, 0, 9, 9⟩⟩, ⟨⟨0, 2, 0, 1, 0, 1⟩, ⟨0, 2, 6, 1, 0, 2⟩⟩⟩, ⟨⟨⟨0, 2, 8, 1, 0, 5⟩, ⟨0, 2, 1, 0, 4, 5⟩⟩, ⟨⟨0, 2, 9, 1, 0, 5⟩, ⟨0, 2, 5, 1, 0, 3⟩⟩, ⟨⟨0, 2, 8, 0, 4, 6⟩, ⟨0, 2, 7, 1, 0, 3⟩⟩⟩, ⟨⟨⟨0, 2, 8, 1, 0, 1⟩, ⟨0, 2, 1, 0, 4, 2⟩⟩, ⟨⟨0, 2, 9, 1, 0, 1⟩, ⟨0, 2, 5, 1, 0, 9⟩⟩, ⟨⟨0, 2, 8, 0, 1, 0⟩, ⟨0, 2, 7, 1, 0, 9⟩⟩⟩⟩
private def lw53_7_1 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 0, 7, 1, 2, 1⟩, ⟨0, 3, 2, 0, 9, 9⟩⟩, ⟨⟨0, 0, 6, 1, 0, 5⟩, ⟨0, 3, 1, 1, 0, 4⟩⟩, ⟨⟨0, 0, 6, 1, 0, 1⟩, ⟨0, 3, 1, 1, 1, 1⟩⟩⟩, ⟨⟨⟨0, 3, 3, 1, 0, 0⟩, ⟨0, 3, 6, 0, 9, 9⟩⟩, ⟨⟨0, 3, 7, 1, 0, 5⟩, ⟨0, 3, 5, 1, 0, 4⟩⟩, ⟨⟨0, 3, 7, 1, 0, 1⟩, ⟨0, 3, 5, 1, 1, 1⟩⟩⟩, ⟨⟨⟨0, 1, 0, 0, 5, 5⟩, ⟨0, 1, 2, 1, 6, 6⟩⟩, ⟨⟨0, 3, 7, 1, 3, 3⟩, ⟨0, 4, 1, 0, 9, 9⟩⟩, ⟨⟨0, 3, 7, 1, 7, 2⟩, ⟨0, 4, 1, 1, 0, 2⟩⟩⟩, ⟨⟨⟨0, 1, 3, 0, 5, 4⟩, ⟨0, 1, 1, 1, 7, 3⟩⟩, ⟨⟨0, 4, 2, 1, 0, 5⟩, ⟨0, 4, 0, 1, 0, 3⟩⟩, ⟨⟨0, 2, 9, 0, 4, 6⟩, ⟨0, 4, 1, 1, 7, 0⟩⟩⟩, ⟨⟨⟨0, 1, 3, 1, 2, 6⟩, ⟨0, 1, 1, 1, 7, 1⟩⟩, ⟨⟨0, 4, 2, 1, 0, 1⟩, ⟨0, 4, 0, 1, 0, 9⟩⟩, ⟨⟨0, 2, 9, 0, 1, 0⟩, ⟨0, 4, 1, 1, 7, 4⟩⟩⟩⟩
private def lw53_7_2 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 1, 4, 1, 2, 1⟩, ⟨0, 1, 9, 1, 1, 6⟩⟩, ⟨⟨0, 2, 4, 1, 2, 4⟩, ⟨0, 1, 8, 1, 2, 2⟩⟩, ⟨⟨0, 2, 4, 1, 2, 5⟩, ⟨0, 1, 8, 1, 2, 3⟩⟩⟩, ⟨⟨⟨0, 4, 4, 1, 0, 0⟩, ⟨0, 4, 7, 0, 4, 2⟩⟩, ⟨⟨0, 4, 8, 1, 0, 5⟩, ⟨0, 4, 6, 0, 4, 5⟩⟩, ⟨⟨0, 4, 8, 1, 0, 1⟩, ⟨0, 4, 6, 0, 4, 2⟩⟩⟩, ⟨⟨⟨0, 3, 4, 0, 5, 5⟩, ⟨0, 3, 6, 1, 4, 3⟩⟩, ⟨⟨0, 4, 9, 1, 0, 5⟩, ⟨0, 5, 1, 0, 5, 2⟩⟩, ⟨⟨0, 4, 9, 1, 0, 1⟩, ⟨0, 5, 1, 0, 3, 6⟩⟩⟩, ⟨⟨⟨0, 3, 7, 0, 5, 4⟩, ⟨0, 3, 5, 1, 4, 5⟩⟩, ⟨⟨0, 4, 9, 1, 4, 4⟩, ⟨0, 5, 0, 0, 5, 2⟩⟩, ⟨⟨0, 2, 0, 1, 2, 7⟩, ⟨0, 5, 2, 0, 2, 7⟩⟩⟩, ⟨⟨⟨0, 3, 7, 1, 2, 6⟩, ⟨0, 3, 5, 1, 4, 3⟩⟩, ⟨⟨0, 4, 9, 0, 3, 1⟩, ⟨0, 5, 0, 0, 3, 6⟩⟩, ⟨⟨0, 2, 0, 1, 7, 5⟩, ⟨0, 5, 2, 0, 3, 0⟩⟩⟩⟩
private def lw53_7_3 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 1, 0, 1, 1, 8⟩, ⟨0, 1, 2, 1, 7, 6⟩⟩, ⟨⟨0, 2, 0, 1, 3, 3⟩, ⟨0, 1, 1, 1, 6, 8⟩⟩, ⟨⟨0, 2, 0, 1, 7, 2⟩, ⟨0, 1, 1, 1, 7, 6⟩⟩⟩, ⟨⟨⟨0, 3, 4, 1, 1, 8⟩, ⟨0, 3, 9, 0, 6, 7⟩⟩, ⟨⟨0, 4, 3, 1, 2, 4⟩, ⟨0, 3, 8, 0, 6, 8⟩⟩, ⟨⟨0, 4, 3, 1, 2, 5⟩, ⟨0, 3, 8, 0, 6, 7⟩⟩⟩, ⟨⟨⟨0, 1, 7, 0, 3, 9⟩, ⟨0, 1, 2, 1, 4, 3⟩⟩, ⟨⟨0, 4, 8, 0, 4, 6⟩, ⟨0, 4, 1, 0, 2, 4⟩⟩, ⟨⟨0, 4, 8, 0, 1, 0⟩, ⟨0, 4, 1, 0, 3, 3⟩⟩⟩, ⟨⟨⟨0, 2, 0, 1, 4, 4⟩, ⟨0, 1, 1, 1, 4, 5⟩⟩, ⟨⟨0, 4, 9, 0, 4, 6⟩, ⟨0, 4, 0, 0, 6, 8⟩⟩, ⟨⟨0, 3, 7, 0, 3, 7⟩, ⟨0, 4, 1, 0, 6, 8⟩⟩⟩, ⟨⟨⟨0, 2, 0, 0, 3, 1⟩, ⟨0, 1, 1, 1, 4, 3⟩⟩, ⟨⟨0, 4, 9, 0, 1, 0⟩, ⟨0, 4, 0, 0, 6, 7⟩⟩, ⟨⟨0, 3, 7, 0, 2, 8⟩, ⟨0, 4, 1, 0, 6, 7⟩⟩⟩⟩
private def lw53_7_4 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 0, 3, 1, 1, 8⟩, ⟨0, 0, 5, 1, 1, 3⟩⟩, ⟨⟨0, 1, 3, 1, 3, 3⟩, ⟨0, 2, 7, 1, 2, 2⟩⟩, ⟨⟨0, 1, 3, 1, 7, 2⟩, ⟨0, 2, 7, 1, 2, 3⟩⟩⟩, ⟨⟨⟨0, 3, 0, 1, 1, 8⟩, ⟨0, 3, 2, 1, 1, 3⟩⟩, ⟨⟨0, 4, 2, 0, 7, 9⟩, ⟨0, 4, 1, 0, 8, 3⟩⟩, ⟨⟨0, 4, 2, 0, 7, 6⟩, ⟨0, 4, 1, 0, 9, 3⟩⟩⟩, ⟨⟨⟨0, 2, 3, 0, 3, 9⟩, ⟨0, 1, 9, 1, 4, 3⟩⟩, ⟨⟨0, 4, 3, 0, 7, 9⟩, ⟨0, 5, 2, 0, 6, 8⟩⟩, ⟨⟨0, 4, 3, 0, 7, 6⟩, ⟨0, 5, 2, 0, 6, 7⟩⟩⟩, ⟨⟨⟨0, 2, 9, 1, 4, 4⟩, ⟨0, 2, 6, 1, 5, 0⟩⟩, ⟨⟨0, 4, 2, 1, 4, 4⟩, ⟨0, 4, 1, 1, 5, 0⟩⟩, ⟨⟨0, 1, 3, 0, 3, 7⟩, ⟨0, 2, 7, 0, 4, 5⟩⟩⟩, ⟨⟨⟨0, 2, 9, 0, 3, 1⟩, ⟨0, 2, 6, 1, 4, 0⟩⟩, ⟨⟨0, 4, 2, 0, 3, 1⟩, ⟨0, 4, 1, 1, 4, 0⟩⟩, ⟨⟨0, 1, 3, 0, 2, 8⟩, ⟨0, 2, 7, 0, 4, 2⟩⟩⟩⟩
private def lw53_7_5 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 0, 6, 1, 1, 9⟩, ⟨0, 0, 4, 1, 1, 7⟩⟩, ⟨⟨0, 1, 3, 1, 1, 9⟩, ⟨0, 2, 5, 1, 2, 8⟩⟩, ⟨⟨0, 2, 8, 1, 1, 9⟩, ⟨0, 2, 6, 1, 1, 4⟩⟩⟩, ⟨⟨⟨0, 0, 6, 1, 1, 9⟩, ⟨0, 3, 1, 1, 1, 7⟩⟩, ⟨⟨0, 3, 7, 1, 1, 9⟩, ⟨0, 4, 0, 1, 2, 8⟩⟩, ⟨⟨0, 1, 3, 1, 2, 7⟩, ⟨0, 4, 1, 1, 1, 4⟩⟩⟩, ⟨⟨⟨0, 2, 4, 1, 4, 4⟩, ⟨0, 1, 8, 1, 4, 5⟩⟩, ⟨⟨0, 4, 8, 1, 1, 9⟩, ⟨0, 5, 0, 0, 6, 8⟩⟩, ⟨⟨0, 3, 7, 1, 2, 7⟩, ⟨0, 5, 1, 0, 6, 8⟩⟩⟩, ⟨⟨⟨0, 2, 0, 0, 2, 0⟩, ⟨0, 2, 5, 1, 5, 0⟩⟩, ⟨⟨0, 4, 3, 1, 4, 4⟩, ⟨0, 4, 0, 1, 5, 0⟩⟩, ⟨⟨0, 2, 0, 0, 3, 7⟩, ⟨0, 2, 5, 0, 4, 5⟩⟩⟩, ⟨⟨⟨0, 0, 6, 1, 4, 2⟩, ⟨0, 2, 7, 0, 5, 7⟩⟩, ⟨⟨0, 0, 6, 1, 4, 2⟩, ⟨0, 4, 1, 1, 7, 7⟩⟩, ⟨⟨0, 2, 4, 0, 3, 7⟩, ⟨0, 2, 6, 0, 4, 5⟩⟩⟩⟩
private def lw53_7_6 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 0, 6, 1, 2, 9⟩, ⟨0, 0, 4, 1, 1, 3⟩⟩, ⟨⟨0, 1, 3, 1, 2, 9⟩, ⟨0, 2, 5, 1, 1, 6⟩⟩, ⟨⟨0, 2, 8, 1, 2, 9⟩, ⟨0, 2, 6, 1, 1, 2⟩⟩⟩, ⟨⟨⟨0, 0, 6, 1, 2, 9⟩, ⟨0, 3, 1, 1, 1, 3⟩⟩, ⟨⟨0, 3, 7, 1, 2, 9⟩, ⟨0, 4, 0, 1, 1, 6⟩⟩, ⟨⟨0, 1, 3, 1, 7, 5⟩, ⟨0, 4, 1, 1, 1, 2⟩⟩⟩, ⟨⟨⟨0, 2, 4, 0, 3, 1⟩, ⟨0, 1, 8, 1, 4, 3⟩⟩, ⟨⟨0, 4, 8, 1, 2, 9⟩, ⟨0, 5, 0, 0, 6, 7⟩⟩, ⟨⟨0, 3, 7, 1, 7, 5⟩, ⟨0, 5, 1, 0, 6, 7⟩⟩⟩, ⟨⟨⟨0, 2, 0, 0, 9, 4⟩, ⟨0, 2, 5, 1, 4, 0⟩⟩, ⟨⟨0, 4, 3, 0, 3, 1⟩, ⟨0, 4, 0, 1, 4, 0⟩⟩, ⟨⟨0, 2, 0, 0, 2, 8⟩, ⟨0, 2, 5, 0, 4, 2⟩⟩⟩, ⟨⟨⟨0, 0, 6, 0, 3, 9⟩, ⟨0, 2, 7, 1, 3, 6⟩⟩, ⟨⟨0, 0, 6, 0, 3, 9⟩, ⟨0, 4, 1, 1, 6, 6⟩⟩, ⟨⟨0, 2, 4, 0, 2, 8⟩, ⟨0, 2, 6, 0, 4, 2⟩⟩⟩⟩
private def lwBlk_7 : Seven (Five (Three LeafWit)) := ⟨lw53_7_0, lw53_7_1, lw53_7_2, lw53_7_3, lw53_7_4, lw53_7_5, lw53_7_6⟩
private def lw53_8_0 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 0, 0, 1, 0, 1⟩, ⟨0, 0, 4, 1, 0, 2⟩⟩, ⟨⟨0, 0, 6, 0, 9, 8⟩, ⟨0, 0, 5, 1, 0, 4⟩⟩, ⟨⟨0, 0, 6, 1, 0, 7⟩, ⟨0, 0, 4, 1, 0, 6⟩⟩⟩, ⟨⟨⟨0, 0, 7, 1, 0, 1⟩, ⟨0, 1, 1, 1, 0, 2⟩⟩, ⟨⟨0, 1, 3, 0, 9, 8⟩, ⟨0, 1, 2, 1, 0, 4⟩⟩, ⟨⟨0, 1, 3, 1, 0, 7⟩, ⟨0, 1, 1, 1, 0, 6⟩⟩⟩, ⟨⟨⟨0, 1, 4, 1, 0, 1⟩, ⟨0, 2, 1, 0, 4, 9⟩⟩, ⟨⟨0, 2, 0, 0, 9, 8⟩, ⟨0, 2, 5, 0, 9, 9⟩⟩, ⟨⟨0, 2, 0, 1, 0, 7⟩, ⟨0, 2, 7, 0, 9, 9⟩⟩⟩, ⟨⟨⟨0, 2, 8, 0, 9, 8⟩, ⟨0, 2, 2, 0, 4, 9⟩⟩, ⟨⟨0, 2, 9, 0, 9, 8⟩, ⟨0, 2, 6, 1, 0, 3⟩⟩, ⟨⟨0, 2, 8, 0, 1, 4⟩, ⟨0, 2, 6, 1, 0, 4⟩⟩⟩, ⟨⟨⟨0, 2, 8, 1, 0, 7⟩, ⟨0, 2, 1, 0, 5, 2⟩⟩, ⟨⟨0, 2, 9, 1, 0, 7⟩, ⟨0, 2, 7, 1, 0, 8⟩⟩, ⟨⟨0, 2, 8, 0, 5, 3⟩, ⟨0, 2, 5, 1, 0, 8⟩⟩⟩⟩
private def lw53_8_1 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 0, 7, 1, 2, 7⟩, ⟨0, 3, 1, 1, 0, 2⟩⟩, ⟨⟨0, 0, 6, 0, 9, 8⟩, ⟨0, 3, 2, 1, 0, 4⟩⟩, ⟨⟨0, 0, 6, 1, 0, 7⟩, ⟨0, 3, 1, 1, 0, 6⟩⟩⟩, ⟨⟨⟨0, 3, 3, 1, 0, 1⟩, ⟨0, 3, 5, 1, 0, 2⟩⟩, ⟨⟨0, 3, 7, 0, 9, 8⟩, ⟨0, 3, 6, 1, 0, 4⟩⟩, ⟨⟨0, 3, 7, 1, 0, 7⟩, ⟨0, 3, 5, 1, 0, 6⟩⟩⟩, ⟨⟨⟨0, 1, 0, 0, 5, 6⟩, ⟨0, 1, 1, 1, 7, 7⟩⟩, ⟨⟨0, 3, 7, 1, 7, 8⟩, ⟨0, 4, 0, 0, 9, 9⟩⟩, ⟨⟨0, 3, 7, 1, 3, 4⟩, ⟨0, 4, 1, 1, 6, 4⟩⟩⟩, ⟨⟨⟨0, 1, 3, 1, 3, 1⟩, ⟨0, 1, 2, 1, 7, 3⟩⟩, ⟨⟨0, 4, 2, 0, 9, 8⟩, ⟨0, 4, 1, 1, 0, 3⟩⟩, ⟨⟨0, 2, 9, 0, 1, 4⟩, ⟨0, 4, 1, 1, 0, 4⟩⟩⟩, ⟨⟨⟨0, 1, 3, 0, 5, 5⟩, ⟨0, 1, 1, 1, 6, 0⟩⟩, ⟨⟨0, 4, 2, 1, 0, 7⟩, ⟨0, 4, 1, 1, 7, 6⟩⟩, ⟨⟨0, 2, 9, 0, 5, 3⟩, ⟨0, 4, 0, 1, 0, 8⟩⟩⟩⟩
private def lw53_8_2 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 1, 4, 1, 2, 7⟩, ⟨0, 1, 8, 1, 2, 8⟩⟩, ⟨⟨0, 2, 4, 1, 2, 9⟩, ⟨0, 1, 9, 1, 2, 2⟩⟩, ⟨⟨0, 2, 4, 1, 3, 0⟩, ⟨0, 1, 8, 1, 1, 3⟩⟩⟩, ⟨⟨⟨0, 4, 4, 1, 0, 1⟩, ⟨0, 4, 6, 0, 4, 9⟩⟩, ⟨⟨0, 4, 8, 0, 9, 8⟩, ⟨0, 4, 7, 0, 4, 9⟩⟩, ⟨⟨0, 4, 8, 1, 0, 7⟩, ⟨0, 4, 6, 0, 5, 2⟩⟩⟩, ⟨⟨⟨0, 3, 4, 0, 5, 6⟩, ⟨0, 3, 5, 0, 5, 8⟩⟩, ⟨⟨0, 4, 9, 0, 9, 8⟩, ⟨0, 5, 0, 0, 4, 2⟩⟩, ⟨⟨0, 4, 9, 1, 0, 7⟩, ⟨0, 5, 2, 0, 3, 4⟩⟩⟩, ⟨⟨⟨0, 3, 7, 1, 3, 1⟩, ⟨0, 3, 6, 0, 5, 8⟩⟩, ⟨⟨0, 4, 9, 0, 3, 9⟩, ⟨0, 5, 1, 0, 4, 2⟩⟩, ⟨⟨0, 2, 0, 1, 7, 9⟩, ⟨0, 5, 1, 0, 3, 0⟩⟩⟩, ⟨⟨⟨0, 3, 7, 0, 5, 5⟩, ⟨0, 3, 5, 1, 5, 0⟩⟩, ⟨⟨0, 4, 9, 1, 4, 9⟩, ⟨0, 5, 2, 0, 3, 6⟩⟩, ⟨⟨0, 2, 0, 1, 1, 5⟩, ⟨0, 5, 0, 0, 3, 0⟩⟩⟩⟩
private def lw53_8_3 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 1, 0, 1, 2, 5⟩, ⟨0, 1, 1, 1, 6, 2⟩⟩, ⟨⟨0, 2, 0, 1, 7, 8⟩, ⟨0, 1, 2, 1, 6, 2⟩⟩, ⟨⟨0, 2, 0, 1, 3, 4⟩, ⟨0, 1, 1, 1, 7, 4⟩⟩⟩, ⟨⟨⟨0, 3, 4, 1, 2, 5⟩, ⟨0, 3, 8, 0, 7, 0⟩⟩, ⟨⟨0, 4, 3, 1, 2, 9⟩, ⟨0, 3, 9, 0, 7, 0⟩⟩, ⟨⟨0, 4, 3, 1, 3, 0⟩, ⟨0, 3, 8, 0, 7, 2⟩⟩⟩, ⟨⟨⟨0, 1, 7, 0, 4, 7⟩, ⟨0, 1, 1, 0, 5, 8⟩⟩, ⟨⟨0, 4, 8, 0, 1, 4⟩, ⟨0, 4, 0, 0, 7, 0⟩⟩, ⟨⟨0, 4, 8, 0, 5, 3⟩, ⟨0, 4, 1, 0, 7, 0⟩⟩⟩, ⟨⟨⟨0, 2, 0, 0, 3, 9⟩, ⟨0, 1, 2, 0, 5, 8⟩⟩, ⟨⟨0, 4, 9, 0, 1, 4⟩, ⟨0, 4, 1, 0, 4, 1⟩⟩, ⟨⟨0, 3, 7, 0, 2, 9⟩, ⟨0, 4, 1, 0, 2, 5⟩⟩⟩, ⟨⟨⟨0, 2, 0, 1, 4, 9⟩, ⟨0, 1, 1, 1, 5, 0⟩⟩, ⟨⟨0, 4, 9, 0, 5, 3⟩, ⟨0, 4, 1, 0, 7, 2⟩⟩, ⟨⟨0, 3, 7, 0, 4, 4⟩, ⟨0, 4, 0, 0, 7, 2⟩⟩⟩⟩
private def lw53_8_4 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 0, 3, 1, 2, 5⟩, ⟨0, 0, 4, 1, 1, 4⟩⟩, ⟨⟨0, 1, 3, 1, 7, 8⟩, ⟨0, 2, 5, 1, 2, 2⟩⟩, ⟨⟨0, 1, 3, 1, 3, 4⟩, ⟨0, 2, 6, 1, 1, 7⟩⟩⟩, ⟨⟨⟨0, 3, 0, 1, 2, 5⟩, ⟨0, 3, 1, 1, 1, 4⟩⟩, ⟨⟨0, 4, 2, 0, 7, 7⟩, ⟨0, 4, 0, 1, 2, 2⟩⟩, ⟨⟨0, 4, 2, 0, 8, 2⟩, ⟨0, 4, 1, 1, 1, 7⟩⟩⟩, ⟨⟨⟨0, 2, 3, 0, 4, 7⟩, ⟨0, 1, 8, 0, 5, 8⟩⟩, ⟨⟨0, 4, 3, 0, 7, 7⟩, ⟨0, 5, 0, 0, 7, 0⟩⟩, ⟨⟨0, 4, 3, 0, 8, 2⟩, ⟨0, 5, 1, 0, 7, 0⟩⟩⟩, ⟨⟨⟨0, 2, 9, 0, 3, 9⟩, ⟨0, 2, 5, 1, 4, 3⟩⟩, ⟨⟨0, 4, 2, 0, 3, 9⟩, ⟨0, 4, 0, 1, 4, 3⟩⟩, ⟨⟨0, 1, 3, 0, 2, 9⟩, ⟨0, 2, 5, 0, 4, 9⟩⟩⟩, ⟨⟨⟨0, 2, 9, 1, 4, 9⟩, ⟨0, 2, 7, 1, 3, 8⟩⟩, ⟨⟨0, 4, 2, 1, 4, 9⟩, ⟨0, 4, 1, 1, 7, 3⟩⟩, ⟨⟨0, 1, 3, 0, 4, 4⟩, ⟨0, 2, 6, 0, 4, 9⟩⟩⟩⟩
private def lw53_8_5 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 0, 6, 1, 1, 8⟩, ⟨0, 0, 5, 1, 1, 4⟩⟩, ⟨⟨0, 1, 3, 1, 1, 8⟩, ⟨0, 2, 7, 1, 2, 8⟩⟩, ⟨⟨0, 2, 8, 1, 1, 8⟩, ⟨0, 2, 7, 1, 1, 3⟩⟩⟩, ⟨⟨⟨0, 0, 6, 1, 1, 8⟩, ⟨0, 3, 2, 1, 1, 4⟩⟩, ⟨⟨0, 3, 7, 1, 1, 8⟩, ⟨0, 4, 1, 0, 7, 3⟩⟩, ⟨⟨0, 1, 3, 1, 7, 9⟩, ⟨0, 4, 1, 0, 8, 9⟩⟩⟩, ⟨⟨⟨0, 2, 4, 0, 3, 9⟩, ⟨0, 1, 9, 0, 5, 8⟩⟩, ⟨⟨0, 4, 8, 1, 1, 8⟩, ⟨0, 5, 2, 0, 7, 0⟩⟩, ⟨⟨0, 3, 7, 1, 7, 9⟩, ⟨0, 5, 2, 0, 7, 2⟩⟩⟩, ⟨⟨⟨0, 2, 0, 0, 8, 4⟩, ⟨0, 2, 6, 1, 4, 3⟩⟩, ⟨⟨0, 4, 3, 0, 3, 9⟩, ⟨0, 4, 1, 1, 4, 3⟩⟩, ⟨⟨0, 2, 0, 0, 2, 9⟩, ⟨0, 2, 7, 0, 4, 9⟩⟩⟩, ⟨⟨⟨0, 0, 6, 0, 4, 7⟩, ⟨0, 2, 6, 1, 3, 6⟩⟩, ⟨⟨0, 0, 6, 0, 4, 7⟩, ⟨0, 4, 1, 1, 3, 6⟩⟩, ⟨⟨0, 2, 4, 0, 2, 9⟩, ⟨0, 2, 7, 0, 5, 2⟩⟩⟩⟩
private def lw53_8_6 : Five (Three LeafWit) := ⟨⟨⟨⟨0, 0, 6, 1, 2, 4⟩, ⟨0, 0, 4, 1, 2, 3⟩⟩, ⟨⟨0, 1, 3, 1, 2, 4⟩, ⟨0, 2, 6, 1, 1, 6⟩⟩, ⟨⟨0, 2, 8, 1, 2, 4⟩, ⟨0, 2, 5, 1, 1, 2⟩⟩⟩, ⟨⟨⟨0, 0, 6, 1, 2, 4⟩, ⟨0, 3, 1, 1, 2, 3⟩⟩, ⟨⟨0, 3, 7, 1, 2, 4⟩, ⟨0, 4, 1, 1, 1, 6⟩⟩, ⟨⟨0, 1, 3, 1, 1, 5⟩, ⟨0, 4, 0, 1, 1, 2⟩⟩⟩, ⟨⟨⟨0, 2, 4, 1, 4, 9⟩, ⟨0, 1, 8, 1, 5, 0⟩⟩, ⟨⟨0, 4, 8, 1, 2, 4⟩, ⟨0, 5, 1, 0, 7, 2⟩⟩, ⟨⟨0, 3, 7, 1, 1, 5⟩, ⟨0, 5, 0, 0, 7, 2⟩⟩⟩, ⟨⟨⟨0, 2, 0, 0, 2, 1⟩, ⟨0, 2, 7, 1, 4, 0⟩⟩, ⟨⟨0, 4, 3, 1, 4, 9⟩, ⟨0, 4, 1, 1, 5, 8⟩⟩, ⟨⟨0, 2, 0, 0, 4, 4⟩, ⟨0, 2, 6, 0, 5, 2⟩⟩⟩, ⟨⟨⟨0, 0, 6, 1, 4, 4⟩, ⟨0, 2, 5, 1, 3, 6⟩⟩, ⟨⟨0, 0, 6, 1, 4, 4⟩, ⟨0, 4, 0, 1, 3, 6⟩⟩, ⟨⟨0, 2, 4, 0, 4, 4⟩, ⟨0, 2, 5, 0, 5, 2⟩⟩⟩⟩
private def lwBlk_8 : Seven (Five (Three LeafWit)) := ⟨lw53_8_0, lw53_8_1, lw53_8_2, lw53_8_3, lw53_8_4, lw53_8_5, lw53_8_6⟩
private def lwGrid : Nine (Seven (Five (Three LeafWit))) := ⟨lwBlk_0, lwBlk_1, lwBlk_2, lwBlk_3, lwBlk_4, lwBlk_5, lwBlk_6, lwBlk_7, lwBlk_8⟩

private def checkMasterRow (mHi : ℕ) : Bool :=
  dig10.all fun mLo =>
    checkStarMatNat 7 ((masterAdjGrid.get mHi).get mLo) ((masterColGrid.get mHi).get mLo)

private lemma checkAllMasterCerts_true :
    ([0, 1, 2, 3] : List ℕ).all checkMasterRow = true := by decide

private lemma mem_mHi {k : ℕ} (hk : k < 4) : k ∈ ([0, 1, 2, 3] : List ℕ) := by
  revert hk; decide +revert

private lemma mem_iHi {k : ℕ} (hk : k < 5) : k ∈ ([0, 1, 2, 3, 4] : List ℕ) := by
  revert hk; decide +revert

private lemma mem_a2 {k : ℕ} (hk : k < 2) : k ∈ ([0, 1] : List ℕ) := by
  revert hk; decide +revert

private lemma mem_tr2 {k : ℕ} (hk : k < 1) : k ∈ ([0] : List ℕ) := by
  revert hk; decide +revert

private lemma masterCert_at {mHi mLo : ℕ} (hHi : mHi < 4) (hLo : mLo < 10) :
    checkStarMatNat 7 ((masterAdjGrid.get mHi).get mLo) ((masterColGrid.get mHi).get mLo) = true := by
  have h1 := List.all_eq_true.mp checkAllMasterCerts_true mHi (mem_mHi hHi)
  exact List.all_eq_true.mp h1 mLo (mem_dig10 hLo)

private lemma checkAllIsoGrid_true :
    (([0, 1, 2, 3, 4] : List ℕ).all fun iHi => dig10.all fun iLo => checkPermNat ((isoGrid.get iHi).get iLo)) = true := by
  decide

private def checkTrEntry (tr : TripleD) : Bool :=
  Nat.ble tr.b.succ 5 && Nat.ble tr.mHi.succ 4 && Nat.ble tr.mLo.succ 10 &&
  Nat.ble tr.iHi.succ 5 && Nat.ble tr.iLo.succ 10 &&
  let iso := (isoGrid.get tr.iHi).get tr.iLo
  let adjMat := (masterAdjGrid.get tr.mHi).get tr.mLo
  (baseEdgesNat tr.b).all fun (u, v) =>
    (adjMat.get (iso.get u)).get (iso.get v) &&
    (adjMat.get (iso.get v)).get (iso.get u)

private lemma checkAllTrGrid_true :
    (([0] : List ℕ).all fun t2 =>
     dig10.all fun t1 => dig10.all fun t0 =>
       checkTrEntry (((trGrid.get t2).get t1).get t0)) = true := by
  decide

private def checkAutEntry (ae : AutEntry) : Bool :=
  Nat.ble ae.b.succ 5 && checkPermNat ae.g &&
  (baseEdgesNat ae.b).all fun (u, v) =>
    baseAdjSymNat ae.b (ae.g.get u) (ae.g.get v)

private lemma checkAllAutGrid_true :
    (([0, 1] : List ℕ).all fun a2 =>
     dig10.all fun a1 => dig10.all fun a0 =>
       checkAutEntry (((autGrid.get a2).get a1).get a0)) = true := by
  decide

private def pickFreeNat (forb : List ℕ) : ℕ :=
  (dig10.find? (fun x => !memNat x forb)).getD 0

private lemma pickFreeNat_lt10 (forb : List ℕ) : pickFreeNat forb < 10 := by
  unfold pickFreeNat
  cases h : dig10.find? (fun x => !memNat x forb) with
  | none => decide
  | some a =>
    simp only [Option.getD_some]
    exact lt_of_mem_dig10 (List.mem_of_find?_eq_some h)

private lemma pickFreeNat_notMem (forb : List ℕ) (hlen : forb.length < 10) :
    pickFreeNat forb ∉ forb := by
  have hex : ∃ x ∈ dig10, (!memNat x forb) = true := by
    by_contra hnone
    push Not at hnone
    have hsub : dig10.toFinset ⊆ forb.toFinset := by
      intro x hx
      rw [List.mem_toFinset] at hx ⊢
      by_contra hnot
      have h1 := hnone x hx
      rw [memNat_eq_false_of_notMem hnot] at h1
      contradiction
    have h10 : dig10.toFinset.card = 10 := by decide
    have hle1 := Finset.card_le_card hsub
    have hle2 := List.toFinset_card_le forb
    omega
  cases hfind : dig10.find? (fun x => !memNat x forb) with
  | none =>
    rcases hex with ⟨x, hx1, hx2⟩
    exact absurd hx2 (List.find?_eq_none.mp hfind x hx1)
  | some a =>
    have ha := List.find?_some hfind
    unfold pickFreeNat
    rw [hfind, Option.getD_some]
    intro hmem
    rw [memNat_iff.mpr hmem] at ha
    contradiction

private def countPosNat (forb : List ℕ) (v : ℕ) : ℕ :=
  (dig10.filter (fun x => !memNat x forb && Nat.ble x.succ v)).length

private def checkEdgesResolvedNat (expectedB : ℕ) (tr : TripleD) (ae : AutEntry)
    (iso : Ten ℕ) (adjMat : Ten (Ten Bool))
    (v0 u1 v1 u2 v2 u3 v3 u4 v4 : ℕ) : Bool :=
  let c0 := iso.get (ae.g.get 0); let cv0 := iso.get (ae.g.get v0)
  let cu1 := iso.get (ae.g.get u1); let cv1 := iso.get (ae.g.get v1)
  let cu2 := iso.get (ae.g.get u2); let cv2 := iso.get (ae.g.get v2)
  let cu3 := iso.get (ae.g.get u3); let cv3 := iso.get (ae.g.get v3)
  let cu4 := iso.get (ae.g.get u4); let cv4 := iso.get (ae.g.get v4)
  Nat.beq tr.b expectedB && Nat.beq ae.b expectedB &&
  (adjMat.get c0).get cv0 &&
  (adjMat.get cu1).get cv1 &&
  (adjMat.get cu2).get cv2 &&
  (adjMat.get cu3).get cv3 &&
  (adjMat.get cu4).get cv4

private def checkOneRefNat (expectedB : ℕ) (r : BaseRef)
    (v0 u1 v1 u2 v2 u3 v3 u4 v4 : ℕ) : Bool :=
  Nat.ble r.tr2.succ 1 && Nat.ble r.tr1.succ 10 && Nat.ble r.tr0.succ 10 &&
  Nat.ble r.a2.succ 2 && Nat.ble r.a1.succ 10 && Nat.ble r.a0.succ 10 &&
  let tr := ((trGrid.get r.tr2).get r.tr1).get r.tr0
  let ae := ((autGrid.get r.a2).get r.a1).get r.a0
  checkEdgesResolvedNat expectedB tr ae
    ((isoGrid.get tr.iHi).get tr.iLo)
    ((masterAdjGrid.get tr.mHi).get tr.mLo)
    v0 u1 v1 u2 v2 u3 v3 u4 v4

private def checkFPFLeafSliceNat (v0 u1 v1 u2 v2 u3 v3 u4 v4 : ℕ)
    (lw : LeafWit) : Bool :=
  let all10 : List ℕ := [0, v0, u1, v1, u2, v2, u3, v3, u4, v4]
  (dig10.all fun x => memNat x all10) &&
  checkOneRefNat 2 lw.r0 v0 u1 v1 u2 v2 u3 v3 u4 v4 &&
  checkOneRefNat 3 lw.r1 v0 u1 v1 u2 v2 u3 v3 u4 v4

private def checkFPF5ForV0Nat (v0 : ℕ) : Bool :=
  memNat v0 [0] ||
    let g0 := lwGrid.get (countPosNat [0] v0)
    let f1 : List ℕ := [v0, 0]
    let u1 := pickFreeNat f1
    dig10.all fun v1 => memNat v1 (u1 :: f1) ||
      let g1 := g0.get (countPosNat (u1 :: f1) v1)
      let f2 : List ℕ := v1 :: u1 :: f1
      let u2 := pickFreeNat f2
      dig10.all fun v2 => memNat v2 (u2 :: f2) ||
        let g2 := g1.get (countPosNat (u2 :: f2) v2)
        let f3 : List ℕ := v2 :: u2 :: f2
        let u3 := pickFreeNat f3
        dig10.all fun v3 => memNat v3 (u3 :: f3) ||
          let lw := g2.get (countPosNat (u3 :: f3) v3)
          let f4 : List ℕ := v3 :: u3 :: f3
          let u4 := pickFreeNat f4
          dig10.all fun v4 => memNat v4 (u4 :: f4) ||
            checkFPFLeafSliceNat v0 u1 v1 u2 v2 u3 v3 u4 v4 lw

private lemma checkFPF5_v0 : checkFPF5ForV0Nat 0 = true := by decide
private lemma checkFPF5_v1 : checkFPF5ForV0Nat 1 = true := by decide
private lemma checkFPF5_v2 : checkFPF5ForV0Nat 2 = true := by decide
private lemma checkFPF5_v3 : checkFPF5ForV0Nat 3 = true := by decide
private lemma checkFPF5_v4 : checkFPF5ForV0Nat 4 = true := by decide
private lemma checkFPF5_v5 : checkFPF5ForV0Nat 5 = true := by decide
private lemma checkFPF5_v6 : checkFPF5ForV0Nat 6 = true := by decide
private lemma checkFPF5_v7 : checkFPF5ForV0Nat 7 = true := by decide
private lemma checkFPF5_v8 : checkFPF5ForV0Nat 8 = true := by decide
private lemma checkFPF5_v9 : checkFPF5ForV0Nat 9 = true := by decide

private lemma checkFPF5ForV0Nat_true {d : ℕ} (hd : d < 10) : checkFPF5ForV0Nat d = true := by
  rcases dig10_cases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkFPF5_v0
  · exact checkFPF5_v1
  · exact checkFPF5_v2
  · exact checkFPF5_v3
  · exact checkFPF5_v4
  · exact checkFPF5_v5
  · exact checkFPF5_v6
  · exact checkFPF5_v7
  · exact checkFPF5_v8
  · exact checkFPF5_v9

private lemma baseGraph_two_neighbors :
    ∀ b : ℕ, b < 5 → ∀ x : Fin 10, ∃ b₁ b₂ : Fin 10,
      b₁ ≠ b₂ ∧ (baseGraph b).Adj x b₁ ∧ (baseGraph b).Adj x b₂ := by
  intro b hb
  have hbc : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 := by omega
  rcases hbc with rfl | rfl | rfl | rfl | rfl <;> decide

private lemma star_seven_of_slice (b : ℕ) (hbs : b = 2 ∨ b = 3)
    (G₁ : SimpleGraph (Fin 10)) [DecidableRel G₁.Adj]
    (hdeg3 : ∀ v : Fin 10, (G₁.neighborFinset v).card ≤ 3)
    (hBG₁ : baseGraph b ≤ G₁) :
    HasStarEdgeColoring G₁ 7 := by
  have hb5 : b < 5 := by rcases hbs with rfl | rfl <;> omega
  rcases exists_fpf_extension_of_two_reg_base hBG₁ hdeg3 (baseGraph_two_neighbors b hb5) with
    ⟨m', hinv, hne, hG₁_edges⟩
  have step_closed : ∀ {forb : List ℕ}
      (hcl : ∀ z : Fin 10, z.val ∈ forb → (m' z).val ∈ forb)
      {u : Fin 10} (hu : u.val ∉ forb),
      (m' u).val ∉ (u.val :: forb) ∧
      (∀ z : Fin 10, z.val ∈ ((m' u).val :: u.val :: forb) →
        (m' z).val ∈ ((m' u).val :: u.val :: forb)) := by
    intro forb hcl u hu
    refine ⟨?_, ?_⟩
    · intro hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with h1 | h2
      · exact hne u (Fin.ext h1)
      · have hmu := hcl (m' u) h2
        rw [hinv u] at hmu
        exact hu hmu
    · intro z hz
      simp only [List.mem_cons] at hz ⊢
      rcases hz with h1 | h2 | hz'
      · have hz_eq : z = m' u := Fin.ext h1
        rw [hz_eq, hinv u]
        exact Or.inr (Or.inl rfl)
      · have hz_eq : z = u := Fin.ext h2
        rw [hz_eq]
        exact Or.inl rfl
      · exact Or.inr (Or.inr (hcl z hz'))
  let z0 : Fin 10 := ⟨0, by decide⟩
  let v0 := m' z0
  have s0 := step_closed (forb := []) (fun _ h => absurd h List.not_mem_nil)
    (u := z0) List.not_mem_nil
  let f1 : List ℕ := [v0.val, 0]
  let u1_nat := pickFreeNat f1
  let u1 : Fin 10 := ⟨u1_nat, pickFreeNat_lt10 f1⟩
  have hu1 : u1.val ∉ f1 := pickFreeNat_notMem f1 (by simp [f1])
  let v1 := m' u1; have s1 := step_closed s0.2 hu1
  let f2 : List ℕ := v1.val :: u1_nat :: f1
  let u2_nat := pickFreeNat f2
  let u2 : Fin 10 := ⟨u2_nat, pickFreeNat_lt10 f2⟩
  have hu2 : u2.val ∉ f2 := pickFreeNat_notMem f2 (by simp [f2, f1])
  let v2 := m' u2; have s2 := step_closed s1.2 hu2
  let f3 : List ℕ := v2.val :: u2_nat :: f2
  let u3_nat := pickFreeNat f3
  let u3 : Fin 10 := ⟨u3_nat, pickFreeNat_lt10 f3⟩
  have hu3 : u3.val ∉ f3 := pickFreeNat_notMem f3 (by simp [f3, f2, f1])
  let v3 := m' u3; have s3 := step_closed s2.2 hu3
  let f4 : List ℕ := v3.val :: u3_nat :: f3
  let u4_nat := pickFreeNat f4
  let u4 : Fin 10 := ⟨u4_nat, pickFreeNat_lt10 f4⟩
  have hu4 : u4.val ∉ f4 := pickFreeNat_notMem f4 (by simp [f4, f3, f2, f1])
  let v4 := m' u4; have s4 := step_closed s3.2 hu4
  have w0 := checkFPF5ForV0Nat_true v0.isLt
  unfold checkFPF5ForV0Nat at w0
  dsimp only at w0
  rw [memNat_eq_false_of_notMem s0.1, Bool.false_or] at w0
  have w1 := List.all_eq_true.mp w0 v1.val (mem_dig10 v1.isLt)
  rw [memNat_eq_false_of_notMem s1.1, Bool.false_or] at w1
  have w2 := List.all_eq_true.mp w1 v2.val (mem_dig10 v2.isLt)
  rw [memNat_eq_false_of_notMem s2.1, Bool.false_or] at w2
  have w3 := List.all_eq_true.mp w2 v3.val (mem_dig10 v3.isLt)
  rw [memNat_eq_false_of_notMem s3.1, Bool.false_or] at w3
  have w4 := List.all_eq_true.mp w3 v4.val (mem_dig10 v4.isLt)
  rw [memNat_eq_false_of_notMem s4.1, Bool.false_or] at w4
  unfold checkFPFLeafSliceNat at w4
  let lw := (((lwGrid.get (countPosNat [0] v0.val)).get (countPosNat (u1_nat :: f1) v1.val)).get
    (countPosNat (u2_nat :: f2) v2.val)).get (countPosNat (u3_nat :: f3) v3.val)
  simp only [Bool.and_eq_true, and_assoc] at w4
  rcases w4 with ⟨hall10, hw0, hw1⟩
  have hm_mem : ∀ x : Fin 10,
      x = z0 ∨ x = v0 ∨ x = u1 ∨ x = v1 ∨ x = u2 ∨ x = v2 ∨ x = u3 ∨ x = v3 ∨ x = u4 ∨ x = v4 := by
    intro x
    have hm := memNat_iff.mp (List.all_eq_true.mp hall10 x.val (mem_dig10 x.isLt))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h | h | h | h | h | h | h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h)))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext h)))))))))
  have hex_ref : ∃ r : BaseRef,
      checkOneRefNat b r v0.val u1_nat v1.val u2_nat v2.val u3_nat v3.val u4_nat v4.val = true := by
    rcases hbs with rfl | rfl
    · exact ⟨lw.r0, hw0⟩
    · exact ⟨lw.r1, hw1⟩
  rcases hex_ref with ⟨r, hbw⟩
  unfold checkOneRefNat checkEdgesResolvedNat at hbw
  dsimp only at hbw
  simp only [Bool.and_eq_true, nat_ble_succ_iff, Nat.beq_eq, and_assoc] at hbw
  rcases hbw with ⟨ht2, ht1, ht0, ha2, ha1, ha0, hb1_eq, hb2_eq, he0, he1, he2, he3, he4⟩
  let tr := ((trGrid.get r.tr2).get r.tr1).get r.tr0
  let ae := ((autGrid.get r.a2).get r.a1).get r.a0
  have ht2_mem : r.tr2 ∈ ([0] : List ℕ) := mem_tr2 ht2
  have ha2_mem : r.a2 ∈ ([0, 1] : List ℕ) := mem_a2 ha2
  have htr_ok := List.all_eq_true.mp
    (List.all_eq_true.mp (List.all_eq_true.mp checkAllTrGrid_true r.tr2 ht2_mem) r.tr1 (mem_dig10 ht1))
    r.tr0 (mem_dig10 ht0)
  unfold checkTrEntry at htr_ok
  dsimp only at htr_ok
  simp only [Bool.and_eq_true, nat_ble_succ_iff, and_assoc] at htr_ok
  rcases htr_ok with ⟨_, hmHi, hmLo, hiHi, hiLo, hbase_iso⟩
  have haut_ok := List.all_eq_true.mp
    (List.all_eq_true.mp (List.all_eq_true.mp checkAllAutGrid_true r.a2 ha2_mem) r.a1 (mem_dig10 ha1))
    r.a0 (mem_dig10 ha0)
  unfold checkAutEntry at haut_ok
  simp only [Bool.and_eq_true, and_assoc] at haut_ok
  rcases haut_ok with ⟨_, hg_perm, hg_aut⟩
  let iso := (isoGrid.get tr.iHi).get tr.iLo
  let adjMat := (masterAdjGrid.get tr.mHi).get tr.mLo
  have hiHi_mem : tr.iHi ∈ ([0, 1, 2, 3, 4] : List ℕ) := mem_iHi hiHi
  have hiso_perm := List.all_eq_true.mp
    (List.all_eq_true.mp checkAllIsoGrid_true tr.iHi hiHi_mem)
    tr.iLo (mem_dig10 hiLo)
  obtain ⟨hg_lt, hg_inj⟩ := checkPermNat_spec hg_perm
  obtain ⟨hiso_lt, hiso_inj⟩ := checkPermNat_spec hiso_perm
  have hmaster_cert := masterCert_at hmHi hmLo
  let comp (x : Fin 10) : ℕ := iso.get (ae.g.get x.val)
  have hcomp_lt : ∀ x : Fin 10, comp x < 10 :=
    fun x => hiso_lt _ (hg_lt _ x.isLt)
  have hcomp_inj : Function.Injective comp := by
    intro x y hxy
    exact Fin.ext (hg_inj _ _ x.isLt y.isLt (hiso_inj _ _ (hg_lt _ x.isLt) (hg_lt _ y.isLt) hxy))
  have hadj_symm : ∀ x y : Fin 10,
      (adjMat.get (comp x)).get (comp y) = (adjMat.get (comp y)).get (comp x) :=
    fun x y => adjMat_symm_of_checkStarMatNat hmaster_cert (hcomp_lt x) (hcomp_lt y)
  refine hasStarEdgeColoring_of_inj_certNat hcomp_lt hcomp_inj hmaster_cert ?_
  intro x y hxy
  rcases hG₁_edges x y hxy with hB | hm
  · have hsym_b := hB.2
    rw [baseAdjSymBool_eq_nat b hb5 x y, ← hb2_eq] at hsym_b
    unfold baseAdjSymNat at hsym_b
    rw [Bool.or_eq_true] at hsym_b
    have hsym_g : baseAdjSymNat ae.b (ae.g.get x.val) (ae.g.get y.val) = true := by
      rcases hsym_b with hmem | hmem
      · exact List.all_eq_true.mp hg_aut (x.val, y.val) (memPairNat_iff.mp hmem)
      · rw [baseAdjSymNat_symm]
        exact List.all_eq_true.mp hg_aut (y.val, x.val) (memPairNat_iff.mp hmem)
    rw [hb2_eq, ← hb1_eq] at hsym_g
    unfold baseAdjSymNat at hsym_g
    rw [Bool.or_eq_true] at hsym_g
    rcases hsym_g with hmem' | hmem'
    · have hp := List.all_eq_true.mp hbase_iso _ (memPairNat_iff.mp hmem')
      rw [Bool.and_eq_true] at hp
      exact hp.1
    · have hp := List.all_eq_true.mp hbase_iso _ (memPairNat_iff.mp hmem')
      rw [Bool.and_eq_true] at hp
      exact hp.2
  · subst hm
    rcases hm_mem x with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact he0
    · rw [hinv z0, hadj_symm v0 z0]; exact he0
    · exact he1
    · rw [hinv u1, hadj_symm v1 u1]; exact he1
    · exact he2
    · rw [hinv u2, hadj_symm v2 u2]; exact he2
    · exact he3
    · rw [hinv u3, hadj_symm v3 u3]; exact he3
    · exact he4
    · rw [hinv u4, hadj_symm v4 u4]; exact he4

private lemma baseGraph_le_of_edges {G : SimpleGraph (Fin 10)} {b : ℕ}
    (hp : ∀ p ∈ baseEdges b, G.Adj p.1 p.2) : baseGraph b ≤ G := by
  intro x y hxy
  have h := hxy.2
  unfold baseAdjSymBool at h
  rw [Bool.or_eq_true] at h
  rcases h with hm | hm
  · exact hp (x, y) (List.mem_of_elem_eq_true hm)
  · exact (hp (y, x) (List.mem_of_elem_eq_true hm)).symm


theorem solution (G : SimpleGraph (Fin 10)) (hsub : IsSubcubic G)
    (hbase :
      (∀ p ∈ ([(0, 1), (0, 6), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (7, 8), (7, 9), (8, 9)] : List (Fin 10 × Fin 10)), G.Adj p.1 p.2) ∨
      (∀ p ∈ ([(0, 1), (0, 5), (1, 2), (2, 3), (3, 4), (4, 5), (6, 7), (6, 9), (7, 8), (8, 9)] : List (Fin 10 × Fin 10)), G.Adj p.1 p.2)) :
    HasStarEdgeColoring G 7 := by
  classical
  have hdeg3 := card_neighborFinset_le_three hsub
  rcases hbase with hA | hB
  · exact star_seven_of_slice 2 (Or.inl rfl) G hdeg3 (baseGraph_le_of_edges hA)
  · exact star_seven_of_slice 3 (Or.inr rfl) G hdeg3 (baseGraph_le_of_edges hB)

