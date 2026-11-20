-- Prove2me | solution 1 for OPG37271.subcubic_ten_with_two_factor_hasStarEdgeColoring_seven
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T07:50:32.391185+00:00
-- url     : https://prove2.me/submissions/461e575c-0264-4067-a534-7a585a4a561b

import Definitions.Def_opg37271_star_edge_coloring
import Theorems.Thm_OPG37271_subcubic_ten_canonical_01
import Theorems.Thm_OPG37271_subcubic_ten_canonical_23
import Theorems.Thm_OPG37271_subcubic_ten_canonical_4
import Mathlib.Data.Finset.Card

set_option autoImplicit false

open OPG37271

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

private def pickFree (forb : List (Fin 10)) : Fin 10 :=
  (fin10List.find? (fun x => !forb.contains x)).getD 0

private lemma pickFree_notMem (forb : List (Fin 10)) (hlen : forb.length < 10) :
    pickFree forb ∉ forb := by
  have hex : ∃ x ∈ fin10List, (!forb.contains x) = true := by
    by_contra hnone
    push Not at hnone
    have hsub : (Finset.univ : Finset (Fin 10)) ⊆ forb.toFinset := by
      intro x _
      rw [List.mem_toFinset]
      by_contra hnot
      have hx := hnone x (mem_fin10List x)
      simp [hnot] at hx
    have h10 : (Finset.univ : Finset (Fin 10)).card = 10 := by decide
    have hle1 := Finset.card_le_card hsub
    have hle2 := List.toFinset_card_le forb
    omega
  cases hfind : fin10List.find? (fun x => !forb.contains x) with
  | none =>
    rcases hex with ⟨x, hx1, hx2⟩
    exact absurd hx2 (List.find?_eq_none.mp hfind x hx1)
  | some a =>
    have ha := List.find?_some hfind
    unfold pickFree
    rw [hfind]
    simp only [Option.getD_some]
    intro hmem
    simp [hmem] at ha

-- Constructive DFS ordering and cycle-type classification of all 2-regular graphs on Fin 10

private noncomputable def dfsNext (T : SimpleGraph (Fin 10)) (vis : List (Fin 10))
    (cur : Fin 10) : Fin 10 :=
  open Classical in
  if h : ∃ y : Fin 10, T.Adj cur y ∧ y ∉ vis then Classical.choose h else pickFree vis

private noncomputable def dfsState (T : SimpleGraph (Fin 10)) : ℕ → List (Fin 10) × Fin 10
  | 0 => ([0], 0)
  | k + 1 =>
    let p := dfsState T k
    let nxt := dfsNext T p.1 p.2
    (nxt :: p.1, nxt)

private lemma dfsState_len (T : SimpleGraph (Fin 10)) :
    ∀ k : ℕ, (dfsState T k).1.length = k + 1
  | 0 => rfl
  | k + 1 => by simp [dfsState, dfsState_len T k]

private lemma dfsState_mem_iff (T : SimpleGraph (Fin 10)) :
    ∀ (k : ℕ) (z : Fin 10), z ∈ (dfsState T k).1 ↔ ∃ m ≤ k, z = (dfsState T m).2
  | 0, z => by
    simp only [dfsState, List.mem_singleton, Nat.le_zero]
    exact ⟨fun h => ⟨0, rfl, h⟩, fun ⟨m, hm, hz⟩ => by subst hm; exact hz⟩
  | k + 1, z => by
    simp only [dfsState, List.mem_cons]
    rw [dfsState_mem_iff T k z]
    constructor
    · rintro (h | ⟨m, hm, rfl⟩)
      · exact ⟨k + 1, le_rfl, h⟩
      · exact ⟨m, Nat.le_succ_of_le hm, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      rcases Nat.eq_or_lt_of_le hm with rfl | hlt
      · exact Or.inl rfl
      · exact Or.inr ⟨m, Nat.lt_succ_iff.mp hlt, rfl⟩

private lemma dfsNext_notMem (T : SimpleGraph (Fin 10)) (vis : List (Fin 10))
    (cur : Fin 10) (hlen : vis.length < 10) :
    dfsNext T vis cur ∉ vis := by
  classical
  unfold dfsNext
  by_cases hex : ∃ y : Fin 10, T.Adj cur y ∧ y ∉ vis
  · simp only [dif_pos hex]
    exact (Classical.choose_spec hex).2
  · simp only [dif_neg hex]
    exact pickFree_notMem vis hlen

private lemma exists_dfs_relabeling (T : SimpleGraph (Fin 10))
    (h2reg : ∀ v : Fin 10, (T.neighborSet v).encard = 2) :
    ∃ π : Fin 10 ≃ Fin 10,
      (∀ (i : Fin 10), ((T.comap π).neighborSet i).encard = 2) ∧
      (∀ (i : Fin 10) (hi : i.val < 9),
        (T.comap π).Adj i ⟨i.val + 1, by omega⟩ ∨
        ∀ j : Fin 10, (T.comap π).Adj i j → j.val < i.val) := by
  classical
  let πFun (i : Fin 10) : Fin 10 := (dfsState T i.val).2
  have hinj : Function.Injective πFun := by
    have hlt_ne : ∀ a b : ℕ, a < b → b < 10 → (dfsState T a).2 ≠ (dfsState T b).2 := by
      intro a b hab hb10 heq
      obtain ⟨k, rfl⟩ : ∃ k, b = k + 1 := ⟨b - 1, by omega⟩
      have hmem : (dfsState T a).2 ∈ (dfsState T k).1 :=
        (dfsState_mem_iff T k _).mpr ⟨a, by omega, rfl⟩
      rw [heq] at hmem
      have hlen : (dfsState T k).1.length < 10 := by rw [dfsState_len]; omega
      exact dfsNext_notMem T (dfsState T k).1 (dfsState T k).2 hlen hmem
    intro i j hij
    rcases lt_trichotomy i.val j.val with hlt | heq | hgt
    · exact absurd hij (hlt_ne i.val j.val hlt j.isLt)
    · exact Fin.ext heq
    · exact absurd hij.symm (hlt_ne j.val i.val hgt i.isLt)
  let π : Fin 10 ≃ Fin 10 := Equiv.ofBijective πFun (Finite.injective_iff_bijective.mp hinj)
  have hπ_apply : ∀ i : Fin 10, π i = (dfsState T i.val).2 := fun _ => rfl
  refine ⟨π, ?_, ?_⟩
  · intro i
    have himg : π '' ((T.comap π).neighborSet i) = T.neighborSet (π i) := by
      ext y
      simp only [Set.mem_image, SimpleGraph.mem_neighborSet, SimpleGraph.comap_adj]
      exact ⟨fun ⟨z, hz, hzy⟩ => hzy ▸ hz,
        fun hy => ⟨π.symm y, by simpa using hy, π.apply_symm_apply y⟩⟩
    rw [← h2reg (π i), ← himg, Set.InjOn.encard_image (fun _ _ _ _ h => π.injective h)]
  · intro i hi
    let vis := (dfsState T i.val).1
    let cur := (dfsState T i.val).2
    by_cases hex : ∃ y : Fin 10, T.Adj cur y ∧ y ∉ vis
    · left
      change T.Adj (π i) (π ⟨i.val + 1, by omega⟩)
      rw [hπ_apply i, hπ_apply ⟨i.val + 1, by omega⟩]
      change T.Adj cur (dfsNext T vis cur)
      unfold dfsNext
      simp only [dif_pos hex]
      exact (Classical.choose_spec hex).1
    · right
      push Not at hex
      intro j hadj
      have hmem : π j ∈ vis := hex (π j) hadj
      rcases (dfsState_mem_iff T i.val (π j)).mp hmem with ⟨m, hm, heq⟩
      have hmj : j = ⟨m, by omega⟩ := π.injective (heq.trans (hπ_apply ⟨m, by omega⟩).symm)
      have hj_ne : j ≠ i := hadj.ne.symm
      have hj_val : j.val = m := congrArg Fin.val hmj
      omega

private def inCycleBlockProp (s w : ℕ) (x z : Fin 10) : Prop :=
  (x.val = s ∧ (z.val = s + 1 ∨ z.val = w)) ∨
  (s < x.val ∧ x.val < w ∧ (z.val + 1 = x.val ∨ z.val = x.val + 1)) ∨
  (x.val = w ∧ (z.val = s ∨ z.val + 1 = w))

private lemma deg2_adj_iff {T' : SimpleGraph (Fin 10)} [DecidableRel T'.Adj]
    (hdeg2 : ∀ i : Fin 10, (T'.neighborFinset i).card = 2)
    {v a b : Fin 10} (hab : a ≠ b) (ha : T'.Adj v a) (hb : T'.Adj v b) :
    ∀ z : Fin 10, T'.Adj v z ↔ z = a ∨ z = b := by
  have hsub : ({a, b} : Finset (Fin 10)) ⊆ T'.neighborFinset v := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rw [SimpleGraph.mem_neighborFinset]
    rcases hz with rfl | rfl <;> assumption
  have hcard : ({a, b} : Finset (Fin 10)).card = 2 := Finset.card_pair hab
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hdeg2 v, hcard])
  intro z
  rw [← SimpleGraph.mem_neighborFinset, ← heq, Finset.mem_insert, Finset.mem_singleton]

private lemma extract_cycle_block {T' : SimpleGraph (Fin 10)} [DecidableRel T'.Adj]
    (hdeg2 : ∀ i : Fin 10, (T'.neighborFinset i).card = 2)
    (hdfs : ∀ (i : Fin 10) (hi : i.val < 9),
      T'.Adj i ⟨i.val + 1, by omega⟩ ∨ ∀ j : Fin 10, T'.Adj i j → j.val < i.val)
    {s : ℕ} (hs10 : s < 10)
    (hsat : ∀ x y : Fin 10, x.val < s → s ≤ y.val → ¬ T'.Adj x y) :
    ∃ w : ℕ, s + 2 ≤ w ∧ w < 10 ∧
      (∀ x z : Fin 10, s ≤ x.val → x.val ≤ w → (T'.Adj x z ↔ inCycleBlockProp s w x z)) ∧
      (∀ x y : Fin 10, x.val < w + 1 → w + 1 ≤ y.val → ¬ T'.Adj x y) := by
  let sFin : Fin 10 := ⟨s, hs10⟩
  have hgt1 : 1 < (T'.neighborFinset sFin).card := by rw [hdeg2 sFin]; decide
  rcases Finset.one_lt_card.mp hgt1 with ⟨a, ha_mem, b, hb_mem, hab⟩
  rw [SimpleGraph.mem_neighborFinset] at ha_mem hb_mem
  have ha_ge : s + 1 ≤ a.val := by
    have hne : a.val ≠ s := fun h => ha_mem.ne.symm (Fin.ext h)
    have hnlt : ¬ a.val < s := fun hlt => hsat a sFin hlt le_rfl ha_mem.symm
    omega
  have hb_ge : s + 1 ≤ b.val := by
    have hne : b.val ≠ s := fun h => hb_mem.ne.symm (Fin.ext h)
    have hnlt : ¬ b.val < s := fun hlt => hsat b sFin hlt le_rfl hb_mem.symm
    omega
  have hs7 : s ≤ 7 := by
    have ha10 := a.isLt; have hb10 := b.isLt
    have habv : a.val ≠ b.val := fun h => hab (Fin.ext h)
    omega
  have hs_next : T'.Adj sFin ⟨s + 1, by omega⟩ := by
    rcases hdfs sFin (by dsimp [sFin]; omega) with h | hall
    · convert h using 2
    · exfalso; have hlt := hall a ha_mem; dsimp [sFin] at hlt; omega
  have hex_w : ∃ wFin : Fin 10, s + 2 ≤ wFin.val ∧ T'.Adj sFin wFin := by
    by_cases ha1 : a.val = s + 1
    · refine ⟨b, ?_, hb_mem⟩
      have habv : a.val ≠ b.val := fun h => hab (Fin.ext h)
      omega
    · exact ⟨a, by omega, ha_mem⟩
  rcases hex_w with ⟨wFin, hw_ge, hw_adj⟩
  let w := wFin.val
  have hw10 : w < 10 := wFin.isLt
  have hs_iff : ∀ z : Fin 10, T'.Adj sFin z ↔ z = ⟨s + 1, by omega⟩ ∨ z = wFin :=
    deg2_adj_iff hdeg2 (fun h => by have hv := congrArg Fin.val h; dsimp at hv; omega) hs_next hw_adj
  have hmid_strong : ∀ (n m : ℕ), m ≤ n → ∀ (hltw : s + 1 + m < w) (z : Fin 10),
      T'.Adj ⟨s + 1 + m, by omega⟩ z ↔
        z = ⟨s + m, by omega⟩ ∨ z = ⟨s + 2 + m, by omega⟩ := by
    intro n
    induction n with
    | zero =>
      intro m hm0 hltw
      have hm_eq : m = 0 := by omega
      subst hm_eq
      let cur : Fin 10 := ⟨s + 1 + 0, by omega⟩
      have hprev : T'.Adj cur ⟨s + 0, by omega⟩ := hs_next.symm
      have honly_prev : ∀ z : Fin 10, z.val < cur.val → T'.Adj cur z → z = ⟨s + 0, by omega⟩ := by
        intro z hzlt hcz
        by_cases hzs : z.val < s
        · exact absurd hcz.symm (hsat z cur hzs (by dsimp [cur]; omega))
        · apply Fin.ext; dsimp [cur] at hzlt ⊢; omega
      have hnext : T'.Adj cur ⟨s + 2 + 0, by omega⟩ := by
        rcases hdfs cur (by dsimp [cur]; omega) with h | hall
        · convert h using 2
        · exfalso
          have hsub1 : T'.neighborFinset cur ⊆ {⟨s + 0, by omega⟩} := by
            intro z hz
            rw [SimpleGraph.mem_neighborFinset] at hz
            rw [Finset.mem_singleton]
            exact honly_prev z (hall z hz) hz
          have hle := Finset.card_le_card hsub1
          rw [hdeg2 cur, Finset.card_singleton] at hle
          omega
      exact deg2_adj_iff hdeg2 (fun h => by have hv := congrArg Fin.val h; dsimp at hv; omega)
        hprev hnext
    | succ d ih =>
      intro m hmd hltw
      rcases Nat.eq_or_lt_of_le hmd with rfl | hmlt
      · let cur : Fin 10 := ⟨s + 1 + (d + 1), by omega⟩
        have hprev_ih := ih d le_rfl (by omega) cur
        have hprev : T'.Adj cur ⟨s + (d + 1), by omega⟩ := by
          have hp : T'.Adj ⟨s + 1 + d, by omega⟩ cur :=
            hprev_ih.mpr (Or.inr (Fin.ext (by dsimp [cur]; omega)))
          convert hp.symm using 2
          omega
        have honly_prev : ∀ z : Fin 10, z.val < cur.val → T'.Adj cur z →
            z = ⟨s + (d + 1), by omega⟩ := by
          intro z hzlt hcz
          by_cases hzs : z.val < s
          · exact absurd hcz.symm (hsat z cur hzs (by dsimp [cur]; omega))
          · by_cases hzeq : z.val = s
            · have hz_s : z = sFin := Fin.ext hzeq
              rw [hz_s] at hcz
              rcases (hs_iff cur).mp hcz.symm with h1 | h2
              · have hv := congrArg Fin.val h1; dsimp [cur] at hv; omega
              · have hv := congrArg Fin.val h2; dsimp [cur] at hv; omega
            · by_cases hzprev : z.val = s + (d + 1)
              · exact Fin.ext hzprev
              · exfalso
                let d' := z.val - (s + 1)
                have hcur_lt : z.val < s + 1 + (d + 1) := hzlt
                have hd'_le : d' ≤ d := by dsimp [d']; omega
                have hd'_ltw : s + 1 + d' < w := by dsimp [d']; omega
                have hz_eq : z = ⟨s + 1 + d', by omega⟩ := Fin.ext (by dsimp [d']; omega)
                rw [hz_eq] at hcz
                rcases (ih d' hd'_le hd'_ltw cur).mp hcz.symm with h1 | h2
                · have hv := congrArg Fin.val h1; dsimp [cur, d'] at hv; omega
                · have hv := congrArg Fin.val h2; dsimp [cur, d'] at hv; omega
        have hnext : T'.Adj cur ⟨s + 2 + (d + 1), by omega⟩ := by
          rcases hdfs cur (by dsimp [cur]; omega) with h | hall
          · convert h using 2
            dsimp [cur]; omega
          · exfalso
            have hsub1 : T'.neighborFinset cur ⊆ {⟨s + (d + 1), by omega⟩} := by
              intro z hz
              rw [SimpleGraph.mem_neighborFinset] at hz
              rw [Finset.mem_singleton]
              exact honly_prev z (hall z hz) hz
            have hle := Finset.card_le_card hsub1
            rw [hdeg2 cur, Finset.card_singleton] at hle
            omega
        exact deg2_adj_iff hdeg2 (fun h => by have hv := congrArg Fin.val h; dsimp at hv; omega)
          hprev hnext
      · exact ih m (Nat.lt_succ_iff.mp hmlt) hltw
  have hmid : ∀ (d : ℕ) (hltw : s + 1 + d < w) (z : Fin 10),
      T'.Adj ⟨s + 1 + d, by omega⟩ z ↔ z = ⟨s + d, by omega⟩ ∨ z = ⟨s + 2 + d, by omega⟩ :=
    fun d => hmid_strong d d le_rfl
  have hw_prev : T'.Adj wFin ⟨w - 1, by omega⟩ := by
    let d := w - 1 - (s + 1)
    have h := (hmid d (by dsimp [d]; omega) wFin).mpr (Or.inr (Fin.ext (by dsimp [d, w]; omega)))
    convert h.symm using 2
    dsimp [d]; omega
  have hw_iff : ∀ z : Fin 10, T'.Adj wFin z ↔ z = sFin ∨ z = ⟨w - 1, by omega⟩ :=
    deg2_adj_iff hdeg2 (fun h => by have hv := congrArg Fin.val h; dsimp [sFin] at hv; omega)
      hw_adj.symm hw_prev
  have hblock : ∀ x z : Fin 10, s ≤ x.val → x.val ≤ w → (T'.Adj x z ↔ inCycleBlockProp s w x z) := by
    intro x z hxs hxw
    unfold inCycleBlockProp
    by_cases hxeq_s : x.val = s
    · have hx_s : x = sFin := Fin.ext hxeq_s
      rw [hx_s, hs_iff z]
      simp only [Fin.ext_iff]
      dsimp [sFin]
      omega
    · by_cases hxeq_w : x.val = w
      · have hx_w : x = wFin := Fin.ext hxeq_w
        rw [hx_w, hw_iff z]
        simp only [Fin.ext_iff]
        dsimp [sFin]
        omega
      · let d := x.val - (s + 1)
        have hx_mid : x = ⟨s + 1 + d, by dsimp [d]; omega⟩ := Fin.ext (by dsimp [d]; omega)
        rw [hx_mid, hmid d (by dsimp [d]; omega) z]
        simp only [Fin.ext_iff]
        dsimp [d]
        omega
  refine ⟨w, hw_ge, hw10, hblock, ?_⟩
  intro x y hxl hyr hxy
  by_cases hxs : x.val < s
  · exact hsat x y hxs (by omega) hxy
  · have hb_xy := (hblock x y (by omega) (by omega)).mp hxy
    unfold inCycleBlockProp at hb_xy
    omega

-- Bool check mapping the 9 DFS cycle partitions to the 5 canonical bases

private def inCycleBlockBool (s w : ℕ) (x z : Fin 10) : Bool :=
  decide (s ≤ x.val) && decide (x.val ≤ w) &&
  ((decide (x.val = s) && (decide (z.val = s + 1) || decide (z.val = w))) ||
   (decide (s < x.val) && decide (x.val < w) &&
     (decide (z.val + 1 = x.val) || decide (z.val = x.val + 1))) ||
   (decide (x.val = w) && (decide (z.val = s) || decide (z.val + 1 = w))))

private def dfsModelAdjBool (w0 w1 w2 : ℕ) (x z : Fin 10) : Bool :=
  inCycleBlockBool 0 w0 x z ||
  (decide (w0 < 9) && inCycleBlockBool (w0 + 1) w1 x z) ||
  (decide (w1 < 9) && inCycleBlockBool (w1 + 1) w2 x z)

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

private def dfsConfigAt : ℕ → ℕ × ℕ × ℕ × ℕ × Ten (Fin 10)
  | 0 => (9, 9, 9, 0, ⟨0, 1, 2, 3, 4, 5, 6, 7, 8, 9⟩)
  | 1 => (4, 9, 9, 1, ⟨0, 1, 2, 3, 4, 5, 6, 7, 8, 9⟩)
  | 2 => (6, 9, 9, 2, ⟨0, 1, 2, 3, 4, 5, 6, 7, 8, 9⟩)
  | 3 => (2, 9, 9, 2, ⟨3, 4, 5, 6, 7, 8, 9, 0, 1, 2⟩)
  | 4 => (5, 9, 9, 3, ⟨0, 1, 2, 3, 4, 5, 6, 7, 8, 9⟩)
  | 5 => (3, 9, 9, 3, ⟨4, 5, 6, 7, 8, 9, 0, 1, 2, 3⟩)
  | 6 => (3, 6, 9, 4, ⟨0, 1, 2, 3, 4, 5, 6, 7, 8, 9⟩)
  | 7 => (2, 6, 9, 4, ⟨3, 4, 5, 6, 0, 1, 2, 7, 8, 9⟩)
  | _ => (2, 5, 9, 4, ⟨6, 7, 8, 9, 0, 1, 2, 3, 4, 5⟩)

private def checkDfsConfigs : Bool :=
  ([0, 1, 2, 3, 4, 5, 6, 7, 8] : List ℕ).all fun idx =>
    let (w0, w1, w2, b, sig) := dfsConfigAt idx
    decide (b < 5) && checkPermTen sig &&
    (baseEdges b).all fun (u, v) =>
      dfsModelAdjBool w0 w1 w2 (sig.getFin u) (sig.getFin v)

private lemma checkDfsConfigs_true : checkDfsConfigs = true := by decide

private lemma dfsConfig_lookup :
    ∀ cfg ∈ ([(9,9,9), (4,9,9), (6,9,9), (2,9,9), (5,9,9),
        (3,9,9), (3,6,9), (2,6,9), (2,5,9)] : List (ℕ × ℕ × ℕ)),
      ∃ idx ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 8] : List ℕ),
        (dfsConfigAt idx).1 = cfg.1 ∧
        (dfsConfigAt idx).2.1 = cfg.2.1 ∧
        (dfsConfigAt idx).2.2.1 = cfg.2.2 := by
  decide

private lemma exists_canonical_base_relabeling (T : SimpleGraph (Fin 10))
    (h2reg : ∀ v : Fin 10, (T.neighborSet v).encard = 2) :
    ∃ (b : ℕ) (φ : Fin 10 ≃ Fin 10), b < 5 ∧ baseGraph b ≤ T.comap φ := by
  classical
  rcases exists_dfs_relabeling T h2reg with ⟨π, hdeg2_enc, hdfs⟩
  let T' := T.comap π
  have hdeg2 : ∀ i : Fin 10, (T'.neighborFinset i).card = 2 :=
    card_neighborFinset_eq_two hdeg2_enc
  rcases extract_cycle_block hdeg2 hdfs (s := 0) (by decide)
      (fun x _ hx => absurd hx (Nat.not_lt_zero _)) with ⟨w0, hw0_ge, hw0_lt, hb0, hsat0⟩
  have finish_cfg : ∀ (w1 w2 : ℕ),
      (∀ x z : Fin 10, dfsModelAdjBool w0 w1 w2 x z = true → T'.Adj x z) →
      (w0, w1, w2) ∈ ([(9,9,9), (4,9,9), (6,9,9), (2,9,9), (5,9,9),
        (3,9,9), (3,6,9), (2,6,9), (2,5,9)] : List (ℕ × ℕ × ℕ)) →
      ∃ (b : ℕ) (φ : Fin 10 ≃ Fin 10), b < 5 ∧ baseGraph b ≤ T.comap φ := by
    intro w1 w2 hmodel hmem
    rcases dfsConfig_lookup (w0, w1, w2) hmem with ⟨idx, hidx_mem, hw0_eq, hw1_eq, hw2_eq⟩
    have hchk := List.all_eq_true.mp checkDfsConfigs_true idx hidx_mem
    dsimp only at hchk
    rcases hcfg : dfsConfigAt idx with ⟨w0', w1', w2', b, sig⟩
    rw [hcfg] at hw0_eq hw1_eq hw2_eq hchk
    dsimp only at hw0_eq hw1_eq hw2_eq
    subst hw0_eq; subst hw1_eq; subst hw2_eq
    rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hchk
    rcases hchk with ⟨⟨hb5, hsig_perm⟩, hedges_ok⟩
    have hsig_inj := injective_of_checkPermTen hsig_perm
    let σ : Fin 10 ≃ Fin 10 := Equiv.ofBijective sig.getFin (Finite.injective_iff_bijective.mp hsig_inj)
    refine ⟨b, σ.trans π, hb5, ?_⟩
    intro x y hxy
    change T'.Adj (sig.getFin x) (sig.getFin y)
    have hsym_b := hxy.2
    unfold baseAdjSymBool at hsym_b
    rw [Bool.or_eq_true] at hsym_b
    rcases hsym_b with hmem_e | hmem_e
    · have he := List.all_eq_true.mp hedges_ok (x, y) (List.mem_of_elem_eq_true hmem_e)
      exact hmodel _ _ he
    · have he := List.all_eq_true.mp hedges_ok (y, x) (List.mem_of_elem_eq_true hmem_e)
      exact (hmodel _ _ he).symm
  have block_imp : ∀ {s w : ℕ}
      (hb : ∀ x z : Fin 10, s ≤ x.val → x.val ≤ w → (T'.Adj x z ↔ inCycleBlockProp s w x z))
      (x z : Fin 10), inCycleBlockBool s w x z = true → T'.Adj x z := by
    intro s w hb x z hbool
    unfold inCycleBlockBool at hbool
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hbool
    refine (hb x z hbool.1.1 hbool.1.2).mpr ?_
    unfold inCycleBlockProp
    rcases hbool.2 with (h1 | ⟨⟨hs, hw⟩, hm⟩) | h3
    · exact Or.inl h1
    · exact Or.inr (Or.inl ⟨hs, hw, hm⟩)
    · exact Or.inr (Or.inr h3)
  by_cases hw0_9 : w0 = 9
  · subst hw0_9
    refine finish_cfg 9 9 ?_ (by simp)
    intro x z hz
    unfold dfsModelAdjBool at hz
    simp only [Nat.lt_irrefl, decide_false, Bool.false_and, Bool.or_false] at hz
    exact block_imp hb0 x z hz
  · rcases extract_cycle_block hdeg2 hdfs (s := w0 + 1) (by omega) hsat0 with
      ⟨w1, hw1_ge, hw1_lt, hb1, hsat1⟩
    by_cases hw1_9 : w1 = 9
    · subst hw1_9
      have hw0_cases : (w0, 9, 9) ∈ ([(9,9,9), (4,9,9), (6,9,9), (2,9,9), (5,9,9),
          (3,9,9), (3,6,9), (2,6,9), (2,5,9)] : List (ℕ × ℕ × ℕ)) := by
        have hc : w0 = 2 ∨ w0 = 3 ∨ w0 = 4 ∨ w0 = 5 ∨ w0 = 6 := by omega
        rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp
      refine finish_cfg 9 9 ?_ hw0_cases
      intro x z hz
      unfold dfsModelAdjBool at hz
      simp only [Nat.lt_irrefl, decide_false, Bool.false_and, Bool.or_false,
        Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hz
      rcases hz with hz0 | ⟨_, hz1⟩
      · exact block_imp hb0 x z hz0
      · exact block_imp hb1 x z hz1
    · rcases extract_cycle_block hdeg2 hdfs (s := w1 + 1) (by omega) hsat1 with
        ⟨w2, hw2_ge, hw2_lt, hb2, hsat2⟩
      have hw2_9 : w2 = 9 := by
        by_contra hne9
        rcases extract_cycle_block hdeg2 hdfs (s := w2 + 1) (by omega) hsat2 with
          ⟨w3, hw3_ge, hw3_lt, _, _⟩
        omega
      subst hw2_9
      have hw_cases : (w0, w1, 9) ∈ ([(9,9,9), (4,9,9), (6,9,9), (2,9,9), (5,9,9),
          (3,9,9), (3,6,9), (2,6,9), (2,5,9)] : List (ℕ × ℕ × ℕ)) := by
        have hc : (w0 = 2 ∧ w1 = 5) ∨ (w0 = 2 ∧ w1 = 6) ∨ (w0 = 3 ∧ w1 = 6) := by omega
        rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
      refine finish_cfg w1 9 ?_ hw_cases
      intro x z hz
      unfold dfsModelAdjBool at hz
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hz
      rcases hz with (hz0 | ⟨_, hz1⟩) | ⟨_, hz2⟩
      · exact block_imp hb0 x z hz0
      · exact block_imp hb1 x z hz1
      · exact block_imp hb2 x z hz2



private lemma isSubcubic_comap (G : SimpleGraph (Fin 10)) (hsub : IsSubcubic G)
    (φ : Fin 10 ≃ Fin 10) : IsSubcubic (G.comap φ) := by
  classical
  intro v
  have hmap : ((G.comap φ).neighborFinset v).map φ.toEmbedding = G.neighborFinset (φ v) := by
    ext y
    simp only [Finset.mem_map, SimpleGraph.mem_neighborFinset, Equiv.coe_toEmbedding]
    refine ⟨fun ⟨z, hz, hzy⟩ => hzy ▸ hz, fun hy => ⟨φ.symm y, ?_, φ.apply_symm_apply y⟩⟩
    change G.Adj (φ v) (φ (φ.symm y))
    simpa using hy
  have hle : ((G.comap φ).neighborFinset v).card ≤ 3 := by
    have h := card_neighborFinset_le_three hsub (φ v)
    rwa [← hmap, Finset.card_map] at h
  have henc : (((G.comap φ).neighborFinset v : Set (Fin 10))).encard ≤ 3 := by
    rw [Set.encard_coe_eq_coe_finsetCard]
    exact Nat.cast_le.mpr hle
  convert henc using 1
  congr 1; ext x; simp

private lemma edges_of_baseGraph_le {b : ℕ} {G₁ : SimpleGraph (Fin 10)}
    (hBG₁ : baseGraph b ≤ G₁) (hno_loop : ∀ p ∈ baseEdges b, p.1 ≠ p.2) :
    ∀ p ∈ baseEdges b, G₁.Adj p.1 p.2 := by
  intro p hp
  apply hBG₁
  refine ⟨hno_loop p hp, ?_⟩
  unfold baseAdjSymBool
  rw [Bool.or_eq_true]
  exact Or.inl (List.elem_eq_true_of_mem hp)

theorem solution
    (G T : SimpleGraph (Fin 10)) (hsub : IsSubcubic G) (hTG : T ≤ G)
    (h2reg : ∀ v : Fin 10, (T.neighborSet v).encard = 2) :
    HasStarEdgeColoring G 7 := by
  classical
  rcases exists_canonical_base_relabeling T h2reg with ⟨b, φ, hb5, hB_le_T⟩
  let G₁ := G.comap φ
  have hBG₁ : baseGraph b ≤ G₁ := fun x y hxy => hTG (hB_le_T hxy)
  have hsub₁ : IsSubcubic G₁ := isSubcubic_comap G hsub φ
  have hc₁_ex : HasStarEdgeColoring G₁ 7 := by
    have hbc : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 := by omega
    rcases hbc with rfl | rfl | rfl | rfl | rfl
    · exact OPG37271.subcubic_ten_canonical_01 G₁ hsub₁
        (Or.inl (edges_of_baseGraph_le hBG₁ (by decide)))
    · exact OPG37271.subcubic_ten_canonical_01 G₁ hsub₁
        (Or.inr (edges_of_baseGraph_le hBG₁ (by decide)))
    · exact OPG37271.subcubic_ten_canonical_23 G₁ hsub₁
        (Or.inl (edges_of_baseGraph_le hBG₁ (by decide)))
    · exact OPG37271.subcubic_ten_canonical_23 G₁ hsub₁
        (Or.inr (edges_of_baseGraph_le hBG₁ (by decide)))
    · exact OPG37271.subcubic_ten_canonical_4 G₁ hsub₁
        (edges_of_baseGraph_le hBG₁ (by decide))
  rcases hc₁_ex with ⟨c₁, hprop₁, hpath₁, hcyc₁⟩
  let c : EdgeColoring G (Fin 7) := fun e =>
    c₁ ⟨Sym2.map φ.symm e.1, by
      rcases e with ⟨⟨x, y⟩, hxy⟩
      change G.Adj (φ (φ.symm x)) (φ (φ.symm y))
      simpa using hxy⟩
  have hc_get : ∀ x y (hxy : G.Adj x y),
      c.get x y hxy = c₁.get (φ.symm x) (φ.symm y) (by change G.Adj (φ (φ.symm x)) (φ (φ.symm y)); simpa using hxy) :=
    fun _ _ _ => rfl
  refine ⟨c, ?_, ?_, ?_⟩
  · intro v u w hvu hvw huw heq
    rw [hc_get, hc_get] at heq
    exact hprop₁ (φ.symm v) (φ.symm u) (φ.symm w) _ _ (fun h => huw (φ.symm.injective h)) heq
  · rintro ⟨v₀, v₁, v₂, v₃, v₄, hnd, h01, h12, h23, h34, hc1, hc2⟩
    rw [hc_get, hc_get] at hc1 hc2
    exact hpath₁ ⟨φ.symm v₀, φ.symm v₁, φ.symm v₂, φ.symm v₃, φ.symm v₄,
      hnd.map φ.symm.injective, _, _, _, _, hc1, hc2⟩
  · rintro ⟨v₀, v₁, v₂, v₃, hnd, h01, h12, h23, h30, hc1, hc2⟩
    rw [hc_get, hc_get] at hc1 hc2
    exact hcyc₁ ⟨φ.symm v₀, φ.symm v₁, φ.symm v₂, φ.symm v₃,
      hnd.map φ.symm.injective, _, _, _, _, hc1, hc2⟩

