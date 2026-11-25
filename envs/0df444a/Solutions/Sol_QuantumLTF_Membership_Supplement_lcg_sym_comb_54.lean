-- Prove2me | solution 1 for QuantumLTF.Membership.Supplement.lcg_sym_comb_54
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-25T03:01:04.351841+00:00
-- url     : https://prove2.me/submissions/8fc56735-8f86-4704-af27-e134b92bbdab

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54Comb

set_option autoImplicit false

namespace Aux_w54_comb

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open QuantumLTF.Membership.Supplement.LcgSym54

namespace Aux_as
lemma card_les (N : ℕ) :
    Fintype.card { s : Fin N → ℕ // IsLES N s } = Nat.factorial N := by
  rw [Fintype.card_congr (lesEquivPi N), Fintype.card_pi]
  simp only [Fintype.card_fin]
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih, Nat.factorial_succ, mul_comm]


lemma permToLES_isLES (N : ℕ) (σ : Equiv.Perm (Fin N)) : IsLES N (permToLES N σ) := by
  intro j
  have hsub : (Finset.univ.filter fun c : Fin N => c < j ∧ σ c < σ j) ⊆
      Finset.univ.filter fun c : Fin N => c < j := by
    intro c hc
    rw [Finset.mem_filter] at hc ⊢
    exact ⟨hc.1, hc.2.1⟩
  have hcard : (Finset.univ.filter fun c : Fin N => c < j).card = j.1 := by
    have himg : (Finset.univ.filter fun c : Fin N => c < j).image Fin.val = Finset.range j.1 := by
      ext x
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
      constructor
      · rintro ⟨c, hc, rfl⟩; exact hc
      · intro hx; exact ⟨⟨x, by omega⟩, hx, rfl⟩
    rw [← Finset.card_image_of_injective _ Fin.val_injective, himg, Finset.card_range]
  exact le_trans (Finset.card_le_card hsub) (le_of_eq hcard)

/-! ### Generic List Helpers -/

lemma pairwise_range_lt (n : ℕ) : (List.range n).Pairwise (· < ·) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  simpa using hij

lemma pairwise_lt_eraseIdx {l : List ℕ} (hl : l.Pairwise (· < ·)) (k : ℕ) :
    (l.eraseIdx k).Pairwise (· < ·) := by
  induction l generalizing k with
  | nil => simp
  | cons a t ih =>
    rw [List.pairwise_cons] at hl
    cases k with
    | zero => simpa using hl.2
    | succ k =>
      simp only [List.eraseIdx_cons_succ, List.pairwise_cons]
      refine ⟨fun y hy => hl.1 y (List.mem_of_mem_eraseIdx hy), ih hl.2 k⟩

lemma pairwise_lt_of_le_of_nodup {α κ : Type*} [LinearOrder κ]
    (key : α → κ) (L : List α)
    (hnd : (L.map key).Nodup)
    (hle : L.Pairwise (fun x y => key x ≤ key y)) :
    L.Pairwise (fun x y => key x < key y) := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    rw [List.pairwise_cons] at hle ⊢
    rw [List.map_cons, List.nodup_cons] at hnd
    refine ⟨fun y hy => ?_, ih hnd.2 hle.2⟩
    have hxy := hle.1 y hy
    have hne : key x ≠ key y := fun h => hnd.1 (h ▸ List.mem_map_of_mem hy)
    exact lt_of_le_of_ne hxy hne

lemma pairwise_le_mergeSort_key {α κ : Type*} [LinearOrder κ]
    (key : α → κ) (L : List α) :
    (L.mergeSort (fun x y => decide (key x ≤ key y))).Pairwise (fun x y => key x ≤ key y) := by
  have hp := List.pairwise_mergeSort (le := fun x y => decide (key x ≤ key y))
    (fun a b c => by
      intro h1 h2
      rw [decide_eq_true_iff] at h1 h2 ⊢
      exact le_trans h1 h2)
    (fun a b => by
      rcases le_total (key a) (key b) with h | h <;> simp [h]) L
  exact hp.imp fun h => decide_eq_true_eq.mp h

lemma perm_eq_of_sorted_of_inj {α κ : Type*} [LinearOrder κ]
    (key : α → κ) (L₁ L₂ : List α)
    (hperm : List.Perm L₁ L₂)
    (h1 : L₁.Pairwise (fun x y => key x ≤ key y))
    (h2 : L₂.Pairwise (fun x y => key x ≤ key y))
    (hinj : ∀ x ∈ L₂, ∀ y ∈ L₂, key x = key y → x = y) :
    L₁ = L₂ := by
  induction L₁ generalizing L₂ with
  | nil =>
    exact (List.perm_nil.mp hperm.symm).symm
  | cons x xs ih =>
    cases L₂ with
    | nil =>
      exact absurd (List.perm_nil.mp hperm) (List.cons_ne_nil x xs)
    | cons y ys =>
      rw [List.pairwise_cons] at h1 h2
      have hx_in : x ∈ y :: ys := hperm.mem_iff.mp List.mem_cons_self
      have hy_in : y ∈ x :: xs := hperm.mem_iff.mpr List.mem_cons_self
      have hkx : key y ≤ key x := by
        rcases List.mem_cons.mp hx_in with rfl | hx_ys
        · exact le_rfl
        · exact h2.1 x hx_ys
      have hky : key x ≤ key y := by
        rcases List.mem_cons.mp hy_in with rfl | hy_xs
        · exact le_rfl
        · exact h1.1 y hy_xs
      have hxy : x = y := hinj x hx_in y List.mem_cons_self (le_antisymm hky hkx)
      subst hxy
      congr 1
      apply ih ys (List.Perm.cons_inv hperm) h1.2 h2.2
      intro a ha b hb hab
      exact hinj a (List.mem_cons_of_mem x ha) b (List.mem_cons_of_mem x hb) hab

/-! ### Reverse Greedy Placement `greedyState` -/


lemma eraseIdx_map {α β : Type*} (f : α → β) (l : List α) (k : ℕ) :
    (l.map f).eraseIdx k = (l.eraseIdx k).map f := by
  induction l generalizing k with
  | nil => simp
  | cons a t ih =>
    cases k with
    | zero => simp
    | succ k => simp [ih k]

lemma getD_map {α β : Type*} (f : α → β) (l : List α) (k : ℕ) (d₀ : α) (d₁ : β)
    (hk : k < l.length) :
    (l.map f).getD k d₁ = f (l.getD k d₀) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  simp [hk]

lemma greedyState_map (s : ℕ → ℕ) (lo len : ℕ) (f : ℕ → ℕ) (I : List ℕ)
    (hI : I.length = lo + len) (hs : ∀ c, lo ≤ c → c < lo + len → s c ≤ c) :
    greedyState s lo len (I.map f) =
      ((greedyState s lo len I).1.map (fun p => (f p.1, p.2)),
       (greedyState s lo len I).2.map f) := by
  induction len generalizing I with
  | zero => rfl
  | succ len ih =>
    have hlt : s (lo + len) < I.length := by
      have := hs (lo + len) (by omega) (by omega)
      omega
    have hlen_erase : (I.eraseIdx (s (lo + len))).length = lo + len := by
      rw [List.length_eraseIdx_of_lt hlt, hI]
      omega
    have ih' := ih (I.eraseIdx (s (lo + len))) hlen_erase (fun c hc1 hc2 => hs c hc1 (by omega))
    dsimp only [greedyState]
    rw [getD_map f I (s (lo + len)) 0 0 hlt, eraseIdx_map, ih']
    rfl

lemma range'_concat_one (lo len : ℕ) :
    List.range' lo (len + 1) = List.range' lo len ++ [lo + len] := by
  induction len generalizing lo with
  | zero => simp
  | succ len ih =>
    rw [List.range'_succ, ih (lo + 1), List.range'_succ]
    simp [Nat.add_left_comm, Nat.add_comm]

private lemma length_filter_add_not {α : Type*} (p : α → Bool) (l : List α) :
    (l.filter p).length + (l.filter (fun x => !p x)).length = l.length := by
  induction l with
  | nil => simp
  | cons x xs ih => cases h : p x <;> simp [h] <;> omega

private lemma length_filter_map_comm {α β : Type*} (l : List α) (f : α → β) (p : β → Bool) :
    (l.filter (fun x => p (f x))).length = ((l.map f).filter p).length := by
  induction l with
  | nil => simp
  | cons x xs ih => cases h : p (f x) <;> simp [h, ih]

lemma greedyState_add (s : ℕ → ℕ) (lo a b : ℕ) (U : List ℕ) :
    greedyState s lo (a + b) U =
      let top := greedyState s (lo + a) b U
      let bot := greedyState s lo a top.2
      (top.1 ++ bot.1, bot.2) := by
  induction b generalizing U with
  | zero => rfl
  | succ b ih =>
    have hadd : lo + (a + b) = (lo + a) + b := by omega
    have hadd1 : a + (b + 1) = (a + b) + 1 := by omega
    rw [hadd1]
    dsimp only [greedyState]
    rw [hadd, ih (U.eraseIdx (s (lo + a + b)))]
    rfl

lemma take_eraseIdx_of_le {α : Type*} (l : List α) (a idx : ℕ) (h : a ≤ idx) :
    (l.eraseIdx idx).take a = l.take a := by
  induction l generalizing a idx with
  | nil => simp
  | cons x xs ih =>
    cases a with
    | zero => simp
    | succ a =>
      cases idx with
      | zero => omega
      | succ idx =>
        simp only [List.eraseIdx_cons_succ, List.take_succ_cons]
        congr 1
        exact ih a idx (by omega)

lemma drop_eraseIdx_of_le {α : Type*} (l : List α) (a idx : ℕ) (h : a ≤ idx) :
    (l.eraseIdx idx).drop a = (l.drop a).eraseIdx (idx - a) := by
  induction l generalizing a idx with
  | nil => simp
  | cons x xs ih =>
    cases a with
    | zero => simp
    | succ a =>
      cases idx with
      | zero => omega
      | succ idx =>
        simp only [List.eraseIdx_cons_succ, List.drop_succ_cons]
        have hsub : idx + 1 - (a + 1) = idx - a := by omega
        rw [hsub]
        exact ih a idx (by omega)

/-- Core invariants of `greedyState` on any strictly increasing row pool `U` of length `lo + len`. -/
lemma greedyState_props (s : ℕ → ℕ) (lo len : ℕ) (U : List ℕ)
    (hU_pw : U.Pairwise (· < ·)) (hU_len : U.length = lo + len)
    (hs : ∀ c, lo ≤ c → c < lo + len → s c ≤ c) :
    let res := greedyState s lo len U
    res.1.length = len ∧
    res.2.length = lo ∧
    res.2.Pairwise (· < ·) ∧
    (∀ x, x ∈ U ↔ (∃ c, (x, c) ∈ res.1) ∨ x ∈ res.2) ∧
    (res.1.map Prod.fst).Nodup ∧
    (∀ p ∈ res.1, p.1 ∈ U ∧ p.1 ∉ res.2 ∧ lo ≤ p.2 ∧ p.2 < lo + len) ∧
    (∀ c, lo ≤ c → c < lo + len → ∃ r, (r, c) ∈ res.1) ∧
    (∀ p₁ ∈ res.1, ∀ p₂ ∈ res.1, p₁.2 = p₂.2 → p₁ = p₂) ∧
    (res.1.map Prod.snd = (List.range' lo len).reverse) ∧
    (∀ c, lo ≤ c → c < lo + len → ∀ r, (r, c) ∈ res.1 →
      s c = ((res.1.filter (fun p => decide (p.2 < c ∧ p.1 < r))).length +
             (res.2.filter (fun x => decide (x < r))).length)) := by
  induction len generalizing U with
  | zero =>
    refine ⟨rfl, by simpa [greedyState] using hU_len, hU_pw, fun x => by simp [greedyState],
      by simp [greedyState], fun p hp => by simp [greedyState] at hp,
      fun c hc1 hc2 => by omega, fun p₁ hp₁ => by simp [greedyState] at hp₁,
      by simp [greedyState], fun c hc1 hc2 => by omega⟩
  | succ len ih =>
    set c₀ := lo + len
    set idx := s c₀
    have hidx : idx < U.length := by
      have := hs c₀ (by omega) (by omega)
      omega
    set r₀ := U[idx]
    have hr₀_eq : U.getD idx 0 = r₀ := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx]
      rfl
    set U' := U.eraseIdx idx
    have hU'_pw : U'.Pairwise (· < ·) := pairwise_lt_eraseIdx hU_pw idx
    have hU'_len : U'.length = lo + len := by
      rw [List.length_eraseIdx_of_lt hidx, hU_len]; omega
    rcases ih U' hU'_pw hU'_len (fun c hc1 hc2 => hs c hc1 (by omega)) with
      ⟨hlen1, hlen2, hpw2, hmem_split, hnd1, hmem1, hex_c, huniq_c, hsnd_eq, hcount⟩
    set rest := greedyState s lo len U'
    have hres1 : (greedyState s lo (len + 1) U).1 = (r₀, c₀) :: rest.1 := by
      dsimp only [greedyState]; rw [hr₀_eq]
    have hres2 : (greedyState s lo (len + 1) U).2 = rest.2 := rfl
    have hr₀_mem : r₀ ∈ U := List.getElem_mem hidx
    have hr₀_not_U' : r₀ ∉ U' := by
      intro hmem
      rcases List.getElem_of_mem hmem with ⟨j, hj, hj_eq⟩
      have hU_nd : U.Nodup := hU_pw.nodup
      by_cases hji : j < idx
      · have hj' : j < U'.length := hj
        have hg := @List.getElem_eraseIdx_of_lt _ U idx j hj' hji
        rw [hg] at hj_eq
        have hjU : j < U.length := by omega
        have heq : (⟨j, hjU⟩ : Fin U.length) = ⟨idx, hidx⟩ :=
          (List.nodup_iff_injective_getElem.mp hU_nd) hj_eq
        have hv := congrArg Fin.val heq
        dsimp only at hv
        omega
      · have hle : idx ≤ j := Nat.le_of_not_lt hji
        have hj' : j < U'.length := hj
        have hj1 : j + 1 < U.length := by
          rw [List.length_eraseIdx_of_lt hidx] at hj; omega
        have hg := @List.getElem_eraseIdx_of_ge _ U idx j hj' hle
        rw [hg] at hj_eq
        have heq : (⟨j + 1, hj1⟩ : Fin U.length) = ⟨idx, hidx⟩ :=
          (List.nodup_iff_injective_getElem.mp hU_nd) hj_eq
        have hv := congrArg Fin.val heq
        dsimp only at hv
        omega
    have hU_mem_iff : ∀ x, x ∈ U ↔ x = r₀ ∨ x ∈ U' := by
      intro x
      constructor
      · intro hx
        rcases List.getElem_of_mem hx with ⟨j, hj, rfl⟩
        rcases lt_trichotomy j idx with hlt | rfl | hgt
        · right
          have hj' : j < U'.length := by rw [List.length_eraseIdx_of_lt hidx]; omega
          refine List.mem_of_getElem (i := j) (h := hj') ?_
          exact @List.getElem_eraseIdx_of_lt _ U idx j hj' hlt
        · left; rfl
        · right
          have hj' : j - 1 < U'.length := by rw [List.length_eraseIdx_of_lt hidx]; omega
          refine List.mem_of_getElem (i := j - 1) (h := hj') ?_
          have hg := @List.getElem_eraseIdx_of_ge _ U idx (j - 1) hj' (by omega)
          rw [hg]
          congr 1; omega
      · rintro (rfl | hx)
        · exact hr₀_mem
        · exact List.mem_of_mem_eraseIdx hx
    have hU'_lt_r₀ : (U'.filter (fun x => decide (x < r₀))).length = idx := by
      have htake : U'.filter (fun x => decide (x < r₀)) = U.take idx := by
        have hU'_eq : U' = U.take idx ++ U.drop (idx + 1) := List.eraseIdx_eq_take_drop_succ U idx
        rw [hU'_eq, List.filter_append]
        have hL : (U.take idx).filter (fun x => decide (x < r₀)) = U.take idx := by
          rw [List.filter_eq_self]
          intro x hx
          simp only [decide_eq_true_eq]
          rcases List.getElem_of_mem hx with ⟨j, hj, rfl⟩
          have hj_len : j < idx := by have := List.length_take_le idx U; omega
          rw [List.getElem_take]
          exact (List.pairwise_iff_getElem.mp hU_pw) j idx (by omega) hidx hj_len
        have hR : (U.drop (idx + 1)).filter (fun x => decide (x < r₀)) = [] := by
          rw [List.filter_eq_nil_iff]
          intro x hx
          simp only [decide_eq_true_eq]
          rcases List.getElem_of_mem hx with ⟨j, hj, rfl⟩
          have hlen_d : (U.drop (idx + 1)).length = U.length - (idx + 1) := List.length_drop
          rw [List.getElem_drop]
          exact not_lt_of_gt ((List.pairwise_iff_getElem.mp hU_pw) idx (idx + 1 + j) hidx (by omega) (by omega))
        rw [hL, hR, List.append_nil]
      rw [htake, List.length_take_of_le (le_of_lt hidx)]
    dsimp only
    rw [hres1, hres2]
    refine ⟨by simp [hlen1], hlen2, hpw2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x
      rw [hU_mem_iff x, hmem_split x]
      constructor
      · rintro (rfl | ⟨c, hc⟩ | hx)
        · left; exact ⟨c₀, List.mem_cons_self⟩
        · left; exact ⟨c, List.mem_cons_of_mem _ hc⟩
        · right; exact hx
      · rintro (⟨c, hc⟩ | hx)
        · rcases List.mem_cons.mp hc with h | hc'
          · left; exact congrArg Prod.fst h
          · right; left; exact ⟨c, hc'⟩
        · right; right; exact hx
    · rw [List.map_cons, List.nodup_cons]
      refine ⟨?_, hnd1⟩
      intro hr_in
      rw [List.mem_map] at hr_in
      rcases hr_in with ⟨p, hp, hp_fst⟩
      dsimp only at hp_fst
      rw [← hp_fst] at hr₀_not_U'
      exact hr₀_not_U' (hmem1 p hp).1
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp'
      · refine ⟨hr₀_mem, fun h => hr₀_not_U' ((hmem_split r₀).mpr (Or.inr h)), by omega, by omega⟩
      · have hp1 := hmem1 p hp'
        exact ⟨List.mem_of_mem_eraseIdx hp1.1, hp1.2.1, by omega, by omega⟩
    · intro c hc1 hc2
      by_cases hc : c = c₀
      · subst hc; exact ⟨r₀, List.mem_cons_self⟩
      · obtain ⟨r, hr⟩ := hex_c c hc1 (by omega)
        exact ⟨r, List.mem_cons_of_mem _ hr⟩
    · intro p₁ hp₁ p₂ hp₂ heq
      rcases List.mem_cons.mp hp₁ with rfl | hp₁' <;>
      rcases List.mem_cons.mp hp₂ with rfl | hp₂'
      · rfl
      · exfalso; have := (hmem1 p₂ hp₂').2.2.2; dsimp [c₀] at heq; omega
      · exfalso; have := (hmem1 p₁ hp₁').2.2.2; dsimp [c₀] at heq; omega
      · exact huniq_c p₁ hp₁' p₂ hp₂' heq
    · rw [List.map_cons, hsnd_eq, range'_concat_one, List.reverse_append]
      rfl
    · intro c hc1 hc2 r hr
      by_cases hc : c = c₀
      · subst hc
        have hr_eq : (r, c₀) = (r₀, c₀) := by
          rcases List.mem_cons.mp hr with h | hr'
          · exact h
          · exfalso; have := (hmem1 (r, c₀) hr').2.2.2; dsimp [c₀] at this; omega
        have hr_r₀ : r = r₀ := congrArg Prod.fst hr_eq
        subst hr_r₀
        have hpart : (rest.1.filter (fun p => decide (p.2 < c₀ ∧ p.1 < r₀))).length +
            (rest.2.filter (fun x => decide (x < r₀))).length =
            (U'.filter (fun x => decide (x < r₀))).length := by
          have hfil1 : rest.1.filter (fun p => decide (p.2 < c₀ ∧ p.1 < r₀)) =
              rest.1.filter (fun p => decide (p.1 < r₀)) := by
            refine List.filter_congr fun p hp => ?_
            have hlt_c := (hmem1 p hp).2.2.2
            simp [hlt_c, c₀]
          rw [hfil1]
          have hmap_len : (rest.1.filter (fun p => decide (p.1 < r₀))).length =
              ((rest.1.map Prod.fst).filter (fun x => decide (x < r₀))).length := by
            rw [List.filter_map, List.length_map]; rfl
          rw [hmap_len]
          have hnd_lhs1 : ((rest.1.map Prod.fst).filter (fun x => decide (x < r₀))).Nodup :=
            hnd1.filter _
          have hnd_lhs2 : (rest.2.filter (fun x => decide (x < r₀))).Nodup :=
            hpw2.nodup.filter _
          have hnd_rhs : (U'.filter (fun x => decide (x < r₀))).Nodup :=
            hU'_pw.nodup.filter _
          rw [← List.toFinset_card_of_nodup hnd_lhs1,
              ← List.toFinset_card_of_nodup hnd_lhs2,
              ← List.toFinset_card_of_nodup hnd_rhs]
          have hdisj : Disjoint
              ((rest.1.map Prod.fst).filter (fun x => decide (x < r₀))).toFinset
              (rest.2.filter (fun x => decide (x < r₀))).toFinset := by
            rw [Finset.disjoint_left]
            intro x hx1 hx2
            simp only [List.mem_toFinset, List.mem_filter, List.mem_map, decide_eq_true_eq] at hx1 hx2
            rcases hx1.1 with ⟨p, hp, rfl⟩
            exact (hmem1 p hp).2.1 hx2.1
          rw [← Finset.card_union_of_disjoint hdisj]
          congr 1
          ext x
          simp only [Finset.mem_union, List.mem_toFinset, List.mem_filter, List.mem_map,
            decide_eq_true_eq]
          rw [hmem_split x]
          constructor
          · rintro (⟨⟨p, hp, rfl⟩, hx⟩ | ⟨hx1, hx2⟩)
            · exact ⟨Or.inl ⟨p.2, by simpa using hp⟩, hx⟩
            · exact ⟨Or.inr hx1, hx2⟩
          · rintro ⟨⟨c, hc⟩ | hx1, hx2⟩
            · left; exact ⟨⟨(x, c), hc, rfl⟩, hx2⟩
            · right; exact ⟨hx1, hx2⟩
        rw [List.filter_cons]
        simp only [lt_irrefl, and_false, decide_false, Bool.false_eq_true, ↓reduceIte]
        rw [hpart, hU'_lt_r₀]
      · rcases List.mem_cons.mp hr with h | hr'
        · exfalso; exact hc (congrArg Prod.snd h)
        · rw [List.filter_cons]
          have hnot_lt : ¬ (c₀ < c ∧ r₀ < r) := by
            rintro ⟨h1, _⟩; dsimp [c₀] at h1; omega
          simp only [decide_eq_false hnot_lt, Bool.false_eq_true, ↓reduceIte]
          exact hcount c hc1 (by omega) r hr'

/-- Block-preservation property: if `∀ c ∈ [lo, lo + len), lo ≤ s c ≤ c`, then
the first `lo` rows of `U` are untouched and all placed rows come from `U.drop lo`. -/
lemma greedyState_rem_take (s : ℕ → ℕ) (lo len : ℕ) (U : List ℕ)
    (hU_len : U.length = lo + len)
    (hs_lo : ∀ c, lo ≤ c → c < lo + len → lo ≤ s c)
    (hs_hi : ∀ c, lo ≤ c → c < lo + len → s c ≤ c) :
    (greedyState s lo len U).2.take lo = U.take lo ∧
    ∀ p ∈ (greedyState s lo len U).1, p.1 ∈ U.drop lo := by
  induction len generalizing U with
  | zero => simp [greedyState]
  | succ len ih =>
    have hs_top_lo := hs_lo (lo + len) (by omega) (by omega)
    have hs_top_hi := hs_hi (lo + len) (by omega) (by omega)
    have hidx : s (lo + len) < U.length := by omega
    have hU'_len : (U.eraseIdx (s (lo + len))).length = lo + len := by
      rw [List.length_eraseIdx_of_lt hidx, hU_len]; omega
    rcases ih (U.eraseIdx (s (lo + len))) hU'_len
      (fun c hc1 hc2 => hs_lo c hc1 (by omega))
      (fun c hc1 hc2 => hs_hi c hc1 (by omega)) with ⟨htake, hdrop⟩
    dsimp only [greedyState]
    refine ⟨?_, ?_⟩
    · rw [htake, take_eraseIdx_of_le U lo (s (lo + len)) hs_top_lo]
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp'
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx]
        dsimp
        have hsub : s (lo + len) - lo < (U.drop lo).length := by
          rw [List.length_drop]; omega
        have hget : U[s (lo + len)] = (U.drop lo)[s (lo + len) - lo] := by
          rw [List.getElem_drop]
          congr 1; omega
        rw [hget]
        exact List.getElem_mem hsub
      · have hp'' := hdrop p hp'
        rw [drop_eraseIdx_of_le U lo (s (lo + len)) hs_top_lo] at hp''
        exact List.mem_of_mem_eraseIdx hp''

lemma greedyState_rem_eq_take (s : ℕ → ℕ) (lo len : ℕ) (U : List ℕ)
    (hU_pw : U.Pairwise (· < ·)) (hU_len : U.length = lo + len)
    (hs_lo : ∀ c, lo ≤ c → c < lo + len → lo ≤ s c)
    (hs_hi : ∀ c, lo ≤ c → c < lo + len → s c ≤ c) :
    (greedyState s lo len U).2 = U.take lo := by
  have hlen := (greedyState_props s lo len U hU_pw hU_len hs_hi).2.1
  have htake := (greedyState_rem_take s lo len U hU_len hs_lo hs_hi).1
  simpa [List.take_of_length_le (le_of_eq hlen)] using htake

/-! ### `lesToPerm` and the Bijection `{s // IsLES N s} ≃ Equiv.Perm (Fin N)` -/


/-- Inverse map `LES → Equiv.Perm (Fin N)` sending `c` to the unique `r` with `(r, c) ∈ pairs`. -/
def lesToPermFun (N : ℕ) (s : Fin N → ℕ) (hs : IsLES N s) : Fin N → Fin N := fun c =>
  let pairs := (greedyState (sExt s) 0 N (List.range N)).1
  have hprops := greedyState_props (sExt s) 0 N (List.range N) (pairwise_range_lt N)
    (by simp) (fun j _ hj => by
      have hjN : j < N := by omega
      simpa [sExt, hjN] using hs ⟨j, hjN⟩)
  have hrev_len : pairs.reverse.length = N := by
    rw [List.length_reverse]; exact hprops.1
  have hp_mem : pairs.reverse[c.1]'(by omega) ∈ pairs :=
    List.mem_reverse.mp (List.getElem_mem _)
  have hr_mem : (pairs.reverse[c.1]'(by omega)).1 ∈ List.range N :=
    (hprops.2.2.2.2.2.1 _ hp_mem).1
  ⟨(pairs.reverse[c.1]'(by omega)).1, List.mem_range.mp hr_mem⟩

lemma lesToPermFun_spec (N : ℕ) (s : Fin N → ℕ) (hs : IsLES N s) (c : Fin N) :
    (lesToPermFun N s hs c |>.1, c.1) ∈ (greedyState (sExt s) 0 N (List.range N)).1 := by
  have hprops := greedyState_props (sExt s) 0 N (List.range N) (pairwise_range_lt N)
    (by simp) (fun j _ hj => by
      have hjN : j < N := by omega
      simpa [sExt, hjN] using hs ⟨j, hjN⟩)
  have hlen : (greedyState (sExt s) 0 N (List.range N)).1.length = N := hprops.1
  have hsnd : ((greedyState (sExt s) 0 N (List.range N)).1.reverse.map Prod.snd) = List.range N := by
    rw [List.map_reverse, hprops.2.2.2.2.2.2.2.2.1, List.reverse_reverse, ← List.range_eq_range']
  have hc_lt : c.1 < (greedyState (sExt s) 0 N (List.range N)).1.reverse.length := by
    rw [List.length_reverse, hlen]; exact c.isLt
  have hsnd_c : ((greedyState (sExt s) 0 N (List.range N)).1.reverse[c.1]'hc_lt).2 = c.1 := by
    have hget : ((greedyState (sExt s) 0 N (List.range N)).1.reverse.map Prod.snd)[c.1]'
        (by rw [List.length_map]; exact hc_lt) = (List.range N)[c.1]'(by simp) := by
      congr 1
    simpa using hget
  have hmem : (greedyState (sExt s) 0 N (List.range N)).1.reverse[c.1]'hc_lt ∈
      (greedyState (sExt s) 0 N (List.range N)).1 :=
    List.mem_reverse.mp (List.getElem_mem hc_lt)
  change ((greedyState (sExt s) 0 N (List.range N)).1.reverse[c.1]'hc_lt |>.1, c.1) ∈
      (greedyState (sExt s) 0 N (List.range N)).1
  have hp_eq : (greedyState (sExt s) 0 N (List.range N)).1.reverse[c.1]'hc_lt =
      ((greedyState (sExt s) 0 N (List.range N)).1.reverse[c.1]'hc_lt |>.1, c.1) :=
    Prod.ext rfl hsnd_c
  rw [← hp_eq]
  exact hmem

lemma lesToPermFun_inj (N : ℕ) (s : Fin N → ℕ) (hs : IsLES N s) :
    Function.Injective (lesToPermFun N s hs) := by
  intro c₁ c₂ heq
  have hprops := greedyState_props (sExt s) 0 N (List.range N) (pairwise_range_lt N)
    (by simp) (fun j _ hj => by
      have hjN : j < N := by omega
      simpa [sExt, hjN] using hs ⟨j, hjN⟩)
  have hp1 := lesToPermFun_spec N s hs c₁
  have hp2 := lesToPermFun_spec N s hs c₂
  have hfst : (lesToPermFun N s hs c₁).1 = (lesToPermFun N s hs c₂).1 := congrArg Fin.val heq
  have hp_eq : (lesToPermFun N s hs c₁ |>.1, c₁.1) = (lesToPermFun N s hs c₂ |>.1, c₂.1) := by
    rcases List.getElem_of_mem hp1 with ⟨i1, hi1, h_i1⟩
    rcases List.getElem_of_mem hp2 with ⟨i2, hi2, h_i2⟩
    have hi12 : i1 = i2 := by
      have hnd := List.nodup_iff_injective_getElem.mp hprops.2.2.2.2.1
      have hi1' : i1 < ((greedyState (sExt s) 0 N (List.range N)).1.map Prod.fst).length := by simp [hi1]
      have hi2' : i2 < ((greedyState (sExt s) 0 N (List.range N)).1.map Prod.fst).length := by simp [hi2]
      have heq_f : ((greedyState (sExt s) 0 N (List.range N)).1.map Prod.fst)[i1]'hi1' =
          ((greedyState (sExt s) 0 N (List.range N)).1.map Prod.fst)[i2]'hi2' := by
        simp only [List.getElem_map]
        rw [h_i1, h_i2]; exact hfst
      exact congrArg Fin.val (@hnd ⟨i1, hi1'⟩ ⟨i2, hi2'⟩ heq_f)
    subst hi12
    rw [← h_i1, h_i2]
  exact Fin.ext (congrArg Prod.snd hp_eq)

noncomputable def lesToPerm (N : ℕ) (s : Fin N → ℕ) (hs : IsLES N s) : Equiv.Perm (Fin N) :=
  Equiv.ofBijective (lesToPermFun N s hs) (Finite.injective_iff_bijective.mp (lesToPermFun_inj N s hs))

theorem permToLES_lesToPerm (N : ℕ) (s : Fin N → ℕ) (hs : IsLES N s) :
    permToLES N (lesToPerm N s hs) = s := by
  funext j
  set res := greedyState (sExt s) 0 N (List.range N)
  have hprops := greedyState_props (sExt s) 0 N (List.range N) (pairwise_range_lt N)
    (by simp) (fun c _ hc => by
      have hcN : c < N := by omega
      simpa [sExt, hcN] using hs ⟨c, hcN⟩)
  have hrem_nil : res.2 = [] := List.eq_nil_of_length_eq_zero hprops.2.1
  have hj_spec := hprops.2.2.2.2.2.2.2.2.2 j.1 (Nat.zero_le _) (by omega)
    (lesToPerm N s hs j).1 (lesToPermFun_spec N s hs j)
  rw [hrem_nil] at hj_spec
  simp only [List.filter_nil, List.length_nil, add_zero, sExt, j.isLt, ↓reduceDIte] at hj_spec
  rw [hj_spec]
  dsimp only [permToLES]
  have hnd_res : (res.1.filter (fun p => decide (p.2 < j.1 ∧ p.1 < (lesToPerm N s hs j).1))).Nodup := by
    have hnd_snd : (res.1.map Prod.snd).Nodup := by
      rw [hprops.2.2.2.2.2.2.2.2.1, ← List.range_eq_range']
      exact List.nodup_reverse.mpr List.nodup_range
    exact (List.Nodup.of_map Prod.snd hnd_snd).filter _
  rw [← List.toFinset_card_of_nodup hnd_res]
  refine Finset.card_bij (fun c _ => ((lesToPerm N s hs c).1, c.1)) ?_ ?_ ?_
  · intro c hc
    rw [Finset.mem_filter] at hc
    rw [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨lesToPermFun_spec N s hs c, hc.2.1, hc.2.2⟩
  · intro c₁ _ c₂ _ heq
    exact Fin.ext (congrArg Prod.snd heq)
  · intro p hp
    rw [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hp
    have hp_lt : p.2 < N := by
      have := (hprops.2.2.2.2.2.1 p hp.1).2.2.2
      omega
    let c : Fin N := ⟨p.2, hp_lt⟩
    have hp_eq := hprops.2.2.2.2.2.2.2.1 p hp.1 _ (lesToPermFun_spec N s hs c) rfl
    have hfst0 : p.1 = ((lesToPermFun N s hs c).1, c.1).1 := congrArg Prod.fst hp_eq
    have hfst : p.1 = ((lesToPerm N s hs) c).1 := hfst0
    refine ⟨c, ?_, Prod.ext hfst.symm rfl⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hp.2.1, show ((lesToPerm N s hs) c).1 < ((lesToPerm N s hs) j).1 by
      rw [← hfst]; exact hp.2.2⟩

/-- Bijection between `LES_N` and `S_N = Equiv.Perm (Fin N)`. -/
noncomputable def lesEquivPerm (N : ℕ) :
    { s : Fin N → ℕ // IsLES N s } ≃ Equiv.Perm (Fin N) := by
  refine Equiv.ofBijective (fun s => lesToPerm N s.1 s.2) ?_
  have hinj : Function.Injective (fun s : { s : Fin N → ℕ // IsLES N s } => lesToPerm N s.1 s.2) := by
    intro s₁ s₂ h
    have h1 := congrArg (permToLES N) h
    rw [permToLES_lesToPerm, permToLES_lesToPerm] at h1
    exact Subtype.ext h1
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, ?_⟩
  rw [card_les, Fintype.card_perm, Fintype.card_fin]

theorem lesEquivPerm_symm_apply (N : ℕ) (σ : Equiv.Perm (Fin N)) :
    ((lesEquivPerm N).symm σ).1 = permToLES N σ := by
  have h := permToLES_lesToPerm N ((lesEquivPerm N).symm σ).1 ((lesEquivPerm N).symm σ).2
  change permToLES N ((lesEquivPerm N) ((lesEquivPerm N).symm σ)) = _ at h
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

/-! ### Recursive Divide-and-Conquer Merge `Γ_0 ↔ Γ_1` (`mergePhi`, `dR`) -/


lemma greedyDiag_length (s : ℕ → ℕ) (lo hi : ℕ) (hle : lo ≤ hi) (hs : ∀ c, lo ≤ c → c < hi → s c ≤ c) :
    (greedyDiag s lo hi).length = hi - lo := by
  have hprops := greedyState_props s lo (hi - lo) (List.range hi) (pairwise_range_lt hi)
    (by simp; omega) (fun c hc1 hc2 => hs c hc1 (by omega))
  simp [greedyDiag, List.length_mergeSort, hprops.1]

lemma greedyDiag_pairwise_lt (s : ℕ → ℕ) (lo hi : ℕ) (hle : lo ≤ hi)
    (hs : ∀ c, lo ≤ c → c < hi → s c ≤ c) :
    (greedyDiag s lo hi).Pairwise (fun p q => p.1 < q.1) := by
  have hprops := greedyState_props s lo (hi - lo) (List.range hi) (pairwise_range_lt hi)
    (by simp; omega) (fun c hc1 hc2 => hs c hc1 (by omega))
  set orig := (greedyState s lo (hi - lo) (List.range hi)).1
  have hperm : List.Perm (greedyDiag s lo hi) orig := List.mergeSort_perm _ _
  have hnd : ((greedyDiag s lo hi).map Prod.fst).Nodup :=
    hperm.map Prod.fst |>.nodup_iff.mpr hprops.2.2.2.2.1
  have hle_pw : (greedyDiag s lo hi).Pairwise (fun p q => p.1 ≤ q.1) :=
    pairwise_le_mergeSort_key Prod.fst orig
  exact pairwise_lt_of_le_of_nodup Prod.fst (greedyDiag s lo hi) hnd hle_pw


private lemma lex_lt_fst_gen {α β : Type*} [LinearOrder α] [LinearOrder β]
    {a₁ a₂ : α} (b₁ b₂ : β) (h : a₁ < a₂) :
    (toLex (a₁, b₁) : α ×ₗ β) < toLex (a₂, b₂) := by
  simp [Prod.Lex.lt_iff, h]

private lemma lex_lt_snd_gen {α β : Type*} [LinearOrder α] [LinearOrder β]
    (a : α) {b₁ b₂ : β} (h : b₁ < b₂) :
    (toLex (a, b₁) : α ×ₗ β) < toLex (a, b₂) := by
  simp [Prod.Lex.lt_iff, h]

/-- Auxiliary: `U_mid` complements `R` in `List.range hi`, and counts of `< r'` in `U_mid` equal `r' - v`. -/
lemma merge_unfilled_count (hi : ℕ) (R_fsts : List ℕ)
    (hR_pw : R_fsts.Pairwise (· < ·))
    (hR_sub : ∀ x ∈ R_fsts, x < hi) :
    let U := List.range hi
    let U_mid := U.filter (· ∉ R_fsts)
    U_mid.Pairwise (· < ·) ∧
    (∀ x, x < hi ↔ x ∈ R_fsts ∨ x ∈ U_mid) ∧
    (∀ (v : ℕ) (hv : v < R_fsts.length),
      (U_mid.filter (fun x => decide (x < R_fsts[v]))).length = R_fsts[v] - v ∧
      v ≤ R_fsts[v]) := by
  intro U U_mid
  have hpw : U_mid.Pairwise (· < ·) := (pairwise_range_lt hi).filter _
  have hUm_eq : ∀ x, x < hi ↔ x ∈ R_fsts ∨ x ∈ U_mid := by
    intro x
    simp only [U_mid, U, List.mem_filter, List.mem_range, decide_eq_true_eq]
    constructor
    · intro hx; by_cases hr : x ∈ R_fsts <;> [left; right] <;> simp_all
    · rintro (hr | ⟨hx, _⟩)
      · exact hR_sub x hr
      · exact hx
  refine ⟨hpw, hUm_eq, fun v hv => ?_⟩
  set r := R_fsts[v]
  have hr_lt : r < hi := hR_sub r (List.getElem_mem hv)
  have hR_lt_r : (R_fsts.filter (fun x => decide (x < r))).length = v := by
    have htake : R_fsts.filter (fun x => decide (x < r)) = R_fsts.take v := by
      have hdrop : R_fsts.drop v = r :: R_fsts.drop (v + 1) := List.drop_eq_getElem_cons hv
      have hsp : R_fsts = R_fsts.take v ++ r :: R_fsts.drop (v + 1) := by
        rw [← hdrop, List.take_append_drop]
      conv_lhs => rw [hsp]
      rw [List.filter_append, List.filter_cons]
      have h1 : (R_fsts.take v).filter (fun x => decide (x < r)) = R_fsts.take v := by
        rw [List.filter_eq_self]
        intro x hx; simp only [decide_eq_true_eq]
        rcases List.getElem_of_mem hx with ⟨j, hj, rfl⟩
        have hjv : j < v := by have := List.length_take_le v R_fsts; omega
        rw [List.getElem_take]
        exact (List.pairwise_iff_getElem.mp hR_pw) j v (by omega) hv hjv
      have h2 : decide (r < r) = false := decide_eq_false (lt_irrefl _)
      have h3 : (R_fsts.drop (v + 1)).filter (fun x => decide (x < r)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro x hx; simp only [decide_eq_true_eq]
        rcases List.getElem_of_mem hx with ⟨j, hj, rfl⟩
        have hld : (R_fsts.drop (v + 1)).length = R_fsts.length - (v + 1) := List.length_drop
        rw [List.getElem_drop]
        exact not_lt_of_gt ((List.pairwise_iff_getElem.mp hR_pw) v (v + 1 + j) hv (by omega) (by omega))
      rw [h1, h2, h3]; simp
    rw [htake, List.length_take_of_le (le_of_lt hv)]
  have hU_lt_r : (U.filter (fun x => decide (x < r))).length = r := by
    have heq : U.filter (fun x => decide (x < r)) = List.range r := by
      have htake : U.take r = List.range r := by
        simp [U, List.take_range, min_eq_left (le_of_lt hr_lt)]
      rw [← htake]
      have hsp : U = U.take r ++ U.drop r := (List.take_append_drop r U).symm
      conv_lhs => rw [hsp]
      rw [List.filter_append]
      have h1 : (U.take r).filter (fun x => decide (x < r)) = U.take r := by
        rw [List.filter_eq_self]
        intro x hx; rw [htake, List.mem_range] at hx; simp [hx]
      have h2 : (U.drop r).filter (fun x => decide (x < r)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro x hx
        rcases List.getElem_of_mem hx with ⟨j, hj, rfl⟩
        have hld : (U.drop r).length = hi - r := by simp [U, List.length_drop]
        rw [List.getElem_drop]
        have hget : U[r + j]'(by simp [U]; omega) = r + j := List.getElem_range _
        rw [hget]; simp
      rw [h1, h2, List.append_nil]
    rw [heq, List.length_range]
  have hsum : (R_fsts.filter (fun x => decide (x < r))).length +
      (U_mid.filter (fun x => decide (x < r))).length = r := by
    conv_rhs => rw [← hU_lt_r]
    have hnd1 : (R_fsts.filter (fun x => decide (x < r))).Nodup := hR_pw.nodup.filter _
    have hnd2 : (U_mid.filter (fun x => decide (x < r))).Nodup := hpw.nodup.filter _
    have hndU : (U.filter (fun x => decide (x < r))).Nodup := (pairwise_range_lt hi).nodup.filter _
    rw [← List.toFinset_card_of_nodup hnd1, ← List.toFinset_card_of_nodup hnd2, ← List.toFinset_card_of_nodup hndU]
    have hdisj : Disjoint (R_fsts.filter (fun x => decide (x < r))).toFinset
        (U_mid.filter (fun x => decide (x < r))).toFinset := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hx1 hx2
      exact (decide_eq_true_eq.mp (List.mem_filter.mp hx2.1).2) (by simpa using hx1.1)
    rw [← Finset.card_union_of_disjoint hdisj]
    congr 1; ext x
    simp only [Finset.mem_union, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro (⟨hx, hxr⟩ | ⟨hx, hxr⟩)
      · exact ⟨List.mem_range.mpr ((hUm_eq x).mpr (Or.inl hx)), hxr⟩
      · exact ⟨List.mem_range.mpr ((hUm_eq x).mpr (Or.inr hx)), hxr⟩
    · rintro ⟨hxU, hxr⟩
      rcases (hUm_eq x).mp (List.mem_range.mp hxU) with hxR | hxM
      · exact Or.inl ⟨hxR, hxr⟩
      · exact Or.inr ⟨hxM, hxr⟩
  rw [hR_lt_r] at hsum
  omega

/-- Strictly-increasing list lookup equivalence: `U[r] < x ↔ r < (U.filter (· < x)).length`. -/
lemma getElem_lt_iff_lt_filter_length (U : List ℕ) (hU : U.Pairwise (· < ·))
    (r : ℕ) (hr : r < U.length) (x : ℕ) :
    U[r] < x ↔ r < (U.filter (fun y => decide (y < x))).length := by
  have hsplit : U = U.take r ++ U[r] :: U.drop (r + 1) := by
    have := List.drop_eq_getElem_cons hr
    rw [← this, List.take_append_drop]
  constructor
  · intro hlt
    have htake : (U.take (r + 1)).filter (fun y => decide (y < x)) = U.take (r + 1) := by
      rw [List.filter_eq_self]
      intro y hy
      simp only [decide_eq_true_eq]
      rcases List.getElem_of_mem hy with ⟨j, hj, rfl⟩
      have hj_le : j ≤ r := by have := List.length_take_le (r + 1) U; omega
      rw [List.getElem_take]
      rcases eq_or_lt_of_le hj_le with rfl | hjr
      · exact hlt
      · exact lt_trans ((List.pairwise_iff_getElem.mp hU) j r (by omega) hr hjr) hlt
    have hsub : (U.take (r + 1)).length ≤ (U.filter (fun y => decide (y < x))).length := by
      rw [← htake]
      conv_rhs => rw [← List.take_append_drop (r + 1) U]
      rw [List.filter_append, List.length_append]
      exact Nat.le_add_right _ _
    rw [List.length_take_of_le (by omega)] at hsub
    omega
  · intro hlen
    by_contra hge
    have hle : x ≤ U[r] := Nat.le_of_not_lt hge
    have hfil : U.filter (fun y => decide (y < x)) = (U.take r).filter (fun y => decide (y < x)) := by
      conv_lhs => rw [hsplit]
      rw [List.filter_append, List.filter_cons]
      have hu_not : decide (U[r] < x) = false := decide_eq_false (not_lt_of_ge hle)
      have hdrop_nil : (U.drop (r + 1)).filter (fun y => decide (y < x)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro y hy
        simp only [decide_eq_true_eq]
        rcases List.getElem_of_mem hy with ⟨j, hj, rfl⟩
        have hld : (U.drop (r + 1)).length = U.length - (r + 1) := List.length_drop
        rw [List.getElem_drop]
        have hgt := (List.pairwise_iff_getElem.mp hU) r (r + 1 + j) hr (by omega) (by omega)
        omega
      rw [hu_not, hdrop_nil]; simp
    have hle_take : (U.filter (fun y => decide (y < x))).length ≤ r := by
      rw [hfil]
      exact le_trans (List.length_filter_le _ _) (List.length_take_le r U)
    omega

/-- Master Divide-and-Conquer Merge Theorem (`Γ_0 ↔ Γ_1` via `mergePhi` and `dR`). -/
theorem alonsoSchott_merge_spec (s : ℕ → ℕ) (lo mid hi : ℕ)
    (hlo : lo ≤ mid) (hhi : mid ≤ hi) (hs : ∀ c, c < hi → s c ≤ c) :
    let L := greedyDiag s lo mid
    let R := greedyDiag s mid hi
    let k := mid - lo
    let Ttilde0 := ((L ++ R).zipIdx).map (fun ((r, c), idx) => (idx, r, c))
    let Ttilde1 := Ttilde0.mergeSort (fun a b => decide (mergePhi k a ≤ mergePhi k b))
    let U_mid := (greedyState s mid (hi - mid) (List.range hi)).2
    Ttilde1.length = hi - lo ∧
    (∀ (pos : ℕ) (hpos : pos < Ttilde1.length),
      let t := Ttilde1[pos]
      let dR := ((Ttilde1.take pos).filter (fun u => decide (k ≤ u.1))).length
      (t.1 < k → ∃ hr : t.2.1 < U_mid.length, t.1 = pos - dR ∧ U_mid[t.2.1]'hr = t.2.1 + dR) ∧
      (k ≤ t.1 → t.1 = k + dR)) ∧
    ((List.finRange Ttilde1.length).map (fun pos =>
      let t := Ttilde1[pos.1]
      let dR := ((Ttilde1.take pos.1).filter (fun u => decide (k ≤ u.1))).length
      (if t.1 < k then t.2.1 + dR else t.2.1, t.2.2))) = greedyDiag s lo hi := by
  intro L R k Ttilde0 Ttilde1 U_mid
  have hL_props := greedyState_props s lo (mid - lo) (List.range mid) (pairwise_range_lt mid)
    (by simp; omega) (fun c hc1 hc2 => hs c (by omega))
  have hR_props := greedyState_props s mid (hi - mid) (List.range hi) (pairwise_range_lt hi)
    (by simp; omega) (fun c hc1 hc2 => hs c (by omega))
  have hhi_props := greedyState_props s lo (hi - lo) (List.range hi) (pairwise_range_lt hi)
    (by simp; omega) (fun c hc1 hc2 => hs c (by omega))
  have hL_len : L.length = k := greedyDiag_length s lo mid hlo (fun c _ hc => hs c (by omega))
  have hR_len : R.length = hi - mid := greedyDiag_length s mid hi hhi (fun c _ hc => hs c (by omega))
  have hL_pw : L.Pairwise (fun p q => p.1 < q.1) :=
    greedyDiag_pairwise_lt s lo mid hlo (fun c _ hc => hs c (by omega))
  have hR_pw : R.Pairwise (fun p q => p.1 < q.1) :=
    greedyDiag_pairwise_lt s mid hi hhi (fun c _ hc => hs c (by omega))
  have hU_len : U_mid.length = mid := hR_props.2.1
  have hU_pw : U_mid.Pairwise (· < ·) := hR_props.2.2.1
  -- Relate U_mid to (List.range hi).filter (∉ R.map Prod.fst)
  have hR_perm : List.Perm R (greedyState s mid (hi - mid) (List.range hi)).1 :=
    List.mergeSort_perm _ _
  have hU_mid_eq : U_mid = (List.range hi).filter (· ∉ R.map Prod.fst) := by
    have hU_sub : ∀ x ∈ U_mid, x ∈ List.range hi := fun x hx => by
      rcases (hR_props.2.2.2.1 x).mpr (Or.inr hx) with hx'
      exact hx'
    have hU_notR : ∀ x ∈ U_mid, x ∉ R.map Prod.fst := by
      intro x hx hmem
      rw [List.mem_map] at hmem
      rcases hmem with ⟨p, hp, rfl⟩
      have hp' := hR_perm.mem_iff.mp hp
      exact (hR_props.2.2.2.2.2.1 p hp').2.1 hx
    have hR_notU : ∀ x ∈ List.range hi, x ∉ R.map Prod.fst → x ∈ U_mid := by
      intro x hx hnot
      rcases (hR_props.2.2.2.1 x).mp hx with ⟨c, hc⟩ | hxU
      · exfalso; apply hnot; rw [List.mem_map]; exact ⟨(x, c), hR_perm.mem_iff.mpr hc, rfl⟩
      · exact hxU
    refine perm_eq_of_sorted_of_inj id U_mid ((List.range hi).filter (· ∉ R.map Prod.fst))
      ?_ (hU_pw.imp le_of_lt) (((pairwise_range_lt hi).filter _).imp le_of_lt) (fun _ _ _ _ h => h)
    refine (List.perm_ext_iff_of_nodup hU_pw.nodup ((pairwise_range_lt hi).nodup.filter _)).mpr ?_
    intro x
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    constructor
    · intro hx; exact ⟨List.mem_range.mp (hU_sub x hx), hU_notR x hx⟩
    · rintro ⟨hx, hnot⟩; exact hR_notU x (List.mem_range.mpr hx) hnot
  -- Unfilled count properties
  have hR_fst_pw : (R.map Prod.fst).Pairwise (· < ·) := by
    rw [List.pairwise_map]; exact hR_pw
  have hR_fst_sub : ∀ x ∈ R.map Prod.fst, x < hi := by
    intro x hx
    rw [List.mem_map] at hx
    rcases hx with ⟨p, hp, rfl⟩
    exact List.mem_range.mp (hR_props.2.2.2.2.2.1 p (hR_perm.mem_iff.mp hp)).1
  have h_unfill := merge_unfilled_count hi (R.map Prod.fst) hR_fst_pw hR_fst_sub
  dsimp only at h_unfill
  rw [← hU_mid_eq] at h_unfill
  -- Define finalRow on triples
  let f : ℕ → ℕ := fun r => U_mid.getD r 0
  let finalRow : ℕ × ℕ × ℕ → ℕ := fun t => if t.1 < k then f t.2.1 else t.2.1
  -- Properties of Ttilde0
  have hT0_len : Ttilde0.length = hi - lo := by
    simp [Ttilde0, hL_len, hR_len]; omega
  have hT1_perm : List.Perm Ttilde1 Ttilde0 := List.mergeSort_perm _ _
  have hT1_len : Ttilde1.length = hi - lo := by
    rw [hT1_perm.length_eq, hT0_len]
  -- Characterize elements of Ttilde0
  have hT0_get : ∀ (idx : ℕ) (hidx : idx < Ttilde0.length),
      Ttilde0[idx] = if h : idx < k then (idx, L[idx]!.1, L[idx]!.2)
        else (idx, R[idx - k]!.1, R[idx - k]!.2) := by
    intro idx hidx
    have hidx' : idx < (L ++ R).length := by
      simpa [Ttilde0, List.length_zipIdx] using hidx
    simp only [Ttilde0, List.getElem_map, List.getElem_zipIdx, zero_add]
    by_cases hk : idx < k
    · rw [dif_pos hk]
      have hL_lt : idx < L.length := by omega
      rw [List.getElem_append_left hL_lt, getElem!_pos L idx hL_lt]
    · rw [dif_neg hk]
      have hL_le : L.length ≤ idx := by omega
      have hR_lt' : idx - L.length < R.length := by rw [hL_len, hR_len]; omega
      have hR_lt : idx - k < R.length := by omega
      have hget : (R[idx - L.length]'hR_lt') = R[idx - k]! := by
        rw [getElem!_pos R (idx - k) hR_lt]
        congr 1
        rw [hL_len]
      rw [List.getElem_append_right hL_le, hget]
  -- Check L elements have r < mid and R elements have r < hi
  have hL_r_lt : ∀ u (hu : u < L.length), L[u].1 < mid := fun u hu => by
    have hmem := (List.mergeSort_perm _ _).mem_iff.mp (List.getElem_mem hu)
    exact List.mem_range.mp (hL_props.2.2.2.2.2.1 _ hmem).1
  have hR_r_lt : ∀ v (hv : v < R.length), R[v].1 < hi := fun v hv => by
    have hmem := hR_perm.mem_iff.mp (List.getElem_mem hv)
    exact List.mem_range.mp (hR_props.2.2.2.2.2.1 _ hmem).1
  -- finalRow is injective on Ttilde0 and strictly agrees with mergePhi
  have hphi_iff : ∀ t₁ ∈ Ttilde0, ∀ t₂ ∈ Ttilde0,
      mergePhi k t₁ < mergePhi k t₂ ↔ finalRow t₁ < finalRow t₂ := by
    intro t₁ ht₁ t₂ ht₂
    rcases List.getElem_of_mem ht₁ with ⟨i₁, hi₁, rfl⟩
    rcases List.getElem_of_mem ht₂ with ⟨i₂, hi₂, rfl⟩
    rw [hT0_get i₁ hi₁, hT0_get i₂ hi₂]
    by_cases h1 : i₁ < k <;> by_cases h2 : i₂ < k
    · -- both in L
      rw [dif_pos h1, dif_pos h2]
      have hi1L : i₁ < L.length := by omega
      have hi2L : i₂ < L.length := by omega
      have hr1 : L[i₁]!.1 < U_mid.length := by rw [hU_len, getElem!_pos L i₁ hi1L]; exact hL_r_lt i₁ hi1L
      have hr2 : L[i₂]!.1 < U_mid.length := by rw [hU_len, getElem!_pos L i₂ hi2L]; exact hL_r_lt i₂ hi2L
      simp only [mergePhi, h1, h2, ↓reduceIte, finalRow, f,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr1, List.getElem?_eq_getElem hr2,
        Option.getD_some]
      have hgetL1 : L[i₁]!.1 = L[i₁].1 := by rw [getElem!_pos L i₁ hi1L]
      have hgetL2 : L[i₂]!.1 = L[i₂].1 := by rw [getElem!_pos L i₂ hi2L]
      have hiff_L : L[i₁].1 < L[i₂].1 ↔ i₁ < i₂ := by
        constructor
        · intro hlt
          by_contra hge
          rcases eq_or_lt_of_le (Nat.le_of_not_lt hge) with rfl | hgt
          · exact Nat.lt_irrefl _ hlt
          · have := (List.pairwise_iff_getElem.mp hL_pw) i₂ i₁ hi2L hi1L hgt
            omega
        · intro hlt; exact (List.pairwise_iff_getElem.mp hL_pw) i₁ i₂ hi1L hi2L hlt
      have hiff_U : U_mid[L[i₁]!.1]'hr1 < U_mid[L[i₂]!.1]'hr2 ↔ L[i₁].1 < L[i₂].1 := by
        simp only [hgetL1, hgetL2]
        constructor
        · intro hlt
          by_contra hge
          rcases eq_or_lt_of_le (Nat.le_of_not_lt hge) with he | hgt
          · have : L[i₁].1 = L[i₂].1 := he.symm
            simp only [this] at hlt
            exact Nat.lt_irrefl _ hlt
          · have := (List.pairwise_iff_getElem.mp hU_pw) L[i₂].1 L[i₁].1 (by rw [← hgetL2]; exact hr2)
              (by rw [← hgetL1]; exact hr1) hgt
            omega
        · intro hlt
          exact (List.pairwise_iff_getElem.mp hU_pw) L[i₁].1 L[i₂].1 (by rw [← hgetL1]; exact hr1)
            (by rw [← hgetL2]; exact hr2) hlt
      rw [hiff_U, Prod.Lex.lt_iff]
      simp only [Prod.Lex.lt_iff, ofLex_toLex, hgetL1, hgetL2, lt_irrefl, false_or, true_and]
      constructor
      · rintro (hlt | ⟨heq, h12⟩)
        · exact hlt
        · exact False.elim (Nat.ne_of_lt (hiff_L.mpr h12) heq)
      · intro hlt; exact Or.inl hlt
    · -- t₁ in L, t₂ in R
      rw [dif_pos h1, dif_neg h2]
      have hi1L : i₁ < L.length := by omega
      have hv2 : i₂ - k < R.length := by rw [hR_len]; rw [hT0_len] at hi₂; omega
      have hr1 : L[i₁]!.1 < U_mid.length := by rw [hU_len, getElem!_pos L i₁ hi1L]; exact hL_r_lt i₁ hi1L
      have hunf := h_unfill.2.2 (i₂ - k) (by simpa using hv2)
      have hR_get : (R.map Prod.fst)[i₂ - k]'(by simpa using hv2) = R[i₂ - k]!.1 := by
        rw [List.getElem_map, getElem!_pos R (i₂ - k) hv2]
      simp only [hR_get] at hunf
      simp only [mergePhi, h1, h2, ↓reduceIte, finalRow, f,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr1, Option.getD_some]
      rw [Prod.Lex.lt_iff]
      have hU_iff := getElem_lt_iff_lt_filter_length U_mid hU_pw L[i₁]!.1 hr1 R[i₂ - k]!.1
      rw [hunf.1] at hU_iff
      rw [hU_iff]
      constructor
      · rintro (hlt | ⟨_, h10⟩)
        · exact hlt
        · exfalso; rw [Prod.Lex.lt_iff] at h10; simp at h10
      · intro hlt; exact Or.inl hlt
    · -- t₁ in R, t₂ in L
      rw [dif_neg h1, dif_pos h2]
      have hv1 : i₁ - k < R.length := by rw [hR_len]; rw [hT0_len] at hi₁; omega
      have hi2L : i₂ < L.length := by omega
      have hr2 : L[i₂]!.1 < U_mid.length := by rw [hU_len, getElem!_pos L i₂ hi2L]; exact hL_r_lt i₂ hi2L
      have hunf := h_unfill.2.2 (i₁ - k) (by simpa using hv1)
      have hR_get : (R.map Prod.fst)[i₁ - k]'(by simpa using hv1) = R[i₁ - k]!.1 := by
        rw [List.getElem_map, getElem!_pos R (i₁ - k) hv1]
      simp only [hR_get] at hunf
      simp only [mergePhi, h1, h2, ↓reduceIte, finalRow, f,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr2, Option.getD_some]
      rw [Prod.Lex.lt_iff]
      have hU_iff := getElem_lt_iff_lt_filter_length U_mid hU_pw L[i₂]!.1 hr2 R[i₁ - k]!.1
      rw [hunf.1] at hU_iff
      have hdisj : R[i₁ - k]!.1 ≠ U_mid[L[i₂]!.1]'hr2 := by
        intro heq
        have hr_in_R : R[i₁ - k]!.1 ∈ R.map Prod.fst := by
          rw [List.mem_map]; exact ⟨R[i₁ - k]!, by rw [getElem!_pos R (i₁ - k) hv1]; exact List.getElem_mem hv1, rfl⟩
        have hu_in_U : U_mid[L[i₂]!.1]'hr2 ∈ U_mid := List.getElem_mem hr2
        rw [← heq] at hu_in_U
        rw [hU_mid_eq, List.mem_filter, decide_eq_true_eq] at hu_in_U
        exact hu_in_U.2 hr_in_R
      constructor
      · rintro (hlt | ⟨heq, _⟩)
        · simp only [ofLex_toLex] at hlt
          by_contra hge
          have hlt2 : U_mid[L[i₂]!.1]'hr2 < R[i₁ - k]!.1 := lt_of_le_of_ne (Nat.le_of_not_lt hge) hdisj.symm
          have hlt2' := hU_iff.mp hlt2
          omega
        · simp only [ofLex_toLex] at heq
          by_contra hge
          have hlt2 : U_mid[L[i₂]!.1]'hr2 < R[i₁ - k]!.1 := lt_of_le_of_ne (Nat.le_of_not_lt hge) hdisj.symm
          have hlt2' := hU_iff.mp hlt2
          omega
      · intro hlt
        have hnot : ¬ U_mid[L[i₂]!.1]'hr2 < R[i₁ - k]!.1 := by omega
        have hle2 : R[i₁ - k]!.1 - (i₁ - k) ≤ L[i₂]!.1 := by
          by_contra hgt
          exact hnot (hU_iff.mpr (Nat.lt_of_not_ge hgt))
        rcases eq_or_lt_of_le hle2 with heq | hlt2
        · right; refine ⟨heq, ?_⟩; rw [Prod.Lex.lt_iff]; left; norm_num
        · left; exact hlt2
    · -- both in R
      rw [dif_neg h1, dif_neg h2]
      have hv1 : i₁ - k < R.length := by rw [hR_len]; rw [hT0_len] at hi₁; omega
      have hv2 : i₂ - k < R.length := by rw [hR_len]; rw [hT0_len] at hi₂; omega
      have hr1 : R[i₁ - k]!.1 = (R[i₁ - k]'hv1).1 := congrArg Prod.fst (getElem!_pos R (i₁ - k) hv1)
      have hr2 : R[i₂ - k]!.1 = (R[i₂ - k]'hv2).1 := congrArg Prod.fst (getElem!_pos R (i₂ - k) hv2)
      have hmono : ∀ (a b : ℕ) (ha : a < R.length) (hb : b < R.length), a < b →
          (R[a]'ha).1 - a ≤ (R[b]'hb).1 - b ∧ (R[a]'ha).1 < (R[b]'hb).1 := by
        intro a b ha hb hab
        have hlt_ab : (R[a]'ha).1 < (R[b]'hb).1 := (List.pairwise_iff_getElem.mp hR_pw) a b ha hb hab
        have hstep : ∀ (d : ℕ) (hd : a + d < R.length), (R[a]'ha).1 + d ≤ (R[a + d]'hd).1 := by
          intro d hd
          induction d with
          | zero => simp
          | succ d ihd =>
            have h1' := ihd (by omega)
            have h2' : (R[a + d]'(by omega)).1 < (R[a + (d + 1)]'hd).1 :=
              (List.pairwise_iff_getElem.mp hR_pw) (a + d) (a + (d + 1)) (by omega) hd (by omega)
            omega
        have hdiff := hstep (b - a) (by omega)
        have ha_eq : a + (b - a) = b := by omega
        have hdiff' : (R[a]'ha).1 + (b - a) ≤ (R[b]'hb).1 := by
          simpa [ha_eq] using hdiff
        have hle_a : a ≤ (R[a]'ha).1 := by
          have ha_lt : a < (R.map Prod.fst).length := by rw [List.length_map]; exact ha
          have h := (h_unfill.2.2 a ha_lt).2
          rwa [List.getElem_map] at h
        have hle_b : b ≤ (R[b]'hb).1 := by
          have hb_lt : b < (R.map Prod.fst).length := by rw [List.length_map]; exact hb
          have h := (h_unfill.2.2 b hb_lt).2
          rwa [List.getElem_map] at h
        exact ⟨by omega, hlt_ab⟩
      simp only [mergePhi, h1, h2, ↓reduceIte, finalRow, hr1, hr2]
      rw [Prod.Lex.lt_iff]
      simp only [ofLex_toLex]
      rcases lt_trichotomy (i₁ - k) (i₂ - k) with hlt | heq | hgt
      · have hm := hmono (i₁ - k) (i₂ - k) hv1 hv2 hlt
        constructor
        · intro _; exact hm.2
        · intro _
          rcases eq_or_lt_of_le hm.1 with he | hlt'
          · right; refine ⟨he, ?_⟩
            rw [Prod.Lex.lt_iff]; simp only [ofLex_toLex, lt_irrefl, false_or, true_and]; omega
          · left; exact hlt'
      · have hi12 : i₁ = i₂ := by omega
        subst hi12
        simp
      · have hm := hmono (i₂ - k) (i₁ - k) hv2 hv1 hgt
        constructor
        · rintro (hlt' | ⟨_, hlex⟩)
          · omega
          · rw [Prod.Lex.lt_iff] at hlex
            simp only [ofLex_toLex] at hlex
            rcases hlex with h00 | ⟨_, hi12⟩
            · omega
            · omega
        · intro hlt'; omega
  -- Prove Ttilde1 is strictly sorted by mergePhi (and hence finalRow)
  have hTtilde0_phi_nodup : (Ttilde0.map (mergePhi k)).Nodup := by
    have hmap_fst : Ttilde0.map Prod.fst = (L ++ R).zipIdx.map Prod.snd := by
      simp [Ttilde0, List.map_map, Function.comp_def]
    have hnd_fst : (Ttilde0.map Prod.fst).Nodup := by
      rw [hmap_fst, List.zipIdx_map_snd, ← List.range_eq_range']
      exact List.nodup_range
    refine List.Nodup.of_map (fun p : ℕ ×ₗ ℕ ×ₗ ℕ => (ofLex (ofLex p).2).2) ?_
    rw [List.map_map]
    have hmap_eq : Ttilde0.map ((fun p : ℕ ×ₗ ℕ ×ₗ ℕ => (ofLex (ofLex p).2).2) ∘ mergePhi k) =
        Ttilde0.map Prod.fst := by
      refine List.map_congr_left fun t _ => ?_
      dsimp [mergePhi]; split_ifs <;> rfl
    rw [hmap_eq]
    exact hnd_fst
  have hT1_phi_nd : (Ttilde1.map (mergePhi k)).Nodup :=
    hT1_perm.map (mergePhi k) |>.nodup_iff.mpr hTtilde0_phi_nodup
  have hT1_phi_lt : Ttilde1.Pairwise (fun a b => mergePhi k a < mergePhi k b) :=
    pairwise_lt_of_le_of_nodup (mergePhi k) Ttilde1 hT1_phi_nd (pairwise_le_mergeSort_key (mergePhi k) Ttilde0)
  have hT1_final_lt : Ttilde1.Pairwise (fun a b => finalRow a < finalRow b) := by
    refine List.Pairwise.imp_of_mem ?_ hT1_phi_lt
    intro a b ha hb hab
    exact (hphi_iff a (hT1_perm.mem_iff.mp ha) b (hT1_perm.mem_iff.mp hb)).mp hab
  -- Now prove the dR / t.1 / U_mid[t.2.1] properties at each pos!
  have hpos_props : ∀ (pos : ℕ) (hpos : pos < Ttilde1.length),
      let t := Ttilde1[pos]
      let dR := ((Ttilde1.take pos).filter (fun u => decide (k ≤ u.1))).length
      (t.1 < k → ∃ hr : t.2.1 < U_mid.length, t.1 = pos - dR ∧ U_mid[t.2.1]'hr = t.2.1 + dR) ∧
      (k ≤ t.1 → t.1 = k + dR) := by
    intro pos hpos
    dsimp only
    set t := Ttilde1[pos]
    set dR := ((Ttilde1.take pos).filter (fun u => decide (k ≤ u.1))).length
    set dL := ((Ttilde1.take pos).filter (fun u => decide (u.1 < k))).length
    have hdLdR : dL + dR = pos := by
      have hsum := length_filter_add_not (fun u : ℕ × ℕ × ℕ => decide (u.1 < k)) (Ttilde1.take pos)
      have hnot : (Ttilde1.take pos).filter (fun u => !decide (u.1 < k)) =
          (Ttilde1.take pos).filter (fun u => decide (k ≤ u.1)) := by
        refine List.filter_congr fun u _ => ?_
        by_cases hu : u.1 < k
        · simp [hu, Nat.not_le.mpr hu]
        · simp [hu, Nat.le_of_not_lt hu]
      rw [hnot, List.length_take_of_le (le_of_lt hpos)] at hsum
      exact hsum
    have htake_iff : ∀ u ∈ Ttilde1, u ∈ Ttilde1.take pos ↔ finalRow u < finalRow t := by
      intro u hu
      rcases List.getElem_of_mem hu with ⟨j, hj, rfl⟩
      constructor
      · intro hmem
        rcases List.getElem_of_mem hmem with ⟨j', hj', hj'_eq⟩
        have hj'_pos : j' < pos := by have := List.length_take_le pos Ttilde1; omega
        rw [List.getElem_take] at hj'_eq
        rw [← hj'_eq]
        exact (List.pairwise_iff_getElem.mp hT1_final_lt) j' pos (by omega) hpos hj'_pos
      · intro hlt
        have hj_pos : j < pos := by
          by_contra hge
          rcases eq_or_lt_of_le (Nat.le_of_not_lt hge) with rfl | hgt
          · exact Nat.lt_irrefl _ hlt
          · have hlt2 := (List.pairwise_iff_getElem.mp hT1_final_lt) pos j hpos hj hgt
            dsimp only [t] at hlt
            omega
        have hj' : j < (Ttilde1.take pos).length := by rw [List.length_take_of_le (le_of_lt hpos)]; exact hj_pos
        refine List.mem_of_getElem (i := j) (h := hj') ?_
        exact List.getElem_take
    -- Count of u in Ttilde1.take pos with u.1 < k vs k ≤ u.1
    have hL_dL : ∀ (hk_t : t.1 < k), dL = t.1 := by
      intro hk_t
      have hfil_perm : List.Perm ((Ttilde1.take pos).filter (fun u => decide (u.1 < k)))
          (Ttilde0.filter (fun u => decide (u.1 < k ∧ u.1 < t.1))) := by
        have ht_in_T0 : t ∈ Ttilde0 := hT1_perm.mem_iff.mp (List.getElem_mem hpos)
        have hT0_nd : Ttilde0.Nodup := by
          have := hTtilde0_phi_nodup
          exact List.Nodup.of_map (mergePhi k) this
        have hT1_nd : Ttilde1.Nodup := hT1_perm.nodup_iff.mpr hT0_nd
        refine (List.perm_ext_iff_of_nodup (hT1_nd.take.filter _) (hT0_nd.filter _)).mpr ?_
        intro u
        simp only [List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro ⟨hu_take, hu_k⟩
          have hu_T1 : u ∈ Ttilde1 := List.mem_of_mem_take hu_take
          have hu_T0 : u ∈ Ttilde0 := hT1_perm.mem_iff.mp hu_T1
          have hu_fin : finalRow u < finalRow t := (htake_iff u hu_T1).mp hu_take
          refine ⟨hu_T0, hu_k, ?_⟩
          -- Since both u.1 < k and t.1 < k, finalRow u < finalRow t ↔ u.1 < t.1!
          rcases List.getElem_of_mem hu_T0 with ⟨iu, hiu, rfl⟩
          rcases List.getElem_of_mem ht_in_T0 with ⟨it, hit, hteq⟩
          rw [hT0_get iu hiu] at hu_k hu_fin ⊢
          rw [hT0_get it hit] at hteq
          have hiu_k : iu < k := by
            by_contra h
            rw [dif_neg h] at hu_k
            dsimp only at hu_k
            omega
          have hit_k : it < k := by
            by_contra h
            rw [dif_neg h] at hteq
            have : t.1 = it := by rw [← hteq]
            omega
          rw [dif_pos hiu_k] at hu_k hu_fin ⊢
          rw [dif_pos hit_k] at hteq
          rw [← hteq] at hu_fin ⊢
          have hiuL : iu < L.length := by omega
          have hitL : it < L.length := by omega
          have hr1 : L[iu]!.1 < U_mid.length := by rw [hU_len, getElem!_pos L iu hiuL]; exact hL_r_lt iu hiuL
          have hr2 : L[it]!.1 < U_mid.length := by rw [hU_len, getElem!_pos L it hitL]; exact hL_r_lt it hitL
          simp only [finalRow, hiu_k, hit_k, ↓reduceIte, f,
            List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr1, List.getElem?_eq_getElem hr2,
            Option.getD_some] at hu_fin
          have hgetL1 : L[iu]!.1 = (L[iu]'hiuL).1 := congrArg Prod.fst (getElem!_pos L iu hiuL)
          have hgetL2 : L[it]!.1 = (L[it]'hitL).1 := congrArg Prod.fst (getElem!_pos L it hitL)
          have hr1' : (L[iu]'hiuL).1 < U_mid.length := hgetL1 ▸ hr1
          have hr2' : (L[it]'hitL).1 < U_mid.length := hgetL2 ▸ hr2
          have hUeq1 : (U_mid[L[iu]!.1]'hr1) = U_mid[(L[iu]'hiuL).1]'hr1' := by congr 1
          have hUeq2 : (U_mid[L[it]!.1]'hr2) = U_mid[(L[it]'hitL).1]'hr2' := by congr 1
          rw [hUeq1, hUeq2] at hu_fin
          by_contra hge
          rcases eq_or_lt_of_le (Nat.le_of_not_lt hge) with rfl | hgt
          · exact Nat.lt_irrefl _ hu_fin
          · have hL_lt := (List.pairwise_iff_getElem.mp hL_pw) it iu hitL hiuL hgt
            have hU_lt := (List.pairwise_iff_getElem.mp hU_pw) (L[it]'hitL).1 (L[iu]'hiuL).1 hr2' hr1' hL_lt
            omega
        · rintro ⟨hu_T0, hu_k, hu_t⟩
          have hu_T1 : u ∈ Ttilde1 := hT1_perm.mem_iff.mpr hu_T0
          refine ⟨(htake_iff u hu_T1).mpr ?_, hu_k⟩
          rcases List.getElem_of_mem hu_T0 with ⟨iu, hiu, rfl⟩
          rcases List.getElem_of_mem ht_in_T0 with ⟨it, hit, hteq⟩
          rw [hT0_get iu hiu] at hu_k hu_t ⊢
          rw [hT0_get it hit] at hteq
          have hiu_k : iu < k := by
            by_contra h
            rw [dif_neg h] at hu_k
            dsimp only at hu_k
            omega
          have hit_k : it < k := by
            by_contra h
            rw [dif_neg h] at hteq
            have : t.1 = it := by rw [← hteq]
            omega
          rw [dif_pos hiu_k] at hu_t ⊢
          rw [dif_pos hit_k] at hteq
          rw [← hteq] at hu_t ⊢
          have hiuL : iu < L.length := by omega
          have hitL : it < L.length := by omega
          have hr1 : L[iu]!.1 < U_mid.length := by rw [hU_len, getElem!_pos L iu hiuL]; exact hL_r_lt iu hiuL
          have hr2 : L[it]!.1 < U_mid.length := by rw [hU_len, getElem!_pos L it hitL]; exact hL_r_lt it hitL
          simp only [finalRow, hiu_k, hit_k, ↓reduceIte, f,
            List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr1, List.getElem?_eq_getElem hr2,
            Option.getD_some]
          have hgetL1 : L[iu]!.1 = (L[iu]'hiuL).1 := congrArg Prod.fst (getElem!_pos L iu hiuL)
          have hgetL2 : L[it]!.1 = (L[it]'hitL).1 := congrArg Prod.fst (getElem!_pos L it hitL)
          have hr1' : (L[iu]'hiuL).1 < U_mid.length := hgetL1 ▸ hr1
          have hr2' : (L[it]'hitL).1 < U_mid.length := hgetL2 ▸ hr2
          have hUeq1 : (U_mid[L[iu]!.1]'hr1) = U_mid[(L[iu]'hiuL).1]'hr1' := by congr 1
          have hUeq2 : (U_mid[L[it]!.1]'hr2) = U_mid[(L[it]'hitL).1]'hr2' := by congr 1
          rw [hUeq1, hUeq2]
          have hL_lt := (List.pairwise_iff_getElem.mp hL_pw) iu it hiuL hitL (by dsimp only at hu_t; exact hu_t)
          exact (List.pairwise_iff_getElem.mp hU_pw) (L[iu]'hiuL).1 (L[it]'hitL).1 hr1' hr2' hL_lt
      dsimp only [dL]
      rw [hfil_perm.length_eq]
      -- Now compute length of Ttilde0.filter (u.1 < k ∧ u.1 < t.1) = t.1!
      have ht_in_T0 : t ∈ Ttilde0 := hT1_perm.mem_iff.mp (List.getElem_mem hpos)
      have ht_lt_T0 : t.1 < k := hk_t
      have hfil_T0 : Ttilde0.filter (fun u => decide (u.1 < k ∧ u.1 < t.1)) = Ttilde0.take t.1 := by
        have ht1_le : t.1 ≤ Ttilde0.length := by rw [hT0_len]; omega
        conv_lhs => rw [← List.take_append_drop t.1 Ttilde0, List.filter_append]
        have hA : (Ttilde0.take t.1).filter (fun u => decide (u.1 < k ∧ u.1 < t.1)) = Ttilde0.take t.1 := by
          rw [List.filter_eq_self]
          intro u hu
          rcases List.getElem_of_mem hu with ⟨j, hj, rfl⟩
          have hj_lt : j < t.1 := by have := List.length_take_le t.1 Ttilde0; omega
          rw [List.getElem_take, hT0_get j (by omega)]
          rw [dif_pos (by omega)]
          simp [hj_lt, show j < k by omega]
        have hB : (Ttilde0.drop t.1).filter (fun u => decide (u.1 < k ∧ u.1 < t.1)) = [] := by
          rw [List.filter_eq_nil_iff]
          intro u hu
          rcases List.getElem_of_mem hu with ⟨j, hj, rfl⟩
          have hld : (Ttilde0.drop t.1).length = Ttilde0.length - t.1 := List.length_drop
          rw [List.getElem_drop, hT0_get (t.1 + j) (by omega)]
          split_ifs <;> (simp; try omega)
        rw [hA, hB, List.append_nil]
      rw [hfil_T0, List.length_take_of_le (by rw [hT0_len]; omega)]
    have hR_dR : ∀ (hk_t : k ≤ t.1), dR = t.1 - k := by
      intro hk_t
      have hfil_perm : List.Perm ((Ttilde1.take pos).filter (fun u => decide (k ≤ u.1)))
          (Ttilde0.filter (fun u => decide (k ≤ u.1 ∧ u.1 < t.1))) := by
        have ht_in_T0 : t ∈ Ttilde0 := hT1_perm.mem_iff.mp (List.getElem_mem hpos)
        have hT0_nd : Ttilde0.Nodup := List.Nodup.of_map (mergePhi k) hTtilde0_phi_nodup
        have hT1_nd : Ttilde1.Nodup := hT1_perm.nodup_iff.mpr hT0_nd
        refine (List.perm_ext_iff_of_nodup (hT1_nd.take.filter _) (hT0_nd.filter _)).mpr ?_
        intro u
        simp only [List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro ⟨hu_take, hu_k⟩
          have hu_T1 : u ∈ Ttilde1 := List.mem_of_mem_take hu_take
          have hu_T0 : u ∈ Ttilde0 := hT1_perm.mem_iff.mp hu_T1
          have hu_fin : finalRow u < finalRow t := (htake_iff u hu_T1).mp hu_take
          refine ⟨hu_T0, hu_k, ?_⟩
          rcases List.getElem_of_mem hu_T0 with ⟨iu, hiu, rfl⟩
          rcases List.getElem_of_mem ht_in_T0 with ⟨it, hit, hteq⟩
          rw [hT0_get iu hiu] at hu_k hu_fin ⊢
          rw [hT0_get it hit] at hteq
          have hiu_nk : ¬ iu < k := by
            by_contra h
            rw [dif_pos h] at hu_k
            dsimp only at hu_k
            omega
          have hit_nk : ¬ it < k := by
            by_contra h
            rw [dif_pos h] at hteq
            have : t.1 = it := by rw [← hteq]
            omega
          rw [dif_neg hiu_nk] at hu_k hu_fin ⊢
          rw [dif_neg hit_nk] at hteq
          rw [← hteq] at hu_fin ⊢
          have hiuR : iu - k < R.length := by rw [hR_len]; rw [hT0_len] at hiu; omega
          have hitR : it - k < R.length := by rw [hR_len]; rw [hT0_len] at hit; omega
          have hgetR1 : R[iu - k]!.1 = (R[iu - k]'hiuR).1 := congrArg Prod.fst (getElem!_pos R (iu - k) hiuR)
          have hgetR2 : R[it - k]!.1 = (R[it - k]'hitR).1 := congrArg Prod.fst (getElem!_pos R (it - k) hitR)
          simp only [finalRow, hiu_nk, hit_nk, ↓reduceIte, hgetR1, hgetR2] at hu_fin
          by_contra hge
          rcases eq_or_lt_of_le (Nat.le_of_not_lt hge) with heq | hgt
          · have hsub : iu - k = it - k := by dsimp only at heq; omega
            have hu_fin' : (R[iu - k]'hiuR).1 < (R[it - k]'hitR).1 := hu_fin
            simp only [hsub] at hu_fin'
            exact Nat.lt_irrefl _ hu_fin'
          · have hlt_R := (List.pairwise_iff_getElem.mp hR_pw) (it - k) (iu - k) hitR hiuR (by dsimp only at hgt; omega)
            omega
        · rintro ⟨hu_T0, hu_k, hu_t⟩
          have hu_T1 : u ∈ Ttilde1 := hT1_perm.mem_iff.mpr hu_T0
          refine ⟨(htake_iff u hu_T1).mpr ?_, hu_k⟩
          rcases List.getElem_of_mem hu_T0 with ⟨iu, hiu, rfl⟩
          rcases List.getElem_of_mem ht_in_T0 with ⟨it, hit, hteq⟩
          rw [hT0_get iu hiu] at hu_k hu_t ⊢
          rw [hT0_get it hit] at hteq
          have hiu_nk : ¬ iu < k := by
            by_contra h
            rw [dif_pos h] at hu_k
            dsimp only at hu_k
            omega
          have hit_nk : ¬ it < k := by
            by_contra h
            rw [dif_pos h] at hteq
            have : t.1 = it := by rw [← hteq]
            omega
          rw [dif_neg hiu_nk] at hu_t ⊢
          rw [dif_neg hit_nk] at hteq
          rw [← hteq] at hu_t ⊢
          have hiuR : iu - k < R.length := by rw [hR_len]; rw [hT0_len] at hiu; omega
          have hitR : it - k < R.length := by rw [hR_len]; rw [hT0_len] at hit; omega
          have hgetR1 : R[iu - k]!.1 = (R[iu - k]'hiuR).1 := congrArg Prod.fst (getElem!_pos R (iu - k) hiuR)
          have hgetR2 : R[it - k]!.1 = (R[it - k]'hitR).1 := congrArg Prod.fst (getElem!_pos R (it - k) hitR)
          simp only [finalRow, hiu_nk, hit_nk, ↓reduceIte, hgetR1, hgetR2]
          exact (List.pairwise_iff_getElem.mp hR_pw) (iu - k) (it - k) hiuR hitR (by dsimp only at hu_t; omega)
      dsimp only [dR]
      rw [hfil_perm.length_eq]
      have ht_in_T0 : t ∈ Ttilde0 := hT1_perm.mem_iff.mp (List.getElem_mem hpos)
      have ht_lt_T0 : t.1 < Ttilde0.length := by
        rcases List.getElem_of_mem ht_in_T0 with ⟨it, hit, hteq⟩
        rw [hT0_get it hit] at hteq
        split_ifs at hteq <;> rw [← hteq] <;> exact hit
      have hfil_T0 : Ttilde0.filter (fun u => decide (k ≤ u.1 ∧ u.1 < t.1)) =
          (Ttilde0.drop k).take (t.1 - k) := by
        have hk_le : k ≤ Ttilde0.length := by rw [hT0_len]; omega
        conv_lhs => rw [← List.take_append_drop k Ttilde0, List.filter_append]
        have hA : (Ttilde0.take k).filter (fun u => decide (k ≤ u.1 ∧ u.1 < t.1)) = [] := by
          rw [List.filter_eq_nil_iff]
          intro u hu
          rcases List.getElem_of_mem hu with ⟨j, hj, rfl⟩
          have hjk : j < k := by have := List.length_take_le k Ttilde0; omega
          rw [List.getElem_take, hT0_get j (by omega), dif_pos hjk]
          simp [hjk]
        have hB : (Ttilde0.drop k).filter (fun u => decide (k ≤ u.1 ∧ u.1 < t.1)) =
            (Ttilde0.drop k).take (t.1 - k) := by
          have hdt : t.1 - k ≤ (Ttilde0.drop k).length := by rw [List.length_drop]; omega
          conv_lhs => rw [← List.take_append_drop (t.1 - k) (Ttilde0.drop k), List.filter_append]
          have hB1 : ((Ttilde0.drop k).take (t.1 - k)).filter (fun u => decide (k ≤ u.1 ∧ u.1 < t.1)) =
              (Ttilde0.drop k).take (t.1 - k) := by
            rw [List.filter_eq_self]
            intro u hu
            rcases List.getElem_of_mem hu with ⟨j, hj, rfl⟩
            have hj_lt : j < t.1 - k := by have := List.length_take_le (t.1 - k) (Ttilde0.drop k); omega
            rw [List.getElem_take, List.getElem_drop, hT0_get (k + j) (by omega), dif_neg (by omega)]
            simp; omega
          have hB2 : ((Ttilde0.drop k).drop (t.1 - k)).filter (fun u => decide (k ≤ u.1 ∧ u.1 < t.1)) = [] := by
            rw [List.filter_eq_nil_iff]
            intro u hu
            rcases List.getElem_of_mem hu with ⟨j, hj, rfl⟩
            have hld1 : ((Ttilde0.drop k).drop (t.1 - k)).length = Ttilde0.length - k - (t.1 - k) := by
              rw [List.length_drop, List.length_drop]
            rw [List.getElem_drop, List.getElem_drop, hT0_get (k + (t.1 - k + j)) (by omega), dif_neg (by omega)]
            simp; omega
          rw [hB1, hB2, List.append_nil]
        rw [hA, hB, List.nil_append]
      rw [hfil_T0, List.length_take_of_le (by rw [List.length_drop]; omega)]
    refine ⟨fun hk_t => ?_, fun hk_t => ?_⟩
    · have hdL_eq := hL_dL hk_t
      have ht_in_T0 : t ∈ Ttilde0 := hT1_perm.mem_iff.mp (List.getElem_mem hpos)
      have hr_lt : t.2.1 < U_mid.length := by
        rcases List.getElem_of_mem ht_in_T0 with ⟨it, hit, hteq⟩
        rw [hT0_get it hit] at hteq
        split_ifs at hteq with hit_k
        · have hitL : it < L.length := by omega
          have h1 : t.1 = it := by rw [← hteq]
          have h2 : t.2.1 = L[it]!.1 := by rw [← hteq]
          rw [h2, getElem!_pos L it hitL, hU_len]
          exact hL_r_lt it hitL
        · exfalso
          have h1 : t.1 = it := by rw [← hteq]
          omega
      refine ⟨hr_lt, by omega, ?_⟩
      -- Prove U_mid[t.2.1] = t.2.1 + dR
      set val := U_mid[t.2.1]'hr_lt
      have hval_eq_fin : val = finalRow t := by
        simp [finalRow, hk_t, f, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr_lt, val]
      have hval_lt_hi : val < hi := by
        have hm : val ∈ (List.range hi).filter (· ∉ R.map Prod.fst) :=
          hU_mid_eq ▸ List.getElem_mem hr_lt
        rw [List.mem_filter, List.mem_range] at hm
        exact hm.1
      have hU_lt_val : (U_mid.filter (fun x => decide (x < val))).length = t.2.1 := by
        have htake : U_mid.filter (fun x => decide (x < val)) = U_mid.take t.2.1 := by
          have hdrop := List.drop_eq_getElem_cons hr_lt
          have hsp : U_mid = U_mid.take t.2.1 ++ val :: U_mid.drop (t.2.1 + 1) := by
            rw [← hdrop, List.take_append_drop]
          conv_lhs => rw [hsp]
          rw [List.filter_append, List.filter_cons]
          have hA : (U_mid.take t.2.1).filter (fun x => decide (x < val)) = U_mid.take t.2.1 := by
            rw [List.filter_eq_self]
            intro x hx
            rcases List.getElem_of_mem hx with ⟨j, hj, rfl⟩
            have hj_lt : j < t.2.1 := by have := List.length_take_le t.2.1 U_mid; omega
            rw [List.getElem_take]
            simp only [decide_eq_true_eq]
            exact (List.pairwise_iff_getElem.mp hU_pw) j t.2.1 (by omega) hr_lt hj_lt
          have hB : (U_mid.drop (t.2.1 + 1)).filter (fun x => decide (x < val)) = [] := by
            rw [List.filter_eq_nil_iff]
            intro x hx
            rcases List.getElem_of_mem hx with ⟨j, hj, rfl⟩
            have hld : (U_mid.drop (t.2.1 + 1)).length = U_mid.length - (t.2.1 + 1) := List.length_drop
            rw [List.getElem_drop]
            simp only [decide_eq_true_eq]
            exact not_lt_of_gt ((List.pairwise_iff_getElem.mp hU_pw) t.2.1 (t.2.1 + 1 + j) hr_lt (by omega) (by omega))
          rw [hA, decide_eq_false (lt_irrefl val), hB]; simp
        rw [htake, List.length_take_of_le (le_of_lt hr_lt)]
      have hR_lt_val : ((R.map Prod.fst).filter (fun x => decide (x < val))).length = dR := by
        -- (R.map fst).filter (< val) permutes with (Ttilde1.take pos).filter (k ≤ u.1)
        have hperm_R : List.Perm ((Ttilde1.take pos).filter (fun u => decide (k ≤ u.1)))
            (Ttilde0.filter (fun u => decide (k ≤ u.1 ∧ finalRow u < val))) := by
          have hT0_nd : Ttilde0.Nodup := List.Nodup.of_map (mergePhi k) hTtilde0_phi_nodup
          have hT1_nd : Ttilde1.Nodup := hT1_perm.nodup_iff.mpr hT0_nd
          refine (List.perm_ext_iff_of_nodup (hT1_nd.take.filter _) (hT0_nd.filter _)).mpr ?_
          intro u
          simp only [List.mem_filter, decide_eq_true_eq]
          constructor
          · rintro ⟨hu_take, hu_k⟩
            have hu_T1 : u ∈ Ttilde1 := List.mem_of_mem_take hu_take
            exact ⟨hT1_perm.mem_iff.mp hu_T1, hu_k, hval_eq_fin ▸ (htake_iff u hu_T1).mp hu_take⟩
          · rintro ⟨hu_T0, hu_k, hu_val⟩
            have hu_T1 : u ∈ Ttilde1 := hT1_perm.mem_iff.mpr hu_T0
            exact ⟨(htake_iff u hu_T1).mpr (hval_eq_fin ▸ hu_val), hu_k⟩
        have hmap_R : ((Ttilde0.filter (fun u => decide (k ≤ u.1))).map (fun u => u.2.1)) =
            R.map Prod.fst := by
          have hT0_drop : Ttilde0.filter (fun u => decide (k ≤ u.1)) = Ttilde0.drop k := by
            conv_lhs => rw [← List.take_append_drop k Ttilde0, List.filter_append]
            have hA : (Ttilde0.take k).filter (fun u => decide (k ≤ u.1)) = [] := by
              rw [List.filter_eq_nil_iff]
              intro u hu
              rcases List.getElem_of_mem hu with ⟨j, hj, rfl⟩
              have hjk : j < k := by have := List.length_take_le k Ttilde0; omega
              rw [List.getElem_take, hT0_get j (by omega), dif_pos hjk]; simp [hjk]
            have hB : (Ttilde0.drop k).filter (fun u => decide (k ≤ u.1)) = Ttilde0.drop k := by
              rw [List.filter_eq_self]
              intro u hu
              rcases List.getElem_of_mem hu with ⟨j, hj, rfl⟩
              have hld : (Ttilde0.drop k).length = Ttilde0.length - k := List.length_drop
              rw [List.getElem_drop, hT0_get (k + j) (by omega), dif_neg (by omega)]; simp
            rw [hA, hB, List.nil_append]
          rw [hT0_drop]
          apply List.ext_getElem
          · simp only [List.length_map, List.length_drop, hT0_len, hR_len]
            omega
          · intro j hj1 hj2
            have hjR : j < R.length := by simpa [hR_len] using hj2
            simp only [List.getElem_map, List.getElem_drop]
            rw [hT0_get (k + j) (by rw [hT0_len]; omega), dif_neg (by omega)]
            simp [getElem!_pos R j hjR]
        dsimp only [dR]
        rw [hperm_R.length_eq]
        have hfil_comm : (Ttilde0.filter (fun u => decide (k ≤ u.1 ∧ finalRow u < val))) =
            (Ttilde0.filter (fun u => decide (k ≤ u.1))).filter (fun u => decide (u.2.1 < val)) := by
          rw [List.filter_filter]
          congr 1; funext u
          by_cases hk : k ≤ u.1
          · have hnt : ¬ u.1 < k := by omega
            simp [hk, finalRow, hnt]
          · simp [hk]
        rw [hfil_comm]
        conv_rhs => rw [length_filter_map_comm _ (fun u : ℕ × ℕ × ℕ => u.2.1) (fun x => decide (x < val)), hmap_R]
      have htot_lt_val : ((List.range hi).filter (fun x => decide (x < val))).length = val := by
        have hsp : List.range hi = List.range val ++ (List.range hi).drop val := by
          have : (List.range hi).take val = List.range val := by rw [List.take_range, min_eq_left (le_of_lt hval_lt_hi)]
          rw [← this, List.take_append_drop]
        conv_lhs => rw [hsp, List.filter_append]
        have hA : (List.range val).filter (fun x => decide (x < val)) = List.range val := by
          rw [List.filter_eq_self]; intro x hx; rw [List.mem_range] at hx; simp [hx]
        have hB : ((List.range hi).drop val).filter (fun x => decide (x < val)) = [] := by
          rw [List.filter_eq_nil_iff]
          intro x hx
          rcases List.getElem_of_mem hx with ⟨j, hj, rfl⟩
          have hld : ((List.range hi).drop val).length = hi - val := by simp [List.length_drop]
          rw [List.getElem_drop, List.getElem_range]
          simp
        rw [hA, hB, List.append_nil, List.length_range]
      rw [← htot_lt_val, ← hU_lt_val, ← hR_lt_val]
      have hndR : ((R.map Prod.fst).filter (fun x => decide (x < val))).Nodup := hR_fst_pw.nodup.filter _
      have hndU : (U_mid.filter (fun x => decide (x < val))).Nodup := hU_pw.nodup.filter _
      have hndAll : ((List.range hi).filter (fun x => decide (x < val))).Nodup :=
        (pairwise_range_lt hi).nodup.filter _
      rw [← List.toFinset_card_of_nodup hndAll, ← List.toFinset_card_of_nodup hndU,
          ← List.toFinset_card_of_nodup hndR]
      have hdisj : Disjoint (U_mid.filter (fun x => decide (x < val))).toFinset
          ((R.map Prod.fst).filter (fun x => decide (x < val))).toFinset := by
        rw [Finset.disjoint_left]
        intro x hxU hxR
        simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hxU hxR
        rw [hU_mid_eq, List.mem_filter, decide_eq_true_eq] at hxU
        exact hxU.1.2 hxR.1
      rw [← Finset.card_union_of_disjoint hdisj]
      congr 1; ext x
      simp only [Finset.mem_union, List.mem_toFinset, List.mem_filter, List.mem_range, decide_eq_true_eq]
      constructor
      · rintro ⟨hx, hxv⟩
        rcases h_unfill.2.1 x |>.mp hx with hxR | hxU
        · right; exact ⟨hxR, hxv⟩
        · left; exact ⟨hxU, hxv⟩
      · rintro (⟨hxU, hxv⟩ | ⟨hxR, hxv⟩)
        · exact ⟨(h_unfill.2.1 x).mpr (Or.inr hxU), hxv⟩
        · exact ⟨(h_unfill.2.1 x).mpr (Or.inl hxR), hxv⟩
    · have hdR_eq := hR_dR hk_t
      have ht_in_T0 : t ∈ Ttilde0 := hT1_perm.mem_iff.mp (List.getElem_mem hpos)
      have hk_le_t : k ≤ t.1 := hk_t
      have ht_lt_hi : t.1 < hi - lo := by
        rcases List.getElem_of_mem ht_in_T0 with ⟨it, hit, hteq⟩
        rw [hT0_get it hit] at hteq
        split_ifs at hteq with hit_k
        · exfalso
          have h1 : t.1 = it := by rw [← hteq]
          omega
        · have h1 : t.1 = it := by rw [← hteq]
          rw [h1]; rw [hT0_len] at hit; exact hit
      omega
  -- Finally prove the mapped list equals greedyDiag s lo hi!
  refine ⟨hT1_len, hpos_props, ?_⟩
  let outList := (List.finRange Ttilde1.length).map (fun pos =>
    let t := Ttilde1[pos.1]
    let dR := ((Ttilde1.take pos.1).filter (fun u => decide (k ≤ u.1))).length
    (if t.1 < k then t.2.1 + dR else t.2.1, t.2.2))
  have hout_eq_final : outList = Ttilde1.map (fun t => (finalRow t, t.2.2)) := by
    apply List.ext_getElem
    · simp [outList]
    · intro pos hp1 hp2
      have hpos : pos < Ttilde1.length := by simpa using hp2
      simp only [outList, List.getElem_map, List.getElem_finRange, Fin.val_cast]
      have hpp := hpos_props pos hpos
      dsimp only at hpp ⊢
      by_cases hk : Ttilde1[pos].1 < k
      · obtain ⟨hr, _, hur⟩ := hpp.1 hk
        simp only [hk, ↓reduceIte, finalRow, f, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hr, Option.getD_some]
        exact Prod.ext hur.symm rfl
      · simp only [hk, ↓reduceIte, finalRow]
  change outList = greedyDiag s lo hi
  rw [hout_eq_final]
  -- Prove Ttilde1.map (fun t => (finalRow t, t.2.2)) is sorted by Prod.fst and Perm greedyDiag s lo hi!
  have h_sorted_out : (Ttilde1.map (fun t => (finalRow t, t.2.2))).Pairwise (fun p q => p.1 ≤ q.1) := by
    rw [List.pairwise_map]
    exact hT1_final_lt.imp fun h => le_of_lt h
  have h_sorted_gd : (greedyDiag s lo hi).Pairwise (fun p q => p.1 ≤ q.1) :=
    (greedyDiag_pairwise_lt s lo hi (by omega) (fun c _ hc => hs c (by omega))).imp le_of_lt
  have h_perm_out : List.Perm (Ttilde1.map (fun t => (finalRow t, t.2.2))) (greedyDiag s lo hi) := by
    have h1 : List.Perm (Ttilde1.map (fun t => (finalRow t, t.2.2)))
        (Ttilde0.map (fun t => (finalRow t, t.2.2))) := hT1_perm.map _
    have hT0_map_eq : Ttilde0.map (fun t => (finalRow t, t.2.2)) =
        L.map (fun p => (f p.1, p.2)) ++ R := by
      apply List.ext_getElem
      · simp [hT0_len, hL_len, hR_len]; omega
      · intro j hj1 hj2
        have hj0 : j < Ttilde0.length := by simpa using hj1
        rw [List.getElem_map, hT0_get j hj0]
        by_cases hjk : j < k
        · rw [dif_pos hjk, List.getElem_append_left (by simp [hL_len]; exact hjk)]
          rw [List.getElem_map, getElem!_pos L j (by omega)]
          simp [finalRow, hjk]
        · rw [dif_neg hjk, List.getElem_append_right (by simp [hL_len]; omega)]
          simp only [List.length_map, hL_len]
          rw [getElem!_pos R (j - k) (by rw [hR_len]; rw [hT0_len] at hj0; omega)]
          simp [finalRow, hjk]
    have hsplit_gd := greedyState_add s lo (mid - lo) (hi - mid) (List.range hi)
    have hsub_add : lo + (mid - lo) = mid := by omega
    have hsub_len : mid - lo + (hi - mid) = hi - lo := by omega
    rw [hsub_len, hsub_add] at hsplit_gd
    have hU_eq_map : U_mid = (List.range mid).map f := by
      apply List.ext_getElem
      · simp [hU_len]
      · intro r hr1 hr2
        simp only [List.getElem_map, List.getElem_range]
        dsimp [f]; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr1]; rfl
    have hL_map_perm : List.Perm (L.map (fun p => (f p.1, p.2)))
        (greedyState s lo (mid - lo) U_mid).1 := by
      rw [hU_eq_map, greedyState_map s lo (mid - lo) f (List.range mid) (by simp; omega)
        (fun c _ hc => hs c (by omega))]
      exact (List.mergeSort_perm _ _).map _
    have h_gd_perm : List.Perm (L.map (fun p => (f p.1, p.2)) ++ R) (greedyDiag s lo hi) := by
      have hLR : List.Perm (L.map (fun p => (f p.1, p.2)) ++ R)
          ((greedyState s mid (hi - mid) (List.range hi)).1 ++ (greedyState s lo (mid - lo) U_mid).1) :=
        (List.Perm.append hL_map_perm hR_perm).trans List.perm_append_comm
      have hres_eq : (greedyState s lo (hi - lo) (List.range hi)).1 =
          (greedyState s mid (hi - mid) (List.range hi)).1 ++ (greedyState s lo (mid - lo) U_mid).1 :=
        congrArg Prod.fst hsplit_gd
      refine hLR.trans ?_
      rw [← hres_eq]
      exact (List.mergeSort_perm _ _).symm
    exact h1.trans (hT0_map_eq ▸ h_gd_perm)
  refine perm_eq_of_sorted_of_inj Prod.fst _ _ h_perm_out h_sorted_out h_sorted_gd ?_
  intro x hx y hy hxy
  have hnd_gd : ((greedyDiag s lo hi).map Prod.fst).Nodup :=
    ((List.mergeSort_perm _ _).map Prod.fst).nodup_iff.mpr hhi_props.2.2.2.2.1
  rcases List.getElem_of_mem hx with ⟨ix, hix, rfl⟩
  rcases List.getElem_of_mem hy with ⟨iy, hiy, rfl⟩
  have hix' : ix < ((greedyDiag s lo hi).map Prod.fst).length := by simp [hix]
  have hiy' : iy < ((greedyDiag s lo hi).map Prod.fst).length := by simp [hiy]
  have h_inj := List.nodup_iff_injective_getElem.mp hnd_gd
  have heq_f : ((greedyDiag s lo hi).map Prod.fst)[ix]'hix' =
      ((greedyDiag s lo hi).map Prod.fst)[iy]'hiy' := by
    simpa using hxy
  have h_fin := @h_inj ⟨ix, hix'⟩ ⟨iy, hiy'⟩ heq_f
  have h_ixy : ix = iy := congrArg Fin.val h_fin
  subst h_ixy; rfl

end Aux_as

namespace Aux_nsil
private lemma card_fin_lt {N : ℕ} (k : ℕ) (hk : k ≤ N) :
    (Finset.univ.filter fun j : Fin N => j.1 < k).card = k := by
  have himg : (Finset.univ.filter fun j : Fin N => j.1 < k).image Fin.val = Finset.range k := by
    ext x
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact hj
    · intro hx; exact ⟨⟨x, lt_of_lt_of_le hx hk⟩, hx, rfl⟩
  rw [← Finset.card_image_of_injective _ Fin.val_injective, himg, Finset.card_range]

private lemma card_fin_le {N : ℕ} (i : Fin N) :
    (Finset.univ.filter fun j : Fin N => j ≤ i).card = i.1 + 1 := by
  have hsub : (Finset.univ.filter fun j : Fin N => j ≤ i) =
      (Finset.univ.filter fun j : Fin N => j.1 < i.1 + 1) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def]
    omega
  rw [hsub]
  exact card_fin_lt (i.1 + 1) i.isLt

lemma runStart_le {α : Type*} [LinearOrder α] {N : ℕ} {l : Fin N → α}
    (hl : Monotone l) (i : Fin N) : runStart l i ≤ i.1 := by
  have hsub : (Finset.univ.filter fun j : Fin N => l j < l i) ⊆
      (Finset.univ.filter fun j : Fin N => j.1 < i.1) := by
    intro j hj
    rw [Finset.mem_filter] at hj ⊢
    refine ⟨hj.1, ?_⟩
    by_contra hge
    have hij : i ≤ j := Fin.le_iff_val_le_val.mpr (Nat.le_of_not_lt hge)
    exact absurd (hl hij) (not_le_of_gt hj.2)
  exact le_trans (Finset.card_le_card hsub) (le_of_eq (card_fin_lt i.1 (le_of_lt i.isLt)))

lemma lt_runEndSucc {α : Type*} [LinearOrder α] {N : ℕ} {l : Fin N → α}
    (hl : Monotone l) (i : Fin N) : i.1 < runEndSucc l i := by
  have hsub : (Finset.univ.filter fun j : Fin N => j ≤ i) ⊆
      (Finset.univ.filter fun j : Fin N => l j ≤ l i) := by
    intro j hj
    rw [Finset.mem_filter] at hj ⊢
    exact ⟨hj.1, hl hj.2⟩
  have hle := Finset.card_le_card hsub
  rw [card_fin_le i] at hle
  exact hle

lemma runEndSucc_le {α : Type*} [LinearOrder α] {N : ℕ} (l : Fin N → α) (i : Fin N) :
    runEndSucc l i ≤ N := by
  dsimp only [runEndSucc]
  simpa using Finset.card_filter_le (Finset.univ : Finset (Fin N)) (fun j => l j ≤ l i)

lemma eq_iff_mem_runBlock {α : Type*} [LinearOrder α] {N : ℕ} {l : Fin N → α}
    (hl : Monotone l) (i j : Fin N) :
    l j = l i ↔ runStart l i ≤ j.1 ∧ j.1 < runEndSucc l i := by
  constructor
  · intro heq
    have h1 : runStart l i ≤ j.1 := by
      have := runStart_le hl j
      have hrs : runStart l i = runStart l j := by simp [runStart, heq]
      omega
    have h2 : j.1 < runEndSucc l i := by
      have := lt_runEndSucc hl j
      have hre : runEndSucc l i = runEndSucc l j := by simp [runEndSucc, heq]
      omega
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    rcases lt_trichotomy (l j) (l i) with hlt | heq | hgt
    · have hsub : (Finset.univ.filter fun r : Fin N => r ≤ j) ⊆
          (Finset.univ.filter fun r : Fin N => l r < l i) := by
        intro r hr
        rw [Finset.mem_filter] at hr ⊢
        exact ⟨hr.1, lt_of_le_of_lt (hl hr.2) hlt⟩
      have hle := Finset.card_le_card hsub
      rw [card_fin_le j] at hle
      change j.1 + 1 ≤ runStart l i at hle
      omega
    · exact heq
    · have hsub : (Finset.univ.filter fun r : Fin N => l r ≤ l i) ⊆
          (Finset.univ.filter fun r : Fin N => r.1 < j.1) := by
        intro r hr
        rw [Finset.mem_filter] at hr ⊢
        refine ⟨hr.1, ?_⟩
        by_contra hge
        have hjr : j ≤ r := Fin.le_iff_val_le_val.mpr (Nat.le_of_not_lt hge)
        have := lt_of_lt_of_le hgt (hl hjr)
        exact absurd hr.2 (not_le_of_gt this)
      have hle := le_trans (Finset.card_le_card hsub) (le_of_eq (card_fin_lt j.1 (le_of_lt j.isLt)))
      change runEndSucc l i ≤ j.1 at hle
      omega

lemma runStart_eq_of_eq {α : Type*} [LinearOrder α] {N : ℕ} (l : Fin N → α)
    {i j : Fin N} (h : l i = l j) : runStart l i = runStart l j := by
  simp [runStart, h]

lemma runEndSucc_eq_of_eq {α : Type*} [LinearOrder α] {N : ℕ} (l : Fin N → α)
    {i j : Fin N} (h : l i = l j) : runEndSucc l i = runEndSucc l j := by
  simp [runEndSucc, h]

lemma runCount_eq_runEndSucc_sub_runStart {α : Type*} [LinearOrder α] {N : ℕ} {l : Fin N → α}
    (i : Fin N) : runCount l i = runEndSucc l i - runStart l i := by
  dsimp only [runCount, runEndSucc, runStart]
  have hsub : (Finset.univ.filter fun j : Fin N => l j < l i) ⊆
      (Finset.univ.filter fun j : Fin N => l j ≤ l i) := by
    intro j hj
    rw [Finset.mem_filter] at hj ⊢
    exact ⟨hj.1, le_of_lt hj.2⟩
  have hpart : (Finset.univ.filter fun j : Fin N => l j < l i).card +
      (Finset.univ.filter fun j : Fin N => l j = l i).card =
      (Finset.univ.filter fun j : Fin N => l j ≤ l i).card := by
    have hdisj : Disjoint (Finset.univ.filter fun j : Fin N => l j < l i)
        (Finset.univ.filter fun j : Fin N => l j = l i) := by
      rw [Finset.disjoint_left]
      intro j hj1 hj2
      rw [Finset.mem_filter] at hj1 hj2
      exact absurd hj2.2 (ne_of_lt hj1.2)
    rw [← Finset.card_union_of_disjoint hdisj]
    congr 1; ext j
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    exact le_iff_lt_or_eq.symm
  omega

lemma runOffset_pos {α : Type*} [LinearOrder α] {N : ℕ} (l : Fin N → α) (i : Fin N) :
    1 ≤ runOffset l i := by
  dsimp [runOffset]; omega

lemma runOffset_le_runCount {α : Type*} [LinearOrder α] {N : ℕ} {l : Fin N → α}
    (hl : Monotone l) (i : Fin N) : runOffset l i ≤ runCount l i := by
  have hrs := runStart_le hl i
  have hre := lt_runEndSucc hl i
  rw [runCount_eq_runEndSucc_sub_runStart]
  dsimp [runOffset]
  omega

lemma runOffset_le_succ_val {α : Type*} [LinearOrder α] {N : ℕ} (l : Fin N → α) (i : Fin N) :
    runOffset l i ≤ i.1 + 1 := by
  dsimp [runOffset]; omega

lemma runOffset_le_N {α : Type*} [LinearOrder α] {N : ℕ} (l : Fin N → α) (i : Fin N) :
    runOffset l i ≤ N :=
  le_trans (runOffset_le_succ_val l i) i.isLt

lemma runOffset_zero {α : Type*} [LinearOrder α] {N : ℕ} {l : Fin N → α}
    (hl : Monotone l) (h0 : 0 < N) : runOffset l ⟨0, h0⟩ = 1 := by
  have hle := runStart_le hl ⟨0, h0⟩
  dsimp [runOffset]
  omega

lemma runOffset_succ {α : Type*} [LinearOrder α] {N : ℕ} {l : Fin N → α}
    (hl : Monotone l) {i : ℕ} (hi : i + 1 < N) :
    runOffset l ⟨i + 1, hi⟩ =
      if l ⟨i + 1, hi⟩ = l ⟨i, by omega⟩ then runOffset l ⟨i, by omega⟩ + 1 else 1 := by
  split_ifs with heq
  · have hrs := runStart_eq_of_eq l heq
    have hle := runStart_le hl ⟨i, by omega⟩
    dsimp [runOffset] at hle ⊢
    rw [hrs]
    omega
  · have hlt : l ⟨i, by omega⟩ < l ⟨i + 1, hi⟩ :=
      lt_of_le_of_ne (hl (Fin.le_iff_val_le_val.mpr (by dsimp; omega))) (Ne.symm heq)
    have hrs : runStart l ⟨i + 1, hi⟩ = i + 1 := by
      dsimp only [runStart]
      have hset : (Finset.univ.filter fun j : Fin N => l j < l ⟨i + 1, hi⟩) =
          (Finset.univ.filter fun j : Fin N => j.1 < i + 1) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hj
          by_contra hge
          have hij : ⟨i + 1, hi⟩ ≤ j := Fin.le_iff_val_le_val.mpr (Nat.le_of_not_lt hge)
          exact absurd (hl hij) (not_le_of_gt hj)
        · intro hj
          have hji : j ≤ ⟨i, by omega⟩ := Fin.le_iff_val_le_val.mpr (by dsimp; omega)
          exact lt_of_le_of_lt (hl hji) hlt
      rw [hset]
      exact card_fin_lt (i + 1) (le_of_lt hi)
    dsimp [runOffset]
    rw [hrs]
    omega

/-! ### Part 2: Multiplicity & Harmonic-Bucket Bounds -/

/-- At most `N / m` indices in an NSIL of length `N` have `runOffset l i = m`. -/
theorem runOffset_card_le {α : Type*} [LinearOrder α] {N : ℕ} {l : Fin N → α}
    (hl : Monotone l) {m : ℕ} (hm : 1 ≤ m) :
    (Finset.univ.filter fun i : Fin N => runOffset l i = m).card ≤ N / m := by
  set S := Finset.univ.filter fun i : Fin N => runOffset l i = m
  have hinj : Function.Injective (fun p : ↥S × Fin m =>
      (⟨p.1.1.1 - p.2.1, by have := p.1.1.isLt; omega⟩ : Fin N)) := by
    intro ⟨⟨i₁, hi₁⟩, t₁⟩ ⟨⟨i₂, hi₂⟩, t₂⟩ heq
    have hm1 : runOffset l i₁ = m := (Finset.mem_filter.mp hi₁).2
    have hm2 : runOffset l i₂ = m := (Finset.mem_filter.mp hi₂).2
    have hrs1 := runStart_le hl i₁
    have hrs2 := runStart_le hl i₂
    have hre1 := lt_runEndSucc hl i₁
    have hre2 := lt_runEndSucc hl i₂
    have hx_val : i₁.1 - t₁.1 = i₂.1 - t₂.1 := congrArg Fin.val heq
    set x : Fin N := ⟨i₁.1 - t₁.1, by have := i₁.isLt; omega⟩
    have hx1_block : runStart l i₁ ≤ x.1 ∧ x.1 < runEndSucc l i₁ := by
      dsimp [x, runOffset] at hm1 ⊢
      omega
    have hx2_block : runStart l i₂ ≤ x.1 ∧ x.1 < runEndSucc l i₂ := by
      have : x.1 = i₂.1 - t₂.1 := hx_val
      dsimp [runOffset] at hm2
      rw [this]
      omega
    have hl1 : l x = l i₁ := (eq_iff_mem_runBlock hl i₁ x).mpr hx1_block
    have hl2 : l x = l i₂ := (eq_iff_mem_runBlock hl i₂ x).mpr hx2_block
    have hrs_eq : runStart l i₁ = runStart l i₂ := runStart_eq_of_eq l (hl1.symm.trans hl2)
    have hi_val : i₁.1 = i₂.1 := by
      dsimp [runOffset] at hm1 hm2
      omega
    have hi_eq : i₁ = i₂ := Fin.ext hi_val
    have ht_eq : t₁ = t₂ := by
      apply Fin.ext
      dsimp [runOffset] at hm1 hm2
      omega
    subst hi_eq
    subst ht_eq
    rfl
  have hle_card := Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin] at hle_card
  exact (Nat.le_div_iff_mul_le hm).mpr hle_card

/-- Harmonic bucket sum bound: `∑_{m=2}^N ⌊N / m⌋ ≤ N * Nat.clog 2 (N + 2)`. -/
theorem harmonicBucketSum_le (N : ℕ) :
    ∑ m ∈ Finset.Icc 2 N, (N / m) ≤ N * Nat.clog 2 (N + 2) := by
  set d := Nat.clog 2 (N + 2)
  have hd_le : N + 2 ≤ 2 ^ d := Nat.le_pow_clog (by norm_num : 1 < 2) (N + 2)
  have hcov : Finset.Icc 2 N ⊆
      (Finset.Ico 1 d).biUnion (fun j => Finset.Ico (2 ^ j) (2 ^ (j + 1))) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    rw [Finset.mem_biUnion]
    refine ⟨Nat.log 2 m, Finset.mem_Ico.mpr ⟨?_, ?_⟩, Finset.mem_Ico.mpr ⟨?_, ?_⟩⟩
    · by_contra h0
      have hlog0 : Nat.log 2 m = 0 := by omega
      have hlt2 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) m
      rw [hlog0] at hlt2
      omega
    · have hpow_le : 2 ^ Nat.log 2 m ≤ m := Nat.pow_log_le_self 2 (by omega)
      have hpow_lt : 2 ^ Nat.log 2 m < 2 ^ d := by omega
      exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hpow_lt
    · exact Nat.pow_log_le_self 2 (by omega)
    · exact Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) m
  have hbiu_le : ∑ m ∈ (Finset.Ico 1 d).biUnion (fun j => Finset.Ico (2 ^ j) (2 ^ (j + 1))), (N / m) ≤
      ∑ j ∈ Finset.Ico 1 d, ∑ m ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), (N / m) := by
    induction (Finset.Ico 1 d) using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert hj]
      have hu := Finset.sum_union_inter (s₁ := Finset.Ico (2 ^ j) (2 ^ (j + 1)))
        (s₂ := s.biUnion (fun j => Finset.Ico (2 ^ j) (2 ^ (j + 1)))) (f := fun m => N / m)
      omega
  calc
    ∑ m ∈ Finset.Icc 2 N, (N / m)
        ≤ ∑ m ∈ (Finset.Ico 1 d).biUnion (fun j => Finset.Ico (2 ^ j) (2 ^ (j + 1))), (N / m) :=
          Finset.sum_le_sum_of_subset hcov
    _ ≤ ∑ j ∈ Finset.Ico 1 d, ∑ m ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), (N / m) := hbiu_le
    _ ≤ ∑ j ∈ Finset.Ico 1 d, N := by
          refine Finset.sum_le_sum fun j _ => ?_
          calc
            ∑ m ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), (N / m)
                ≤ ∑ _m ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), (N / 2 ^ j) := by
                  refine Finset.sum_le_sum fun m hm => ?_
                  exact Nat.div_le_div_left (Finset.mem_Ico.mp hm).1 (Nat.two_pow_pos j)
            _ = (2 ^ (j + 1) - 2 ^ j) * (N / 2 ^ j) := by
                  rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]
            _ = 2 ^ j * (N / 2 ^ j) := by
                  have : 2 ^ (j + 1) - 2 ^ j = 2 ^ j := by rw [pow_succ]; omega
                  rw [this]
            _ ≤ N := Nat.mul_div_le N (2 ^ j)
    _ = (d - 1) * N := by rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]
    _ ≤ d * N := Nat.mul_le_mul_right N (Nat.sub_le d 1)
    _ = N * d := mul_comm d N

/-! ### Part 3: 2-Sort Harmonic-Bucket Table & Routing Correctness -/


lemma mem_bucketPairs_iff (N m occ : ℕ) :
    (m, occ) ∈ bucketPairs N ↔ 2 ≤ m ∧ m ≤ N ∧ occ < N / m := by
  simp only [bucketPairs, List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨m', ⟨k, hk, rfl⟩, occ', hocc, heq⟩
    have hm_eq : k + 2 = m := congrArg Prod.fst heq
    have ho_eq : occ' = occ := congrArg Prod.snd heq
    subst hm_eq; subst ho_eq
    omega
  · rintro ⟨hm1, hm2, ho⟩
    refine ⟨m, ⟨m - 2, by omega, by omega⟩, occ, ho, rfl⟩

private lemma sum_map_flatMap {α β : Type*} (L : List α) (f : α → List β) :
    (L.flatMap f).length = (L.map (fun a => (f a).length)).sum := by
  induction L with
  | nil => simp
  | cons a t ih => simp [ih]

lemma bucketPairs_length (N : ℕ) :
    (bucketPairs N).length = ∑ m ∈ Finset.Icc 2 N, (N / m) := by
  dsimp only [bucketPairs]
  rw [sum_map_flatMap, List.map_map]
  have hmap : (((List.range (N - 1)).map (· + 2)).map (fun a => ((List.range (N / a)).map (fun occ => (a, occ))).length)) =
      ((List.range (N - 1)).map (· + 2)).map (fun a => N / a) := by
    refine List.map_congr_left fun a _ => ?_
    simp
  have hmap2 : (((List.range (N - 1)).map (· + 2)).map (fun a => N / a)) =
      (List.range (N - 1)).map (fun k => N / (k + 2)) := by
    rw [List.map_map]; rfl
  have hnd : ((List.range (N - 1)).map (· + 2)).Nodup :=
    List.Nodup.map (fun _ _ h => by omega) List.nodup_range
  have hIcc : Finset.Icc 2 N = ((List.range (N - 1)).map (· + 2)).toFinset := by
    ext m
    simp only [Finset.mem_Icc, List.mem_toFinset, List.mem_map, List.mem_range]
    constructor
    · intro ⟨h1, h2⟩; exact ⟨m - 2, by omega, by omega⟩
    · rintro ⟨k, hk, rfl⟩; omega
  rw [← List.map_map, hmap, hIcc, ← List.sum_toFinset _ hnd]

lemma bucketPairs_nodup (N : ℕ) : (bucketPairs N).Nodup := by
  dsimp only [bucketPairs]
  rw [List.nodup_flatMap]
  refine ⟨fun _ _ => List.Nodup.map (fun _ _ h => congrArg Prod.snd h) List.nodup_range, ?_⟩
  have hnd : ((List.range (N - 1)).map (· + 2)).Nodup :=
    List.Nodup.map (fun _ _ h => by omega) List.nodup_range
  refine List.Pairwise.imp (fun {m₁ m₂} hne => ?_) hnd
  intro x hx₁ hx₂
  simp only [List.mem_map] at hx₁ hx₂
  rcases hx₁ with ⟨_, _, rfl⟩
  rcases hx₂ with ⟨_, _, h2⟩
  exact hne (congrArg Prod.fst h2).symm


lemma runOcc_lt_div {α : Type*} [LinearOrder α] {N : ℕ} {l : Fin N → α}
    (hl : Monotone l) (i : Fin N) : runOcc l i < N / runOffset l i := by
  have hsub : (Finset.univ.filter fun j : Fin N => j < i ∧ runOffset l j = runOffset l i) ⊂
      (Finset.univ.filter fun j : Fin N => runOffset l j = runOffset l i) := by
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, fun h =>
        (lt_irrefl i) (Finset.mem_filter.mp h).2.1⟩
    · intro j hj
      rw [Finset.mem_filter] at hj ⊢
      exact ⟨hj.1, hj.2.2⟩
  exact lt_of_lt_of_le (Finset.card_lt_card hsub) (runOffset_card_le hl (runOffset_pos l i))

lemma runOffset_runOcc_mem_bucketPairs {α : Type*} [LinearOrder α] {N : ℕ} {l : Fin N → α}
    (hl : Monotone l) {i : Fin N} (hm : 2 ≤ runOffset l i) :
    (runOffset l i, runOcc l i) ∈ bucketPairs N := by
  rw [mem_bucketPairs_iff]
  exact ⟨hm, runOffset_le_N l i, runOcc_lt_div hl i⟩

lemma runOffset_runOcc_inj {α : Type*} [LinearOrder α] {N : ℕ} (l : Fin N → α) :
    Function.Injective (fun i : Fin N => (runOffset l i, runOcc l i)) := by
  intro i₁ i₂ heq
  have hm : runOffset l i₁ = runOffset l i₂ := congrArg Prod.fst heq
  have ho : runOcc l i₁ = runOcc l i₂ := congrArg Prod.snd heq
  rcases lt_trichotomy i₁ i₂ with hlt | rfl | hgt
  · exfalso
    have hsub : (Finset.univ.filter fun j : Fin N => j < i₁ ∧ runOffset l j = runOffset l i₁) ⊂
        (Finset.univ.filter fun j : Fin N => j < i₂ ∧ runOffset l j = runOffset l i₂) := by
      rw [Finset.ssubset_iff_of_subset]
      · exact ⟨i₁, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, hm⟩, fun h =>
          (lt_irrefl i₁) (Finset.mem_filter.mp h).2.1⟩
      · intro j hj
        rw [Finset.mem_filter] at hj ⊢
        exact ⟨hj.1, lt_trans hj.2.1 hlt, hj.2.2.trans hm⟩
    have hlt_c := Finset.card_lt_card hsub
    change runOcc l i₁ < runOcc l i₂ at hlt_c
    omega
  · rfl
  · exfalso
    have hsub : (Finset.univ.filter fun j : Fin N => j < i₂ ∧ runOffset l j = runOffset l i₂) ⊂
        (Finset.univ.filter fun j : Fin N => j < i₁ ∧ runOffset l j = runOffset l i₁) := by
      rw [Finset.ssubset_iff_of_subset]
      · exact ⟨i₂, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt, hm.symm⟩, fun h =>
          (lt_irrefl i₂) (Finset.mem_filter.mp h).2.1⟩
      · intro j hj
        rw [Finset.mem_filter] at hj ⊢
        exact ⟨hj.1, lt_trans hj.2.1 hgt, hj.2.2.trans hm.symm⟩
    have hlt_c := Finset.card_lt_card hsub
    change runOcc l i₂ < runOcc l i₁ at hlt_c
    omega

private lemma pairwise_le_mergeSort_key {α κ : Type*} [LinearOrder κ]
    (key : α → κ) (L : List α) :
    (L.mergeSort (fun x y => decide (key x ≤ key y))).Pairwise (fun x y => key x ≤ key y) := by
  have hp := List.pairwise_mergeSort (le := fun x y => decide (key x ≤ key y))
    (fun _ _ _ h1 h2 => by
      rw [decide_eq_true_iff] at h1 h2 ⊢
      exact le_trans h1 h2)
    (fun a b => by
      rcases le_total (key a) (key b) with h | h <;> simp [h]) L
  exact hp.imp fun h => decide_eq_true_eq.mp h

private lemma pairwise_lt_of_le_of_nodup {α κ : Type*} [LinearOrder κ]
    (key : α → κ) (L : List α) (hnd : (L.map key).Nodup)
    (hle : L.Pairwise (fun x y => key x ≤ key y)) :
    L.Pairwise (fun x y => key x < key y) := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    rw [List.pairwise_cons] at hle ⊢
    rw [List.map_cons, List.nodup_cons] at hnd
    refine ⟨fun y hy => ?_, ih hnd.2 hle.2⟩
    exact lt_of_le_of_ne (hle.1 y hy) (fun h => hnd.1 (h ▸ List.mem_map_of_mem hy))

private lemma perm_eq_of_sorted_of_inj {α κ : Type*} [LinearOrder κ]
    (key : α → κ) (L₁ L₂ : List α) (hperm : List.Perm L₁ L₂)
    (h1 : L₁.Pairwise (fun x y => key x ≤ key y))
    (h2 : L₂.Pairwise (fun x y => key x ≤ key y))
    (hinj : ∀ x ∈ L₂, ∀ y ∈ L₂, key x = key y → x = y) :
    L₁ = L₂ := by
  induction L₁ generalizing L₂ with
  | nil => exact (List.perm_nil.mp hperm.symm).symm
  | cons x xs ih =>
    cases L₂ with
    | nil => exact absurd (List.perm_nil.mp hperm) (List.cons_ne_nil x xs)
    | cons y ys =>
      rw [List.pairwise_cons] at h1 h2
      have hx_in : x ∈ y :: ys := hperm.mem_iff.mp List.mem_cons_self
      have hy_in : y ∈ x :: xs := hperm.mem_iff.mpr List.mem_cons_self
      have hkx : key y ≤ key x := by
        rcases List.mem_cons.mp hx_in with rfl | hx_ys
        · exact le_rfl
        · exact h2.1 x hx_ys
      have hky : key x ≤ key y := by
        rcases List.mem_cons.mp hy_in with rfl | hy_xs
        · exact le_rfl
        · exact h1.1 y hy_xs
      have hxy : x = y := hinj x hx_in y List.mem_cons_self (le_antisymm hky hkx)
      subst hxy
      congr 1
      apply ih ys (List.Perm.cons_inv hperm) h1.2 h2.2
      intro a ha b hb hab
      exact hinj a (List.mem_cons_of_mem x ha) b (List.mem_cons_of_mem x hb) hab


theorem seqScanOcc_eq_runOcc {α : Type*} [LinearOrder α] (N : ℕ) (l : Fin N → α) :
    let L := occSortedList N l
    L.length = N ∧
    (∀ p (hp : p < L.length), (L[p]'hp).1 = true → seqScanOcc L p = runOcc l (L[p]'hp).2.2) := by
  intro L
  set orig := (List.finRange N).map fun i : Fin N => (decide (2 ≤ runOffset l i), runOffset l i, i)
  have hperm : List.Perm L orig := List.mergeSort_perm _ _
  have hlen : L.length = N := by rw [hperm.length_eq]; simp [orig]
  refine ⟨hlen, ?_⟩
  have hnd_orig : (orig.map occSortKey).Nodup := by
    refine List.Nodup.of_map (fun k : ℕ ×ₗ ℕ ×ₗ ℕ => (ofLex (ofLex k).2).2) ?_
    rw [List.map_map]
    have hm : orig.map ((fun k : ℕ ×ₗ ℕ ×ₗ ℕ => (ofLex (ofLex k).2).2) ∘ occSortKey) =
        (List.finRange N).map Fin.val := by
      simp [orig, List.map_map, Function.comp_def, occSortKey]
    rw [hm]
    exact List.Nodup.map Fin.val_injective (List.nodup_finRange N)
  have hnd_L : (L.map occSortKey).Nodup := hperm.map occSortKey |>.nodup_iff.mpr hnd_orig
  have hpw_L : L.Pairwise (fun x y => occSortKey x < occSortKey y) :=
    pairwise_lt_of_le_of_nodup occSortKey L hnd_L (pairwise_le_mergeSort_key occSortKey orig)
  have hcount : ∀ p (hp : p < L.length), (L[p]'hp).1 = true →
      seqScanOcc L p =
        (Finset.univ.filter fun q : Fin L.length =>
          q.1 < p ∧ (L[q.1]'q.isLt).1 = true ∧ (L[q.1]'q.isLt).2.1 = (L[p]'hp).2.1).card := by
    intro p
    induction p with
    | zero =>
      intro hp _
      simp [seqScanOcc]
    | succ p ih =>
      intro hp hact
      have hp' : p < L.length := by omega
      dsimp only [seqScanOcc]
      rw [List.getElem?_eq_getElem hp, List.getElem?_eq_getElem hp']
      dsimp only
      by_cases hmatch : (L[p]'hp').1 = true ∧ (L[p]'hp').2.1 = (L[p + 1]'hp).2.1
      · have ihp := ih hp' hmatch.1
        have hif : ((L[p + 1]'hp).1 && (L[p]'hp').1 &&
            ((L[p + 1]'hp).2.1 == (L[p]'hp').2.1)) = true := by
          simp [hact, hmatch.1, hmatch.2]
        rw [if_pos hif, ihp]
        have hset : (Finset.univ.filter fun q : Fin L.length =>
            q.1 < p + 1 ∧ (L[q.1]'q.isLt).1 = true ∧ (L[q.1]'q.isLt).2.1 = (L[p + 1]'hp).2.1) =
            insert ⟨p, hp'⟩ (Finset.univ.filter fun q : Fin L.length =>
              q.1 < p ∧ (L[q.1]'q.isLt).1 = true ∧ (L[q.1]'q.isLt).2.1 = (L[p]'hp').2.1) := by
          ext q
          simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and, Fin.ext_iff]
          constructor
          · rintro ⟨hq1, hq2, hq3⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hq1 with hlt | heq
            · right; exact ⟨hlt, hq2, hq3.trans hmatch.2.symm⟩
            · left; exact heq
          · rintro (heq | ⟨hq1, hq2, hq3⟩)
            · have hqp : q = ⟨p, hp'⟩ := Fin.ext heq
              subst hqp
              exact ⟨Nat.lt_succ_self p, hmatch.1, hmatch.2⟩
            · exact ⟨by omega, hq2, hq3.trans hmatch.2⟩
        have hnot : (⟨p, hp'⟩ : Fin L.length) ∉
            (Finset.univ.filter fun q : Fin L.length =>
              q.1 < p ∧ (L[q.1]'q.isLt).1 = true ∧ (L[q.1]'q.isLt).2.1 = (L[p]'hp').2.1) := by
          simp
        rw [hset, Finset.card_insert_of_notMem hnot, add_comm]
      · have hif : ¬ ((L[p + 1]'hp).1 && (L[p]'hp').1 &&
            ((L[p + 1]'hp).2.1 == (L[p]'hp').2.1)) = true := by
          intro hc
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          exact hmatch ⟨hc.1.2, hc.2.symm⟩
        rw [if_neg hif]
        symm
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro q _ hq
        have hqp : q.1 ≤ p := Nat.le_of_lt_succ hq.1
        have hle1 : occSortKey (L[q.1]'q.isLt) ≤ occSortKey (L[p]'hp') := by
          rcases eq_or_lt_of_le hqp with he | hlt
          · subst he; exact le_rfl
          · exact le_of_lt ((List.pairwise_iff_getElem.mp hpw_L) q.1 p q.isLt hp' hlt)
        have hle2 : occSortKey (L[p]'hp') ≤ occSortKey (L[p + 1]'hp) :=
          le_of_lt ((List.pairwise_iff_getElem.mp hpw_L) p (p + 1) hp' hp (Nat.lt_succ_self p))
        dsimp [occSortKey] at hle1 hle2
        rw [Prod.Lex.le_iff] at hle1 hle2
        simp only [ofLex_toLex, hact, hq.2.1, ↓reduceIte] at hle1 hle2
        have hp_act : (L[p]'hp').1 = true := by
          cases hb : (L[p]'hp').1
          · simp only [hb, Bool.false_eq_true, ↓reduceIte] at hle2
            rcases hle2 with h01 | ⟨h01, _⟩ <;> omega
          · rfl
        simp only [hp_act, ↓reduceIte, Prod.Lex.le_iff, ofLex_toLex] at hle1 hle2
        have hpm : (L[p]'hp').2.1 = (L[p + 1]'hp).2.1 := by
          have ha : (L[q.1]'q.isLt).2.1 ≤ (L[p]'hp').2.1 := by
            rcases hle1 with h0 | ⟨_, h1 | ⟨h1, _⟩⟩
            · exfalso; omega
            · exact le_of_lt h1
            · exact le_of_eq h1
          have hb : (L[p]'hp').2.1 ≤ (L[p + 1]'hp).2.1 := by
            rcases hle2 with h0 | ⟨_, h1 | ⟨h1, _⟩⟩
            · exfalso; omega
            · exact le_of_lt h1
            · exact le_of_eq h1
          omega
        exact hmatch ⟨hp_act, hpm⟩
  intro p hp hact
  rw [hcount p hp hact]
  dsimp [runOcc]
  refine Finset.card_bij (fun q _ => (L[q.1]'q.isLt).2.2) ?_ ?_ ?_
  · intro q hq
    rw [Finset.mem_filter] at hq ⊢
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · have hlt_key := (List.pairwise_iff_getElem.mp hpw_L) q.1 p q.isLt hp hq.2.1
      dsimp [occSortKey] at hlt_key
      rw [Prod.Lex.lt_iff] at hlt_key
      simp only [ofLex_toLex, hact, hq.2.2.1, ↓reduceIte, lt_irrefl, true_and, false_or,
        Prod.Lex.lt_iff, hq.2.2.2] at hlt_key
      exact hlt_key
    · have hmem : L[q.1]'q.isLt ∈ orig := hperm.mem_iff.mp (List.getElem_mem q.isLt)
      simp only [orig, List.mem_map, List.mem_finRange, true_and] at hmem
      rcases hmem with ⟨j, hj_eq⟩
      have hmem_p : L[p]'hp ∈ orig := hperm.mem_iff.mp (List.getElem_mem hp)
      simp only [orig, List.mem_map, List.mem_finRange, true_and] at hmem_p
      rcases hmem_p with ⟨i, hi_eq⟩
      have hj1 : (L[q.1]'q.isLt).2.1 = runOffset l j := by rw [← hj_eq]
      have hj2 : (L[q.1]'q.isLt).2.2 = j := by rw [← hj_eq]
      have hi1 : (L[p]'hp).2.1 = runOffset l i := by rw [← hi_eq]
      have hi2 : (L[p]'hp).2.2 = i := by rw [← hi_eq]
      rw [hj2, hi2, ← hj1, ← hi1, hq.2.2.2]
  · intro q₁ hq₁ q₂ hq₂ heq
    rw [Finset.mem_filter] at hq₁ hq₂
    have hmem1 : L[q₁.1]'q₁.isLt ∈ orig := hperm.mem_iff.mp (List.getElem_mem q₁.isLt)
    have hmem2 : L[q₂.1]'q₂.isLt ∈ orig := hperm.mem_iff.mp (List.getElem_mem q₂.isLt)
    simp only [orig, List.mem_map, List.mem_finRange, true_and] at hmem1 hmem2
    rcases hmem1 with ⟨j₁, hj₁⟩
    rcases hmem2 with ⟨j₂, hj₂⟩
    have hj12 : j₁ = j₂ := by
      have : j₁ = (L[q₁.1]'q₁.isLt).2.2 := by rw [← hj₁]
      have : j₂ = (L[q₂.1]'q₂.isLt).2.2 := by rw [← hj₂]
      omega
    subst hj12
    have hL12 : L[q₁.1]'q₁.isLt = L[q₂.1]'q₂.isLt := hj₁.symm.trans hj₂
    have hkey12 : occSortKey (L[q₁.1]'q₁.isLt) = occSortKey (L[q₂.1]'q₂.isLt) := congrArg occSortKey hL12
    have hinj_k := List.nodup_iff_injective_getElem.mp hnd_L
    have hfin := @hinj_k ⟨q₁.1, by simp [q₁.isLt]⟩ ⟨q₂.1, by simp [q₂.isLt]⟩ (by simpa using hkey12)
    exact Fin.ext (by simpa using congrArg Fin.val hfin)
  · intro j hj
    rw [Finset.mem_filter] at hj
    have hmem_p : L[p]'hp ∈ orig := hperm.mem_iff.mp (List.getElem_mem hp)
    simp only [orig, List.mem_map, List.mem_finRange, true_and] at hmem_p
    rcases hmem_p with ⟨i, hi_eq⟩
    have hi_m : (L[p]'hp).2.1 = runOffset l i := by rw [← hi_eq]
    have hi_act : (L[p]'hp).1 = decide (2 ≤ runOffset l i) := by rw [← hi_eq]
    have hi_i : (L[p]'hp).2.2 = i := by rw [← hi_eq]
    have hj_m : runOffset l j = (L[p]'hp).2.1 := by rw [hi_m, ← hi_i]; exact hj.2.2
    have hj_act : decide (2 ≤ runOffset l j) = true := by rw [hj.2.2, hi_i, ← hi_act]; exact hact
    have hj_mem : (true, runOffset l j, j) ∈ L := by
      rw [hperm.mem_iff]
      simp only [orig, List.mem_map, List.mem_finRange, true_and]
      exact ⟨j, by rw [← hj_act]⟩
    rcases List.getElem_of_mem hj_mem with ⟨q, hq, hq_eq⟩
    have hqp : q < p := by
      by_contra hge
      rcases eq_or_lt_of_le (Nat.le_of_not_lt hge) with rfl | hgt
      · have h1 : j = i := by
          have hpj : (L[p]'hq).2.2 = j := by rw [hq_eq]
          exact hpj.symm.trans hi_i
        have hj' : j < j := by
          calc j < (L[p]'hp).2.2 := hj.2.1
            _ = i := hi_i
            _ = j := h1.symm
        exact absurd hj' (lt_irrefl _)
      · have hlt_k := (List.pairwise_iff_getElem.mp hpw_L) p q hp hq hgt
        rw [hq_eq, ← hi_eq] at hlt_k
        dsimp [occSortKey] at hlt_k
        have hlt_j : i < j := by
          rw [Prod.Lex.lt_iff] at hlt_k
          have h1 : decide (2 ≤ runOffset l i) = true := hi_act ▸ hact
          simp only [ofLex_toLex, h1, ↓reduceIte, lt_irrefl, false_or, true_and, Prod.Lex.lt_iff] at hlt_k
          have hm_eq : runOffset l i = runOffset l j := by rw [← hi_i, hj.2.2]
          rcases hlt_k with hlt_m | ⟨_, hlt_ij⟩
          · omega
          · exact hlt_ij
        rw [← hi_i] at hlt_j
        exact absurd (lt_trans hj.2.1 hlt_j) (lt_irrefl _)
    refine ⟨⟨q, hq⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hq_eq]
      exact ⟨hqp, rfl, hj_m⟩
    · rw [hq_eq]


private lemma getElemBang_eq {α : Type*} [Inhabited α] (l : List α) {i : ℕ} (h : i < l.length) :
    l[i]! = l[i] := by simp [h]

theorem harmBucket_routing_spec {α : Type*} [LinearOrder α] (N B2 : ℕ)
    (hN : N ≤ B2) (hB : (bucketPairs N).length ≤ B2) (l : Fin N → α) (hl : Monotone l) :
    let init := hbInit N B2 l
    let s1 := init.mergeSort (fun x y => decide (hbKey1 x ≤ hbKey1 y))
    let matched := hbSeqPass s1
    let s2 := matched.mergeSort (fun x y => decide (hbKey2 x ≤ hbKey2 y))
    s2.length = 2 * B2 ∧
    (∀ b : Fin B2,
      s2[b.1]!.dest = b.1 ∧
      hbGroup s2[b.1]! = 0 ∧
      (∀ hb : b.1 < (bucketPairs N).length,
        let r := s2[b.1]!
        (r.kind = 0 ↔ ∃ i : Fin N, 2 ≤ runOffset l i ∧
          (runOffset l i, runOcc l i) = (bucketPairs N)[b.1]'hb) ∧
        (r.kind = 0 → r.m = ((bucketPairs N)[b.1]'hb).1 ∧ r.occ = ((bucketPairs N)[b.1]'hb).2 ∧
          r.orig < N ∧ ∃ h : r.orig < N, 2 ≤ runOffset l ⟨r.orig, h⟩) ∧
        (r.kind ≠ 0 → r.kind = 1))) := by
  intro init s1 matched s2
  have hinit_len : init.length = 2 * B2 := by
    simp [init, hbInit]; omega
  have hs1_perm : List.Perm s1 init := List.mergeSort_perm _ _
  have hs1_len : s1.length = 2 * B2 := hs1_perm.length_eq.trans hinit_len
  have hinit_orig_get : ∀ k (hk : k < init.length), (init[k]'hk).orig = k := by
    intro k hk
    dsimp only [init, hbInit] at hk ⊢
    by_cases hkB : k < B2
    · have h1 : k < ((List.finRange B2).map fun i : Fin B2 =>
          (if h : i.1 < N then
            if 2 ≤ runOffset l ⟨i.1, h⟩ then
              { kind := 0, m := runOffset l ⟨i.1, h⟩, occ := runOcc l ⟨i.1, h⟩, dest := 0, orig := i.1 }
            else { kind := 3, m := 0, occ := 0, dest := 0, orig := i.1 }
          else { kind := 3, m := 0, occ := 0, dest := 0, orig := i.1 } : HBRec)).length := by
        simp [hkB]
      rw [List.getElem_append_left h1, List.getElem_map, List.getElem_finRange]
      simp only [Fin.val_cast]
      split_ifs <;> rfl
    · have h1 : ((List.finRange B2).map fun i : Fin B2 =>
          (if h : i.1 < N then
            if 2 ≤ runOffset l ⟨i.1, h⟩ then
              { kind := 0, m := runOffset l ⟨i.1, h⟩, occ := runOcc l ⟨i.1, h⟩, dest := 0, orig := i.1 }
            else { kind := 3, m := 0, occ := 0, dest := 0, orig := i.1 }
          else { kind := 3, m := 0, occ := 0, dest := 0, orig := i.1 } : HBRec)).length ≤ k := by
        simp; omega
      rw [List.getElem_append_right h1, List.getElem_map, List.getElem_finRange]
      simp only [List.length_map, List.length_finRange, Fin.val_cast]
      split_ifs <;> dsimp <;> omega
  have horig_init : init.map HBRec.orig = List.range (2 * B2) := by
    apply List.ext_getElem
    · simp [hinit_len]
    · intro k hk1 hk2
      have hk' : k < init.length := by simpa using hk1
      rw [List.getElem_map, List.getElem_range, hinit_orig_get k hk']
  have hnd_orig : (init.map HBRec.orig).Nodup := by rw [horig_init]; exact List.nodup_range
  have hnd_k1_init : (init.map hbKey1).Nodup := by
    refine List.Nodup.of_map (fun k : ℕ ×ₗ ℕ ×ₗ ℕ ×ₗ ℕ ×ₗ ℕ =>
        (ofLex (ofLex (ofLex (ofLex k).2).2).2).2) ?_
    rw [List.map_map]
    have hm : init.map ((fun k : ℕ ×ₗ ℕ ×ₗ ℕ ×ₗ ℕ ×ₗ ℕ =>
        (ofLex (ofLex (ofLex (ofLex k).2).2).2).2) ∘ hbKey1) = init.map HBRec.orig := rfl
    rw [hm]; exact hnd_orig
  have hs1_lt : s1.Pairwise (fun x y => hbKey1 x < hbKey1 y) :=
    pairwise_lt_of_le_of_nodup hbKey1 s1 (hs1_perm.map hbKey1 |>.nodup_iff.mpr hnd_k1_init)
      (pairwise_le_mergeSort_key hbKey1 init)
  have hs1_nd_orig : (s1.map HBRec.orig).Nodup :=
    hs1_perm.map HBRec.orig |>.nodup_iff.mpr hnd_orig
  let itemMatchB (m occ : ℕ) : Prop :=
    ∃ i : Fin N, 2 ≤ runOffset l i ∧ runOffset l i = m ∧ runOcc l i = occ
  have _ : DecidablePred (fun p : ℕ × ℕ => itemMatchB p.1 p.2) :=
    fun p => Fintype.decidableExistsFintype
  let idealTransform (r : HBRec) : HBRec :=
    if r.kind = 0 then
      { r with dest := (bucketPairs N).idxOf (r.m, r.occ) }
    else if r.kind = 1 ∧ itemMatchB r.m r.occ then
      { r with kind := 2 }
    else r
  -- Every ITEM (kind = 0) in s1 sits immediately left of the unique matching MARKER_FREE (kind = 1)
  have hs1_pair : ∀ (p : ℕ) (hp : p < s1.length), (s1[p]'hp).kind = 0 →
      ∃ hp1 : p + 1 < s1.length,
        (s1[p + 1]'hp1).kind = 1 ∧
        (s1[p + 1]'hp1).m = (s1[p]'hp).m ∧
        (s1[p + 1]'hp1).occ = (s1[p]'hp).occ ∧
        (s1[p + 1]'hp1).dest = (bucketPairs N).idxOf ((s1[p]'hp).m, (s1[p]'hp).occ) := by
    intro p hp hk0
    have hmem_p : s1[p]'hp ∈ init := hs1_perm.mem_iff.mp (List.getElem_mem hp)
    simp only [init, hbInit, List.mem_append, List.mem_map, List.mem_finRange, true_and] at hmem_p
    rcases hmem_p with ⟨i, hi_eq⟩ | ⟨b, hb_eq⟩
    · split_ifs at hi_eq with hiN hrun
      · have hr_m : (s1[p]'hp).m = runOffset l ⟨i.1, hiN⟩ := by rw [← hi_eq]
        have hr_occ : (s1[p]'hp).occ = runOcc l ⟨i.1, hiN⟩ := by rw [← hi_eq]
        have hbp := runOffset_runOcc_mem_bucketPairs hl hrun
        rcases List.getElem_of_mem hbp with ⟨b_idx, hb_idx, hb_val⟩
        have hb_B2 : b_idx < B2 := lt_of_lt_of_le hb_idx hB
        let mrk : HBRec := ⟨1, (bucketPairs N)[b_idx].1, (bucketPairs N)[b_idx].2, b_idx, B2 + b_idx⟩
        have hmrk_init : mrk ∈ init := by
          simp only [init, hbInit, List.mem_append, List.mem_map, List.mem_finRange, true_and]
          right; refine ⟨⟨b_idx, hb_B2⟩, ?_⟩
          simp [hb_idx, mrk]
        have hmrk_s1 : mrk ∈ s1 := hs1_perm.mem_iff.mpr hmrk_init
        rcases List.getElem_of_mem hmrk_s1 with ⟨q, hq, hq_eq⟩
        have hpq : p < q := by
          by_contra hge
          rcases eq_or_lt_of_le (Nat.le_of_not_lt hge) with rfl | hgt
          · have hmrk_k : mrk.kind = 0 := (congrArg HBRec.kind hq_eq.symm).trans hk0
            dsimp [mrk] at hmrk_k
            omega
          · have hlt := (List.pairwise_iff_getElem.mp hs1_lt) q p hq hp hgt
            rw [hq_eq] at hlt
            have hm1 : (s1[p]'hp).m = mrk.m := hr_m.trans (congrArg Prod.fst hb_val).symm
            have ho1 : (s1[p]'hp).occ = mrk.occ := hr_occ.trans (congrArg Prod.snd hb_val).symm
            have hi_p : hbInactive (s1[p]'hp) = 0 := by simp [hbInactive, hk0]
            have hi_m : hbInactive mrk = 0 := by simp [hbInactive, mrk]
            have hr_p : hbKindRank1 (s1[p]'hp) = 0 := by simp [hbKindRank1, hk0]
            have hr_m' : hbKindRank1 mrk = 1 := by simp [hbKindRank1, mrk]
            dsimp [hbKey1] at hlt
            rw [hi_p, hi_m, hr_p, hr_m', hm1, ho1] at hlt
            simp only [Prod.Lex.lt_iff, ofLex_toLex] at hlt
            rcases hlt with h1 | ⟨_, h2 | ⟨_, h3 | ⟨_, h4 | ⟨_, _⟩⟩⟩⟩ <;> omega
        have hp1 : p + 1 < s1.length := by omega
        have hp1_eq : s1[p + 1]'hp1 = mrk := by
          by_contra hne
          have hp1_lt_q : p + 1 < q := by
            rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt hpq) with hlt | heq
            · exact hlt
            · exfalso; subst heq; exact hne hq_eq
          have hlt1 := (List.pairwise_iff_getElem.mp hs1_lt) p (p + 1) hp hp1 (Nat.lt_succ_self p)
          have hlt2 := (List.pairwise_iff_getElem.mp hs1_lt) (p + 1) q hp1 hq hp1_lt_q
          rw [hq_eq] at hlt2
          have hm1 : (s1[p]'hp).m = mrk.m := hr_m.trans (congrArg Prod.fst hb_val).symm
          have ho1 : (s1[p]'hp).occ = mrk.occ := hr_occ.trans (congrArg Prod.snd hb_val).symm
          have hkind1 : hbInactive (s1[p]'hp) = 0 := by simp [hbInactive, hk0]
          have hkindm : hbInactive mrk = 0 := by simp [hbInactive, mrk]
          dsimp [hbKey1] at hlt1 hlt2
          rw [hkind1] at hlt1
          rw [hkindm, ← hm1, ← ho1] at hlt2
          have h12 : hbInactive (s1[p + 1]'hp1) = 0 ∧
              (s1[p + 1]'hp1).m = (s1[p]'hp).m ∧
              (s1[p + 1]'hp1).occ = (s1[p]'hp).occ := by
            simp only [Prod.Lex.lt_iff, ofLex_toLex] at hlt1 hlt2
            have hi0 : hbInactive (s1[p + 1]'hp1) = 0 := by
              rcases hlt1 with h | ⟨h, _⟩ <;> rcases hlt2 with h' | ⟨h', _⟩ <;> omega
            have hm0 : (s1[p + 1]'hp1).m = (s1[p]'hp).m := by
              rcases hlt1 with h | ⟨_, h1 | ⟨h1, _⟩⟩ <;> rcases hlt2 with h' | ⟨_, h2 | ⟨h2, _⟩⟩ <;> omega
            have ho0 : (s1[p + 1]'hp1).occ = (s1[p]'hp).occ := by
              rcases hlt1 with h | ⟨_, h1 | ⟨_, h2 | ⟨h2, _⟩⟩⟩ <;>
                rcases hlt2 with h' | ⟨_, h1' | ⟨_, h2' | ⟨h2', _⟩⟩⟩ <;> omega
            exact ⟨hi0, hm0, ho0⟩
          have hmem_p1 : s1[p + 1]'hp1 ∈ init := hs1_perm.mem_iff.mp (List.getElem_mem hp1)
          simp only [init, hbInit, List.mem_append, List.mem_map, List.mem_finRange, true_and] at hmem_p1
          rcases hmem_p1 with ⟨j, hj_eq⟩ | ⟨b2, hb2_eq⟩
          · split_ifs at hj_eq with hjN hjr
            · have hm_eq' : runOffset l ⟨j.1, hjN⟩ = runOffset l ⟨i.1, hiN⟩ :=
                (by rw [← hj_eq] : runOffset l ⟨j.1, hjN⟩ = (s1[p + 1]'hp1).m).trans (h12.2.1.trans hr_m)
              have ho_eq' : runOcc l ⟨j.1, hjN⟩ = runOcc l ⟨i.1, hiN⟩ :=
                (by rw [← hj_eq] : runOcc l ⟨j.1, hjN⟩ = (s1[p + 1]'hp1).occ).trans (h12.2.2.trans hr_occ)
              have heq_ji : (⟨j.1, hjN⟩ : Fin N) = ⟨i.1, hiN⟩ :=
                runOffset_runOcc_inj l (Prod.ext hm_eq' ho_eq')
              have hji : j = i := Fin.ext (congrArg (Fin.val : Fin N → ℕ) heq_ji)
              subst hji
              have heq_rec : s1[p]'hp = s1[p + 1]'hp1 := hi_eq.symm.trans hj_eq
              have hk_eq : hbKey1 (s1[p]'hp) = hbKey1 (s1[p + 1]'hp1) := congrArg hbKey1 heq_rec
              exact ne_of_lt ((List.pairwise_iff_getElem.mp hs1_lt) p (p + 1) hp hp1 (Nat.lt_succ_self p)) hk_eq
            · have hk3 : (s1[p + 1]'hp1).kind = 3 := by rw [← hj_eq]
              have : hbInactive (s1[p + 1]'hp1) = 1 := by simp [hbInactive, hk3]
              omega
            · have hk3 : (s1[p + 1]'hp1).kind = 3 := by rw [← hj_eq]
              have : hbInactive (s1[p + 1]'hp1) = 1 := by simp [hbInactive, hk3]
              omega
          · split_ifs at hb2_eq with hb2_lt
            · have heq_b : (bucketPairs N)[b2.1]'hb2_lt = (bucketPairs N)[b_idx]'hb_idx := by
                apply Prod.ext
                · have hbm : (s1[p + 1]'hp1).m = ((bucketPairs N)[b2.1]'hb2_lt).1 := by rw [← hb2_eq]
                  exact hbm.symm.trans (h12.2.1.trans (hr_m.trans (congrArg Prod.fst hb_val).symm))
                · have hbo : (s1[p + 1]'hp1).occ = ((bucketPairs N)[b2.1]'hb2_lt).2 := by rw [← hb2_eq]
                  exact hbo.symm.trans (h12.2.2.trans (hr_occ.trans (congrArg Prod.snd hb_val).symm))
              have hinj_bp := List.nodup_iff_injective_getElem.mp (bucketPairs_nodup N)
              have hfin_bp : (⟨b2.1, hb2_lt⟩ : Fin (bucketPairs N).length) = ⟨b_idx, hb_idx⟩ :=
                @hinj_bp ⟨b2.1, hb2_lt⟩ ⟨b_idx, hb_idx⟩ heq_b
              have hb_eq_idx : b2.1 = b_idx := congrArg Fin.val hfin_bp
              have : s1[p + 1]'hp1 = mrk := by rw [← hb2_eq]; simp [mrk, hb_eq_idx]
              exact hne this
            · have hm_gt : N + 1 ≤ (s1[p + 1]'hp1).m := by rw [← hb2_eq]; dsimp; omega
              have hm_le : (s1[p]'hp).m ≤ N := by rw [hr_m]; exact runOffset_le_N l ⟨i.1, hiN⟩
              omega
        refine ⟨hp1, ?_, ?_, ?_, ?_⟩
        · rw [hp1_eq]
        · rw [hp1_eq]; dsimp [mrk]; exact (congrArg Prod.fst hb_val).trans hr_m.symm
        · rw [hp1_eq]; dsimp [mrk]; exact (congrArg Prod.snd hb_val).trans hr_occ.symm
        · rw [hp1_eq]; dsimp [mrk]
          have hp_eq_bp : ((s1[p]'hp).m, (s1[p]'hp).occ) = (bucketPairs N)[b_idx]'hb_idx :=
            (Prod.ext hr_m hr_occ).trans hb_val.symm
          rw [hp_eq_bp]
          exact ((bucketPairs_nodup N).idxOf_getElem b_idx hb_idx).symm
      · exfalso; rw [← hi_eq] at hk0; exact absurd hk0 (by norm_num)
      · exfalso; rw [← hi_eq] at hk0; exact absurd hk0 (by norm_num)
    · exfalso; split_ifs at hb_eq <;> rw [← hb_eq] at hk0 <;> exact absurd hk0 (by norm_num)
  -- Reverse correspondence: matched MARKER_FREE (kind = 1, itemMatchB) sits at p + 1 after ITEM at p
  have hs1_marker_prev : ∀ (q : ℕ) (hq : q < s1.length),
      (s1[q]'hq).kind = 1 → itemMatchB (s1[q]'hq).m (s1[q]'hq).occ →
      ∃ p : ℕ, ∃ hp : p < s1.length, p + 1 = q ∧ (s1[p]'hp).kind = 0 := by
    intro q hq hkq hmatch
    rcases hmatch with ⟨i, hrun, hm_eq, ho_eq⟩
    let it : HBRec := { kind := 0, m := runOffset l i, occ := runOcc l i, dest := 0, orig := i.1 }
    have hit_init : it ∈ init := by
      simp only [init, hbInit, List.mem_append, List.mem_map, List.mem_finRange, true_and]
      left; refine ⟨⟨i.1, lt_of_lt_of_le i.isLt hN⟩, ?_⟩
      simp [i.isLt, hrun, it]
    have hit_s1 : it ∈ s1 := hs1_perm.mem_iff.mpr hit_init
    rcases List.getElem_of_mem hit_s1 with ⟨p, hp, hp_eq⟩
    have hp0 : (s1[p]'hp).kind = 0 := by rw [hp_eq]
    obtain ⟨hp1, hk1, hm1, ho1, _⟩ := hs1_pair p hp hp0
    have hq_pair : s1[p + 1]'hp1 = s1[q]'hq := by
      -- Both are MARKER_FREE in init with the same (m, occ) = (it.m, it.occ)
      have hmem1 : s1[p + 1]'hp1 ∈ init := hs1_perm.mem_iff.mp (List.getElem_mem hp1)
      have hmem2 : s1[q]'hq ∈ init := hs1_perm.mem_iff.mp (List.getElem_mem hq)
      simp only [init, hbInit, List.mem_append, List.mem_map, List.mem_finRange, true_and] at hmem1 hmem2
      rcases hmem1 with ⟨_, h_bad⟩ | ⟨b1, hb1⟩
      · exfalso; split_ifs at h_bad <;> rw [← h_bad] at hk1 <;> exact absurd hk1 (by norm_num)
      rcases hmem2 with ⟨_, h_bad⟩ | ⟨b2, hb2⟩
      · exfalso; split_ifs at h_bad <;> rw [← h_bad] at hkq <;> exact absurd hkq (by norm_num)
      have hm_it : (s1[p]'hp).m = it.m := by rw [hp_eq]
      have ho_it : (s1[p]'hp).occ = it.occ := by rw [hp_eq]
      have hle_m : (s1[q]'hq).m ≤ N := by
        rw [← hm_eq]; exact runOffset_le_N l i
      split_ifs at hb1 with hb1_lt <;> split_ifs at hb2 with hb2_lt
      · have heq_bp : (bucketPairs N)[b1.1]'hb1_lt = (bucketPairs N)[b2.1]'hb2_lt := by
          apply Prod.ext
          · have h1 : (s1[p + 1]'hp1).m = (bucketPairs N)[b1.1].1 := by rw [← hb1]
            have h2 : (s1[q]'hq).m = (bucketPairs N)[b2.1].1 := by rw [← hb2]
            rw [← h1, ← h2, hm1, hm_it, ← hm_eq]
          · have h1 : (s1[p + 1]'hp1).occ = (bucketPairs N)[b1.1].2 := by rw [← hb1]
            have h2 : (s1[q]'hq).occ = (bucketPairs N)[b2.1].2 := by rw [← hb2]
            rw [← h1, ← h2, ho1, ho_it, ← ho_eq]
        have hinj_bp := List.nodup_iff_injective_getElem.mp (bucketPairs_nodup N)
        have hfin_bp : (⟨b1.1, hb1_lt⟩ : Fin (bucketPairs N).length) = ⟨b2.1, hb2_lt⟩ :=
          @hinj_bp ⟨b1.1, hb1_lt⟩ ⟨b2.1, hb2_lt⟩ heq_bp
        have hb12 : b1 = b2 := Fin.ext (congrArg (Fin.val : Fin (bucketPairs N).length → ℕ) hfin_bp)
        subst hb12; exact hb1.symm.trans hb2
      · exfalso; have : N + 1 ≤ (s1[q]'hq).m := by rw [← hb2]; dsimp; omega
        omega
      · exfalso
        have : N + 1 ≤ (s1[p + 1]'hp1).m := by rw [← hb1]; dsimp; omega
        have : (s1[p]'hp).m ≤ N := by rw [hm_it]; exact runOffset_le_N l i
        omega
      · exfalso; have : N + 1 ≤ (s1[q]'hq).m := by rw [← hb2]; dsimp; omega
        omega
    have hfin_eq : p + 1 = q := by
      have horig_eq : (s1[p + 1]'hp1).orig = (s1[q]'hq).orig := congrArg HBRec.orig hq_pair
      have hinj := List.nodup_iff_injective_getElem.mp hs1_nd_orig
      exact congrArg Fin.val (@hinj ⟨p + 1, by simp [hp1]⟩ ⟨q, by simp [hq]⟩ (by simpa using horig_eq))
    exact ⟨p, hp, hfin_eq, hp0⟩
  -- Define exact k-step state for foldl induction
  let stepState (k : ℕ) : List HBRec :=
    s1.mapIdx fun idx r =>
      if idx < k ∧ r.kind = 0 then idealTransform r
      else if 0 < idx ∧ idx - 1 < k ∧ (s1[idx - 1]!).kind = 0 then idealTransform r
      else r
  have hfold_step : ∀ k ≤ s1.length, (List.range k).foldl hbNeighborStep s1 = stepState k := by
    intro k hk
    induction k with
    | zero =>
      simp only [List.range_zero, List.foldl_nil]
      apply List.ext_getElem
      · simp [stepState]
      · intro idx hi1 hi2
        simp [stepState]
    | succ k ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih (by omega)]
      dsimp only [hbNeighborStep]
      have hst_len : (stepState k).length = s1.length := by simp [stepState]
      by_cases hk1 : k + 1 < (stepState k).length
      · rw [dif_pos hk1]
        have hk_s1 : k < s1.length := by omega
        have hk1_s1 : k + 1 < s1.length := by omega
        have hk_eq : (stepState k)[k]'(by omega) =
            if 0 < k ∧ (s1[k - 1]!).kind = 0 then idealTransform (s1[k]'hk_s1) else s1[k]'hk_s1 := by
          simp [stepState]
        have hk1_eq : (stepState k)[k + 1]'hk1 = s1[k + 1]'hk1_s1 := by
          simp only [stepState, List.getElem_mapIdx]
          have h1 : ¬ (k + 1 < k ∧ (s1[k + 1]'hk1_s1).kind = 0) := by omega
          have h2 : ¬ (0 < k + 1 ∧ (k + 1) - 1 < k ∧ (s1[(k + 1) - 1]!).kind = 0) := by omega
          rw [if_neg h1, if_neg h2]
        by_cases hk0 : (s1[k]'hk_s1).kind = 0
        · have hnot_prev : ¬ (0 < k ∧ (s1[k - 1]!).kind = 0) := by
            rintro ⟨hkpos, hp0⟩
            have hkm1 : k - 1 < s1.length := by omega
            rw [getElemBang_eq s1 hkm1] at hp0
            obtain ⟨hk1', hkind1, _⟩ := hs1_pair (k - 1) hkm1 hp0
            have hkeq : k - 1 + 1 = k := by omega
            have hkind1' : (s1[k]'hk_s1).kind = 1 := by
              simpa [hkeq] using hkind1
            omega
          have hcur0 : (stepState k)[k]'(by omega) = s1[k]'hk_s1 := by
            rw [hk_eq, if_neg hnot_prev]
          obtain ⟨hk1', hkind1, hm1, ho1, hdest1⟩ := hs1_pair k hk_s1 hk0
          have hcond : ((stepState k)[k]'(by omega)).kind = 0 ∧
              ((stepState k)[k + 1]'hk1).kind = 1 ∧
              ((stepState k)[k]'(by omega)).m = ((stepState k)[k + 1]'hk1).m ∧
              ((stepState k)[k]'(by omega)).occ = ((stepState k)[k + 1]'hk1).occ := by
            rw [hcur0, hk1_eq]
            exact ⟨hk0, hkind1, hm1.symm, ho1.symm⟩
          rw [if_pos hcond, hcur0, hk1_eq]
          apply List.ext_getElem
          · simp [stepState]
          · intro idx hi1 hi2
            have hi_s1 : idx < s1.length := by simpa [stepState] using hi2
            rcases eq_or_ne idx (k + 1) with heq1 | hne1
            · subst heq1
              rw [List.getElem_set_self (by simp [hst_len]; exact hk1_s1)]
              simp only [stepState, List.getElem_mapIdx]
              have ha : ¬ (k + 1 < k + 1 ∧ (s1[k + 1]'hk1_s1).kind = 0) := by
                intro ⟨hlt, _⟩; exact Nat.lt_irrefl _ hlt
              have hb : 0 < k + 1 ∧ k + 1 - 1 < k + 1 ∧ (s1[k + 1 - 1]!).kind = 0 := by
                refine ⟨by omega, by omega, ?_⟩
                have hk_eq' : k + 1 - 1 = k := by omega
                rw [hk_eq', getElemBang_eq s1 hk_s1]; exact hk0
              rw [if_neg ha, if_pos hb]
              have hmem : ∃ i : Fin N, 2 ≤ runOffset l i ∧
                  runOffset l i = (s1[k + 1]'hk1_s1).m ∧ runOcc l i = (s1[k + 1]'hk1_s1).occ := by
                have hmem_k : s1[k]'hk_s1 ∈ init := hs1_perm.mem_iff.mp (List.getElem_mem hk_s1)
                simp only [init, hbInit, List.mem_append, List.mem_map, List.mem_finRange, true_and] at hmem_k
                rcases hmem_k with ⟨i, hi_eq⟩ | ⟨b, hb_eq⟩
                · split_ifs at hi_eq with hiN hrun
                  · refine ⟨⟨i.1, hiN⟩, hrun, ?_, ?_⟩
                    · have : (s1[k]'hk_s1).m = runOffset l ⟨i.1, hiN⟩ := by rw [← hi_eq]
                      rw [← this]; exact hm1.symm
                    · have : (s1[k]'hk_s1).occ = runOcc l ⟨i.1, hiN⟩ := by rw [← hi_eq]
                      rw [← this]; exact ho1.symm
                  · exfalso; rw [← hi_eq] at hk0; exact absurd hk0 (by norm_num)
                  · exfalso; rw [← hi_eq] at hk0; exact absurd hk0 (by norm_num)
                · exfalso; split_ifs at hb_eq <;> rw [← hb_eq] at hk0 <;> exact absurd hk0 (by norm_num)
              have hne0 : (s1[k + 1]'hk1_s1).kind ≠ 0 := by omega
              have hmatch1 : (s1[k + 1]'hk1_s1).kind = 1 ∧
                  itemMatchB (s1[k + 1]'hk1_s1).m (s1[k + 1]'hk1_s1).occ := ⟨hkind1, hmem⟩
              dsimp [idealTransform]
              rw [if_neg hne0, if_pos hmatch1]
            · rw [List.getElem_set_ne (by omega)]
              rcases eq_or_ne idx k with rfl | hne0
              · rw [List.getElem_set_self (by simp [hst_len]; exact hk_s1)]
                simp only [stepState, List.getElem_mapIdx]
                rw [if_pos ⟨Nat.lt_succ_self idx, hk0⟩]
                dsimp [idealTransform]
                rw [if_pos hk0]
                ext <;> simp [hdest1]
              · rw [List.getElem_set_ne (by omega)]
                simp only [stepState, List.getElem_mapIdx]
                have h1 : (idx < k ∧ (s1[idx]'hi_s1).kind = 0) ↔ (idx < k + 1 ∧ (s1[idx]'hi_s1).kind = 0) := by
                  constructor <;> intro h <;> exact ⟨by omega, h.2⟩
                have h2 : (0 < idx ∧ idx - 1 < k ∧ (s1[idx - 1]!).kind = 0) ↔
                    (0 < idx ∧ idx - 1 < k + 1 ∧ (s1[idx - 1]!).kind = 0) := by
                  constructor <;> intro h <;> exact ⟨h.1, by omega, h.2.2⟩
                simp only [h1, h2]
        · have hnot0 : ((stepState k)[k]'(by omega)).kind ≠ 0 := by
            rw [hk_eq]
            split_ifs with hprev
            · dsimp [idealTransform]
              split_ifs <;> simp [hk0]
            · exact hk0
          rw [if_neg (fun hc => hnot0 hc.1)]
          apply List.ext_getElem
          · simp [stepState]
          · intro idx hi1 hi2
            have hi_s1 : idx < s1.length := by simpa [stepState] using hi2
            simp only [stepState, List.getElem_mapIdx]
            have h1 : (idx < k ∧ (s1[idx]'hi_s1).kind = 0) ↔ (idx < k + 1 ∧ (s1[idx]'hi_s1).kind = 0) := by
              constructor
              · intro h; exact ⟨by omega, h.2⟩
              · intro ⟨hlt, hkind⟩
                rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h | rfl
                · exact ⟨h, hkind⟩
                · exact absurd hkind hk0
            have h2 : (0 < idx ∧ idx - 1 < k ∧ (s1[idx - 1]!).kind = 0) ↔
                (0 < idx ∧ idx - 1 < k + 1 ∧ (s1[idx - 1]!).kind = 0) := by
              constructor
              · intro h; exact ⟨h.1, by omega, h.2.2⟩
              · intro ⟨hpos, hlt, hkind⟩
                rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h | heq
                · exact ⟨hpos, h, hkind⟩
                · exfalso
                  have hk_eq' : idx - 1 = k := heq
                  rw [hk_eq', getElemBang_eq s1 hk_s1] at hkind
                  exact hk0 hkind
            simp only [h1, h2]
      · rw [dif_neg hk1]
        have hk_last : k + 1 = s1.length := by omega
        have hk_s1 : k < s1.length := by omega
        have hnot_k : (s1[k]'hk_s1).kind ≠ 0 := by
          intro hk0
          obtain ⟨hp1, _⟩ := hs1_pair k hk_s1 hk0
          omega
        apply List.ext_getElem
        · simp [stepState]
        · intro idx hi1 hi2
          have hi_s1 : idx < s1.length := by simpa [stepState] using hi2
          simp only [stepState, List.getElem_mapIdx]
          have h1 : (idx < k ∧ (s1[idx]'hi_s1).kind = 0) ↔ (idx < k + 1 ∧ (s1[idx]'hi_s1).kind = 0) := by
            constructor
            · intro h; exact ⟨by omega, h.2⟩
            · intro ⟨hlt, hkind⟩
              rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h | rfl
              · exact ⟨h, hkind⟩
              · exact absurd hkind hnot_k
          have h2 : (0 < idx ∧ idx - 1 < k ∧ (s1[idx - 1]!).kind = 0) ↔
              (0 < idx ∧ idx - 1 < k + 1 ∧ (s1[idx - 1]!).kind = 0) := by
            constructor
            · intro h; exact ⟨h.1, by omega, h.2.2⟩
            · intro ⟨hpos, hlt, hkind⟩
              rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h | heq
              · exact ⟨hpos, h, hkind⟩
              · exfalso
                have hk_eq' : idx - 1 = k := heq
                rw [hk_eq', getElemBang_eq s1 hk_s1] at hkind
                exact hnot_k hkind
          simp only [h1, h2]
  have hfold : matched = s1.map idealTransform := by
    dsimp [matched, hbSeqPass]
    rw [hfold_step s1.length le_rfl]
    apply List.ext_getElem
    · simp [stepState]
    · intro idx hi1 hi2
      have hi_s1 : idx < s1.length := by simpa using hi2
      simp only [stepState, List.getElem_mapIdx, List.getElem_map, hi_s1, true_and]
      by_cases hk0 : (s1[idx]'hi_s1).kind = 0
      · rw [if_pos hk0]
      · rw [if_neg hk0]
        by_cases hprev : 0 < idx ∧ (s1[idx - 1]!).kind = 0
        · have hidx1 : idx - 1 < s1.length := by omega
          have hprev0 : (s1[idx - 1]'hidx1).kind = 0 := by
            rw [← getElemBang_eq s1 hidx1]; exact hprev.2
          rw [if_pos ⟨hprev.1, by omega, hprev.2⟩]
        · rw [if_neg (fun ⟨hpos, _, hkind⟩ => hprev ⟨hpos, hkind⟩)]
          dsimp [idealTransform]
          rw [if_neg hk0]
          split_ifs with hm
          · exfalso
            obtain ⟨p, hp, hpq, hp0⟩ := hs1_marker_prev idx hi_s1 hm.1 hm.2
            have hp_eq : idx - 1 = p := by omega
            apply hprev ⟨by omega, ?_⟩
            rw [hp_eq, getElemBang_eq s1 hp]
            exact hp0
          · rfl
  -- Now prove s2 length, group-0 uniqueness on dest < B2, and exact slot property!
  have hm_perm : List.Perm matched (init.map idealTransform) := by
    rw [hfold]; exact hs1_perm.map idealTransform
  have hs2_perm : List.Perm s2 (init.map idealTransform) := (List.mergeSort_perm _ _).trans hm_perm
  have hs2_len : s2.length = 2 * B2 := by rw [hs2_perm.length_eq, List.length_map, hinit_len]
  -- Group-0 elements in (init.map idealTransform) have dest ∈ [0, B2) in bijection with Fin B2!
  have hg0_inj : ∀ r₁ ∈ init.map idealTransform, ∀ r₂ ∈ init.map idealTransform,
      hbKey2 r₁ = hbKey2 r₂ → r₁ = r₂ := by
    intro r₁ hr₁ r₂ hr₂ hkey
    have horig_eq : r₁.orig = r₂.orig :=
      congrArg (fun k : ℕ ×ₗ ℕ ×ₗ ℕ => (ofLex (ofLex k).2).2) hkey
    rw [List.mem_map] at hr₁ hr₂
    rcases hr₁ with ⟨x₁, hx₁, rfl⟩
    rcases hr₂ with ⟨x₂, hx₂, rfl⟩
    have hx_orig : x₁.orig = x₂.orig := by
      have h1 : (idealTransform x₁).orig = x₁.orig := by dsimp [idealTransform]; split_ifs <;> rfl
      have h2 : (idealTransform x₂).orig = x₂.orig := by dsimp [idealTransform]; split_ifs <;> rfl
      rw [← h1, ← h2, horig_eq]
    rcases List.getElem_of_mem hx₁ with ⟨i₁, hi₁, rfl⟩
    rcases List.getElem_of_mem hx₂ with ⟨i₂, hi₂, rfl⟩
    have hinj := List.nodup_iff_injective_getElem.mp hnd_orig
    have hfin := @hinj ⟨i₁, by simp [hi₁]⟩ ⟨i₂, by simp [hi₂]⟩ (by simpa using hx_orig)
    have hieq : i₁ = i₂ := by simpa using congrArg Fin.val hfin
    subst hieq; rfl
  have hnd_k2_init : ((init.map idealTransform).map hbKey2).Nodup := by
    refine List.Nodup.of_map (fun k : ℕ ×ₗ ℕ ×ₗ ℕ => (ofLex (ofLex k).2).2) ?_
    rw [List.map_map, List.map_map]
    have hmap_eq : init.map (((fun k : ℕ ×ₗ ℕ ×ₗ ℕ => (ofLex (ofLex k).2).2) ∘ hbKey2) ∘ idealTransform) =
        init.map HBRec.orig := by
      refine List.map_congr_left fun x _ => ?_
      dsimp [hbKey2, idealTransform]; split_ifs <;> rfl
    rw [hmap_eq]; exact hnd_orig
  have hs2_lt : s2.Pairwise (fun x y => hbKey2 x < hbKey2 y) :=
    pairwise_lt_of_le_of_nodup hbKey2 s2 ((hs2_perm.map hbKey2).nodup_iff.mpr hnd_k2_init)
      (pairwise_le_mergeSort_key hbKey2 matched)
  -- For every b : Fin B2, there is a unique group-0 record in s2 with dest = b.1!
  have hex_b : ∀ b : Fin B2, ∃ r ∈ s2, hbGroup r = 0 ∧ r.dest = b.1 := by
    intro b
    by_cases hb_lt : b.1 < (bucketPairs N).length
    · set pair := (bucketPairs N)[b.1]'hb_lt
      by_cases hm : itemMatchB pair.1 pair.2
      · rcases hm with ⟨i, hrun, hm_eq, ho_eq⟩
        let x : HBRec := { kind := 0, m := runOffset l i, occ := runOcc l i, dest := 0, orig := i.1 }
        have hx_init : x ∈ init := by
          simp only [init, hbInit, List.mem_append, List.mem_map, List.mem_finRange, true_and]
          left; refine ⟨⟨i.1, lt_of_lt_of_le i.isLt hN⟩, ?_⟩
          simp [i.isLt, hrun, x]
        have hr_s2 : idealTransform x ∈ s2 := hs2_perm.mem_iff.mpr (List.mem_map_of_mem hx_init)
        refine ⟨idealTransform x, hr_s2, ?_, ?_⟩
        · simp [idealTransform, x, hbGroup]
        · have hpair_eq : (x.m, x.occ) = pair := Prod.ext hm_eq ho_eq
          simp only [idealTransform, x, ↓reduceIte]
          rw [hpair_eq]
          exact (bucketPairs_nodup N).idxOf_getElem b.1 hb_lt
      · let x : HBRec := { kind := 1, m := pair.1, occ := pair.2, dest := b.1, orig := B2 + b.1 }
        have hx_init : x ∈ init := by
          simp only [init, hbInit, List.mem_append, List.mem_map, List.mem_finRange, true_and]
          right; refine ⟨b, ?_⟩
          simp [hb_lt, x, pair]
        have hr_s2 : idealTransform x ∈ s2 := hs2_perm.mem_iff.mpr (List.mem_map_of_mem hx_init)
        have hnot1 : x.kind ≠ 0 := by simp [x]
        have hnot2 : ¬ (x.kind = 1 ∧ itemMatchB x.m x.occ) := fun hc => hm hc.2
        refine ⟨idealTransform x, hr_s2, ?_, ?_⟩
        · dsimp only [idealTransform]
          rw [if_neg hnot1, if_neg hnot2]
          simp [hbGroup, x]
        · dsimp only [idealTransform]
          rw [if_neg hnot1, if_neg hnot2]
    · let x : HBRec := { kind := 1, m := N + 1 + b.1, occ := 0, dest := b.1, orig := B2 + b.1 }
      have hx_init : x ∈ init := by
        simp only [init, hbInit, List.mem_append, List.mem_map, List.mem_finRange, true_and]
        right; refine ⟨b, ?_⟩
        simp [hb_lt, x]
      have hr_s2 : idealTransform x ∈ s2 := hs2_perm.mem_iff.mpr (List.mem_map_of_mem hx_init)
      have hnotm : ¬ itemMatchB (N + 1 + b.1) 0 := by
        rintro ⟨i, _, hm_eq, _⟩
        have := runOffset_le_N l i
        omega
      have hnot1 : x.kind ≠ 0 := by simp [x]
      have hnot2 : ¬ (x.kind = 1 ∧ itemMatchB x.m x.occ) := fun hc => hnotm hc.2
      refine ⟨idealTransform x, hr_s2, ?_, ?_⟩
      · dsimp only [idealTransform]
        rw [if_neg hnot1, if_neg hnot2]
        simp [hbGroup, x]
      · dsimp only [idealTransform]
        rw [if_neg hnot1, if_neg hnot2]
  -- Also prove every group-0 element in s2 has dest < B2 and dest's in group-0 are distinct!
  have hg0_bound : ∀ r ∈ s2, hbGroup r = 0 → r.dest < B2 := by
    intro r hr hg0
    rw [hs2_perm.mem_iff, List.mem_map] at hr
    rcases hr with ⟨x, hx, rfl⟩
    simp only [init, hbInit, List.mem_append, List.mem_map, List.mem_finRange, true_and] at hx
    rcases hx with ⟨i, hi_eq⟩ | ⟨b, hb_eq⟩
    · split_ifs at hi_eq with hiN hrun
      · rw [← hi_eq]
        simp only [idealTransform, ↓reduceIte]
        have hbp := runOffset_runOcc_mem_bucketPairs hl hrun
        have hidx_lt : (bucketPairs N).idxOf (runOffset l ⟨i.1, hiN⟩, runOcc l ⟨i.1, hiN⟩) <
            (bucketPairs N).length := List.idxOf_lt_length_of_mem hbp
        exact lt_of_lt_of_le hidx_lt hB
      · exfalso; rw [← hi_eq] at hg0; simp [idealTransform, hbGroup] at hg0
      · exfalso; rw [← hi_eq] at hg0; simp [idealTransform, hbGroup] at hg0
    · split_ifs at hb_eq with hb_lt <;> rw [← hb_eq] at hg0 ⊢
      · dsimp [idealTransform] at hg0 ⊢
        split_ifs at hg0 ⊢
        · exact absurd hg0 (by simp [hbGroup])
        · exact b.isLt
      · dsimp [idealTransform] at hg0 ⊢
        split_ifs at hg0 ⊢
        · exact absurd hg0 (by simp [hbGroup])
        · exact b.isLt
  have hg0_dest_uniq : ∀ r₁ ∈ s2, ∀ r₂ ∈ s2,
      hbGroup r₁ = 0 → hbGroup r₂ = 0 → r₁.dest = r₂.dest → r₁ = r₂ := by
    intro r₁ hr₁ r₂ hr₂ hg1 hg2 hdest
    rw [hs2_perm.mem_iff, List.mem_map] at hr₁ hr₂
    rcases hr₁ with ⟨x₁, hx₁, rfl⟩
    rcases hr₂ with ⟨x₂, hx₂, rfl⟩
    simp only [init, hbInit, List.mem_append, List.mem_map, List.mem_finRange, true_and] at hx₁ hx₂
    -- Case analysis on whether x₁, x₂ are ITEM or MARKER_FREE
    have hcase : ∀ x ∈ init, hbGroup (idealTransform x) = 0 →
        ∃ d < B2, (idealTransform x).dest = d ∧
          ((x.kind = 0 ∧ ∃ i : Fin N, 2 ≤ runOffset l i ∧ x.orig = i.1 ∧
              ∃ hd : d < (bucketPairs N).length, (runOffset l i, runOcc l i) = (bucketPairs N)[d]'hd) ∨
           (x.kind = 1 ∧ x.orig = B2 + d ∧
              (∀ hd : d < (bucketPairs N).length, ¬ itemMatchB (bucketPairs N)[d].1 (bucketPairs N)[d].2))) := by
      intro x hx hgx
      simp only [init, hbInit, List.mem_append, List.mem_map, List.mem_finRange, true_and] at hx
      rcases hx with ⟨i, hi_eq⟩ | ⟨b, hb_eq⟩
      · split_ifs at hi_eq with hiN hrun
        · subst hi_eq
          have hbp := runOffset_runOcc_mem_bucketPairs hl hrun
          rcases List.getElem_of_mem hbp with ⟨d_bp, hd_bp, hd_bp_eq⟩
          have hidx_eq : (bucketPairs N).idxOf (runOffset l ⟨i.1, hiN⟩, runOcc l ⟨i.1, hiN⟩) = d_bp := by
            rw [← hd_bp_eq]
            exact (bucketPairs_nodup N).idxOf_getElem d_bp hd_bp
          refine ⟨d_bp, lt_of_lt_of_le hd_bp hB, ?_, Or.inl ⟨rfl, ⟨i.1, hiN⟩, hrun, rfl, hd_bp, hd_bp_eq.symm⟩⟩
          simp [idealTransform, hidx_eq]
        · exfalso; rw [← hi_eq] at hgx; simp [idealTransform, hbGroup] at hgx
        · exfalso; rw [← hi_eq] at hgx; simp [idealTransform, hbGroup] at hgx
      · split_ifs at hb_eq with hb_lt <;> subst hb_eq
        · have hnot1 : (HBRec.mk 1 (bucketPairs N)[b.1].1 (bucketPairs N)[b.1].2 b.1 (B2 + b.1)).kind ≠ 0 := by
            simp
          dsimp only [idealTransform] at hgx ⊢
          rw [if_neg hnot1] at hgx ⊢
          split_ifs at hgx with hm
          · exact absurd hgx (by simp [hbGroup])
          · have hnm : ¬ itemMatchB (bucketPairs N)[b.1].1 (bucketPairs N)[b.1].2 :=
              fun h => hm ⟨rfl, h⟩
            refine ⟨b.1, b.isLt, ?_, Or.inr ⟨rfl, rfl, fun _ => hnm⟩⟩
            rw [if_neg hm]
        · have hnot1 : (HBRec.mk 1 (N + 1 + b.1) 0 b.1 (B2 + b.1)).kind ≠ 0 := by simp
          dsimp only [idealTransform] at hgx ⊢
          rw [if_neg hnot1] at hgx ⊢
          have hnotm : ¬ itemMatchB (N + 1 + b.1) 0 := by
            rintro ⟨i, _, hm_eq, _⟩; have := runOffset_le_N l i; omega
          have hnot2 : ¬ ((HBRec.mk 1 (N + 1 + b.1) 0 b.1 (B2 + b.1)).kind = 1 ∧
              itemMatchB (N + 1 + b.1) 0) :=
            fun hc => hnotm hc.2
          rw [if_neg hnot2]
          refine ⟨b.1, b.isLt, rfl, Or.inr ⟨rfl, rfl, fun h => absurd h hb_lt⟩⟩
    have hx1_in : x₁ ∈ init := by
      simp only [init, hbInit, List.mem_append, List.mem_map, List.mem_finRange, true_and]
      exact hx₁
    have hx2_in : x₂ ∈ init := by
      simp only [init, hbInit, List.mem_append, List.mem_map, List.mem_finRange, true_and]
      exact hx₂
    have init_inj_orig : ∀ a ∈ init, ∀ b ∈ init, a.orig = b.orig → a = b := by
      intro a ha b hb hor
      rcases List.getElem_of_mem ha with ⟨ia, hia, rfl⟩
      rcases List.getElem_of_mem hb with ⟨ib, hib, rfl⟩
      have hinj := List.nodup_iff_injective_getElem.mp hnd_orig
      have hfin := @hinj ⟨ia, by simp [hia]⟩ ⟨ib, by simp [hib]⟩ (by simpa using hor)
      have hieq : ia = ib := by simpa using congrArg Fin.val hfin
      subst hieq; rfl
    obtain ⟨d₁, hd1, hd1_eq, hc1⟩ := hcase x₁ hx1_in hg1
    obtain ⟨d₂, hd2, hd2_eq, hc2⟩ := hcase x₂ hx2_in hg2
    have hd12 : d₁ = d₂ := by rw [← hd1_eq, ← hd2_eq, hdest]
    subst hd12
    rcases hc1 with ⟨_, i₁, hrun1, ho1, hd_lt1, hbp1⟩ | ⟨_, ho1, hnm1⟩ <;>
    rcases hc2 with ⟨_, i₂, hrun2, ho2, hd_lt2, hbp2⟩ | ⟨_, ho2, hnm2⟩
    · have hi12 : i₁ = i₂ := runOffset_runOcc_inj l (hbp1.trans hbp2.symm)
      subst hi12
      rw [init_inj_orig x₁ hx1_in x₂ hx2_in (ho1.trans ho2.symm)]
    · exfalso; exact hnm2 hd_lt1 ⟨i₁, hrun1, congrArg Prod.fst hbp1, congrArg Prod.snd hbp1⟩
    · exfalso; exact hnm1 hd_lt2 ⟨i₂, hrun2, congrArg Prod.fst hbp2, congrArg Prod.snd hbp2⟩
    · rw [init_inj_orig x₁ hx1_in x₂ hx2_in (ho1.trans ho2.symm)]
  -- Combine hex_b + hg0_bound + hg0_dest_uniq + hs2_lt to get exact index b!
  refine ⟨hs2_len, fun b => ?_⟩
  obtain ⟨rb, hrb_s2, hrb_g0, hrb_dest⟩ := hex_b b
  rcases List.getElem_of_mem hrb_s2 with ⟨pos, hpos, hpos_eq⟩
  have hpos_b : pos = b.1 := by
    have hcard_pos : (Finset.univ.filter fun q : Fin s2.length => q.1 < pos).card = pos :=
      card_fin_lt pos (le_of_lt hpos)
    rw [← hcard_pos, ← Finset.card_range b.1]
    refine Finset.card_bij (fun q _ => (s2[q.1]'q.isLt).dest) ?_ ?_ ?_
    · intro q hq
      rw [Finset.mem_filter] at hq
      rw [Finset.mem_range]
      have hlt_k2 := (List.pairwise_iff_getElem.mp hs2_lt) q.1 pos q.isLt hpos hq.2
      rw [hpos_eq] at hlt_k2
      dsimp [hbKey2] at hlt_k2
      rw [hrb_g0, hrb_dest] at hlt_k2
      simp only [Prod.Lex.lt_iff, ofLex_toLex] at hlt_k2
      have hqg0 : hbGroup (s2[q.1]'q.isLt) = 0 := by
        rcases hlt_k2 with h | ⟨h, _⟩ <;> omega
      have hqd_le : (s2[q.1]'q.isLt).dest ≤ b.1 := by
        rcases hlt_k2 with h | ⟨_, h1 | ⟨h1, _⟩⟩
        · omega
        · exact le_of_lt h1
        · exact le_of_eq h1
      rcases lt_or_eq_of_le hqd_le with hlt | heq
      · exact hlt
      · exfalso
        have hq_eq := hg0_dest_uniq _ (List.getElem_mem q.isLt) _ hrb_s2 hqg0 hrb_g0 (heq.trans hrb_dest.symm)
        have hlt_orig := (List.pairwise_iff_getElem.mp hs2_lt) q.1 pos q.isLt hpos hq.2
        rw [hpos_eq, hq_eq] at hlt_orig
        exact lt_irrefl _ hlt_orig
    · intro q₁ hq₁ q₂ hq₂ heq
      rw [Finset.mem_filter] at hq₁ hq₂
      have hg1 : hbGroup (s2[q₁.1]'q₁.isLt) = 0 := by
        have hlt := (List.pairwise_iff_getElem.mp hs2_lt) q₁.1 pos q₁.isLt hpos hq₁.2
        rw [hpos_eq] at hlt; dsimp [hbKey2] at hlt; rw [hrb_g0, Prod.Lex.lt_iff] at hlt
        simp only [ofLex_toLex] at hlt
        rcases hlt with h | ⟨h, _⟩ <;> omega
      have hg2 : hbGroup (s2[q₂.1]'q₂.isLt) = 0 := by
        have hlt := (List.pairwise_iff_getElem.mp hs2_lt) q₂.1 pos q₂.isLt hpos hq₂.2
        rw [hpos_eq] at hlt; dsimp [hbKey2] at hlt; rw [hrb_g0, Prod.Lex.lt_iff] at hlt
        simp only [ofLex_toLex] at hlt
        rcases hlt with h | ⟨h, _⟩ <;> omega
      have hreq := hg0_dest_uniq _ (List.getElem_mem q₁.isLt) _ (List.getElem_mem q₂.isLt) hg1 hg2 heq
      have hkeq : hbKey2 (s2[q₁.1]'q₁.isLt) = hbKey2 (s2[q₂.1]'q₂.isLt) := congrArg hbKey2 hreq
      have hnd_s2 : (s2.map hbKey2).Nodup :=
        (hs2_perm.map hbKey2).nodup_iff.mpr hnd_k2_init
      have hinj := List.nodup_iff_injective_getElem.mp hnd_s2
      have hfin := @hinj ⟨q₁.1, by simp [q₁.isLt]⟩ ⟨q₂.1, by simp [q₂.isLt]⟩ (by simpa using hkeq)
      exact Fin.ext (by simpa using congrArg Fin.val hfin)
    · intro d hd
      rw [Finset.mem_range] at hd
      obtain ⟨rd, hrd_s2, hrd_g0, hrd_dest⟩ := hex_b ⟨d, lt_trans hd b.isLt⟩
      rcases List.getElem_of_mem hrd_s2 with ⟨qd, hqd, hqd_eq⟩
      have hq_lt : qd < pos := by
        by_contra hge
        rcases eq_or_lt_of_le (Nat.le_of_not_lt hge) with rfl | hgt
        · rw [hpos_eq] at hqd_eq
          dsimp only [Fin.val_mk] at hrd_dest
          have : d = b.1 := by rw [← hrd_dest, ← hqd_eq, hrb_dest]
          omega
        · have hlt := (List.pairwise_iff_getElem.mp hs2_lt) pos qd hpos hqd hgt
          rw [hpos_eq, hqd_eq] at hlt
          dsimp [hbKey2] at hlt
          rw [hrb_g0, hrd_g0, hrb_dest, hrd_dest, Prod.Lex.lt_iff] at hlt
          simp only [ofLex_toLex, lt_irrefl, false_or, true_and, Prod.Lex.lt_iff] at hlt
          rcases hlt with h | ⟨h, _⟩ <;> omega
      exact ⟨⟨qd, hqd⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq_lt⟩, by rw [hqd_eq, hrd_dest]⟩
  have hb_eq_rb : s2[b.1]! = rb := by
    have hb_s2 : b.1 < s2.length := by omega
    rw [getElemBang_eq s2 hb_s2]
    have : s2[b.1]'hb_s2 = s2[pos]'hpos := by congr 1; exact hpos_b.symm
    rw [this, hpos_eq]
  refine ⟨by rw [hb_eq_rb, hrb_dest], by rw [hb_eq_rb, hrb_g0], fun hb_lt => ?_⟩
  rw [hb_eq_rb]
  have hrb_mem : rb ∈ init.map idealTransform := hs2_perm.mem_iff.mp hrb_s2
  rw [List.mem_map] at hrb_mem
  rcases hrb_mem with ⟨x, hx, rfl⟩
  simp only [init, hbInit, List.mem_append, List.mem_map, List.mem_finRange, true_and] at hx
  rcases hx with ⟨i, hi_eq⟩ | ⟨b', hb'_eq⟩
  · split_ifs at hi_eq with hiN hrun
    · subst hi_eq
      have hdest_eq : (bucketPairs N).idxOf (runOffset l ⟨i.1, hiN⟩, runOcc l ⟨i.1, hiN⟩) = b.1 := by
        simpa [idealTransform] using hrb_dest
      have hbp_mem := runOffset_runOcc_mem_bucketPairs hl hrun
      rcases List.getElem_of_mem hbp_mem with ⟨idx, hidx, hidx_eq⟩
      have hidx_b : idx = b.1 := by
        have := (bucketPairs_nodup N).idxOf_getElem idx hidx
        rw [hidx_eq] at this
        exact this.symm.trans hdest_eq
      subst hidx_b
      refine ⟨?_, ?_, ?_⟩
      · constructor
        · intro _; exact ⟨⟨i.1, hiN⟩, hrun, hidx_eq.symm⟩
        · intro _; rfl
      · intro _
        let r : HBRec := HBRec.mk 0 (runOffset l ⟨i.1, hiN⟩) (runOcc l ⟨i.1, hiN⟩) 0 i.1
        have hm_eq : (idealTransform r).m = ((bucketPairs N)[b.1]'hidx).1 := by
          simp [idealTransform, r]; exact congrArg Prod.fst hidx_eq.symm
        have ho_eq : (idealTransform r).occ = ((bucketPairs N)[b.1]'hidx).2 := by
          simp [idealTransform, r]; exact congrArg Prod.snd hidx_eq.symm
        exact ⟨hm_eq, ho_eq, hiN, hiN, hrun⟩
      · intro hne; exfalso; exact hne (by simp [idealTransform])
    · exfalso; rw [← hi_eq] at hrb_g0; simp [idealTransform, hbGroup] at hrb_g0
    · exfalso; rw [← hi_eq] at hrb_g0; simp [idealTransform, hbGroup] at hrb_g0
  · split_ifs at hb'_eq with hb'_lt <;> subst hb'_eq
    · have hnot1 : (HBRec.mk 1 (bucketPairs N)[b'.1].1 (bucketPairs N)[b'.1].2 b'.1 (B2 + b'.1)).kind ≠ 0 := by
        simp
      dsimp only [idealTransform] at hrb_g0 hrb_dest ⊢
      rw [if_neg hnot1] at hrb_g0 hrb_dest ⊢
      split_ifs at hrb_g0 hrb_dest ⊢ with hm
      · exfalso; simp [hbGroup] at hrb_g0
      · have hb'_eq_b : b' = b := Fin.ext hrb_dest
        subst hb'_eq_b
        refine ⟨?_, ?_, ?_⟩
        · constructor
          · intro h0; exfalso; exact absurd h0 (by norm_num)
          · rintro ⟨i, hrun, heq⟩
            exfalso; apply hm
            refine ⟨rfl, i, hrun, congrArg Prod.fst heq, congrArg Prod.snd heq⟩
        · intro h0; exfalso; exact absurd h0 (by norm_num)
        · intro _; rfl
    · exfalso
      have hnot1 : (HBRec.mk 1 (N + 1 + b'.1) 0 b'.1 (B2 + b'.1)).kind ≠ 0 := by simp
      dsimp only [idealTransform] at hrb_dest
      rw [if_neg hnot1] at hrb_dest
      have hnotm : ¬ itemMatchB (N + 1 + b'.1) 0 := by
        rintro ⟨i, _, hm_eq, _⟩; have := runOffset_le_N l i; omega
      have hnot2 : ¬ ((HBRec.mk 1 (N + 1 + b'.1) 0 b'.1 (B2 + b'.1)).kind = 1 ∧
          itemMatchB (N + 1 + b'.1) 0) :=
        fun hc => hnotm hc.2
      rw [if_neg hnot2] at hrb_dest
      dsimp at hrb_dest
      omega

/-! ### Part 4: Stabilizer Subgroup `H_l`, `LES_l`, Counting & Padding -/


lemma mem_stabGroup_iff_permList {α : Type*} {N : ℕ} {l : Fin N → α} {h : Equiv.Perm (Fin N)} :
    h ∈ stabGroup N l ↔ permList h l = l := by
  simp [mem_stabGroup_iff, permList, funext_iff]

private def piPermApply {β : Type*} {N : ℕ} (l : Fin N → β)
    (g : (b : β) → Equiv.Perm { i : Fin N // l i = b }) (i : Fin N) : Fin N :=
  (g (l i) ⟨i, rfl⟩).1

private lemma piPermApply_mem {β : Type*} {N : ℕ} (l : Fin N → β)
    (g : (b : β) → Equiv.Perm { i : Fin N // l i = b }) (i : Fin N) :
    l (piPermApply l g i) = l i :=
  (g (l i) ⟨i, rfl⟩).2

private lemma piPermApply_subtype_eq {β : Type*} {N : ℕ} {l : Fin N → β}
    (g : (b : β) → Equiv.Perm { i : Fin N // l i = b }) :
    ∀ {b₁ b₂ : β} (hb : b₁ = b₂) (x : { i : Fin N // l i = b₁ }),
      (g b₁ x).1 = (g b₂ ⟨x.1, x.2.trans hb⟩).1 := by
  rintro b₁ _ rfl x; rfl

private lemma piPermApply_mul {β : Type*} {N : ℕ} (l : Fin N → β)
    (g₁ g₂ : (b : β) → Equiv.Perm { i : Fin N // l i = b }) (i : Fin N) :
    piPermApply l (g₁ * g₂) i = piPermApply l g₁ (piPermApply l g₂ i) := by
  dsimp only [piPermApply, Pi.mul_apply]
  rw [Equiv.Perm.mul_apply]
  exact (piPermApply_subtype_eq g₁ (piPermApply_mem l g₂ i) ⟨piPermApply l g₂ i, rfl⟩).symm

private lemma piPermApply_one {β : Type*} {N : ℕ} (l : Fin N → β) (i : Fin N) :
    piPermApply l 1 i = i := rfl

/-- Fiberwise isomorphism `H_l ≃* ∏_b Perm {i | l i = b}`. -/
noncomputable def stabGroupEquivPiPerm {β : Type*} (N : ℕ) (l : Fin N → β) :
    stabGroup N l ≃* ((b : β) → Equiv.Perm { i : Fin N // l i = b }) where
  toFun h b :=
    { toFun := fun i => ⟨h.1 i.1, by rw [h.2 i.1, i.2]⟩
      invFun := fun i => ⟨h.1⁻¹ i.1, by
        have hi := (stabGroup N l).inv_mem h.2 i.1
        exact hi.trans i.2⟩
      left_inv := fun i => Subtype.ext (by simp)
      right_inv := fun i => Subtype.ext (by simp) }
  invFun g :=
    ⟨{ toFun := piPermApply l g
       invFun := piPermApply l g⁻¹
       left_inv := fun i => by
         rw [← piPermApply_mul, inv_mul_cancel, piPermApply_one]
       right_inv := fun i => by
         rw [← piPermApply_mul, mul_inv_cancel, piPermApply_one] },
     fun i => piPermApply_mem l g i⟩
  left_inv h := by ext i; rfl
  right_inv g := by
    ext b i
    rcases i with ⟨i, hi⟩
    exact congrArg Fin.val (piPermApply_subtype_eq g hi ⟨i, rfl⟩)
  map_mul' h₁ h₂ := by ext b i; rfl

theorem card_stabGroup_eq_prod_modeCount {β : Type*} [Fintype β] [DecidableEq β]
    (N : ℕ) (l : Fin N → β) :
    Fintype.card (stabGroup N l) =
      ∏ b : β, (Finset.univ.filter fun i : Fin N => l i = b).card.factorial := by
  rw [Fintype.card_congr (stabGroupEquivPiPerm N l).toEquiv, Fintype.card_pi]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [Fintype.card_perm, Fintype.card_subtype]


/-- Equivalence between `LES_l` and `∏_i Fin (runOffset l i)` via `s i = i - d i`. -/
def isLESOfEquivPiFin {α : Type*} [LinearOrder α] (N : ℕ) (l : Fin N → α)
    (hl : Monotone l) :
    { s : Fin N → ℕ // IsLESOf N l s } ≃ ((i : Fin N) → Fin (runOffset l i)) where
  toFun s i := ⟨i.1 - s.1 i, by
    have hs := s.2 i
    dsimp [runOffset]
    omega⟩
  invFun d := ⟨fun i => i.1 - (d i).1, fun i => by
    have hd := (d i).isLt
    have hrs := runStart_le hl i
    dsimp [runOffset] at hd ⊢
    omega⟩
  left_inv s := Subtype.ext <| funext fun i => by
    have hs := s.2 i
    dsimp only
    omega
  right_inv d := funext fun i => Fin.ext <| by
    have hd := (d i).isLt
    have hrs := runStart_le hl i
    dsimp [runOffset] at hd ⊢
    omega

theorem card_isLESOf_eq_prod_runOffset {α : Type*} [LinearOrder α] (N : ℕ) (l : Fin N → α)
    (hl : Monotone l) :
    @Fintype.card { s : Fin N → ℕ // IsLESOf N l s }
      (Fintype.ofEquiv _ (isLESOfEquivPiFin N l hl).symm) = ∏ i : Fin N, runOffset l i := by
  let : Fintype { s : Fin N → ℕ // IsLESOf N l s } :=
    Fintype.ofEquiv _ (isLESOfEquivPiFin N l hl).symm
  rw [Fintype.card_congr (isLESOfEquivPiFin N l hl), Fintype.card_pi]
  simp only [Fintype.card_fin]

theorem prod_runOffset_eq_prod_modeCount {β : Type*} [LinearOrder β] [Fintype β]
    (N : ℕ) (l : Fin N → β) (hl : Monotone l) :
    ∏ i : Fin N, runOffset l i =
      ∏ b : β, (Finset.univ.filter fun i : Fin N => l i = b).card.factorial := by
  have hfib : ∏ i : Fin N, runOffset l i =
      ∏ b : β, ∏ i ∈ Finset.univ.filter (fun j : Fin N => l j = b), runOffset l i :=
    (Finset.prod_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
      (fun (i : Fin N) _ => Finset.mem_univ (l i)) (fun i => runOffset l i)).symm
  rw [hfib]
  refine Finset.prod_congr rfl fun b _ => ?_
  set F := Finset.univ.filter fun j : Fin N => l j = b
  by_cases hne : F.Nonempty
  · obtain ⟨i₀, hi₀⟩ := hne
    have hl₀ : l i₀ = b := (Finset.mem_filter.mp hi₀).2
    have hF_eq : F = Finset.univ.filter fun j : Fin N =>
        runStart l i₀ ≤ j.1 ∧ j.1 < runEndSucc l i₀ := by
      ext j
      simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hl₀]
      exact eq_iff_mem_runBlock hl i₀ j
    have hcard_F : F.card = runEndSucc l i₀ - runStart l i₀ := by
      dsimp only [F]
      rw [← hl₀]
      exact runCount_eq_runEndSucc_sub_runStart i₀
    have hbij : ∏ i ∈ F, runOffset l i = ∏ k ∈ Finset.range F.card, (k + 1) := by
      refine Finset.prod_bij (fun i _ => i.1 - runStart l i₀) ?_ ?_ ?_ ?_
      · intro i hi
        rw [hF_eq, Finset.mem_filter] at hi
        rw [Finset.mem_range]
        omega
      · intro i₁ hi₁ i₂ hi₂ heq
        rw [hF_eq, Finset.mem_filter] at hi₁ hi₂
        exact Fin.ext (by omega)
      · intro k hk
        rw [Finset.mem_range] at hk
        have hlt_re : runStart l i₀ + k < runEndSucc l i₀ := by omega
        have hlt_N : runStart l i₀ + k < N := lt_of_lt_of_le hlt_re (runEndSucc_le l i₀)
        refine ⟨⟨runStart l i₀ + k, hlt_N⟩, ?_, by dsimp; omega⟩
        rw [hF_eq, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, by dsimp; omega, by dsimp; omega⟩
      · intro i hi
        have hli : l i = l i₀ := ((Finset.mem_filter.mp hi).2).trans hl₀.symm
        rw [runOffset, runStart_eq_of_eq l hli]
    rw [hbij, Finset.prod_range_add_one_eq_factorial]
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    simp [hne]


lemma padNSIL_mono (N M : ℕ) (l : Fin N → ℕ) (hl : Monotone l) :
    Monotone (padNSIL N M l) := by
  intro i j hij
  dsimp [padNSIL]
  split_ifs with hi hj hj
  · rw [Prod.Lex.le_iff]
    simp only [ofLex_toLex, lt_irrefl, false_or, true_and]
    exact hl (Fin.le_iff_val_le_val.mpr (Fin.le_def.mp hij))
  · rw [Prod.Lex.le_iff]
    simp only [ofLex_toLex]
    left; norm_num
  · exfalso; have := Fin.le_def.mp hij; omega
  · rw [Prod.Lex.le_iff]
    simp only [ofLex_toLex, lt_irrefl, false_or, true_and]
    exact Fin.le_def.mp hij

lemma runStart_padNSIL_lt {N M : ℕ} (hNM : N ≤ M) {l : Fin N → ℕ}
    (i : Fin N) :
    runStart (padNSIL N M l) ⟨i.1, lt_of_lt_of_le i.isLt hNM⟩ = runStart l i := by
  dsimp [runStart]
  refine Finset.card_bij (fun j hj => ⟨j.1, by
      have hj2 := (Finset.mem_filter.mp hj).2
      dsimp only [padNSIL, Fin.val_mk] at hj2
      rw [dif_pos i.isLt] at hj2
      split_ifs at hj2 with hjn
      · exact hjn
      · exfalso; rw [Prod.Lex.lt_iff] at hj2; simp only [ofLex_toLex] at hj2
        rcases hj2 with h | ⟨h, _⟩ <;> omega⟩) ?_ ?_ ?_
  · intro j hj
    rw [Finset.mem_filter] at hj ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    have hj2 := hj.2
    dsimp only [padNSIL, Fin.val_mk] at hj2
    rw [dif_pos i.isLt] at hj2
    split_ifs at hj2 with hjn
    · rw [Prod.Lex.lt_iff] at hj2
      simp only [ofLex_toLex, lt_irrefl, false_or, true_and] at hj2
      exact hj2
    · exfalso; rw [Prod.Lex.lt_iff] at hj2; simp only [ofLex_toLex] at hj2
      rcases hj2 with h | ⟨h, _⟩ <;> omega
  · intro j₁ _ j₂ _ heq
    have hval := congrArg Fin.val heq
    dsimp at hval
    exact Fin.ext hval
  · intro j hj
    rw [Finset.mem_filter] at hj
    refine ⟨⟨j.1, lt_of_lt_of_le j.isLt hNM⟩, ?_, Fin.ext rfl⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    dsimp only [padNSIL, Fin.val_mk]
    rw [dif_pos j.isLt, dif_pos i.isLt, Prod.Lex.lt_iff]
    simp only [ofLex_toLex, lt_irrefl, false_or, true_and]; exact hj.2

lemma runOffset_padNSIL_lt {N M : ℕ} (hNM : N ≤ M) (l : Fin N → ℕ) (i : Fin N) :
    runOffset (padNSIL N M l) ⟨i.1, lt_of_lt_of_le i.isLt hNM⟩ = runOffset l i := by
  simp [runOffset, runStart_padNSIL_lt hNM]

lemma runOffset_padNSIL_ge {N M : ℕ} (l : Fin N → ℕ) (hl : Monotone l)
    {j : Fin M} (hj : N ≤ j.1) :
    runOffset (padNSIL N M l) j = 1 := by
  have hstart : runStart (padNSIL N M l) j = j.1 := by
    have hle := runStart_le (padNSIL_mono N M l hl) j
    have hge : j.1 ≤ runStart (padNSIL N M l) j := by
      rw [← card_fin_lt j.1 (le_of_lt j.isLt)]
      refine Finset.card_le_card fun r hr => ?_
      rw [Finset.mem_filter] at hr ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      dsimp only [padNSIL]
      rw [dif_neg (Nat.not_lt.mpr hj), Prod.Lex.lt_iff]
      simp only [ofLex_toLex]
      split_ifs with hrN
      · left; norm_num
      · right; exact ⟨rfl, hr.2⟩
    omega
  dsimp [runOffset]; omega

/-- Embedding `Equiv.Perm (Fin N)` into `Equiv.Perm (Fin M)` fixing `≥ N`. -/
def padPerm (N M : ℕ) (hNM : N ≤ M) (σ : Equiv.Perm (Fin N)) : Equiv.Perm (Fin M) where
  toFun j := if h : j.1 < N then ⟨(σ ⟨j.1, h⟩).1, lt_of_lt_of_le (σ ⟨j.1, h⟩).isLt hNM⟩ else j
  invFun j := if h : j.1 < N then ⟨(σ⁻¹ ⟨j.1, h⟩).1, lt_of_lt_of_le (σ⁻¹ ⟨j.1, h⟩).isLt hNM⟩ else j
  left_inv j := by
    by_cases h : j.1 < N
    · simp [h, (σ ⟨j.1, h⟩).isLt]
    · simp [h]
  right_inv j := by
    by_cases h : j.1 < N
    · simp [h]
    · simp [h]

noncomputable def padStabEquiv {N M : ℕ} (hNM : N ≤ M) (l : Fin N → ℕ) :
    stabGroup N l ≃* stabGroup M (padNSIL N M l) where
  toFun h := ⟨padPerm N M hNM h.1, fun j => by
    by_cases hj : j.1 < N
    · have hlt_h : (h.1 ⟨j.1, hj⟩).1 < N := (h.1 ⟨j.1, hj⟩).isLt
      simp only [padPerm, padNSIL, Equiv.coe_fn_mk, hj, ↓reduceDIte, Fin.eta, hlt_h]
      exact congrArg (fun x => toLex (0, x)) (h.2 ⟨j.1, hj⟩)
    · simp [padPerm, padNSIL, hj]⟩
  invFun h :=
    have hfix : ∀ j : Fin M, N ≤ j.1 → h.1 j = j := by
      intro j hj
      have heq := h.2 j
      dsimp only [padNSIL] at heq
      rw [dif_neg (Nat.not_lt.mpr hj)] at heq
      split_ifs at heq with h_lt
      · have h01 := congrArg (fun p : ℕ ×ₗ ℕ => (ofLex p).1) heq
        simp at h01
      · have hsnd := congrArg (fun p : ℕ ×ₗ ℕ => (ofLex p).2) heq
        exact Fin.ext hsnd
    have hlt : ∀ j : Fin M, j.1 < N → (h.1 j).1 < N := by
      intro j hj
      by_contra hge
      have hge' : N ≤ (h.1 j).1 := Nat.le_of_not_lt hge
      have hfix_inv : ∀ r : Fin M, N ≤ r.1 → h.1⁻¹ r = r := by
        intro r hr
        exact (Equiv.Perm.eq_inv_iff_eq.mpr (hfix r hr)).symm
      have hj_eq : j = h.1⁻¹ (h.1 j) := (h.1.symm_apply_apply j).symm
      rw [hfix_inv _ hge'] at hj_eq
      have hval := congrArg Fin.val hj_eq
      omega
    ⟨{ toFun := fun i => ⟨(h.1 ⟨i.1, lt_of_lt_of_le i.isLt hNM⟩).1, hlt _ i.isLt⟩
       invFun := fun i => ⟨(h.1⁻¹ ⟨i.1, lt_of_lt_of_le i.isLt hNM⟩).1, by
         by_contra hge
         have hin := hfix (h.1⁻¹ ⟨i.1, lt_of_lt_of_le i.isLt hNM⟩) (Nat.le_of_not_lt hge)
         have h_app : h.1 (h.1⁻¹ ⟨i.1, lt_of_lt_of_le i.isLt hNM⟩) = ⟨i.1, lt_of_lt_of_le i.isLt hNM⟩ :=
           h.1.apply_symm_apply _
         have heq_val : i.1 = (h.1⁻¹ ⟨i.1, lt_of_lt_of_le i.isLt hNM⟩).1 :=
           congrArg Fin.val (h_app.symm.trans hin)
         omega⟩
       left_inv := fun i => Fin.ext (by
         dsimp
         exact congrArg Fin.val (h.1.symm_apply_apply ⟨i.1, lt_of_lt_of_le i.isLt hNM⟩))
       right_inv := fun i => Fin.ext (by
         dsimp
         exact congrArg Fin.val (h.1.apply_symm_apply ⟨i.1, lt_of_lt_of_le i.isLt hNM⟩)) },
     fun i => by
       have heq := h.2 ⟨i.1, lt_of_lt_of_le i.isLt hNM⟩
       dsimp only [padNSIL, Fin.val_mk] at heq
       rw [dif_pos (hlt _ i.isLt), dif_pos i.isLt] at heq
       exact congrArg (fun p : ℕ ×ₗ ℕ => (ofLex p).2) heq⟩
  left_inv h := by
    ext i
    simp [padPerm]
  right_inv h := by
    ext j
    by_cases hj : j.1 < N
    · simp [padPerm, hj]
    · dsimp only [padPerm, Equiv.coe_fn_mk]; rw [dif_neg hj]
      have heq := h.2 j
      dsimp only [padNSIL] at heq
      rw [dif_neg hj] at heq
      split_ifs at heq with h_lt
      · have h01 := congrArg (fun p : ℕ ×ₗ ℕ => (ofLex p).1) heq
        simp at h01
      · exact (congrArg (fun p : ℕ ×ₗ ℕ => (ofLex p).2) heq).symm
  map_mul' h₁ h₂ := by
    ext j
    by_cases hj : j.1 < N
    · simp [padPerm, hj, (h₂.1 ⟨j.1, hj⟩).isLt]
    · simp [padPerm, hj]

/-! ### Part 5: `[LCG26]` Eqs. (655)–(701) & Eq. (693) Factorization -/

/-- Exact permutation-orbit membership: `y ∈ Range (· • l) ↔ y` has the same fiber sizes as `l`. -/
theorem mem_permList_range_iff_fiber_card {β : Type*} [DecidableEq β]
    {N : ℕ} (l y : Fin N → β) :
    (∃ σ : Equiv.Perm (Fin N), permList σ l = y) ↔
      ∀ b : β, (Finset.univ.filter fun i : Fin N => y i = b).card =
        (Finset.univ.filter fun i : Fin N => l i = b).card := by
  constructor
  · rintro ⟨σ, rfl⟩ b
    refine Finset.card_bij (fun i _ => σ i) ?_ ?_ ?_
    · intro i hi
      rw [Finset.mem_filter] at hi ⊢
      exact ⟨Finset.mem_univ _, hi.2⟩
    · intro i₁ _ i₂ _ heq; exact σ.injective heq
    · intro j hj
      rw [Finset.mem_filter] at hj
      refine ⟨σ⁻¹ j, ?_, σ.apply_symm_apply j⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by simpa [permList] using hj.2⟩
  · intro hcard
    have heq_f : ∀ b : β, Nonempty ({ i : Fin N // y i = b } ≃ { j : Fin N // l j = b }) := by
      intro b
      have hc : Fintype.card { i : Fin N // y i = b } = Fintype.card { j : Fin N // l j = b } := by
        rw [Fintype.card_subtype, Fintype.card_subtype]
        exact hcard b
      exact ⟨(Fintype.equivFin _).trans ((finCongr hc).trans (Fintype.equivFin _).symm)⟩
    let e : ∀ b : β, { i : Fin N // y i = b } ≃ { j : Fin N // l j = b } :=
      fun b => Classical.choice (heq_f b)
    let σFun : Fin N → Fin N := fun i => (e (y i) ⟨i, rfl⟩).1
    have hl_σ : ∀ i : Fin N, l (σFun i) = y i := fun i => (e (y i) ⟨i, rfl⟩).2
    have hsub_inj : ∀ (b₁ b₂ : β) (hb : b₁ = b₂)
        (x₁ : { i : Fin N // y i = b₁ }) (x₂ : { i : Fin N // y i = b₂ }),
        (e b₁ x₁).1 = (e b₂ x₂).1 → x₁.1 = x₂.1 := by
      rintro b₁ _ rfl x₁ x₂ heq_e
      exact congrArg Subtype.val ((e b₁).injective (Subtype.ext heq_e))
    have hinj : Function.Injective σFun := by
      intro i₁ i₂ heq
      have hy : y i₁ = y i₂ := by rw [← hl_σ i₁, ← hl_σ i₂, heq]
      exact hsub_inj (y i₁) (y i₂) hy ⟨i₁, rfl⟩ ⟨i₂, rfl⟩ heq
    refine ⟨Equiv.ofBijective σFun (Finite.injective_iff_bijective.mp hinj), funext hl_σ⟩

/-- Master `[LCG26]` Eq. (674)–(693) bijection:
given any deterministic sorting choice `τ : (Fin N → β) → S_N` mapping each `y` in the orbit
back to `l` (`permList (τ y)⁻¹ y = l`), `S_N` factors bijectively as `Orbit(l) × stabGroup N l`. -/
noncomputable def permSplitEquiv {β : Type*} (N : ℕ) (l : Fin N → β)
    (τ : (Fin N → β) → Equiv.Perm (Fin N))
    (hτ : ∀ y : { z : Fin N → β // ∃ σ : Equiv.Perm (Fin N), permList σ l = z },
      permList (τ y.1)⁻¹ y.1 = l) :
    Equiv.Perm (Fin N) ≃
      { z : Fin N → β // ∃ σ : Equiv.Perm (Fin N), permList σ l = z } × stabGroup N l where
  toFun σ :=
    let y : { z : Fin N → β // ∃ σ : Equiv.Perm (Fin N), permList σ l = z } := ⟨permList σ l, ⟨σ, rfl⟩⟩
    let h := σ * (τ y.1)⁻¹
    ⟨y, ⟨h, mem_stabGroup_iff_permList.mpr (by
      dsimp [h]
      rw [← permList_mul]
      exact hτ y)⟩⟩
  invFun yh := yh.2.1 * τ yh.1.1
  left_inv σ := by simp [mul_assoc]
  right_inv yh := by
    rcases yh with ⟨⟨y, hy⟩, ⟨h, hh⟩⟩
    have hy_eq : permList (h * τ y) l = y := by
      rw [← permList_mul, mem_stabGroup_iff_permList.mp hh]
      have h1 := hτ ⟨y, hy⟩
      have h2 := congrArg (permList (τ y)) h1
      rw [permList_mul, inv_mul_cancel, permList_one] at h2
      exact h2.symm
    ext1
    · exact Subtype.ext hy_eq
    · simp [hy_eq]

theorem eq_655_701_sum_factorization {β V : Type*} [Fintype β] [DecidableEq β]
    [AddCommMonoid V] [Module ℂ V]
    (N : ℕ) (l : Fin N → β)
    (τ : (Fin N → β) → Equiv.Perm (Fin N))
    (hτ : ∀ y : { z : Fin N → β // ∃ σ : Equiv.Perm (Fin N), permList σ l = z },
      permList (τ y.1)⁻¹ y.1 = l)
    (f : (Fin N → β) → Equiv.Perm (Fin N) → V) :
    ∑ σ : Equiv.Perm (Fin N), f (permList σ l) (σ * (τ (permList σ l))⁻¹) =
      ∑ y : { z : Fin N → β // ∃ σ : Equiv.Perm (Fin N), permList σ l = z },
        ∑ h : stabGroup N l, f y.1 h.1 := by
  have h1 := Fintype.sum_equiv (permSplitEquiv N l τ hτ)
    (fun σ => f (permList σ l) (σ * (τ (permList σ l))⁻¹))
    (fun yh => f yh.1.1 yh.2.1)
    (fun _ => rfl)
  rw [h1, Fintype.sum_prod_type]

theorem card_isLESOf_eq_prod_runOffset' {α : Type*} [LinearOrder α] (N : ℕ) (l : Fin N → α)
    (hl : Monotone l) :
    letI : Fintype { s : Fin N → ℕ // IsLESOf N l s } :=
      Fintype.ofEquiv _ (isLESOfEquivPiFinOf N l (runStart_le hl)).symm
    Fintype.card { s : Fin N → ℕ // IsLESOf N l s } = ∏ i : Fin N, runOffset l i := by
  rw [@Fintype.card_congr _ _ (Fintype.ofEquiv _ (isLESOfEquivPiFinOf N l (runStart_le hl)).symm)
    _ (isLESOfEquivPiFinOf N l (runStart_le hl)), Fintype.card_pi]
  simp only [Fintype.card_fin]

end Aux_nsil

/-! ### Bridge Lemmas Linking `Aux_as`, `Aux_nsil`, and `LcgSym54Comb` -/

lemma bitsToNat_natToBits {w x : ℕ} (hx : x < 2 ^ w) : bitsToNat (natToBits w x) = x := by
  rw [← bitsEquivFin_apply]
  simp [natToBits, Nat.mod_eq_of_lt hx]

lemma bitsToNat_inj {w : ℕ} : Function.Injective (@bitsToNat w) := by
  intro b₁ b₂ h
  apply (bitsEquivFin w).injective
  exact Fin.ext (by rw [bitsEquivFin_apply, bitsEquivFin_apply, h])

lemma bitsToNat_lt_two_pow {w : ℕ} (b : Qubits w) : bitsToNat b < 2 ^ w := by
  rw [← bitsEquivFin_apply]
  exact (bitsEquivFin w b).isLt

lemma bitsToNat_append {w_a w_b : ℕ} (a : Qubits w_a) (b : Qubits w_b) :
    bitsToNat (Fin.append a b) = 2 ^ w_b * bitsToNat a + bitsToNat b := by
  dsimp only [bitsToNat]
  rw [Fin.sum_univ_add]
  congr 1
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hfl : Fin.append a b (Fin.castAdd w_b i) = a i := Fin.append_left a b i
    rw [hfl]
    by_cases ha : a i = true
    · rw [if_pos ha, if_pos ha, ← pow_add]
      congr 1; simp only [Fin.val_castAdd]; have := i.isLt; omega
    · rw [if_neg ha, if_neg ha, mul_zero]
  · refine Finset.sum_congr rfl fun j _ => ?_
    have hfr : Fin.append a b (Fin.natAdd w_a j) = b j := Fin.append_right a b j
    rw [hfr]
    by_cases hb : b j = true
    · rw [if_pos hb, if_pos hb]
      congr 1; simp only [Fin.val_natAdd]; have := j.isLt; omega
    · rw [if_neg hb, if_neg hb]

private lemma sum_testBit_eq_mod (w x : ℕ) :
    (∑ i : Fin w, if Nat.testBit x i.1 then 2 ^ i.1 else 0) = x % 2 ^ w := by
  induction w with
  | zero => simp [Nat.mod_one]
  | succ w ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    have hbit : Nat.testBit x w = decide ((x / 2 ^ w) % 2 = 1) := by
      rw [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.and_comm, Nat.and_one_is_mod]
      have hmod2 : (x / 2 ^ w) % 2 = 0 ∨ (x / 2 ^ w) % 2 = 1 := by
        have := Nat.mod_lt (x / 2 ^ w) (by norm_num : 0 < 2)
        omega
      rcases hmod2 with hz | ho
      · simp [hz]
      · simp [ho]
    have hmod_div : x % 2 ^ (w + 1) = x % 2 ^ w + 2 ^ w * ((x / 2 ^ w) % 2) := by
      have h1 : x = 2 ^ w * (x / 2 ^ w) + x % 2 ^ w := (Nat.div_add_mod x (2 ^ w)).symm
      have h2 : x / 2 ^ w = 2 * (x / 2 ^ (w + 1)) + (x / 2 ^ w) % 2 := by
        rw [pow_succ, ← Nat.div_div_eq_div_mul]
        exact (Nat.div_add_mod (x / 2 ^ w) 2).symm
      have hlt : x % 2 ^ w + 2 ^ w * ((x / 2 ^ w) % 2) < 2 ^ (w + 1) := by
        have hlt1 : x % 2 ^ w < 2 ^ w := Nat.mod_lt _ (Nat.two_pow_pos w)
        have hlt2 : (x / 2 ^ w) % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num : 0 < 2))
        rw [pow_succ]
        rcases (by omega : (x / 2 ^ w) % 2 = 0 ∨ (x / 2 ^ w) % 2 = 1) with hz | ho
        · rw [hz]; omega
        · rw [ho]; omega
      conv_lhs => rw [h1, h2, mul_add, ← mul_assoc, ← pow_succ]
      rw [add_assoc, add_comm (2 ^ (w + 1) * (x / 2 ^ (w + 1))), Nat.add_mul_mod_self_left,
        add_comm (2 ^ w * ((x / 2 ^ w) % 2)), Nat.mod_eq_of_lt hlt]
    rw [hbit, hmod_div]
    have hm2 : (x / 2 ^ w) % 2 = 0 ∨ (x / 2 ^ w) % 2 = 1 := by
      have := Nat.mod_lt (x / 2 ^ w) (by norm_num : 0 < 2)
      omega
    rcases hm2 with hz | ho
    · simp [hz]
    · simp [ho]

lemma natToBits_comp_revPerm (w x : ℕ) (i : Fin w) :
    natToBits w x i.rev = Nat.testBit x i.1 := by
  let b : Qubits w := fun j => Nat.testBit x j.rev.1
  have hb : bitsToNat b = x % 2 ^ w := by
    dsimp only [bitsToNat, b]
    have heq : (∑ j : Fin w, if Nat.testBit x j.rev.1 then 2 ^ (w - 1 - j.1) else 0) =
        ∑ j : Fin w, if Nat.testBit x j.1 then 2 ^ j.1 else 0 := by
      refine Fintype.sum_equiv Fin.revPerm _ _ fun j => ?_
      simp only [Fin.revPerm_apply, Fin.val_rev]
      have hj := j.isLt
      have hexp : w - 1 - j.1 = w - (j.1 + 1) := by omega
      rw [hexp]
    rw [heq, sum_testBit_eq_mod]
  have hntb : bitsToNat (natToBits w x) = x % 2 ^ w := by
    rw [← bitsEquivFin_apply]
    simp [natToBits]
  have h_eq : natToBits w x = b := bitsToNat_inj (hntb.trans hb.symm)
  have h_pt := congrFun h_eq i.rev
  dsimp only [b] at h_pt
  rwa [Fin.rev_rev] at h_pt

lemma bitsToNat_particleSym54_eq (n : ℕ) (j : Fin (n + 1)) :
    bitsToNat (particleSym54 n (Nat.clog 2 n + 1) j) = if j.1 < n then j.1 else 2 ^ (Nat.clog 2 n) := by
  have hle : n ≤ 2 ^ Nat.clog 2 n := Nat.le_pow_clog (by norm_num : 1 < 2) n
  have hpow : 2 ^ Nat.clog 2 n < 2 ^ (Nat.clog 2 n + 1) :=
    Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self _)
  by_cases hj : j.1 < n
  · rw [if_pos hj, particleSym54_lt hj, bitsToNat_natToBits (lt_of_lt_of_le (lt_of_lt_of_le hj hle) hpow.le)]
  · rw [if_neg hj, particleSym54, if_neg hj, blankSym54, Nat.add_sub_cancel]
    exact bitsToNat_natToBits hpow

lemma bitsToNat_particleSym54_strictMono (n : ℕ) :
    StrictMono (fun j : Fin (n + 1) => bitsToNat (particleSym54 n (Nat.clog 2 n + 1) j)) := by
  intro i j hij
  dsimp only
  rw [bitsToNat_particleSym54_eq, bitsToNat_particleSym54_eq]
  have hi : i.1 < n := by have := j.isLt; exact lt_of_lt_of_le hij (Nat.le_of_lt_succ this)
  have hle : n ≤ 2 ^ Nat.clog 2 n := Nat.le_pow_clog (by norm_num : 1 < 2) n
  rw [if_pos hi]
  by_cases hj : j.1 < n
  · rw [if_pos hj]; exact hij
  · rw [if_neg hj]; exact lt_of_lt_of_le hi hle

lemma padLES54_le (N : ℕ) (s : Fin N → ℕ) (hs : IsLES N s) (c : ℕ) :
    padLES54 N s c ≤ c := by
  dsimp [padLES54]
  split_ifs with hc
  · exact hs ⟨c, hc⟩
  · exact le_rfl

lemma mergePhi_fst_inj (k : ℕ) (t₁ t₂ : ℕ × ℕ × ℕ)
    (h : mergePhi k t₁ = mergePhi k t₂) : t₁.1 = t₂.1 := by
  dsimp only [mergePhi] at h
  by_cases h1 : t₁.1 < k <;> by_cases h2 : t₂.1 < k
  · rw [if_pos h1, if_pos h2] at h
    have hs := congrArg (fun p : ℕ ×ₗ ℕ ×ₗ ℕ => (ofLex (ofLex p).2).2) h
    exact hs
  · rw [if_pos h1, if_neg h2] at h
    have hs := congrArg (fun p : ℕ ×ₗ ℕ ×ₗ ℕ => (ofLex (ofLex p).2).1) h
    simp at hs
  · rw [if_neg h1, if_pos h2] at h
    have hs := congrArg (fun p : ℕ ×ₗ ℕ ×ₗ ℕ => (ofLex (ofLex p).2).1) h
    simp at hs
  · rw [if_neg h1, if_neg h2] at h
    have hs := congrArg (fun p : ℕ ×ₗ ℕ ×ₗ ℕ => (ofLex (ofLex p).2).2) h
    exact hs

lemma hbKey1_orig_inj (r₁ r₂ : HBRec) (h : hbKey1 r₁ = hbKey1 r₂) : r₁.orig = r₂.orig := by
  dsimp only [hbKey1] at h
  exact congrArg (fun k : ℕ ×ₗ ℕ ×ₗ ℕ ×ₗ ℕ ×ₗ ℕ => (ofLex (ofLex (ofLex (ofLex k).2).2).2).2) h

lemma hbKey2_orig_inj (r₁ r₂ : HBRec) (h : hbKey2 r₁ = hbKey2 r₂) : r₁.orig = r₂.orig := by
  dsimp only [hbKey2] at h
  exact congrArg (fun k : ℕ ×ₗ ℕ ×ₗ ℕ => (ofLex (ofLex k).2).2) h

lemma occSortKey_idx_inj {N : ℕ} (r₁ r₂ : Bool × ℕ × Fin N)
    (h : occSortKey r₁ = occSortKey r₂) : r₁.2.2 = r₂.2.2 := by
  dsimp only [occSortKey] at h
  exact Fin.ext (congrArg (fun k : ℕ ×ₗ ℕ ×ₗ ℕ => (ofLex (ofLex k).2).2) h)

lemma greedyDiag_col_mem (s : ℕ → ℕ) (lo hi : ℕ)
    (hle : lo ≤ hi) (hs : ∀ c, lo ≤ c → c < hi → s c ≤ c) :
    ∀ p ∈ greedyDiag s lo hi, lo ≤ p.2 ∧ p.2 < hi := by
  have hprops := Aux_as.greedyState_props s lo (hi - lo) (List.range hi) (Aux_as.pairwise_range_lt hi)
    (by simp; omega) (fun c hc1 hc2 => hs c hc1 (by omega))
  intro p hp
  have hp' := (List.mergeSort_perm _ _).mem_iff.mp hp
  have hmem := hprops.2.2.2.2.2.1 p hp'
  exact ⟨hmem.2.2.1, by omega⟩

lemma greedyDiag_row_lt (s : ℕ → ℕ) (lo hi : ℕ)
    (hle : lo ≤ hi) (hs : ∀ c, lo ≤ c → c < hi → s c ≤ c) :
    ∀ p ∈ greedyDiag s lo hi, p.1 < hi := by
  have hprops := Aux_as.greedyState_props s lo (hi - lo) (List.range hi) (Aux_as.pairwise_range_lt hi)
    (by simp; omega) (fun c hc1 hc2 => hs c hc1 (by omega))
  intro p hp
  have hp' := (List.mergeSort_perm _ _).mem_iff.mp hp
  exact List.mem_range.mp (hprops.2.2.2.2.2.1 p hp').1

private lemma pairwise_lt_fst_ge_idx (L : List (ℕ × ℕ)) (hpw : L.Pairwise (fun p q => p.1 < q.1)) :
    ∀ (idx : ℕ) (hidx : idx < L.length), idx ≤ (L[idx]'hidx).1 := by
  intro idx
  induction idx with
  | zero => intro _; exact Nat.zero_le _
  | succ idx ih =>
    intro hidx
    have hidx0 : idx < L.length := by omega
    have hih := ih hidx0
    have hlt := (List.pairwise_iff_getElem.mp hpw) idx (idx + 1) hidx0 hidx (Nat.lt_succ_self idx)
    omega

lemma greedyDiag_fst_ge_idx (s : ℕ → ℕ) (lo hi : ℕ)
    (hle : lo ≤ hi) (hs : ∀ c, lo ≤ c → c < hi → s c ≤ c)
    (idx : ℕ) (hidx : idx < (greedyDiag s lo hi).length) :
    idx ≤ ((greedyDiag s lo hi)[idx]'hidx).1 :=
  pairwise_lt_fst_ge_idx _ (Aux_as.greedyDiag_pairwise_lt s lo hi hle hs) idx hidx

lemma greedyDiag_leaf (s : ℕ → ℕ) (lo : ℕ) (hs : s lo ≤ lo) :
    greedyDiag s lo (lo + 1) = [(s lo, lo)] := by
  dsimp [greedyDiag]
  have hlen : lo + 1 - lo = 1 := by omega
  rw [hlen]
  dsimp [greedyState]
  have hlt : s lo < (List.range (lo + 1)).length := by simp; omega
  have hget : (List.range (lo + 1)).getD (s lo) 0 = s lo := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    simp
  rw [hget]
  simp

theorem Ttilde1_col_lt_iff (s : ℕ → ℕ) (lo mid hi : ℕ)
    (hlo : lo ≤ mid) (hhi : mid ≤ hi) (hs : ∀ c, c < hi → s c ≤ c) :
    let L := greedyDiag s lo mid
    let R := greedyDiag s mid hi
    let k := mid - lo
    let Ttilde0 := ((L ++ R).zipIdx).map (fun ((r, c), idx) => (idx, r, c))
    ∀ t ∈ Ttilde0,
      lo ≤ t.2.2 ∧ t.2.2 < hi ∧ t.2.1 < hi ∧ t.1 < hi - lo ∧
      (t.1 < k ↔ t.2.2 < mid) ∧ (k ≤ t.1 → t.1 - k ≤ t.2.1) := by
  intro L R k Ttilde0 t ht
  have hL_len : L.length = k := Aux_as.greedyDiag_length s lo mid hlo (fun c _ hc => hs c (by omega))
  have hR_len : R.length = hi - mid := Aux_as.greedyDiag_length s mid hi hhi (fun c _ hc => hs c (by omega))
  rcases List.getElem_of_mem ht with ⟨idx, hidx, rfl⟩
  have hidx_lr : idx < (L ++ R).length := by simpa [Ttilde0, List.length_zipIdx] using hidx
  have hget : (Ttilde0[idx]'hidx) = (idx, (L ++ R)[idx].1, (L ++ R)[idx].2) := by
    simp [Ttilde0]
  rw [hget]
  dsimp only
  have hidx_lt_sub : idx < hi - lo := by
    rw [List.length_append, hL_len, hR_len] at hidx_lr; omega
  by_cases hik : idx < k
  · have hiL : idx < L.length := by omega
    have happ : (L ++ R)[idx]'hidx_lr = L[idx]'hiL := List.getElem_append_left hiL
    rw [happ]
    have hcm := greedyDiag_col_mem s lo mid hlo (fun c _ hc => hs c (by omega)) (L[idx]'hiL) (List.getElem_mem hiL)
    have hrm := greedyDiag_row_lt s lo mid hlo (fun c _ hc => hs c (by omega)) (L[idx]'hiL) (List.getElem_mem hiL)
    refine ⟨hcm.1, by omega, by omega, hidx_lt_sub, ⟨fun _ => hcm.2, fun _ => hik⟩, fun hk => by omega⟩
  · have hiL : L.length ≤ idx := by omega
    have hiR : idx - L.length < R.length := by rw [List.length_append] at hidx_lr; omega
    have happ : (L ++ R)[idx]'hidx_lr = R[idx - L.length]'hiR := List.getElem_append_right hiL
    rw [happ]
    have hcm := greedyDiag_col_mem s mid hi hhi (fun c _ hc => hs c (by omega)) _ (List.getElem_mem hiR)
    have hrm := greedyDiag_row_lt s mid hi hhi (fun c _ hc => hs c (by omega)) _ (List.getElem_mem hiR)
    have hge := greedyDiag_fst_ge_idx s mid hi hhi (fun c _ hc => hs c (by omega)) (idx - L.length) hiR
    refine ⟨by omega, hcm.2, hrm, hidx_lt_sub, ⟨fun h => absurd h hik, fun _ => by omega⟩, fun _ => ?_⟩
    rw [← hL_len]; exact hge

private lemma greedyState_congr (s₁ s₂ : ℕ → ℕ) (lo len : ℕ) (U : List ℕ)
    (heq : ∀ c, lo ≤ c → c < lo + len → s₁ c = s₂ c) :
    greedyState s₁ lo len U = greedyState s₂ lo len U := by
  induction len generalizing U with
  | zero => rfl
  | succ len ih =>
    dsimp only [greedyState]
    have htop := heq (lo + len) (by omega) (by omega)
    rw [htop, ih _ (fun c hc1 hc2 => heq c hc1 (by omega))]

private lemma greedyState_pad_top (N k : ℕ) (s : Fin N → ℕ) :
    let res := greedyState (padLES54 N s) N k (List.range (N + k))
    res.2 = List.range N ∧
    ∀ p, p ∈ res.1 ↔ ∃ c, N ≤ c ∧ c < N + k ∧ p = (c, c) := by
  induction k with
  | zero =>
    dsimp [greedyState]
    exact ⟨rfl, fun p => Iff.intro (fun h => nomatch h) (fun ⟨c, hc1, hc2, _⟩ => False.elim (by omega))⟩
  | succ k ih =>
    dsimp only [greedyState]
    have hpad : padLES54 N s (N + k) = N + k := by
      dsimp [padLES54]; rw [dif_neg (by omega)]
    have hlen : (List.range (N + (k + 1))).length = N + k + 1 := by simp; omega
    have hget : (List.range (N + (k + 1))).getD (N + k) 0 = N + k := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      simp
    have herase : (List.range (N + (k + 1))).eraseIdx (N + k) = List.range (N + k) := by
      have hsp : List.range (N + (k + 1)) = List.range (N + k) ++ [N + k] := by
        rw [show N + (k + 1) = (N + k) + 1 by omega, List.range_succ]
      rw [hsp, List.eraseIdx_append_of_length_le (by simp)]
      simp
    rw [hpad, hget, herase]
    rcases ih with ⟨hrem, hmem⟩
    refine ⟨hrem, fun p => ?_⟩
    rw [List.mem_cons, hmem]
    constructor
    · rintro (rfl | ⟨c, hc1, hc2, rfl⟩)
      · exact ⟨N + k, by omega, by omega, rfl⟩
      · exact ⟨c, hc1, by omega, rfl⟩
    · rintro ⟨c, hc1, hc2, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp (by omega : c < (N + k) + 1) with hlt | rfl
      · right; exact ⟨c, hc1, hlt, rfl⟩
      · left; rfl

theorem greedyDiag_pad_root (N M : ℕ) (hNM : N ≤ M) (s : Fin N → ℕ) (hs : IsLES N s)
    (pos : ℕ) (hpos : pos < M) :
    (greedyDiag (padLES54 N s) 0 M).length = M ∧
    (greedyDiag (padLES54 N s) 0 M)[pos]! =
      (pos, (padPerm54 N M hNM (Aux_as.lesToPerm N s hs)⁻¹ ⟨pos, hpos⟩).1) := by
  set gd := greedyDiag (padLES54 N s) 0 M
  have hle_c : ∀ c, 0 ≤ c → c < M → padLES54 N s c ≤ c := fun c _ _ => padLES54_le N s hs c
  have hlen : gd.length = M := by
    simpa [gd] using Aux_as.greedyDiag_length (padLES54 N s) 0 M (Nat.zero_le M) hle_c
  refine ⟨hlen, ?_⟩
  have hpw : gd.Pairwise (fun p q => p.1 < q.1) :=
    Aux_as.greedyDiag_pairwise_lt (padLES54 N s) 0 M (Nat.zero_le M) hle_c
  have hrow_lt : ∀ p ∈ gd, p.1 < M := greedyDiag_row_lt (padLES54 N s) 0 M (Nat.zero_le M) hle_c
  have hfsts : gd.map Prod.fst = List.range M := by
    refine Aux_as.perm_eq_of_sorted_of_inj id (gd.map Prod.fst) (List.range M) ?_ ?_ ?_ ?_
    · have hnd_gd : (gd.map Prod.fst).Nodup := by
        rw [List.nodup_iff_pairwise_ne]
        rw [List.pairwise_map]
        exact hpw.imp fun h => ne_of_lt h
      refine (List.perm_ext_iff_of_nodup hnd_gd List.nodup_range).mpr fun r => ?_
      rw [List.mem_range]
      constructor
      · intro hr
        rcases List.mem_map.mp hr with ⟨p, hp, rfl⟩
        exact hrow_lt p hp
      · intro hr
        -- Every r < M sits in greedyState (padLES54 N s) 0 M (List.range M) because remaining is []!
        have hprops := Aux_as.greedyState_props (padLES54 N s) 0 M (List.range M)
          (Aux_as.pairwise_range_lt M) (by simp) (fun c _ hc => padLES54_le N s hs c)
        have hrem_nil : (greedyState (padLES54 N s) 0 M (List.range M)).2 = [] :=
          List.eq_nil_of_length_eq_zero hprops.2.1
        rcases (hprops.2.2.2.1 r).mp (List.mem_range.mpr hr) with ⟨c, hc⟩ | hrem
        · rw [List.mem_map]
          exact ⟨(r, c), (List.mergeSort_perm _ _).mem_iff.mpr hc, rfl⟩
        · rw [hrem_nil] at hrem; cases hrem
    · rw [List.pairwise_map]; exact hpw.imp fun h => le_of_lt h
    · exact (Aux_as.pairwise_range_lt M).imp le_of_lt
    · intro a _ b _ h; exact h
  have hpos_gd : pos < gd.length := by omega
  have hfst_pos : (gd[pos]'hpos_gd).1 = pos := by
    have h1 : (gd.map Prod.fst)[pos]'(by simp [hpos_gd]) = (List.range M)[pos]'(by simp [hpos]) := by
      congr 1
    simpa using h1
  -- Identify the column of gd[pos] using greedyState_add and greedyState_pad_top
  have hsplit := Aux_as.greedyState_add (padLES54 N s) 0 N (M - N) (List.range M)
  have haddM : N + (M - N) = M := by omega
  rw [zero_add, haddM] at hsplit
  have htop := greedyState_pad_top N (M - N) s
  rw [haddM] at htop
  set resTop := greedyState (padLES54 N s) N (M - N) (List.range M)
  have hbot_congr : greedyState (padLES54 N s) 0 N resTop.2 =
      greedyState (sExt s) 0 N (List.range N) := by
    rw [htop.1]
    exact greedyState_congr _ _ 0 N (List.range N) fun c _ hc => by
      dsimp [padLES54, sExt]; rw [dif_pos (by omega), dif_pos (by omega)]
  have hp_mem_gs : gd[pos]'hpos_gd ∈ (greedyState (padLES54 N s) 0 M (List.range M)).1 :=
    (List.mergeSort_perm _ _).mem_iff.mp (List.getElem_mem hpos_gd)
  dsimp only at hsplit
  rw [congrArg Prod.fst hsplit, hbot_congr, List.mem_append] at hp_mem_gs
  have hcol_eq : (gd[pos]'hpos_gd).2 =
      (padPerm54 N M hNM (Aux_as.lesToPerm N s hs)⁻¹ ⟨pos, hpos⟩).1 := by
    rcases hp_mem_gs with hp_top | hp_bot
    · rcases htop.2 _ |>.mp hp_top with ⟨c, hc1, hc2, hpeq⟩
      have hc_ge : N ≤ pos := by
        have hpc : pos = c := by rw [← hfst_pos, hpeq]
        omega
      rw [padPerm54_ge N M hNM _ hc_ge]
      have hpc : pos = c := by rw [← hfst_pos, hpeq]
      rw [hpeq]
      exact hpc.symm
    · have hpropsN := Aux_as.greedyState_props (sExt s) 0 N (List.range N) (Aux_as.pairwise_range_lt N)
        (by simp) (fun c _ hc => by
          have hcN : c < N := by omega
          dsimp [sExt]; rw [dif_pos hcN]; exact hs ⟨c, hcN⟩)
      have hcol := (hpropsN.2.2.2.2.2.1 _ hp_bot).2.2.2
      have hrow := List.mem_range.mp (hpropsN.2.2.2.2.2.1 _ hp_bot).1
      rw [zero_add] at hcol
      have hpos_lt : pos < N := by omega
      let cFin : Fin N := ⟨(gd[pos]'hpos_gd).2, hcol⟩
      have hpair_eq : (gd[pos]'hpos_gd) = ((gd[pos]'hpos_gd).1, cFin.1) := rfl
      have hc_spec := Aux_as.lesToPermFun_spec N s hs cFin
      have hc_uniq := hpropsN.2.2.2.2.2.2.2.1 _ hp_bot _ hc_spec rfl
      have hfst_eq : (Aux_as.lesToPerm N s hs cFin).1 = pos := by
        have h1 : (Aux_as.lesToPermFun N s hs cFin).1 = (gd[pos]'hpos_gd).1 :=
          (congrArg Prod.fst hc_uniq).symm
        change (Aux_as.lesToPermFun N s hs cFin).1 = pos
        rw [h1, hfst_pos]
      have hperm_inv : (Aux_as.lesToPerm N s hs)⁻¹ ⟨pos, hpos_lt⟩ = cFin := by
        rw [Equiv.Perm.inv_eq_iff_eq]
        exact Fin.ext hfst_eq.symm
      rw [padPerm54_lt N M hNM _ hpos_lt, hperm_inv]
  have hbang : gd[pos]! = gd[pos]'hpos_gd := by simp [hpos_gd]
  rw [hbang]
  exact Prod.ext hfst_pos hcol_eq

lemma runOffset_zero' {α : Type*} [LinearOrder α] {N : ℕ} (l : Fin (N + 1) → α)
    (hl : Monotone l) : runOffset l ⟨0, Nat.succ_pos N⟩ = 1 :=
  Aux_nsil.runOffset_zero hl (Nat.succ_pos N)

lemma runOffset_succ' {α : Type*} [LinearOrder α] {N : ℕ} (l : Fin N → α) (hl : Monotone l)
    (i : ℕ) (h : i + 1 < N) :
    runOffset l ⟨i + 1, h⟩ =
      if l ⟨i, by omega⟩ = l ⟨i + 1, h⟩ then runOffset l ⟨i, by omega⟩ + 1 else 1 := by
  rw [Aux_nsil.runOffset_succ hl h]
  by_cases heq : l ⟨i, by omega⟩ = l ⟨i + 1, h⟩
  · simp [heq]
  · simp [heq, Ne.symm heq]

lemma runOffset_comp_strictMono {α β : Type*} [LinearOrder α] [LinearOrder β] {N : ℕ}
    (f : α → β) (hf : StrictMono f) (l : Fin N → α) (i : Fin N) :
    runOffset (f ∘ l) i = runOffset l i := by
  dsimp [runOffset, runStart]
  have hfin : (Finset.univ.filter fun j : Fin N => f (l j) < f (l i)) =
      Finset.univ.filter fun j : Fin N => l j < l i := by
    ext j; simp [hf.lt_iff_lt]
  rw [hfin]

lemma runOcc_comp_strictMono {α β : Type*} [LinearOrder α] [LinearOrder β] {N : ℕ}
    (f : α → β) (hf : StrictMono f) (l : Fin N → α) (i : Fin N) :
    runOcc (f ∘ l) i = runOcc l i := by
  dsimp [runOcc]
  have hfin : (Finset.univ.filter fun j : Fin N => j < i ∧ runOffset (f ∘ l) j = runOffset (f ∘ l) i) =
      Finset.univ.filter fun j : Fin N => j < i ∧ runOffset l j = runOffset l i := by
    ext j; simp [runOffset_comp_strictMono f hf]
  rw [hfin]

theorem mem_stabGroup_iff_isLESOf {α : Type*} [LinearOrder α] (N : ℕ) (l : Fin N → α)
    (hl : Monotone l) (s : Fin N → ℕ) (hs : IsLES N s) :
    Aux_as.lesToPerm N s hs ∈ stabGroup N l ↔ IsLESOf N l s := by
  have hfwd : ∀ τ : Equiv.Perm (Fin N), τ ∈ stabGroup N l →
      IsLESOf N l ((Aux_as.lesEquivPerm N).symm τ).1 := by
    intro τ hτ
    have hs_eq : ((Aux_as.lesEquivPerm N).symm τ).1 = permToLES N τ :=
      Aux_as.lesEquivPerm_symm_apply N τ
    intro i
    rw [hs_eq]
    refine ⟨?_, Aux_as.permToLES_isLES N τ i⟩
    dsimp [runStart, permToLES]
    refine Finset.card_le_card fun j hj => ?_
    rw [Finset.mem_filter] at hj ⊢
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · by_contra hge
      exact absurd (hl (Fin.le_iff_val_le_val.mpr (not_lt.mp hge))) (not_le_of_gt hj.2)
    · have hl_ij : l (τ j) < l (τ i) := by rw [hτ j, hτ i]; exact hj.2
      by_contra hge
      exact absurd (hl (not_lt.mp hge)) (not_le_of_gt hl_ij)
  constructor
  · intro hmem
    have heq : s = ((Aux_as.lesEquivPerm N).symm (Aux_as.lesToPerm N s hs)).1 := by
      rw [Aux_as.lesEquivPerm_symm_apply, Aux_as.permToLES_lesToPerm]
    rw [heq]
    exact hfwd _ hmem
  · intro hs_of
    let S : Finset α := Finset.univ.image l
    let l' : Fin N → S := fun i => ⟨l i, Finset.mem_image_of_mem l (Finset.mem_univ i)⟩
    have hl' : Monotone l' := fun _ _ hij => hl hij
    have hstab_eq : stabGroup N l' = stabGroup N l := by
      ext τ; simp [Aux_nsil.mem_stabGroup_iff_permList, permList, funext_iff, Subtype.ext_iff, l']
    have hro_eq : ∀ i : Fin N, runOffset l' i = runOffset l i := fun i => by
      have hfin : (Finset.univ.filter fun j : Fin N => l' j < l' i) =
          Finset.univ.filter fun j : Fin N => l j < l i := by
        ext j; simp [l', Subtype.mk_lt_mk]
      dsimp only [runOffset, runStart]
      rw [hfin]
    have hcard_eq : Fintype.card (stabGroup N l) =
        @Fintype.card { s : Fin N → ℕ // IsLESOf N l s }
          (Fintype.ofEquiv _ (isLESOfEquivPiFinOf N l (Aux_nsil.runStart_le hl)).symm) := by
      let instF : Fintype { s : Fin N → ℕ // IsLESOf N l s } :=
        Fintype.ofEquiv _ (isLESOfEquivPiFinOf N l (Aux_nsil.runStart_le hl)).symm
      have hc1 : Fintype.card (stabGroup N l) = Fintype.card (stabGroup N l') :=
        Fintype.card_congr (Equiv.setCongr (congrArg SetLike.coe hstab_eq.symm))
      have hc2 := Aux_nsil.card_stabGroup_eq_prod_modeCount N l'
      have hc3 := Aux_nsil.prod_runOffset_eq_prod_modeCount N l' hl'
      have hc4 : (∏ i : Fin N, runOffset l' i) = ∏ i : Fin N, runOffset l i :=
        Finset.prod_congr rfl fun i _ => hro_eq i
      have hc3' :
          (∏ b : S, (Finset.univ.filter fun i : Fin N => l' i = b).card.factorial) =
            ∏ i : Fin N, runOffset l' i := by
        convert hc3.symm
      have hc5 := Aux_nsil.card_isLESOf_eq_prod_runOffset' N l hl
      have hc5' :
          @Fintype.card { s : Fin N → ℕ // IsLESOf N l s }
              (Fintype.ofEquiv _ (isLESOfEquivPiFinOf N l (Aux_nsil.runStart_le hl)).symm) =
            ∏ i : Fin N, runOffset l i := by
        convert hc5
      exact hc1.trans (hc2.trans (hc3'.trans (hc4.trans hc5'.symm)))
    let : Fintype { s : Fin N → ℕ // IsLESOf N l s } :=
      Fintype.ofEquiv _ (isLESOfEquivPiFinOf N l (Aux_nsil.runStart_le hl)).symm
    let φ : stabGroup N l → { s : Fin N → ℕ // IsLESOf N l s } :=
      fun τ => ⟨((Aux_as.lesEquivPerm N).symm τ.1).1, hfwd τ.1 τ.2⟩
    have hinj : Function.Injective φ := by
      intro τ₁ τ₂ h
      have hval : ((Aux_as.lesEquivPerm N).symm τ₁.1).1 = ((Aux_as.lesEquivPerm N).symm τ₂.1).1 :=
        congrArg (fun x : { s : Fin N → ℕ // IsLESOf N l s } => x.1) h
      have h1 : (Aux_as.lesEquivPerm N).symm τ₁.1 = (Aux_as.lesEquivPerm N).symm τ₂.1 :=
        Subtype.ext hval
      exact Subtype.ext ((Aux_as.lesEquivPerm N).symm.injective h1)
    have hbij := (Fintype.bijective_iff_injective_and_card φ).mpr ⟨hinj, hcard_eq⟩
    obtain ⟨τ, hτ⟩ := hbij.2 ⟨s, hs_of⟩
    have hval : ((Aux_as.lesEquivPerm N).symm τ.1).1 = s :=
      congrArg (fun x : { s : Fin N → ℕ // IsLESOf N l s } => x.1) hτ
    have hτ_eq : (Aux_as.lesEquivPerm N).symm τ.1 = ⟨s, hs⟩ := Subtype.ext hval
    have hτ_perm : τ.1 = Aux_as.lesToPerm N s hs := by
      have h_app := congrArg (Aux_as.lesEquivPerm N) hτ_eq
      rw [Equiv.apply_symm_apply] at h_app
      simp only [Aux_as.lesEquivPerm, Equiv.ofBijective_apply] at h_app
      exact h_app
    rw [← hτ_perm]
    exact τ.2

theorem card_stabGroup_fin_succ (n K : ℕ) (α : Fin n → ℕ)
    (l : Fin (2 * K) → Fin (n + 1))
    (hα : ∀ i : Fin n, (Finset.univ.filter fun p => l p = ⟨i.1, by omega⟩).card = α i)
    (hblank : (Finset.univ.filter fun p => l p = ⟨n, Nat.lt_succ_self n⟩).card = 2 * K - ∑ i, α i) :
    Fintype.card (stabGroup (2 * K) l) =
      (∏ i : Fin n, (α i).factorial) * (2 * K - ∑ i : Fin n, α i).factorial := by
  rw [Aux_nsil.card_stabGroup_eq_prod_modeCount (2 * K) l, Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    have hi : i.castSucc = ⟨i.1, by omega⟩ := rfl
    rw [hi, hα i]
  · have hl : Fin.last n = ⟨n, Nat.lt_succ_self n⟩ := rfl
    rw [hl, hblank]

theorem orbit_particleSym54_iff_multinom (n K : ℕ) (α : Fin n → ℕ)
    (l : Fin (2 * K) → Fin (n + 1))
    (hα : ∀ i : Fin n, (Finset.univ.filter fun p => l p = ⟨i.1, by omega⟩).card = α i)
    (hblank : (Finset.univ.filter fun p => l p = ⟨n, Nat.lt_succ_self n⟩).card = 2 * K - ∑ i, α i)
    (y : Fin (2 * K) → Fin (n + 1)) :
    (∃ σ : Equiv.Perm (Fin (2 * K)), permList σ l = y) ↔
      let s := Nat.clog 2 n + 1
      let z := flatReg (2 * K) s fun p => particleSym54 n s (y p)
      (∀ i : Fin n,
          (Finset.univ.filter fun r : Fin (2 * K) =>
            splitReg (2 * K) s z r = natToBits s i.val).card = α i) ∧
        (Finset.univ.filter fun r : Fin (2 * K) =>
          splitReg (2 * K) s z r = blankSym54 s).card = 2 * K - ∑ i : Fin n, α i := by
  let s := Nat.clog 2 n + 1
  let z := flatReg (2 * K) s fun p => particleSym54 n s (y p)
  have hsplit : ∀ r : Fin (2 * K), splitReg (2 * K) s z r = particleSym54 n s (y r) := by
    intro r; funext j
    simp [z, splitReg, flatReg]
  have hinj := particleSym54_inj n
  have hfib_i : ∀ i : Fin n,
      (Finset.univ.filter fun r : Fin (2 * K) => splitReg (2 * K) s z r = natToBits s i.val) =
        (Finset.univ.filter fun r : Fin (2 * K) => y r = ⟨i.1, by omega⟩) := by
    intro i; ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hsplit r]
    rw [← particleSym54_lt (j := ⟨i.1, by omega⟩) (s := s) i.isLt]
    exact hinj.eq_iff
  have hfib_b :
      (Finset.univ.filter fun r : Fin (2 * K) => splitReg (2 * K) s z r = blankSym54 s) =
        (Finset.univ.filter fun r : Fin (2 * K) => y r = ⟨n, Nat.lt_succ_self n⟩) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hsplit r]
    have hlast : (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) = Fin.last n := rfl
    rw [hlast, ← particleSym54_last n s]
    exact hinj.eq_iff
  rw [Aux_nsil.mem_permList_range_iff_fiber_card l y]
  have hcongr_i :
      (∀ i : Fin n, (Finset.univ.filter fun r : Fin (2 * K) => splitReg (2 * K) s z r = natToBits s i.val).card = α i) ↔
      (∀ i : Fin n, (Finset.univ.filter fun r : Fin (2 * K) => y r = ⟨i.1, by omega⟩).card = α i) :=
    forall_congr' fun i => by rw [hfib_i i]
  dsimp only
  dsimp only [s, z] at hcongr_i hfib_b
  rw [hcongr_i, hfib_b]
  constructor
  · intro h
    refine ⟨fun i => (h ⟨i.1, by omega⟩).trans (hα i), (h ⟨n, Nat.lt_succ_self n⟩).trans hblank⟩
  · rintro ⟨hi, hb⟩ b
    rcases Fin.eq_castSucc_or_eq_last b with ⟨b', rfl⟩ | rfl
    · have hc : b'.castSucc = ⟨b'.1, by omega⟩ := rfl
      rw [hc]; exact (hi b').trans (hα b').symm
    · have hl : Fin.last n = ⟨n, Nat.lt_succ_self n⟩ := rfl
      rw [hl]; exact hb.trans hblank.symm

end Aux_w54_comb

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open QuantumLTF.Membership.Supplement.LcgSym54 Aux_w54_comb

theorem solution : Nonempty LcgSym54Comb := ⟨{
  bitsToNat_natToBits := bitsToNat_natToBits
  bitsToNat_append := bitsToNat_append
  bitsToNat_inj := fun {_} => bitsToNat_inj
  bitsToNat_lt_two_pow := bitsToNat_lt_two_pow
  natToBits_comp_revPerm := natToBits_comp_revPerm
  bitsToNat_particleSym54_eq := bitsToNat_particleSym54_eq
  bitsToNat_particleSym54_strictMono := bitsToNat_particleSym54_strictMono
  card_les := Aux_as.card_les
  permToLES_isLES := Aux_as.permToLES_isLES
  lesEquivPerm := Aux_as.lesEquivPerm
  lesToPerm := Aux_as.lesToPerm
  lesToPerm_eq := fun _ _ _ => rfl
  permToLES_lesToPerm := Aux_as.permToLES_lesToPerm
  lesEquivPerm_symm_apply := Aux_as.lesEquivPerm_symm_apply
  perm_eq_of_sorted_of_inj := Aux_as.perm_eq_of_sorted_of_inj
  padLES54_le := padLES54_le
  mergePhi_fst_inj := mergePhi_fst_inj
  hbKey1_orig_inj := hbKey1_orig_inj
  hbKey2_orig_inj := hbKey2_orig_inj
  occSortKey_idx_inj := occSortKey_idx_inj
  greedyDiag_length := Aux_as.greedyDiag_length
  greedyDiag_col_mem := greedyDiag_col_mem
  greedyDiag_fst_lt := Aux_as.greedyDiag_pairwise_lt
  greedyDiag_fst_ge_idx := greedyDiag_fst_ge_idx
  greedyDiag_row_lt := greedyDiag_row_lt
  greedyDiag_leaf := greedyDiag_leaf
  alonsoSchott_merge_spec := Aux_as.alonsoSchott_merge_spec
  Ttilde1_col_lt_iff := Ttilde1_col_lt_iff
  greedyDiag_pad_root := greedyDiag_pad_root
  runStart_le := Aux_nsil.runStart_le
  runOffset_pos := Aux_nsil.runOffset_pos
  runOffset_le_N := Aux_nsil.runOffset_le_N
  runOffset_zero := runOffset_zero'
  runOffset_succ := runOffset_succ'
  runOffset_card_le := fun hl _ hm => Aux_nsil.runOffset_card_le hl hm
  harmonicBucketSum_le := Aux_nsil.harmonicBucketSum_le
  mem_bucketPairs_iff := Aux_nsil.mem_bucketPairs_iff
  bucketPairs_length := Aux_nsil.bucketPairs_length
  bucketPairs_nodup := Aux_nsil.bucketPairs_nodup
  runOcc_lt_div := Aux_nsil.runOcc_lt_div
  runOffset_comp_strictMono := runOffset_comp_strictMono
  runOcc_comp_strictMono := runOcc_comp_strictMono
  prod_runOffset_eq_prod_modeCount := Aux_nsil.prod_runOffset_eq_prod_modeCount
  seqScanOcc_eq_runOcc := fun N l p hp hact => (Aux_nsil.seqScanOcc_eq_runOcc N l).2 p hp hact
  harmBucket_routing_spec := Aux_nsil.harmBucket_routing_spec
  mem_stabGroup_iff_isLESOf := mem_stabGroup_iff_isLESOf
  card_stabGroup_eq_prod_modeCount := Aux_nsil.card_stabGroup_eq_prod_modeCount
  card_isLESOf_eq_prod_runOffset := Aux_nsil.card_isLESOf_eq_prod_runOffset'
  mem_permList_range_iff_fiber_card := Aux_nsil.mem_permList_range_iff_fiber_card
  eq_655_701_sum_factorization := Aux_nsil.eq_655_701_sum_factorization
  card_stabGroup_fin_succ := card_stabGroup_fin_succ
  orbit_particleSym54_iff_multinom := orbit_particleSym54_iff_multinom
}⟩
