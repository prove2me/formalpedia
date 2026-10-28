-- Prove2me | solution 1 for SyncPrefix.Huffman.sc_disjoint_copies_reduction
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T07:36:52.667606+00:00
-- url     : https://prove2.me/submissions/f8ffe7e4-3d6d-4287-9bf4-05f6af68edaa

import Mathlib.Data.Finset.Prod
import Definitions.Def_SyncPrefix_Huffman_Complexity
import Definitions.Def_SyncPrefix_Huffman_DisjointCopies
import Theorems.Thm_SyncPrefix_Huffman_scDisjointCopies_encode_polyTime

set_option autoImplicit false

open SyncPrefix.Huffman SetCoverThreshold.SetCover

namespace ScDisjointCopiesProof

lemma scDisjointCopies_n (I : SCInstance) :
    (scDisjointCopies I).n = I.n ^ 2 := rfl

lemma scDisjointCopies_sets_length (I : SCInstance) :
    (scDisjointCopies I).sets.length = I.n * I.sets.length := by
  unfold scDisjointCopies
  dsimp only
  rw [List.length_flatMap]
  simp

lemma drop_flatMap_const {α β : Type} (f : α → List β) (m : ℕ)
    (hf : ∀ a, (f a).length = m) :
    ∀ (L : List α) (r : ℕ), (L.flatMap f).drop (r * m) = (L.drop r).flatMap f
  | L, 0 => by simp
  | [], r + 1 => by simp
  | a :: L, r + 1 => by
    have h1 : (f a ++ L.flatMap f).drop m = L.flatMap f := by
      rw [← hf a, List.drop_left]
    rw [List.flatMap_cons, Nat.succ_mul, add_comm (r * m) m,
      ← List.drop_drop, h1, List.drop_succ_cons]
    exact drop_flatMap_const f m hf L r

lemma scDisjointCopies_sets_getElem (I : SCInstance) (r : Fin I.n) (i : Fin I.sets.length) :
    (scDisjointCopies I).sets[r.val * I.sets.length + i.val]'(by
      rw [scDisjointCopies_sets_length]
      have hr := r.isLt
      have hi := i.isLt
      nlinarith) = scCopySet I.n r (I.sets.get i) := by
  unfold scDisjointCopies
  dsimp only
  let f : Fin I.n → List (Finset (Fin (I.n ^ 2))) := fun r' => I.sets.map (scCopySet I.n r')
  have hlen : r.val * I.sets.length + i.val < ((List.finRange I.n).flatMap f).length := by
    rw [List.length_flatMap]
    simp only [f, List.map_const', List.length_map, List.sum_replicate, List.length_finRange, smul_eq_mul]
    have hr := r.isLt
    have hi := i.isLt
    nlinarith
  have h1 : Option.some (((List.finRange I.n).flatMap f)[r.val * I.sets.length + i.val]'hlen) =
      ((((List.finRange I.n).flatMap f).drop (r.val * I.sets.length)).drop i.val).head? := by
    rw [List.drop_drop, List.head?_drop, List.getElem?_eq_getElem hlen]
  have hdrop : ((List.finRange I.n).flatMap f).drop (r.val * I.sets.length) =
      ((List.finRange I.n).drop r.val).flatMap f :=
    drop_flatMap_const f I.sets.length (by intro a; simp [f]) (List.finRange I.n) r.val
  have hfin_drop : (List.finRange I.n).drop r.val =
      r :: (List.finRange I.n).drop (r.val + 1) := by
    have hlt : r.val < (List.finRange I.n).length := by simp [r.isLt]
    rw [List.drop_eq_getElem_cons hlt]
    simp
  rw [hdrop, hfin_drop, List.flatMap_cons] at h1
  have hi_lt : i.val < (f r).length := by simp [f, i.isLt]
  rw [List.head?_drop, List.getElem?_append_left hi_lt, List.getElem?_eq_getElem hi_lt] at h1
  simpa [f] using Option.some.inj h1

def ptCopy (n : ℕ) (_hn : 1 ≤ n) (y : Fin (n ^ 2)) : Fin n :=
  ⟨y.val / n, Nat.div_lt_of_lt_mul (by
    have hy := y.isLt
    nlinarith)⟩

def ptElem (n : ℕ) (hn : 1 ≤ n) (y : Fin (n ^ 2)) : Fin n :=
  ⟨y.val % n, Nat.mod_lt y.val (by omega)⟩

lemma scCopyPoint_ptCopy_ptElem (n : ℕ) (hn : 1 ≤ n) (y : Fin (n ^ 2)) :
    scCopyPoint n (ptCopy n hn y) (ptElem n hn y) = y := by
  ext
  simp only [scCopyPoint, ptCopy, ptElem]
  have h := Nat.div_add_mod y.val n
  nlinarith

lemma scCopyPoint_inj (n : ℕ) (r₁ x₁ r₂ x₂ : Fin n)
    (h : scCopyPoint n r₁ x₁ = scCopyPoint n r₂ x₂) :
    r₁ = r₂ ∧ x₁ = x₂ := by
  have hval : r₁.val * n + x₁.val = r₂.val * n + x₂.val := congrArg Fin.val h
  have hx1 := x₁.isLt
  have hx2 := x₂.isLt
  have hr : r₁.val = r₂.val := by nlinarith
  have hx : x₁.val = x₂.val := by nlinarith
  exact ⟨Fin.ext hr, Fin.ext hx⟩

lemma mem_scCopySet_iff (n : ℕ) (hn : 1 ≤ n) (r : Fin n) (S : Finset (Fin n))
    (y : Fin (n ^ 2)) :
    y ∈ scCopySet n r S ↔ r = ptCopy n hn y ∧ ptElem n hn y ∈ S := by
  unfold scCopySet
  rw [Finset.mem_image]
  constructor
  · rintro ⟨x, hxS, hxy⟩
    rw [← scCopyPoint_ptCopy_ptElem n hn y] at hxy
    obtain ⟨hr, hx⟩ := scCopyPoint_inj n r x (ptCopy n hn y) (ptElem n hn y) hxy
    subst hr hx
    exact ⟨rfl, hxS⟩
  · rintro ⟨rfl, hyS⟩
    exact ⟨ptElem n hn y, hyS, scCopyPoint_ptCopy_ptElem n hn y⟩

lemma mem_scCopySet_scCopyPoint_iff (n : ℕ) (r r' : Fin n) (S : Finset (Fin n)) (x : Fin n) :
    scCopyPoint n r x ∈ scCopySet n r' S ↔ r' = r ∧ x ∈ S := by
  unfold scCopySet
  rw [Finset.mem_image]
  constructor
  · rintro ⟨x', hx'S, hxx'⟩
    obtain ⟨hr, hx⟩ := scCopyPoint_inj n r' x' r x hxx'
    subst hr hx
    exact ⟨rfl, hx'S⟩
  · rintro ⟨rfl, hxS⟩
    exact ⟨x, hxS, rfl⟩

lemma coverable_scDisjointCopies (I : SCInstance) (hCov : I.Coverable) (hn : 1 ≤ I.n) :
    (scDisjointCopies I).Coverable := by
  intro y
  let r := ptCopy I.n hn y
  let x := ptElem I.n hn y
  obtain ⟨S, hS_mem, hxS⟩ := hCov x
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hS_mem
  refine ⟨scCopySet I.n r (I.sets.get i), ?_, ?_⟩
  · unfold scDisjointCopies
    rw [List.mem_flatMap]
    exact ⟨r, List.mem_finRange r, List.mem_map_of_mem (List.get_mem _ _)⟩
  · exact (mem_scCopySet_iff I.n hn r (I.sets.get i) y).mpr ⟨rfl, hxS⟩

lemma isCover_univ (I : SCInstance) (hCov : I.Coverable) :
    I.IsCover Finset.univ := by
  intro x
  obtain ⟨S, hS_mem, hxS⟩ := hCov x
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hS_mem
  exact ⟨i, Finset.mem_univ i, hxS⟩

lemma exists_minCover (I : SCInstance) (hCov : I.Coverable) :
    ∃ C, I.IsCover C ∧ C.card = minCover I :=
  Nat.sInf_mem (s := {c | ∃ C, I.IsCover C ∧ C.card = c})
    ⟨_, Finset.univ, isCover_univ I hCov, rfl⟩

lemma one_le_minCover (I : SCInstance) (hCov : I.Coverable) (hn : 1 ≤ I.n) :
    1 ≤ minCover I := by
  obtain ⟨C, hC, hC_card⟩ := exists_minCover I hCov
  obtain ⟨i, hiC, -⟩ := hC ⟨0, hn⟩
  rw [← hC_card]
  exact Finset.one_le_card.mpr ⟨i, hiC⟩

def prodIdx (I : SCInstance) (p : Fin I.n × Fin I.sets.length) :
    Fin (scDisjointCopies I).sets.length :=
  ⟨p.1.val * I.sets.length + p.2.val, by
    rw [scDisjointCopies_sets_length]
    have hr := p.1.isLt
    have hi := p.2.isLt
    nlinarith⟩

lemma minCover_scDisjointCopies_le (I : SCInstance) (hCov : I.Coverable) (hn : 1 ≤ I.n) :
    minCover (scDisjointCopies I) ≤ I.n * minCover I := by
  obtain ⟨C, hC, hC_card⟩ := exists_minCover I hCov
  let C' : Finset (Fin (scDisjointCopies I).sets.length) :=
    ((Finset.univ : Finset (Fin I.n)) ×ˢ C).image (prodIdx I)
  have hIsCov' : (scDisjointCopies I).IsCover C' := by
    intro y
    let r := ptCopy I.n hn y
    let x := ptElem I.n hn y
    obtain ⟨i, hiC, hxi⟩ := hC x
    refine ⟨prodIdx I (r, i), ?_, ?_⟩
    · exact Finset.mem_image_of_mem (prodIdx I) (Finset.mem_product.mpr ⟨Finset.mem_univ r, hiC⟩)
    · change y ∈ (scDisjointCopies I).sets[r.val * I.sets.length + i.val]'_
      rw [scDisjointCopies_sets_getElem I r i]
      exact (mem_scCopySet_iff I.n hn r (I.sets.get i) y).mpr ⟨rfl, hxi⟩
  have hle1 : minCover (scDisjointCopies I) ≤ C'.card :=
    Nat.sInf_le ⟨C', hIsCov', rfl⟩
  have hle2 : C'.card ≤ I.n * C.card := by
    calc C'.card ≤ ((Finset.univ : Finset (Fin I.n)) ×ˢ C).card := Finset.card_image_le
      _ = I.n * C.card := by simp [Finset.card_product]
  rw [← hC_card]
  exact le_trans hle1 hle2

def idxCopy (I : SCInstance) (_hm : 0 < I.sets.length)
    (k : Fin (scDisjointCopies I).sets.length) : Fin I.n :=
  ⟨k.val / I.sets.length, Nat.div_lt_of_lt_mul (by
    have hk := k.isLt
    have hlen := scDisjointCopies_sets_length I
    nlinarith)⟩

def idxSet (I : SCInstance) (hm : 0 < I.sets.length)
    (k : Fin (scDisjointCopies I).sets.length) : Fin I.sets.length :=
  ⟨k.val % I.sets.length, Nat.mod_lt k.val hm⟩

lemma scDisjointCopies_sets_get_decomp (I : SCInstance) (hm : 0 < I.sets.length)
    (k : Fin (scDisjointCopies I).sets.length) :
    (scDisjointCopies I).sets.get k =
      scCopySet I.n (idxCopy I hm k) (I.sets.get (idxSet I hm k)) := by
  have hk_eq : (idxCopy I hm k).val * I.sets.length + (idxSet I hm k).val = k.val := by
    simp only [idxCopy, idxSet]
    have h := Nat.div_add_mod k.val I.sets.length
    nlinarith
  have hget := scDisjointCopies_sets_getElem I (idxCopy I hm k) (idxSet I hm k)
  simpa [List.get_eq_getElem, hk_eq] using hget

lemma le_minCover_scDisjointCopies (I : SCInstance) (hCov : I.Coverable) (hn : 1 ≤ I.n) :
    I.n * minCover I ≤ minCover (scDisjointCopies I) := by
  have hCov' := coverable_scDisjointCopies I hCov hn
  obtain ⟨C', hC', hC'_card⟩ := exists_minCover (scDisjointCopies I) hCov'
  have hm : 0 < I.sets.length := by
    obtain ⟨S, hS_mem, -⟩ := hCov ⟨0, hn⟩
    exact List.length_pos_of_mem hS_mem
  have hslice : ∀ r : Fin I.n,
      minCover I ≤ (C'.filter (fun k => idxCopy I hm k = r)).card := by
    intro r
    let Cr := (C'.filter (fun k => idxCopy I hm k = r)).image (idxSet I hm)
    have hCov_r : I.IsCover Cr := by
      intro x
      obtain ⟨k, hkC', hkx⟩ := hC' (scCopyPoint I.n r x)
      rw [scDisjointCopies_sets_get_decomp I hm k] at hkx
      obtain ⟨hkr, hx_get⟩ := (mem_scCopySet_scCopyPoint_iff I.n r (idxCopy I hm k)
        (I.sets.get (idxSet I hm k)) x).mp hkx
      refine ⟨idxSet I hm k, ?_, hx_get⟩
      exact Finset.mem_image_of_mem (idxSet I hm)
        (Finset.mem_filter.mpr ⟨hkC', hkr⟩)
    exact le_trans (Nat.sInf_le ⟨Cr, hCov_r, rfl⟩) Finset.card_image_le
  rw [← hC'_card]
  have hfib : C'.card = ∑ r : Fin I.n, (C'.filter (fun k => idxCopy I hm k = r)).card := by
    simpa using Finset.card_eq_sum_card_fiberwise
      (f := idxCopy I hm) (s := C') (t := Finset.univ)
      (fun k _ => Finset.mem_univ _)
  rw [hfib]
  calc I.n * minCover I
      = ∑ _r : Fin I.n, minCover I := by simp
    _ ≤ ∑ r : Fin I.n, (C'.filter (fun k => idxCopy I hm k = r)).card :=
        Finset.sum_le_sum (fun r _ => hslice r)

end ScDisjointCopiesProof

theorem solution (Alg : List (Option Bool) → List Unit)
    (hAlg : CookPvsNP.PolyTimeComputable Alg) :
    ∃ Alg' : List (Option Bool) → List Unit, CookPvsNP.PolyTimeComputable Alg' ∧
      ∀ I : SCInstance, I.Coverable → 1 ≤ I.n →
        ∃ I' : SCInstance, I'.Coverable ∧ I'.n = I.n ^ 2 ∧
          I'.sets.length = I.n * I.sets.length ∧
          minCover I' = I.n * minCover I ∧
          1 ≤ minCover I ∧
          (Alg' I.encode).length = (Alg I'.encode).length / I.n := by
  obtain ⟨Alg', hAlg', hAlg'_spec⟩ := scDisjointCopies_encode_polyTime Alg hAlg
  refine ⟨Alg', hAlg', fun I hCov hn => ?_⟩
  refine ⟨scDisjointCopies I,
    ScDisjointCopiesProof.coverable_scDisjointCopies I hCov hn,
    ScDisjointCopiesProof.scDisjointCopies_n I,
    ScDisjointCopiesProof.scDisjointCopies_sets_length I,
    le_antisymm
      (ScDisjointCopiesProof.minCover_scDisjointCopies_le I hCov hn)
      (ScDisjointCopiesProof.le_minCover_scDisjointCopies I hCov hn),
    ScDisjointCopiesProof.one_le_minCover I hCov hn,
    hAlg'_spec I hCov hn⟩
