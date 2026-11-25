-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.G2.sum_splits_evalTwo_word
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:38:39.652633+00:00
-- url     : https://prove2.me/submissions/4f2ce92e-12f0-4caa-bf31-5edb0f076397

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_EvalZeroReplicateAppend
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SumSplitsEvalTwoWord
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_G2_sum_splits_evalOne_word
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_G2_two_mul_choose_two
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.TB.G2
variable {k : Type} [CommRing k] {ι : Type} [DecidableEq ι]
private theorem splits_nil_lemma (w : List ι) (F : List ι → k) (c : k) :
    ((splits w).map (fun p => F p.1 * (if p.2 = [] then c else 0))).sum = F w * c := by
  induction w generalizing F with
  | nil => simp [splits]
  | cons l w ih =>
    simp only [splits, List.map_append, List.map_map, List.sum_append, Function.comp_def]
    rw [ih (fun u => F (l :: u))]
    rw [List.sum_eq_zero (fun x hx => ?_), add_zero]
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hx
    simp
private theorem ev1_cons_lemma_2 (g : ι → k) (l : ι) (t : List ι) :
    ev1 g (l :: t) = if t = [] then g l else 0 := by
  cases t <;> simp [ev1]
private theorem t1_cons_lemma_3 (g : ι → k) (l : ι) (w : List ι) (φ : List ι → k) :
    ((splits (l :: w)).map (fun p => φ p.1 * ev1 g p.2)).sum =
      ((splits w).map (fun p => φ (l :: p.1) * ev1 g p.2)).sum + φ w * g l := by
  simp only [splits, List.map_append, List.map_map, List.sum_append, Function.comp_def,
    ev1_cons_lemma_2]
  rw [splits_nil_lemma w φ (g l)]
private theorem t1_rep_lemma_4 (g : ι → k) (y : ι) (n : ℕ) (w : List ι) (φ : List ι → k) :
    ((splits (List.replicate n y ++ w)).map (fun p => φ p.1 * ev1 g p.2)).sum =
      ((splits w).map (fun p => φ (List.replicate n y ++ p.1) * ev1 g p.2)).sum +
        (n : k) * g y * φ (List.replicate (n - 1) y ++ w) := by
  induction n generalizing φ with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, t1_cons_lemma_3, ih (fun u => φ (y :: u))]
    cases n with
    | zero =>
      simp
      try ring
    | succ n =>
      simp only [Nat.add_sub_cancel, List.replicate_succ, List.cons_append]
      push_cast
      ring
private theorem word_cons_lemma_5 (y : ι) (Ls : List ι) (m : ι →₀ ℕ) :
    word (y :: Ls) m = List.replicate (m y) y ++ word Ls m := by
  simp [word, List.flatMap_cons]
private theorem word_congr_lemma_6 (Ls : List ι) (m m' : ι →₀ ℕ) (h : ∀ z ∈ Ls, m z = m' z) :
    word Ls m = word Ls m' := by
  induction Ls with
  | nil => rfl
  | cons y Ls ih =>
    rw [word_cons_lemma_5, word_cons_lemma_5, h y (by simp), ih fun z hz => h z (by simp [hz])]
private theorem ev2_cons_lemma_7 (c : ι → ι → k) (l : ι) (t : List ι) :
    ev2 c (l :: t) = ev1 (c l) t := by
  rcases t with _ | ⟨a, _ | ⟨b, t⟩⟩ <;> first | rfl | simp [ev1, ev2]
private theorem t2_cons_lemma_8 (c : ι → ι → k) (l : ι) (w : List ι) (φ : List ι → k) :
    ((splits (l :: w)).map (fun p => φ p.1 * ev2 c p.2)).sum =
      ((splits w).map (fun p => φ (l :: p.1) * ev2 c p.2)).sum +
        ((splits w).map (fun p => φ p.1 * ev1 (c l) p.2)).sum := by
  simp only [splits, List.map_append, List.map_map, List.sum_append, Function.comp_def,
    ev2_cons_lemma_7]
private theorem t2_rep_lemma_9 (c : ι → ι → k) (y : ι) (n : ℕ) (w : List ι) (φ : List ι → k) :
    ((splits (List.replicate n y ++ w)).map (fun p => φ p.1 * ev2 c p.2)).sum =
      ((splits w).map (fun p => φ (List.replicate n y ++ p.1) * ev2 c p.2)).sum +
        (n : k) * ((splits w).map (fun p => φ (List.replicate (n - 1) y ++ p.1) * ev1 (c y) p.2)).sum +
        (n.choose 2 : k) * c y y * φ (List.replicate (n - 2) y ++ w) := by
  induction n generalizing φ with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, t2_cons_lemma_8, ih (fun u => φ (y :: u)), t1_rep_lemma_4]
    rcases n with _ | _ | n
    · simp [Nat.choose_zero_succ, Nat.choose_succ_self]
    · simp [Nat.choose_succ_self, Nat.choose_self]
      try ring
    · have e1 : n + 1 + 1 + 1 - 1 = n + 1 + 1 := by omega
      have e2 : n + 1 + 1 - 1 = n + 1 := by omega
      have e3 : n + 1 + 1 + 1 - 2 = n + 1 := by omega
      have e4 : n + 1 + 1 - 2 = n := by omega
      have e5 : (n + 1 + 1 + 1).choose 2 = (n + 1 + 1).choose 2 + (n + 1 + 1) := by
        rw [Nat.choose_succ_succ', Nat.choose_one_right]
        ring
      rw [e1, e2, e3, e4, e5]
      simp only [List.replicate_succ, List.cons_append]
      push_cast
      ring
end ReciprocityTheory.ChartRestriction.G.TB.G2
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.G2
variable {k : Type} [CommRing k] {ι : Type} [DecidableEq ι]
namespace ReciprocityTheory.ChartRestriction.G.TB.G2
theorem _root_.solution (c : ι → ι → k) (hc : ∀ x y, c x y = c y x) (Ls : List ι) (hnd : Ls.Nodup)
    (m : ι →₀ ℕ) (φ : List ι → k) :
    2 * ((splits (word Ls m)).map (fun p => φ p.1 * ev2 c p.2)).sum =
      (Ls.map (fun x => (Ls.map (fun y => c x y * ((m y * (m - Finsupp.single y 1 : ι →₀ ℕ) x : ℕ) : k) *
        φ (word Ls (m - Finsupp.single y 1 - Finsupp.single x 1)))).sum)).sum := by
  revert hnd
  induction Ls generalizing φ with
  | nil =>
    intro _
    simp [word, splits, ev2]
  | cons y0 Ls ih =>
    intro hnd
    have hy : y0 ∉ Ls := (List.nodup_cons.mp hnd).1
    have hnd' : Ls.Nodup := (List.nodup_cons.mp hnd).2
    have hne : ∀ z ∈ Ls, y0 ≠ z := fun z hz h => hy (h ▸ hz)
    rw [word_cons_lemma_5, t2_rep_lemma_9, mul_add, mul_add,
      ih (fun u => φ (List.replicate (m y0) y0 ++ u)) hnd',
      sum_splits_evalOne_word (c y0) Ls hnd' m (fun u => φ (List.replicate (m y0 - 1) y0 ++ u))]
    simp only [List.map_cons, List.sum_cons, List.sum_map_add]
    have ha : c y0 y0 * ((m y0 * (m - Finsupp.single y0 1 : ι →₀ ℕ) y0 : ℕ) : k) *
        φ (word (y0 :: Ls) (m - Finsupp.single y0 1 - Finsupp.single y0 1)) =
        2 * (((m y0).choose 2 : ℕ) * c y0 y0 * φ (List.replicate (m y0 - 2) y0 ++ word Ls m)) := by
      have e1 : (m - Finsupp.single y0 1 : ι →₀ ℕ) y0 = m y0 - 1 := by simp
      have e2 : (m - Finsupp.single y0 1 - Finsupp.single y0 1 : ι →₀ ℕ) y0 = m y0 - 2 := by
        first
        | (simp; done)
        | (simp; omega)
      have e3 : word Ls (m - Finsupp.single y0 1 - Finsupp.single y0 1) = word Ls m :=
        word_congr_lemma_6 _ _ _ fun z hz => by simp [Finsupp.single_apply, hne z hz]
      rw [e1, word_cons_lemma_5, e2, e3, ← two_mul_choose_two]
      push_cast
      ring
    have hb1 : (Ls.map (fun y => c y0 y * ((m y * (m - Finsupp.single y 1 : ι →₀ ℕ) y0 : ℕ) : k) *
          φ (word (y0 :: Ls) (m - Finsupp.single y 1 - Finsupp.single y0 1)))).sum =
        (m y0 : k) * (Ls.map (fun y => (m y : k) * c y0 y *
          φ (List.replicate (m y0 - 1) y0 ++ word Ls (m - Finsupp.single y 1)))).sum := by
      rw [← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun y hyL => ?_
      have hyy : y0 ≠ y := hne y hyL
      have e1 : (m - Finsupp.single y 1 : ι →₀ ℕ) y0 = m y0 := by simp [Finsupp.single_apply, hyy.symm]
      have e2 : (m - Finsupp.single y 1 - Finsupp.single y0 1 : ι →₀ ℕ) y0 = m y0 - 1 := by
        simp [Finsupp.single_apply, hyy.symm]
      have e3 : word Ls (m - Finsupp.single y 1 - Finsupp.single y0 1) = word Ls (m - Finsupp.single y 1) :=
        word_congr_lemma_6 _ _ _ fun z hz => by simp [Finsupp.single_apply, hne z hz]
      rw [e1, word_cons_lemma_5, e2, e3]
      push_cast
      ring
    have hb2 : (Ls.map (fun x => c x y0 * ((m y0 * (m - Finsupp.single y0 1 : ι →₀ ℕ) x : ℕ) : k) *
          φ (word (y0 :: Ls) (m - Finsupp.single y0 1 - Finsupp.single x 1)))).sum =
        (m y0 : k) * (Ls.map (fun y => (m y : k) * c y0 y *
          φ (List.replicate (m y0 - 1) y0 ++ word Ls (m - Finsupp.single y 1)))).sum := by
      rw [← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun x hxL => ?_
      have hxx : y0 ≠ x := hne x hxL
      have e1 : (m - Finsupp.single y0 1 : ι →₀ ℕ) x = m x := by simp [Finsupp.single_apply, hxx]
      have e2 : (m - Finsupp.single y0 1 - Finsupp.single x 1 : ι →₀ ℕ) y0 = m y0 - 1 := by
        simp [Finsupp.single_apply, hxx.symm]
      have e3 : word Ls (m - Finsupp.single y0 1 - Finsupp.single x 1) = word Ls (m - Finsupp.single x 1) :=
        word_congr_lemma_6 _ _ _ fun z hz => by simp [Finsupp.single_apply, hne z hz]
      rw [e1, word_cons_lemma_5, e2, e3, hc x y0]
      push_cast
      ring
    have hcc : (Ls.map (fun x => (Ls.map (fun y => c x y * ((m y * (m - Finsupp.single y 1 : ι →₀ ℕ) x : ℕ) : k) *
          φ (word (y0 :: Ls) (m - Finsupp.single y 1 - Finsupp.single x 1)))).sum)).sum =
        (Ls.map (fun x => (Ls.map (fun y => c x y * ((m y * (m - Finsupp.single y 1 : ι →₀ ℕ) x : ℕ) : k) *
          φ (List.replicate (m y0) y0 ++ word Ls (m - Finsupp.single y 1 - Finsupp.single x 1)))).sum)).sum := by
      congr 1
      refine List.map_congr_left fun x hxL => ?_
      congr 1
      refine List.map_congr_left fun y hyL => ?_
      have e : (m - Finsupp.single y 1 - Finsupp.single x 1 : ι →₀ ℕ) y0 = m y0 := by
        simp [Finsupp.single_apply, (hne y hyL).symm, (hne x hxL).symm]
      rw [word_cons_lemma_5, e]
    linear_combination -ha - hb1 - hb2 - hcc
end ReciprocityTheory.ChartRestriction.G.TB.G2
