-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.G2.sum_splits_evalOne_word
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:31:32.801036+00:00
-- url     : https://prove2.me/submissions/ed00be76-77b6-4c56-ba5c-a65a97b7326e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_EvalZeroReplicateAppend
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SumSplitsEvalTwoWord
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
end ReciprocityTheory.ChartRestriction.G.TB.G2
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.G2
variable {k : Type} [CommRing k] {ι : Type} [DecidableEq ι]
namespace ReciprocityTheory.ChartRestriction.G.TB.G2
theorem _root_.solution (g : ι → k) (Ls : List ι) (hnd : Ls.Nodup) (m : ι →₀ ℕ) (φ : List ι → k) :
    ((splits (word Ls m)).map (fun p => φ p.1 * ev1 g p.2)).sum =
      (Ls.map (fun y => (m y : k) * g y * φ (word Ls (m - Finsupp.single y 1)))).sum := by
  revert hnd
  induction Ls generalizing φ with
  | nil =>
    intro _
    simp [word, splits, ev1]
  | cons y Ls ih =>
    intro hnd
    have hy : y ∉ Ls := (List.nodup_cons.mp hnd).1
    have hnd' : Ls.Nodup := (List.nodup_cons.mp hnd).2
    rw [word_cons_lemma_5, t1_rep_lemma_4, ih (fun u => φ (List.replicate (m y) y ++ u)) hnd',
      List.map_cons, List.sum_cons, add_comm]
    congr 1
    · have e1 : (m - Finsupp.single y 1 : ι →₀ ℕ) y = m y - 1 := by simp
      have e2 : word Ls (m - Finsupp.single y 1) = word Ls m :=
        word_congr_lemma_6 _ _ _ fun z hz => by
          have hyz : y ≠ z := fun h => hy (h ▸ hz)
          simp [Finsupp.single_apply, hyz]
      rw [word_cons_lemma_5, e1, e2]
    · congr 1
      refine List.map_congr_left fun z hz => ?_
      have hzy : z ≠ y := fun h => hy (h ▸ hz)
      have e : (m - Finsupp.single z 1 : ι →₀ ℕ) y = m y := by simp [Finsupp.single_apply, hzy]
      rw [word_cons_lemma_5, e]
end ReciprocityTheory.ChartRestriction.G.TB.G2
