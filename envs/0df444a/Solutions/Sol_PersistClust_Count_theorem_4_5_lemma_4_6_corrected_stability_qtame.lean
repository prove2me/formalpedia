-- Prove2me | solution 1 for PersistClust.Count.theorem_4_5_lemma_4_6_corrected_stability_qtame
-- status  : ACCEPTED   (disprove)
-- author  : @fabianroll
-- created : 2026-10-10T08:53:06.490422+00:00
-- url     : https://prove2.me/submissions/40d149f2-8150-41e5-b8ba-cf5cb700527f

import Mathlib
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_TruncRank

/-! ## Counterexample to `theorem_4_5_lemma_4_6_corrected_stability_qtame`

A pair of genuine 3-point persistence modules (`FiltrationLaw`) whose α-truncated rank functions
satisfy the box-expansion interleaving (`hbox`, α = −2, ε = 1) and all q-tameness / diagram /
finite-support hypotheses, yet for which the asserted multi-bijection of copies with ε-close
control FAILS. The X-truncated diagram carries a mortal bar at (4.2, 0.5); the Y-truncated
diagram's support is {(5,−2),(3.2,−1.5),(1.6,0.3)}, no point of which is ε-close (radius 1) to
(4.2,0.5), and no diagonal point is ε-close to (4.2,0.5) either. Hence the published statement
(rank-level hypothesis ⇒ module-level conclusion) is FALSE. -/

open PersistClust.Count

namespace StabQCE28

noncomputable section

/-! ### Module X : barcode (5,⊥), (4.2, 0.5), (2.5, −0.6) -/

def fX : Fin 3 → ℝ := fun i => if i = 0 then 5 else if i = 1 then 4.2 else 2.5
def stageX (s : ℝ) : Set (Fin 3) := {i | s ≤ fX i}
def JX (t : ℝ) (x y : Fin 3) : Prop :=
  x ∈ stageX t ∧ y ∈ stageX t ∧
    (x = y ∨ (t ≤ 0.5 ∧ ((x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0))) ∨ t ≤ -0.6)

/-! ### Module Y : barcode (5,⊥), (3.2, −1.5), (1.6, 0.3) -/

def fY : Fin 3 → ℝ := fun i => if i = 0 then 5 else if i = 1 then 3.2 else 1.6
def stageY (s : ℝ) : Set (Fin 3) := {i | s ≤ fY i}
def JY (t : ℝ) (x y : Fin 3) : Prop :=
  x ∈ stageY t ∧ y ∈ stageY t ∧
    (x = y ∨ (t ≤ 0.3 ∧ ((x = 0 ∧ y = 2) ∨ (x = 2 ∧ y = 0))) ∨ t ≤ -1.5)

lemma fX_zero : fX 0 = 5 := by simp [fX]
lemma fX_one : fX 1 = 4.2 := by simp [fX]
lemma fX_two : fX 2 = 2.5 := by simp [fX]
lemma fY_zero : fY 0 = 5 := by simp [fY]
lemma fY_one : fY 1 = 3.2 := by simp [fY]
lemma fY_two : fY 2 = 1.6 := by simp [fY]

lemma mem_stageX (s : ℝ) (i : Fin 3) : i ∈ stageX s ↔ s ≤ fX i := Iff.rfl
lemma mem_stageY (s : ℝ) (i : Fin 3) : i ∈ stageY s ↔ s ≤ fY i := Iff.rfl

/-- Exhaustion of `Fin 3`. -/
lemma fin3_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  fin_cases i <;> simp

/-! ### Rank formulas (for `t ≤ s`) -/

noncomputable def indEss (β : ℝ) (s : ℝ) : ℕ∞ := if s ≤ β then 1 else 0
noncomputable def indMort (β δ : ℝ) (s t : ℝ) : ℕ∞ := if s ≤ β ∧ δ < t then 1 else 0

/-- A `Fin 3` value is `≤ 1` iff it is `0` or `1`. -/
lemma fin3_le_one (i : Fin 3) : i.val ≤ 1 ↔ i = 0 ∨ i = 1 := by
  fin_cases i <;> simp [Fin.ext_iff, Fin.val_one, Fin.val_zero, show (2:Fin 3).val = 2 from rfl]

lemma JX_class_eq (t : ℝ) (x : Fin 3) (hx : x ∈ stageX t) :
    {y : Fin 3 | JX t x y} =
      if t ≤ -0.6 then stageX t
      else if t ≤ 0.5 then if x.val ≤ 1 then {y ∈ stageX t | y.val ≤ 1} else ({2} : Set (Fin 3))
      else ({x} : Set (Fin 3)) := by
  ext y
  by_cases ht1 : t ≤ -0.6
  · simp only [if_pos ht1, Set.mem_setOf_eq]
    unfold JX
    refine ⟨fun h => h.2.1, fun hy => ⟨hx, hy, Or.inr (Or.inr ht1)⟩⟩
  · by_cases ht2 : t ≤ 0.5
    · by_cases hxv : x.val ≤ 1
      · simp only [if_neg ht1, if_pos ht2, if_pos hxv, Set.mem_setOf_eq, Set.mem_sep_iff]
        unfold JX
        refine ⟨?_, ?_⟩
        · rintro ⟨_, hy, hd⟩
          refine ⟨hy, ?_⟩
          rcases hd with rfl | ⟨_, ho⟩ | hz
          · exact hxv
          · rcases ho with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
          · exact (ht1 hz).elim
        · rintro ⟨hy, hyv⟩
          refine ⟨hx, hy, ?_⟩
          by_cases hxy : x = y
          · exact Or.inl hxy
          · have hx01 : x = 0 ∨ x = 1 := (fin3_le_one x).mp hxv
            have hy01 : y = 0 ∨ y = 1 := (fin3_le_one y).mp hyv
            refine Or.inr (Or.inl ⟨ht2, ?_⟩)
            rcases hx01 with rfl | rfl
            · rcases hy01 with rfl | h1
              · exact absurd rfl hxy
              · exact Or.inl ⟨rfl, h1⟩
            · rcases hy01 with h0 | rfl
              · exact Or.inr ⟨rfl, h0⟩
              · exact absurd rfl hxy
      · have hx2 : x = 2 := Fin.ext_iff.mpr (by
          have h3 : x.val < 3 := x.isLt
          have h4 : (2:Fin 3).val = 2 := rfl
          omega)
        subst hx2
        simp only [if_neg ht1, if_pos ht2, if_neg hxv,
                   Set.mem_setOf_eq, Set.mem_singleton_iff]
        unfold JX
        refine ⟨?_, ?_⟩
        · rintro ⟨_, _, hd⟩
          rcases hd with rfl | ⟨_, ho⟩ | hz
          · rfl
          · rcases ho with ⟨h, _⟩ | ⟨h, _⟩
            · exfalso
              have hv : (2:Fin 3).val = (0:Fin 3).val := Fin.ext_iff.mp h
              rw [show (2:Fin 3).val = 2 from rfl, show (0:Fin 3).val = 0 from rfl] at hv
              omega
            · exfalso
              have hv : (2:Fin 3).val = (1:Fin 3).val := Fin.ext_iff.mp h
              rw [show (2:Fin 3).val = 2 from rfl, show (1:Fin 3).val = 1 from rfl] at hv
              omega
          · exact (ht1 hz).elim
        · rintro rfl; exact ⟨hx, hx, Or.inl rfl⟩
    · simp only [if_neg ht1, if_neg ht2, Set.mem_setOf_eq, Set.mem_singleton_iff]
      unfold JX
      refine ⟨?_, ?_⟩
      · rintro ⟨_, _, hd⟩
        rcases hd with rfl | ⟨hm, _⟩ | hz
        · rfl
        · exact (ht2 hm).elim
        · exact (ht1 hz).elim
      · rintro rfl; exact ⟨hx, hx, Or.inl rfl⟩

/-- Helpers for evaluating `indEss` / `indMort`. -/
private lemma indEss_pos (β s : ℝ) (h : s ≤ β) : indEss β s = 1 := by simp [indEss, h]
private lemma indEss_neg (β s : ℝ) (h : ¬ s ≤ β) : indEss β s = 0 := by simp [indEss, h]
private lemma indMort_pos (β δ s t : ℝ) (hs : s ≤ β) (ht : δ < t) :
    indMort β δ s t = 1 := by simp [indMort, hs, ht]
private lemma indMort_neg_s (β δ s t : ℝ) (h : ¬ s ≤ β) : indMort β δ s t = 0 := by simp [indMort, h]
private lemma indMort_neg_t (β δ s t : ℝ) (h : ¬ δ < t) : indMort β δ s t = 0 := by simp [indMort, h]
private lemma indMort_neg (β δ s t : ℝ) (h : ¬ (s ≤ β ∧ δ < t)) : indMort β δ s t = 0 := by simp [indMort, h]

/-- `stageX s` as an explicit set, by region of `s`. -/
private lemma stageX_eq_012 {s : ℝ} (h : s ≤ 2.5) :
    stageX s = ({(0:Fin 3),(1:Fin 3),(2:Fin 3)} : Set (Fin 3)) := by
  ext i; fin_cases i <;> simp [mem_stageX, fX_zero, fX_one, fX_two] <;> linarith
private lemma stageX_eq_01 {s : ℝ} (h25 : ¬ s ≤ 2.5) (h42 : s ≤ 4.2) :
    stageX s = ({(0:Fin 3),(1:Fin 3)} : Set (Fin 3)) := by
  ext i; fin_cases i <;> simp [mem_stageX, fX_zero, fX_one, fX_two] <;> linarith
private lemma stageX_eq_0 {s : ℝ} (h42 : ¬ s ≤ 4.2) (h5 : s ≤ 5) :
    stageX s = ({(0:Fin 3)} : Set (Fin 3)) := by
  ext i; fin_cases i <;> simp [mem_stageX, fX_zero, fX_one, fX_two] <;> linarith
private lemma stageX_eq_empty {s : ℝ} (h5 : ¬ s ≤ 5) : stageX s = (∅ : Set (Fin 3)) := by
  ext i; fin_cases i <;> simp [mem_stageX, fX_zero, fX_one, fX_two] <;> linarith

private lemma sepX_eq_01 {t : ℝ} (ht : t ≤ 2.5) :
    {y : Fin 3 | y ∈ stageX t ∧ y.val ≤ 1} = ({(0:Fin 3),(1:Fin 3)} : Set (Fin 3)) := by
  ext y
  fin_cases y <;> simp [mem_stageX, fX_zero, fX_one, fX_two, fin3_le_one] <;> linarith

theorem rankX_eq (s t : ℝ) (hts : t ≤ s) :
    rankFn stageX JX s t = indEss 5 s + indMort 4.2 0.5 s t + indMort 2.5 (-0.6) s t := by
  unfold rankFn
  by_cases htA : 0.5 < t
  · -- Region A: every class is a singleton
    have hle05A : ¬ t ≤ 0.5 := not_le.mpr htA
    have hneg06A : ¬ t ≤ -0.6 := not_le.mpr (by linarith : -0.6 < t)
    have hpos06 : -0.6 < t := by linarith
    have hcls : ∀ x ∈ stageX s, {y : Fin 3 | JX t x y} = ({x} : Set (Fin 3)) := by
      intro x hx
      have hxt : x ∈ stageX t :=
        (mem_stageX t x).mpr (hts.trans ((mem_stageX s x).mp hx))
      rw [JX_class_eq t x hxt, if_neg hneg06A, if_neg hle05A]
    have himg : (fun x => {y : Fin 3 | JX t x y}) '' stageX s =
        (fun x => ({x} : Set (Fin 3))) '' stageX s := by
      ext c
      simp only [Set.mem_image]
      constructor
      · rintro ⟨x, hx, hfx⟩; exact ⟨x, hx, (hcls x hx).symm.trans hfx⟩
      · rintro ⟨x, hx, hfx⟩; exact ⟨x, hx, (hcls x hx).trans hfx⟩
    rw [himg]
    have hcard : ((fun x => ({x} : Set (Fin 3))) '' stageX s).encard = (stageX s).encard :=
      Set.InjOn.encard_image (fun a _ b _ hhe => by simpa using hhe)
    rw [hcard]
    by_cases hs25 : s ≤ 2.5
    · have hs42 : s ≤ 4.2 := hs25.trans (by linarith)
      have hs5 : s ≤ 5 := hs25.trans (by linarith)
      rw [stageX_eq_012 hs25, Set.encard_insert_of_notMem (by decide),
          Set.encard_insert_of_notMem (by decide), Set.encard_singleton,
          indEss_pos 5 s hs5, indMort_pos 4.2 0.5 s t hs42 htA,
          indMort_pos 2.5 (-0.6) s t hs25 hpos06]
    · by_cases hs42 : s ≤ 4.2
      · have hs5 : s ≤ 5 := hs42.trans (by linarith)
        rw [stageX_eq_01 hs25 hs42, Set.encard_insert_of_notMem (by decide),
            Set.encard_singleton, indEss_pos 5 s hs5, indMort_pos 4.2 0.5 s t hs42 htA,
            indMort_neg_s 2.5 (-0.6) s t hs25, add_zero]
      · by_cases hs5 : s ≤ 5
        · rw [stageX_eq_0 hs42 hs5, Set.encard_singleton,
              indEss_pos 5 s hs5, indMort_neg_s 4.2 0.5 s t hs42,
              indMort_neg_s 2.5 (-0.6) s t hs25, add_zero, add_zero]
        · rw [stageX_eq_empty hs5, Set.encard_empty,
              indEss_neg 5 s hs5, indMort_neg_s 4.2 0.5 s t hs42,
              indMort_neg_s 2.5 (-0.6) s t hs25, add_zero, add_zero]
  · by_cases htC : t ≤ -0.6
    · -- Region C: all classes merge to stageX t = {0,1,2}
      have ht25 : t ≤ 2.5 := by linarith
      have hpos05 : ¬ 0.5 < t := not_lt.mpr (by linarith : t ≤ 0.5)
      have hpos06 : ¬ -0.6 < t := not_lt.mpr htC
      by_cases hs5 : s ≤ 5
      · have himg : (fun x => {y : Fin 3 | JX t x y}) '' stageX s =
          ({({(0:Fin 3),(1:Fin 3),(2:Fin 3)} : Set (Fin 3))} : Set (Set (Fin 3))) := by
          ext c
          simp only [Set.mem_image, Set.mem_singleton_iff]
          constructor
          · rintro ⟨x, hx, rfl⟩
            have hxt : x ∈ stageX t :=
              (mem_stageX t x).mpr (hts.trans ((mem_stageX s x).mp hx))
            rw [JX_class_eq t x hxt, if_pos htC, stageX_eq_012 ht25]
          · rintro rfl
            refine ⟨0, (mem_stageX s 0).mpr (by rw [fX_zero]; linarith), ?_⟩
            have h0t : (0:Fin 3) ∈ stageX t :=
              (mem_stageX t 0).mpr (by rw [fX_zero]; linarith)
            rw [JX_class_eq t 0 h0t, if_pos htC, stageX_eq_012 ht25]
        rw [himg, Set.encard_singleton, indEss_pos 5 s hs5,
            indMort_neg_t 4.2 0.5 s t hpos05, indMort_neg_t 2.5 (-0.6) s t hpos06,
            add_zero, add_zero]
      · have himg : (fun x => {y : Fin 3 | JX t x y}) '' stageX s = (∅ : Set (Set (Fin 3))) := by
          rw [Set.image_eq_empty, stageX_eq_empty hs5]
        have hs42 : ¬ s ≤ 4.2 := fun h => hs5 (h.trans (by linarith))
        have hs25 : ¬ s ≤ 2.5 := fun h => hs5 (h.trans (by linarith))
        rw [himg, Set.encard_empty, indEss_neg 5 s hs5,
            indMort_neg_s 4.2 0.5 s t hs42, indMort_neg_s 2.5 (-0.6) s t hs25,
            add_zero, add_zero]
    · -- Region B: -0.6 < t ≤ 0.5
      have hle05 : t ≤ 0.5 := not_lt.mp htA
      have ht25 : t ≤ 2.5 := by linarith
      have hpos06 : -0.6 < t := not_le.mp htC
      by_cases hs25 : s ≤ 2.5
      · have hs42 : s ≤ 4.2 := hs25.trans (by linarith)
        have hs5 : s ≤ 5 := hs25.trans (by linarith)
        have himg : (fun x => {y : Fin 3 | JX t x y}) '' stageX s =
            ({({(0:Fin 3),(1:Fin 3)} : Set (Fin 3)), ({(2:Fin 3)} : Set (Fin 3))}
              : Set (Set (Fin 3))) := by
          ext c
          simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
          constructor
          · rintro ⟨x, hx, rfl⟩
            have hxt : x ∈ stageX t :=
              (mem_stageX t x).mpr (hts.trans ((mem_stageX s x).mp hx))
            rw [JX_class_eq t x hxt, if_neg htC, if_pos hle05]
            by_cases hxv : x.val ≤ 1
            · exact Or.inl (by rw [if_pos hxv]; exact sepX_eq_01 ht25)
            · exact Or.inr (by rw [if_neg hxv])
          · rintro (h | h)
            · subst h
              refine ⟨0, (mem_stageX s 0).mpr (by rw [fX_zero]; linarith), ?_⟩
              have h0t : (0:Fin 3) ∈ stageX t :=
                (mem_stageX t 0).mpr (by rw [fX_zero]; linarith)
              rw [JX_class_eq t 0 h0t, if_neg htC, if_pos hle05,
                  if_pos (by simp [fin3_le_one] : (0:Fin 3).val ≤ 1), sepX_eq_01 ht25]
            · subst h
              refine ⟨2, (mem_stageX s 2).mpr (by rw [fX_two]; exact hs25), ?_⟩
              have h2t : (2:Fin 3) ∈ stageX t :=
                (mem_stageX t 2).mpr (by rw [fX_two]; linarith)
              rw [JX_class_eq t 2 h2t, if_neg htC, if_pos hle05,
                  if_neg (by simp [fin3_le_one] : ¬ (2:Fin 3).val ≤ 1)]
        rw [himg,
            Set.encard_insert_of_notMem
              (show ({(0:Fin 3),(1:Fin 3)} : Set (Fin 3)) ∉
                ({({(2:Fin 3)} : Set (Fin 3))} : Set (Set (Fin 3))) by
                simp only [Set.mem_singleton_iff]
                intro h
                have h1 : (0:Fin 3) ∈ ({(0:Fin 3),(1:Fin 3)} : Set (Fin 3)) :=
                  Set.mem_insert _ _
                rw [h] at h1
                simpa using h1),
            Set.encard_singleton,
            indEss_pos 5 s hs5, indMort_neg_t 4.2 0.5 s t htA,
            indMort_pos 2.5 (-0.6) s t hs25 hpos06, add_zero]
      · by_cases hs5 : s ≤ 5
        · have himg : (fun x => {y : Fin 3 | JX t x y}) '' stageX s =
            ({({(0:Fin 3),(1:Fin 3)} : Set (Fin 3))} : Set (Set (Fin 3))) := by
            ext c
            simp only [Set.mem_image, Set.mem_singleton_iff]
            constructor
            · rintro ⟨x, hx, rfl⟩
              have hxt : x ∈ stageX t :=
                (mem_stageX t x).mpr (hts.trans ((mem_stageX s x).mp hx))
              rw [JX_class_eq t x hxt, if_neg htC, if_pos hle05]
              have hxv : x.val ≤ 1 := by
                rcases fin3_cases x with rfl | rfl | hx2
                · exact (by simp [fin3_le_one] : (0:Fin 3).val ≤ 1)
                · exact (by simp [fin3_le_one] : (1:Fin 3).val ≤ 1)
                · exfalso; rw [hx2, mem_stageX, fX_two] at hx; exact hs25 hx
              rw [if_pos hxv, sepX_eq_01 ht25]
            · rintro rfl
              refine ⟨0, (mem_stageX s 0).mpr (by rw [fX_zero]; linarith), ?_⟩
              have h0t : (0:Fin 3) ∈ stageX t :=
                (mem_stageX t 0).mpr (by rw [fX_zero]; linarith)
              rw [JX_class_eq t 0 h0t, if_neg htC, if_pos hle05,
                  if_pos (by simp [fin3_le_one] : (0:Fin 3).val ≤ 1), sepX_eq_01 ht25]
          rw [himg, Set.encard_singleton, indEss_pos 5 s hs5,
              indMort_neg_t 4.2 0.5 s t htA, indMort_neg_s 2.5 (-0.6) s t hs25,
              add_zero, add_zero]
        · have himg : (fun x => {y : Fin 3 | JX t x y}) '' stageX s = (∅ : Set (Set (Fin 3))) := by
            rw [Set.image_eq_empty, stageX_eq_empty hs5]
          have hs42 : ¬ s ≤ 4.2 := fun h => hs5 (h.trans (by linarith))
          rw [himg, Set.encard_empty, indEss_neg 5 s hs5,
              indMort_neg_s 4.2 0.5 s t hs42, indMort_neg_s 2.5 (-0.6) s t hs25,
              add_zero, add_zero]

/-- Class characterization for `JY` (template: `JX_class_eq`; merge pair is `(0,2)`). -/
lemma JY_class_eq (t : ℝ) (x : Fin 3) (hx : x ∈ stageY t) :
    {y : Fin 3 | JY t x y} =
      if t ≤ -1.5 then stageY t
      else if t ≤ 0.3 then
        if x = 0 ∨ x = 2 then {y ∈ stageY t | y = 0 ∨ y = 2} else ({1} : Set (Fin 3))
      else ({x} : Set (Fin 3)) := by
  ext y
  by_cases ht1 : t ≤ -1.5
  · simp only [if_pos ht1, Set.mem_setOf_eq]
    unfold JY
    refine ⟨fun h => h.2.1, fun hy => ⟨hx, hy, Or.inr (Or.inr ht1)⟩⟩
  · by_cases ht2 : t ≤ 0.3
    · by_cases hxv : x = 0 ∨ x = 2
      · simp only [if_neg ht1, if_pos ht2, if_pos hxv, Set.mem_setOf_eq, Set.mem_sep_iff]
        unfold JY
        refine ⟨?_, ?_⟩
        · rintro ⟨_, hy, hd⟩
          refine ⟨hy, ?_⟩
          rcases hd with rfl | ⟨_, ho⟩ | hz
          · exact hxv
          · rcases ho with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
          · exact (ht1 hz).elim
        · rintro ⟨hy, hyv⟩
          refine ⟨hx, hy, ?_⟩
          by_cases hxy : x = y
          · exact Or.inl hxy
          · refine Or.inr (Or.inl ⟨ht2, ?_⟩)
            rcases hxv with rfl | rfl
            · rcases hyv with rfl | h2
              · exact absurd rfl hxy
              · exact Or.inl ⟨rfl, h2⟩
            · rcases hyv with h0 | rfl
              · exact Or.inr ⟨rfl, h0⟩
              · exact absurd rfl hxy
      · have hx1 : x = 1 := by
          rcases fin3_cases x with h0 | h1 | h2
          · exact absurd (Or.inl h0) hxv
          · exact h1
          · exact absurd (Or.inr h2) hxv
        subst hx1
        simp only [if_neg ht1, if_pos ht2, if_neg hxv,
                   Set.mem_setOf_eq, Set.mem_singleton_iff]
        unfold JY
        refine ⟨?_, ?_⟩
        · rintro ⟨_, _, hd⟩
          rcases hd with rfl | ⟨_, ho⟩ | hz
          · rfl
          · rcases ho with ⟨h, _⟩ | ⟨h, _⟩
            · exfalso
              have hv : (1:Fin 3).val = (0:Fin 3).val := Fin.ext_iff.mp h
              rw [show (1:Fin 3).val = 1 from rfl, show (0:Fin 3).val = 0 from rfl] at hv
              omega
            · exfalso
              have hv : (1:Fin 3).val = (2:Fin 3).val := Fin.ext_iff.mp h
              rw [show (1:Fin 3).val = 1 from rfl, show (2:Fin 3).val = 2 from rfl] at hv
              omega
          · exact (ht1 hz).elim
        · rintro rfl; exact ⟨hx, hx, Or.inl rfl⟩
    · simp only [if_neg ht1, if_neg ht2, Set.mem_setOf_eq, Set.mem_singleton_iff]
      unfold JY
      refine ⟨?_, ?_⟩
      · rintro ⟨_, _, hd⟩
        rcases hd with rfl | ⟨hm, _⟩ | hz
        · rfl
        · exact (ht2 hm).elim
        · exact (ht1 hz).elim
      · rintro rfl; exact ⟨hx, hx, Or.inl rfl⟩

/-- `stageY s` as an explicit set, by region of `s`. -/
private lemma stageY_eq_012 {s : ℝ} (h : s ≤ 1.6) :
    stageY s = ({(0:Fin 3),(1:Fin 3),(2:Fin 3)} : Set (Fin 3)) := by
  ext i; fin_cases i <;> simp [mem_stageY, fY_zero, fY_one, fY_two] <;> linarith
private lemma stageY_eq_01 {s : ℝ} (h16 : ¬ s ≤ 1.6) (h32 : s ≤ 3.2) :
    stageY s = ({(0:Fin 3),(1:Fin 3)} : Set (Fin 3)) := by
  ext i; fin_cases i <;> simp [mem_stageY, fY_zero, fY_one, fY_two] <;> linarith
private lemma stageY_eq_0 {s : ℝ} (h32 : ¬ s ≤ 3.2) (h5 : s ≤ 5) :
    stageY s = ({(0:Fin 3)} : Set (Fin 3)) := by
  ext i; fin_cases i <;> simp [mem_stageY, fY_zero, fY_one, fY_two] <;> linarith
private lemma stageY_eq_empty {s : ℝ} (h5 : ¬ s ≤ 5) : stageY s = (∅ : Set (Fin 3)) := by
  ext i; fin_cases i <;> simp [mem_stageY, fY_zero, fY_one, fY_two] <;> linarith

private lemma sepY_eq_02 {t : ℝ} (ht : t ≤ 1.6) :
    {y : Fin 3 | y ∈ stageY t ∧ (y = 0 ∨ y = 2)} = ({(0:Fin 3),(2:Fin 3)} : Set (Fin 3)) := by
  ext y; fin_cases y <;> simp [mem_stageY, fY_zero, fY_one, fY_two] <;> linarith

theorem rankY_eq (s t : ℝ) (hts : t ≤ s) :
    rankFn stageY JY s t = indEss 5 s + indMort 3.2 (-1.5) s t + indMort 1.6 0.3 s t := by
  unfold rankFn
  by_cases htA : 0.3 < t
  · -- Region A': every class is a singleton
    have hle03A : ¬ t ≤ 0.3 := not_le.mpr htA
    have hneg15A : ¬ t ≤ -1.5 := not_le.mpr (by linarith : -1.5 < t)
    have hpos15 : -1.5 < t := by linarith
    have hcls : ∀ x ∈ stageY s, {y : Fin 3 | JY t x y} = ({x} : Set (Fin 3)) := by
      intro x hx
      have hxt : x ∈ stageY t :=
        (mem_stageY t x).mpr (hts.trans ((mem_stageY s x).mp hx))
      rw [JY_class_eq t x hxt, if_neg hneg15A, if_neg hle03A]
    have himg : (fun x => {y : Fin 3 | JY t x y}) '' stageY s =
        (fun x => ({x} : Set (Fin 3))) '' stageY s := by
      ext c
      simp only [Set.mem_image]
      constructor
      · rintro ⟨x, hx, hfx⟩; exact ⟨x, hx, (hcls x hx).symm.trans hfx⟩
      · rintro ⟨x, hx, hfx⟩; exact ⟨x, hx, (hcls x hx).trans hfx⟩
    rw [himg]
    have hcard : ((fun x => ({x} : Set (Fin 3))) '' stageY s).encard = (stageY s).encard :=
      Set.InjOn.encard_image (fun a _ b _ hhe => by simpa using hhe)
    rw [hcard]
    by_cases hs16 : s ≤ 1.6
    · have hs32 : s ≤ 3.2 := hs16.trans (by linarith)
      have hs5 : s ≤ 5 := hs16.trans (by linarith)
      rw [stageY_eq_012 hs16, Set.encard_insert_of_notMem (by decide),
          Set.encard_insert_of_notMem (by decide), Set.encard_singleton,
          indEss_pos 5 s hs5, indMort_pos 3.2 (-1.5) s t hs32 hpos15,
          indMort_pos 1.6 0.3 s t hs16 htA]
    · by_cases hs32 : s ≤ 3.2
      · have hs5 : s ≤ 5 := hs32.trans (by linarith)
        rw [stageY_eq_01 hs16 hs32, Set.encard_insert_of_notMem (by decide),
            Set.encard_singleton, indEss_pos 5 s hs5, indMort_pos 3.2 (-1.5) s t hs32 hpos15,
            indMort_neg_s 1.6 0.3 s t hs16, add_zero]
      · by_cases hs5 : s ≤ 5
        · rw [stageY_eq_0 hs32 hs5, Set.encard_singleton,
              indEss_pos 5 s hs5, indMort_neg_s 3.2 (-1.5) s t hs32,
              indMort_neg_s 1.6 0.3 s t hs16, add_zero, add_zero]
        · rw [stageY_eq_empty hs5, Set.encard_empty,
              indEss_neg 5 s hs5, indMort_neg_s 3.2 (-1.5) s t hs32,
              indMort_neg_s 1.6 0.3 s t hs16, add_zero, add_zero]
  · by_cases htC : t ≤ -1.5
    · -- Region C': all classes merge to stageY t = {0,1,2}
      have ht16 : t ≤ 1.6 := by linarith
      have hpos03 : ¬ 0.3 < t := not_lt.mpr (by linarith : t ≤ 0.3)
      have hpos15 : ¬ -1.5 < t := not_lt.mpr htC
      by_cases hs5 : s ≤ 5
      · have himg : (fun x => {y : Fin 3 | JY t x y}) '' stageY s =
          ({({(0:Fin 3),(1:Fin 3),(2:Fin 3)} : Set (Fin 3))} : Set (Set (Fin 3))) := by
          ext c
          simp only [Set.mem_image, Set.mem_singleton_iff]
          constructor
          · rintro ⟨x, hx, rfl⟩
            have hxt : x ∈ stageY t :=
              (mem_stageY t x).mpr (hts.trans ((mem_stageY s x).mp hx))
            rw [JY_class_eq t x hxt, if_pos htC, stageY_eq_012 ht16]
          · rintro rfl
            refine ⟨0, (mem_stageY s 0).mpr (by rw [fY_zero]; linarith), ?_⟩
            have h0t : (0:Fin 3) ∈ stageY t :=
              (mem_stageY t 0).mpr (by rw [fY_zero]; linarith)
            rw [JY_class_eq t 0 h0t, if_pos htC, stageY_eq_012 ht16]
        rw [himg, Set.encard_singleton, indEss_pos 5 s hs5,
            indMort_neg_t 3.2 (-1.5) s t hpos15, indMort_neg_t 1.6 0.3 s t hpos03,
            add_zero, add_zero]
      · have himg : (fun x => {y : Fin 3 | JY t x y}) '' stageY s = (∅ : Set (Set (Fin 3))) := by
          rw [Set.image_eq_empty, stageY_eq_empty hs5]
        have hs32 : ¬ s ≤ 3.2 := fun h => hs5 (h.trans (by linarith))
        have hs16 : ¬ s ≤ 1.6 := fun h => hs5 (h.trans (by linarith))
        rw [himg, Set.encard_empty, indEss_neg 5 s hs5,
            indMort_neg_s 3.2 (-1.5) s t hs32, indMort_neg_s 1.6 0.3 s t hs16,
            add_zero, add_zero]
    · -- Region B': -1.5 < t ≤ 0.3
      have hle03 : t ≤ 0.3 := not_lt.mp htA
      have ht16 : t ≤ 1.6 := by linarith
      have hpos15 : -1.5 < t := not_le.mp htC
      by_cases hs16 : s ≤ 1.6
      · have hs32 : s ≤ 3.2 := hs16.trans (by linarith)
        have hs5 : s ≤ 5 := hs16.trans (by linarith)
        have himg : (fun x => {y : Fin 3 | JY t x y}) '' stageY s =
            ({({(0:Fin 3),(2:Fin 3)} : Set (Fin 3)), ({(1:Fin 3)} : Set (Fin 3))}
              : Set (Set (Fin 3))) := by
          ext c
          simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
          constructor
          · rintro ⟨x, hx, rfl⟩
            have hxt : x ∈ stageY t :=
              (mem_stageY t x).mpr (hts.trans ((mem_stageY s x).mp hx))
            rw [JY_class_eq t x hxt, if_neg htC, if_pos hle03]
            by_cases hxv : x = 0 ∨ x = 2
            · exact Or.inl (by rw [if_pos hxv]; exact sepY_eq_02 ht16)
            · exact Or.inr (by rw [if_neg hxv])
          · rintro (h | h)
            · subst h
              refine ⟨0, (mem_stageY s 0).mpr (by rw [fY_zero]; linarith), ?_⟩
              have h0t : (0:Fin 3) ∈ stageY t :=
                (mem_stageY t 0).mpr (by rw [fY_zero]; linarith)
              rw [JY_class_eq t 0 h0t, if_neg htC, if_pos hle03,
                  if_pos (Or.inl rfl), sepY_eq_02 ht16]
            · subst h
              refine ⟨1, (mem_stageY s 1).mpr (by rw [fY_one]; linarith), ?_⟩
              have h1t : (1:Fin 3) ∈ stageY t :=
                (mem_stageY t 1).mpr (by rw [fY_one]; linarith)
              rw [JY_class_eq t 1 h1t, if_neg htC, if_pos hle03,
                  if_neg (by simp : ¬ ((1:Fin 3) = 0 ∨ (1:Fin 3) = 2))]
        rw [himg,
            Set.encard_insert_of_notMem
              (show ({(0:Fin 3),(2:Fin 3)} : Set (Fin 3)) ∉
                ({({(1:Fin 3)} : Set (Fin 3))} : Set (Set (Fin 3))) by
                simp only [Set.mem_singleton_iff]
                intro h
                have h1 : (0:Fin 3) ∈ ({(0:Fin 3),(2:Fin 3)} : Set (Fin 3)) :=
                  Set.mem_insert _ _
                rw [h] at h1
                simpa using h1),
            Set.encard_singleton,
            indEss_pos 5 s hs5, indMort_pos 3.2 (-1.5) s t hs32 hpos15,
            indMort_neg_t 1.6 0.3 s t htA, add_zero]
      · by_cases hs32 : s ≤ 3.2
        · have hs5 : s ≤ 5 := hs32.trans (by linarith)
          have himg : (fun x => {y : Fin 3 | JY t x y}) '' stageY s =
              ({({(0:Fin 3),(2:Fin 3)} : Set (Fin 3)), ({(1:Fin 3)} : Set (Fin 3))}
                : Set (Set (Fin 3))) := by
            ext c
            simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
            constructor
            · rintro ⟨x, hx, rfl⟩
              have hxt : x ∈ stageY t :=
                (mem_stageY t x).mpr (hts.trans ((mem_stageY s x).mp hx))
              rw [JY_class_eq t x hxt, if_neg htC, if_pos hle03]
              by_cases hxv : x = 0 ∨ x = 2
              · exact Or.inl (by rw [if_pos hxv]; exact sepY_eq_02 ht16)
              · exact Or.inr (by rw [if_neg hxv])
            · rintro (h | h)
              · subst h
                refine ⟨0, (mem_stageY s 0).mpr (by rw [fY_zero]; linarith), ?_⟩
                have h0t : (0:Fin 3) ∈ stageY t :=
                  (mem_stageY t 0).mpr (by rw [fY_zero]; linarith)
                rw [JY_class_eq t 0 h0t, if_neg htC, if_pos hle03,
                    if_pos (Or.inl rfl), sepY_eq_02 ht16]
              · subst h
                refine ⟨1, (mem_stageY s 1).mpr (by rw [fY_one]; linarith), ?_⟩
                have h1t : (1:Fin 3) ∈ stageY t :=
                  (mem_stageY t 1).mpr (by rw [fY_one]; linarith)
                rw [JY_class_eq t 1 h1t, if_neg htC, if_pos hle03,
                    if_neg (by simp : ¬ ((1:Fin 3) = 0 ∨ (1:Fin 3) = 2))]
          rw [himg,
              Set.encard_insert_of_notMem
                (show ({(0:Fin 3),(2:Fin 3)} : Set (Fin 3)) ∉
                  ({({(1:Fin 3)} : Set (Fin 3))} : Set (Set (Fin 3))) by
                  simp only [Set.mem_singleton_iff]
                  intro h
                  have h1 : (0:Fin 3) ∈ ({(0:Fin 3),(2:Fin 3)} : Set (Fin 3)) :=
                    Set.mem_insert _ _
                  rw [h] at h1
                  simpa using h1),
              Set.encard_singleton,
              indEss_pos 5 s hs5, indMort_pos 3.2 (-1.5) s t hs32 hpos15,
              indMort_neg_t 1.6 0.3 s t htA, add_zero]
        · by_cases hs5 : s ≤ 5
          · have himg : (fun x => {y : Fin 3 | JY t x y}) '' stageY s =
              ({({(0:Fin 3),(2:Fin 3)} : Set (Fin 3))} : Set (Set (Fin 3))) := by
              ext c
              simp only [Set.mem_image, Set.mem_singleton_iff]
              constructor
              · rintro ⟨x, hx, rfl⟩
                have hxt : x ∈ stageY t :=
                  (mem_stageY t x).mpr (hts.trans ((mem_stageY s x).mp hx))
                rw [JY_class_eq t x hxt, if_neg htC, if_pos hle03]
                have hx0 : x = 0 := by
                  rcases fin3_cases x with rfl | h1 | h2
                  · rfl
                  · exfalso; rw [h1, mem_stageY, fY_one] at hx; exact hs32 hx
                  · exfalso; rw [h2, mem_stageY, fY_two] at hx
                    exact hs32 (hx.trans (by linarith))
                rw [hx0, if_pos (Or.inl rfl), sepY_eq_02 ht16]
              · rintro rfl
                refine ⟨0, (mem_stageY s 0).mpr (by rw [fY_zero]; linarith), ?_⟩
                have h0t : (0:Fin 3) ∈ stageY t :=
                  (mem_stageY t 0).mpr (by rw [fY_zero]; linarith)
                rw [JY_class_eq t 0 h0t, if_neg htC, if_pos hle03,
                    if_pos (Or.inl rfl), sepY_eq_02 ht16]
            rw [himg, Set.encard_singleton, indEss_pos 5 s hs5,
                indMort_neg_s 3.2 (-1.5) s t hs32,
                indMort_neg_s 1.6 0.3 s t hs16, add_zero, add_zero]
          · have himg : (fun x => {y : Fin 3 | JY t x y}) '' stageY s = (∅ : Set (Set (Fin 3))) := by
              rw [Set.image_eq_empty, stageY_eq_empty hs5]
            have hs32' : ¬ s ≤ 3.2 := fun h => hs5 (h.trans (by linarith))
            have hs16' : ¬ s ≤ 1.6 := fun h => hs5 (h.trans (by linarith))
            rw [himg, Set.encard_empty, indEss_neg 5 s hs5,
                indMort_neg_s 3.2 (-1.5) s t hs32', indMort_neg_s 1.6 0.3 s t hs16',
                add_zero, add_zero]

/-! ### q-tameness (Step 2) and stage-emptiness (Step 3) -/

theorem hQX : ∀ s t : ℝ, rankFn stageX JX s t ≠ ⊤ := by
  intro s t
  unfold rankFn
  exact (Set.Finite.encard_lt_top (Set.toFinite _)).ne

theorem hQY : ∀ s t : ℝ, rankFn stageY JY s t ≠ ⊤ := by
  intro s t
  unfold rankFn
  exact (Set.Finite.encard_lt_top (Set.toFinite _)).ne

theorem hTameX : ∃ s₀ : ℝ, ∀ s ≥ s₀, stageX s = ∅ := by
  refine ⟨6, fun s hs => stageX_eq_empty (by intro h; linarith)⟩

theorem hTameY : ∃ s₀ : ℝ, ∀ s ≥ s₀, stageY s = ∅ := by
  refine ⟨6, fun s hs => stageY_eq_empty (by intro h; linarith)⟩

/-! ### FiltrationLaw instances -/

theorem hLawX : FiltrationLaw stageX JX := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- antitone
    intros s t hst i hi
    exact hst.trans ((mem_stageX t i).mp hi)
  · -- mem
    intros t x y h
    exact ⟨h.1, h.2.1⟩
  · -- refl
    intros t x hx
    exact ⟨hx, hx, Or.inl rfl⟩
  · -- symm
    intros t x y h
    obtain ⟨hx, hy, hd⟩ := h
    refine ⟨hy, hx, ?_⟩
    rcases hd with rfl | ⟨hm, ho⟩ | hz
    · exact Or.inl rfl
    · refine Or.inr (Or.inl ⟨hm, ?_⟩)
      rcases ho with ⟨rfl, h1⟩ | ⟨h0, rfl⟩
      · exact Or.inr ⟨h1, rfl⟩
      · exact Or.inl ⟨rfl, h0⟩
    · exact Or.inr (Or.inr hz)
  · -- trans
    intros t x y z h1 h2
    obtain ⟨hx, hy, h1d⟩ := h1
    obtain ⟨hy2, hz, h2d⟩ := h2
    refine ⟨hx, hz, ?_⟩
    rcases h1d with hx_eqy | hm1 | hz1
    · subst hx_eqy; exact h2d
    · rcases h2d with hy_eqz | hm2 | hz2
      · subst hy_eqz; exact Or.inr (Or.inl hm1)
      · -- both merge: x,y ∈{0,1}, x≠y ; y,z ∈{0,1}, y≠z  ⇒  x = z
        obtain ho1 := hm1.2
        obtain ho2 := hm2.2
        have exy : x.val ≠ y.val := by
          rcases ho1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
        have eyz : y.val ≠ z.val := by
          rcases ho2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
        have x01 : x.val ≤ 1 := by
          rcases ho1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
        have y01 : y.val ≤ 1 := by
          rcases ho1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
        have z01 : z.val ≤ 1 := by
          rcases ho2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
        have hval : x.val = z.val := by omega
        exact Or.inl (Fin.ext_iff.mpr hval)
      · exact Or.inr (Or.inr hz2)
    · exact Or.inr (Or.inr hz1)
  · -- compat
    intros s t hst x y h
    obtain ⟨hx, hy, hd⟩ := h
    refine ⟨(mem_stageX s x).mpr (hst.trans ((mem_stageX t x).mp hx)),
            (mem_stageX s y).mpr (hst.trans ((mem_stageX t y).mp hy)), ?_⟩
    rcases hd with rfl | ⟨hm, ho⟩ | hz
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨hst.trans hm, ho⟩)
    · exact Or.inr (Or.inr (hst.trans hz))

theorem hLawY : FiltrationLaw stageY JY := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intros s t hst i hi
    exact hst.trans ((mem_stageY t i).mp hi)
  · intros t x y h
    exact ⟨h.1, h.2.1⟩
  · intros t x hx
    exact ⟨hx, hx, Or.inl rfl⟩
  · intros t x y h
    obtain ⟨hx, hy, hd⟩ := h
    refine ⟨hy, hx, ?_⟩
    rcases hd with rfl | ⟨hm, ho⟩ | hz
    · exact Or.inl rfl
    · refine Or.inr (Or.inl ⟨hm, ?_⟩)
      rcases ho with ⟨rfl, h2⟩ | ⟨h0, rfl⟩
      · exact Or.inr ⟨h2, rfl⟩
      · exact Or.inl ⟨rfl, h0⟩
    · exact Or.inr (Or.inr hz)
  · intros t x y z h1 h2
    obtain ⟨hx, hy, h1d⟩ := h1
    obtain ⟨hy2, hz, h2d⟩ := h2
    refine ⟨hx, hz, ?_⟩
    rcases h1d with hx_eqy | hm1 | hz1
    · subst hx_eqy; exact h2d
    · rcases h2d with hy_eqz | hm2 | hz2
      · subst hy_eqz; exact Or.inr (Or.inl hm1)
      · -- merge: x,y ∈{0,2}, x≠y ; y,z ∈{0,2}, y≠z ⇒ x = z
        obtain ho1 := hm1.2
        obtain ho2 := hm2.2
        have exy : x.val ≠ y.val := by
          rcases ho1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
        have eyz : y.val ≠ z.val := by
          rcases ho2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
        have x02 : x.val = 0 ∨ x.val = 2 := by
          rcases ho1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
        have y02 : y.val = 0 ∨ y.val = 2 := by
          rcases ho1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
        have z02 : z.val = 0 ∨ z.val = 2 := by
          rcases ho2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
        have hval : x.val = z.val := by omega
        exact Or.inl (Fin.ext_iff.mpr hval)
      · exact Or.inr (Or.inr hz2)
    · exact Or.inr (Or.inr hz1)
  · intros s t hst x y h
    obtain ⟨hx, hy, hd⟩ := h
    refine ⟨(mem_stageY s x).mpr (hst.trans ((mem_stageY t x).mp hx)),
            (mem_stageY s y).mpr (hst.trans ((mem_stageY t y).mp hy)), ?_⟩
    rcases hd with rfl | ⟨hm, ho⟩ | hz
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨hst.trans hm, ho⟩)
    · exact Or.inr (Or.inr (hst.trans hz))

/-! ### Banked pure lemmas (ported from the stability_tame sibling) -/

private theorem trunc_above (r : ℝ → ℝ → ℕ∞) (a s t : ℝ) (h1 : a ≤ s) (h2 : a ≤ t) :
    truncRank r a s t = r s t := by simp [truncRank, h1, h2]

private theorem trunc_below (r : ℝ → ℝ → ℕ∞) (a s t : ℝ) (h : ¬(a ≤ s ∧ a ≤ t)) :
    truncRank r a s t = 0 := by simp [truncRank, h]

private theorem truncRank_zero_of_lt (r : ℝ → ℝ → ℕ∞) (α s t : ℝ) (ht : t < α) :
    truncRank r α s t = 0 :=
  trunc_below r α s t (fun h => not_le.mpr ht h.2)

private theorem truncRank_zero_of_lt' (r : ℝ → ℝ → ℕ∞) (α s t : ℝ) (hs : s < α) :
    truncRank r α s t = 0 :=
  trunc_below r α s t (fun h => not_le.mpr hs h.1)

private theorem mult_coe_coe (r : ℝ → ℝ → ℕ∞) (b d : ℝ) (hbd : d < b) :
    mult r (((b : ℝ) : EReal), ((d : ℝ) : EReal)) =
      ⨅ (η : ℝ) (_ : η ∈ Set.Ioo (0 : ℝ) ((b - d) / 2)),
        ((r (b - η) (d + η) - r (b + η) (d + η)) -
          (r (b - η) (d - η) - r (b + η) (d - η))) := by
  unfold mult
  rw [if_pos ⟨EReal.coe_ne_bot b, EReal.coe_ne_top b⟩,
      if_neg (EReal.coe_ne_bot d), if_pos (EReal.coe_lt_coe_iff.mpr hbd)]
  simp only [EReal.toReal_coe]

private theorem mult_coe_bot (r : ℝ → ℝ → ℕ∞) (b : ℝ) :
    mult r (((b : ℝ) : EReal), (⊥ : EReal)) =
      ⨅ (η : ℝ) (_ : 0 < η), ⨅ (t : ℝ) (_ : t ≤ b - η),
        (r (b - η) t - r (b + η) t) := by
  unfold mult
  rw [if_pos ⟨EReal.coe_ne_bot b, EReal.coe_ne_top b⟩, if_pos rfl]
  simp only [EReal.toReal_coe]

private theorem mult_trunc_bot_zero (r : ℝ → ℝ → ℕ∞) (α b : ℝ) :
    mult (truncRank r α) (((b : ℝ) : EReal), (⊥ : EReal)) = 0 := by
  rw [mult_coe_bot]
  refine le_antisymm ?_ (le_iInf fun _ => le_iInf fun _ => le_iInf fun _ => le_iInf fun _ =>
    (zero_le : (0 : ℕ∞) ≤ _))
  have ht0 : min (b - 1) (α - 1) < α := by linarith [min_le_right (b - 1) (α - 1),
                                                        min_le_left (b - 1) (α - 1)]
  have hval : truncRank r α (b - 1) (min (b - 1) (α - 1)) -
      truncRank r α (b + 1) (min (b - 1) (α - 1)) ≤ 0 := by
    rw [truncRank_zero_of_lt r α _ _ ht0, truncRank_zero_of_lt r α _ _ ht0, tsub_self]
  exact iInf_le_of_le 1 (iInf_le_of_le (show (0 : ℝ) < 1 by norm_num)
    (iInf_le_of_le (min (b - 1) (α - 1)) (iInf_le_of_le (min_le_left _ _) hval)))

private theorem mult_trunc_lt_zero (r : ℝ → ℝ → ℕ∞) (α b d : ℝ) (hbd : d < b) (hd : d < α) :
    mult (truncRank r α) (((b : ℝ) : EReal), ((d : ℝ) : EReal)) = 0 := by
  rw [mult_coe_coe _ b d hbd]
  refine le_antisymm ?_ (le_iInf fun _ => le_iInf fun _ => (zero_le : (0 : ℕ∞) ≤ _))
  set η := (min ((b - d) / 2) ((α - d) / 2)) / 2 with hη
  have hbd0 : 0 < (b - d) / 2 := by linarith
  have had0 : 0 < (α - d) / 2 := by linarith
  have hpos : 0 < η := by
    have : 0 < min ((b - d) / 2) ((α - d) / 2) := lt_min hbd0 had0
    linarith
  have hwin : η ∈ Set.Ioo (0 : ℝ) ((b - d) / 2) := by
    constructor
    · exact hpos
    · have h1 : min ((b - d) / 2) ((α - d) / 2) ≤ (b - d) / 2 := min_le_left _ _
      linarith
  have hdη : d + η < α := by
    have h1 : min ((b - d) / 2) ((α - d) / 2) ≤ (α - d) / 2 := min_le_right _ _
    linarith
  have hdmη : d - η < α := by linarith
  have hval : (truncRank r α (b - η) (d + η) - truncRank r α (b + η) (d + η)) -
      (truncRank r α (b - η) (d - η) - truncRank r α (b + η) (d - η)) ≤ 0 := by
    rw [truncRank_zero_of_lt r α _ _ hdη, truncRank_zero_of_lt r α _ _ hdη,
        truncRank_zero_of_lt r α _ _ hdmη, truncRank_zero_of_lt r α _ _ hdmη, tsub_self]
  exact iInf_le_of_le η (iInf_le_of_le hwin hval)

private theorem isDiagramLike_mult (r : ℝ → ℝ → ℕ∞) : IsDiagramLike (mult r) := by
  intro p hp
  by_contra hne
  have hle : p.1 ≤ p.2 := not_lt.mp hne
  have h0 : mult r p = 0 := by
    unfold mult
    by_cases h1 : p.1 ≠ ⊥ ∧ p.1 ≠ ⊤
    · rw [if_pos h1]
      by_cases h2 : p.2 = ⊥
      · have hle' : p.1 ≤ ⊥ := h2 ▸ hle
        exact absurd (le_antisymm hle' bot_le) h1.1
      · rw [if_neg h2]
        by_cases h3 : p.2 < p.1
        · exact absurd h3 (not_lt.mpr hle)
        · rw [if_neg h3]
    · rw [if_neg h1]
  exact hp h0

/-! ### Step 4: plain diagram multiplicities -/

theorem multX_42 :
    mult (rankFn stageX JX) (((4.2:ℝ):EReal), ((0.5:ℝ):EReal)) = 1 := by
  rw [mult_coe_coe _ 4.2 0.5 (by norm_num : (0.5:ℝ) < 4.2)]
  refine le_antisymm ?_ (le_iInf fun ε => le_iInf fun hε => ?_)
  · refine iInf_le_of_le 0.4 (iInf_le_of_le ⟨by norm_num, by norm_num⟩ ?_)
    have hA : rankFn stageX JX (4.2 - 0.4) (0.5 + 0.4) = 2 := by
      rw [rankX_eq _ _ (by norm_num),
          indEss_pos 5 (4.2 - 0.4) (by norm_num),
          indMort_pos 4.2 0.5 (4.2 - 0.4) (0.5 + 0.4) (by norm_num) (by norm_num),
          indMort_neg_s 2.5 (-0.6) (4.2 - 0.4) (0.5 + 0.4) (by norm_num)]
      decide
    have hB : rankFn stageX JX (4.2 + 0.4) (0.5 + 0.4) = 1 := by
      rw [rankX_eq _ _ (by norm_num),
          indEss_pos 5 (4.2 + 0.4) (by norm_num),
          indMort_neg_s 4.2 0.5 (4.2 + 0.4) (0.5 + 0.4) (by norm_num),
          indMort_neg_s 2.5 (-0.6) (4.2 + 0.4) (0.5 + 0.4) (by norm_num)]
      decide
    have hC : rankFn stageX JX (4.2 - 0.4) (0.5 - 0.4) = 1 := by
      rw [rankX_eq _ _ (by norm_num),
          indEss_pos 5 (4.2 - 0.4) (by norm_num),
          indMort_neg_t 4.2 0.5 (4.2 - 0.4) (0.5 - 0.4) (by norm_num),
          indMort_neg_s 2.5 (-0.6) (4.2 - 0.4) (0.5 - 0.4) (by norm_num)]
      decide
    have hD : rankFn stageX JX (4.2 + 0.4) (0.5 - 0.4) = 1 := by
      rw [rankX_eq _ _ (by norm_num),
          indEss_pos 5 (4.2 + 0.4) (by norm_num),
          indMort_neg_s 4.2 0.5 (4.2 + 0.4) (0.5 - 0.4) (by norm_num),
          indMort_neg_s 2.5 (-0.6) (4.2 + 0.4) (0.5 - 0.4) (by norm_num)]
      decide
    rw [hA, hB, hC, hD]
    decide
  · obtain ⟨hε0, hεw⟩ := Set.mem_Ioo.mp hε
    by_cases h80 : ε ≤ 0.8
    · have hA : rankFn stageX JX (4.2 - ε) (0.5 + ε) = 2 := by
        rw [rankX_eq _ _ (by linarith),
            indEss_pos 5 (4.2 - ε) (by linarith),
            indMort_pos 4.2 0.5 (4.2 - ε) (0.5 + ε) (by linarith) (by linarith),
            indMort_neg_s 2.5 (-0.6) (4.2 - ε) (0.5 + ε) (by linarith)]
        decide
      have hB : rankFn stageX JX (4.2 + ε) (0.5 + ε) = 1 := by
        rw [rankX_eq _ _ (by linarith),
            indEss_pos 5 (4.2 + ε) (by linarith),
            indMort_neg_s 4.2 0.5 (4.2 + ε) (0.5 + ε) (by linarith),
            indMort_neg_s 2.5 (-0.6) (4.2 + ε) (0.5 + ε) (by linarith)]
        decide
      have hC : rankFn stageX JX (4.2 - ε) (0.5 - ε) = 1 := by
        rw [rankX_eq _ _ (by linarith),
            indEss_pos 5 (4.2 - ε) (by linarith),
            indMort_neg_t 4.2 0.5 (4.2 - ε) (0.5 - ε) (by linarith),
            indMort_neg_s 2.5 (-0.6) (4.2 - ε) (0.5 - ε) (by linarith)]
        decide
      have hD : rankFn stageX JX (4.2 + ε) (0.5 - ε) = 1 := by
        rw [rankX_eq _ _ (by linarith),
            indEss_pos 5 (4.2 + ε) (by linarith),
            indMort_neg_s 4.2 0.5 (4.2 + ε) (0.5 - ε) (by linarith),
            indMort_neg_s 2.5 (-0.6) (4.2 + ε) (0.5 - ε) (by linarith)]
        decide
      rw [hA, hB, hC, hD]
      decide
    · by_cases h17 : ε < 1.7
      · have hA : rankFn stageX JX (4.2 - ε) (0.5 + ε) = 2 := by
          rw [rankX_eq _ _ (by linarith),
              indEss_pos 5 (4.2 - ε) (by linarith),
              indMort_pos 4.2 0.5 (4.2 - ε) (0.5 + ε) (by linarith) (by linarith),
              indMort_neg_s 2.5 (-0.6) (4.2 - ε) (0.5 + ε) (by linarith)]
          decide
        have hB : rankFn stageX JX (4.2 + ε) (0.5 + ε) = 0 := by
          rw [rankX_eq _ _ (by linarith),
              indEss_neg 5 (4.2 + ε) (by linarith),
              indMort_neg_s 4.2 0.5 (4.2 + ε) (0.5 + ε) (by linarith),
              indMort_neg_s 2.5 (-0.6) (4.2 + ε) (0.5 + ε) (by linarith)]
          decide
        have hC : rankFn stageX JX (4.2 - ε) (0.5 - ε) = 1 := by
          rw [rankX_eq _ _ (by linarith),
              indEss_pos 5 (4.2 - ε) (by linarith),
              indMort_neg_t 4.2 0.5 (4.2 - ε) (0.5 - ε) (by linarith),
              indMort_neg_s 2.5 (-0.6) (4.2 - ε) (0.5 - ε) (by linarith)]
          decide
        have hD : rankFn stageX JX (4.2 + ε) (0.5 - ε) = 0 := by
          rw [rankX_eq _ _ (by linarith),
              indEss_neg 5 (4.2 + ε) (by linarith),
              indMort_neg_s 4.2 0.5 (4.2 + ε) (0.5 - ε) (by linarith),
              indMort_neg_s 2.5 (-0.6) (4.2 + ε) (0.5 - ε) (by linarith)]
          decide
        rw [hA, hB, hC, hD]
        decide
      · have hA : rankFn stageX JX (4.2 - ε) (0.5 + ε) = 3 := by
          rw [rankX_eq _ _ (by linarith),
              indEss_pos 5 (4.2 - ε) (by linarith),
              indMort_pos 4.2 0.5 (4.2 - ε) (0.5 + ε) (by linarith) (by linarith),
              indMort_pos 2.5 (-0.6) (4.2 - ε) (0.5 + ε) (by linarith) (by linarith)]
          decide
        have hB : rankFn stageX JX (4.2 + ε) (0.5 + ε) = 0 := by
          rw [rankX_eq _ _ (by linarith),
              indEss_neg 5 (4.2 + ε) (by linarith),
              indMort_neg_s 4.2 0.5 (4.2 + ε) (0.5 + ε) (by linarith),
              indMort_neg_s 2.5 (-0.6) (4.2 + ε) (0.5 + ε) (by linarith)]
          decide
        have hC : rankFn stageX JX (4.2 - ε) (0.5 - ε) = 1 := by
          rw [rankX_eq _ _ (by linarith),
              indEss_pos 5 (4.2 - ε) (by linarith),
              indMort_neg_t 4.2 0.5 (4.2 - ε) (0.5 - ε) (by linarith),
              indMort_neg_t 2.5 (-0.6) (4.2 - ε) (0.5 - ε) (by linarith)]
          decide
        have hD : rankFn stageX JX (4.2 + ε) (0.5 - ε) = 0 := by
          rw [rankX_eq _ _ (by linarith),
              indEss_neg 5 (4.2 + ε) (by linarith),
              indMort_neg_s 4.2 0.5 (4.2 + ε) (0.5 - ε) (by linarith),
              indMort_neg_s 2.5 (-0.6) (4.2 + ε) (0.5 - ε) (by linarith)]
          decide
        rw [hA, hB, hC, hD]
        decide

theorem multX_25 :
    mult (rankFn stageX JX) (((2.5:ℝ):EReal), ((-0.6:ℝ):EReal)) = 1 := by
  rw [mult_coe_coe _ 2.5 (-0.6) (by norm_num : (-0.6:ℝ) < 2.5)]
  refine le_antisymm ?_ (le_iInf fun ε => le_iInf fun hε => ?_)
  · refine iInf_le_of_le 0.5 (iInf_le_of_le ⟨by norm_num, by norm_num⟩ ?_)
    have hA : rankFn stageX JX (2.5 - 0.5) ((-0.6) + 0.5) = 2 := by
      rw [rankX_eq _ _ (by norm_num),
          indEss_pos 5 (2.5 - 0.5) (by norm_num),
          indMort_neg_t 4.2 0.5 (2.5 - 0.5) ((-0.6) + 0.5) (by norm_num),
          indMort_pos 2.5 (-0.6) (2.5 - 0.5) ((-0.6) + 0.5) (by norm_num) (by norm_num)]
      decide
    have hB : rankFn stageX JX (2.5 + 0.5) ((-0.6) + 0.5) = 1 := by
      rw [rankX_eq _ _ (by norm_num),
          indEss_pos 5 (2.5 + 0.5) (by norm_num),
          indMort_neg_t 4.2 0.5 (2.5 + 0.5) ((-0.6) + 0.5) (by norm_num),
          indMort_neg_s 2.5 (-0.6) (2.5 + 0.5) ((-0.6) + 0.5) (by norm_num)]
      decide
    have hC : rankFn stageX JX (2.5 - 0.5) ((-0.6) - 0.5) = 1 := by
      rw [rankX_eq _ _ (by norm_num),
          indEss_pos 5 (2.5 - 0.5) (by norm_num),
          indMort_neg_t 4.2 0.5 (2.5 - 0.5) ((-0.6) - 0.5) (by norm_num),
          indMort_neg_t 2.5 (-0.6) (2.5 - 0.5) ((-0.6) - 0.5) (by norm_num)]
      decide
    have hD : rankFn stageX JX (2.5 + 0.5) ((-0.6) - 0.5) = 1 := by
      rw [rankX_eq _ _ (by norm_num),
          indEss_pos 5 (2.5 + 0.5) (by norm_num),
          indMort_neg_t 4.2 0.5 (2.5 + 0.5) ((-0.6) - 0.5) (by norm_num),
          indMort_neg_s 2.5 (-0.6) (2.5 + 0.5) ((-0.6) - 0.5) (by norm_num)]
      decide
    rw [hA, hB, hC, hD]
    decide
  · obtain ⟨hε0, hεw⟩ := Set.mem_Ioo.mp hε
    by_cases h11 : ε ≤ 1.1
    · have hA : rankFn stageX JX (2.5 - ε) ((-0.6) + ε) = 2 := by
        rw [rankX_eq _ _ (by linarith),
            indEss_pos 5 (2.5 - ε) (by linarith),
            indMort_neg_t 4.2 0.5 (2.5 - ε) ((-0.6) + ε) (by linarith),
            indMort_pos 2.5 (-0.6) (2.5 - ε) ((-0.6) + ε) (by linarith) (by linarith)]
        decide
      have hB : rankFn stageX JX (2.5 + ε) ((-0.6) + ε) = 1 := by
        rw [rankX_eq _ _ (by linarith),
            indEss_pos 5 (2.5 + ε) (by linarith),
            indMort_neg_t 4.2 0.5 (2.5 + ε) ((-0.6) + ε) (by linarith),
            indMort_neg_s 2.5 (-0.6) (2.5 + ε) ((-0.6) + ε) (by linarith)]
        decide
      have hC : rankFn stageX JX (2.5 - ε) ((-0.6) - ε) = 1 := by
        rw [rankX_eq _ _ (by linarith),
            indEss_pos 5 (2.5 - ε) (by linarith),
            indMort_neg_t 4.2 0.5 (2.5 - ε) ((-0.6) - ε) (by linarith),
            indMort_neg_t 2.5 (-0.6) (2.5 - ε) ((-0.6) - ε) (by linarith)]
        decide
      have hD : rankFn stageX JX (2.5 + ε) ((-0.6) - ε) = 1 := by
        rw [rankX_eq _ _ (by linarith),
            indEss_pos 5 (2.5 + ε) (by linarith),
            indMort_neg_t 4.2 0.5 (2.5 + ε) ((-0.6) - ε) (by linarith),
            indMort_neg_s 2.5 (-0.6) (2.5 + ε) ((-0.6) - ε) (by linarith)]
        decide
      rw [hA, hB, hC, hD]
      decide
    · have hA : rankFn stageX JX (2.5 - ε) ((-0.6) + ε) = 3 := by
        rw [rankX_eq _ _ (by linarith),
            indEss_pos 5 (2.5 - ε) (by linarith),
            indMort_pos 4.2 0.5 (2.5 - ε) ((-0.6) + ε) (by linarith) (by linarith),
            indMort_pos 2.5 (-0.6) (2.5 - ε) ((-0.6) + ε) (by linarith) (by linarith)]
        decide
      have hB : rankFn stageX JX (2.5 + ε) ((-0.6) + ε) = 2 := by
        rw [rankX_eq _ _ (by linarith),
            indEss_pos 5 (2.5 + ε) (by linarith),
            indMort_pos 4.2 0.5 (2.5 + ε) ((-0.6) + ε) (by linarith) (by linarith),
            indMort_neg_s 2.5 (-0.6) (2.5 + ε) ((-0.6) + ε) (by linarith)]
        decide
      have hC : rankFn stageX JX (2.5 - ε) ((-0.6) - ε) = 1 := by
        rw [rankX_eq _ _ (by linarith),
            indEss_pos 5 (2.5 - ε) (by linarith),
            indMort_neg_t 4.2 0.5 (2.5 - ε) ((-0.6) - ε) (by linarith),
            indMort_neg_t 2.5 (-0.6) (2.5 - ε) ((-0.6) - ε) (by linarith)]
        decide
      have hD : rankFn stageX JX (2.5 + ε) ((-0.6) - ε) = 1 := by
        rw [rankX_eq _ _ (by linarith),
            indEss_pos 5 (2.5 + ε) (by linarith),
            indMort_neg_t 4.2 0.5 (2.5 + ε) ((-0.6) - ε) (by linarith),
            indMort_neg_s 2.5 (-0.6) (2.5 + ε) ((-0.6) - ε) (by linarith)]
        decide
      rw [hA, hB, hC, hD]
      decide

theorem multX_5 :
    mult (rankFn stageX JX) (((5:ℝ):EReal), (⊥:EReal)) = 1 := by
  rw [mult_coe_bot _ 5]
  refine le_antisymm ?_ (le_iInf fun ε => le_iInf fun hε => le_iInf fun t => le_iInf fun ht => ?_)
  · refine iInf_le_of_le 1 (iInf_le_of_le (show (0:ℝ) < 1 by norm_num) ?_)
    refine iInf_le_of_le 0 (iInf_le_of_le (show (0:ℝ) ≤ 5 - 1 by norm_num) ?_)
    have hA : rankFn stageX JX (5 - 1) 0 = 1 := by
      rw [rankX_eq _ _ (by norm_num),
          indEss_pos 5 (5 - 1) (by norm_num),
          indMort_neg_t 4.2 0.5 (5 - 1) 0 (by norm_num),
          indMort_neg_s 2.5 (-0.6) (5 - 1) 0 (by norm_num)]
      decide
    have hB : rankFn stageX JX (5 + 1) 0 = 0 := by
      rw [rankX_eq _ _ (by norm_num),
          indEss_neg 5 (5 + 1) (by norm_num),
          indMort_neg_s 4.2 0.5 (5 + 1) 0 (by norm_num),
          indMort_neg_s 2.5 (-0.6) (5 + 1) 0 (by norm_num)]
      decide
    rw [hA, hB]
    decide
  · have hA : rankFn stageX JX (5 - ε) t
          = 1 + (if (5 - ε) ≤ 4.2 ∧ 0.5 < t then (1:ℕ∞) else 0)
            + (if (5 - ε) ≤ 2.5 ∧ (-0.6) < t then (1:ℕ∞) else 0) := by
      rw [rankX_eq _ _ ht, indEss_pos 5 (5 - ε) (by linarith)]
      rfl
    have hB : rankFn stageX JX (5 + ε) t = 0 := by
      rw [rankX_eq _ _ (by linarith),
          indEss_neg 5 (5 + ε) (by linarith),
          indMort_neg_s 4.2 0.5 (5 + ε) t (by linarith),
          indMort_neg_s 2.5 (-0.6) (5 + ε) t (by linarith)]
      decide
    rw [hA, hB]
    split_ifs <;> decide

theorem multY_32 :
    mult (rankFn stageY JY) (((3.2:ℝ):EReal), ((-1.5:ℝ):EReal)) = 1 := by
  rw [mult_coe_coe _ 3.2 (-1.5) (by norm_num : (-1.5:ℝ) < 3.2)]
  refine le_antisymm ?_ (le_iInf fun ε => le_iInf fun hε => ?_)
  · refine iInf_le_of_le 1 (iInf_le_of_le ⟨by norm_num, by norm_num⟩ ?_)
    have hA : rankFn stageY JY (3.2 - 1) ((-1.5) + 1) = 2 := by
      rw [rankY_eq _ _ (by norm_num),
          indEss_pos 5 (3.2 - 1) (by norm_num),
          indMort_pos 3.2 (-1.5) (3.2 - 1) ((-1.5) + 1) (by norm_num) (by norm_num),
          indMort_neg_s 1.6 0.3 (3.2 - 1) ((-1.5) + 1) (by norm_num)]
      decide
    have hB : rankFn stageY JY (3.2 + 1) ((-1.5) + 1) = 1 := by
      rw [rankY_eq _ _ (by norm_num),
          indEss_pos 5 (3.2 + 1) (by norm_num),
          indMort_neg_s 3.2 (-1.5) (3.2 + 1) ((-1.5) + 1) (by norm_num),
          indMort_neg_s 1.6 0.3 (3.2 + 1) ((-1.5) + 1) (by norm_num)]
      decide
    have hC : rankFn stageY JY (3.2 - 1) ((-1.5) - 1) = 1 := by
      rw [rankY_eq _ _ (by norm_num),
          indEss_pos 5 (3.2 - 1) (by norm_num),
          indMort_neg_t 3.2 (-1.5) (3.2 - 1) ((-1.5) - 1) (by norm_num),
          indMort_neg_s 1.6 0.3 (3.2 - 1) ((-1.5) - 1) (by norm_num)]
      decide
    have hD : rankFn stageY JY (3.2 + 1) ((-1.5) - 1) = 1 := by
      rw [rankY_eq _ _ (by norm_num),
          indEss_pos 5 (3.2 + 1) (by norm_num),
          indMort_neg_s 3.2 (-1.5) (3.2 + 1) ((-1.5) - 1) (by norm_num),
          indMort_neg_s 1.6 0.3 (3.2 + 1) ((-1.5) - 1) (by norm_num)]
      decide
    rw [hA, hB, hC, hD]
    decide
  · obtain ⟨hε0, hεw⟩ := Set.mem_Ioo.mp hε
    by_cases h18 : ε ≤ 1.8
    · have hA : rankFn stageY JY (3.2 - ε) ((-1.5) + ε) = 2 := by
        rw [rankY_eq _ _ (by linarith),
            indEss_pos 5 (3.2 - ε) (by linarith),
            indMort_pos 3.2 (-1.5) (3.2 - ε) ((-1.5) + ε) (by linarith) (by linarith),
            indMort_neg 1.6 0.3 (3.2 - ε) ((-1.5) + ε) (by rintro ⟨h1, h2⟩; linarith)]
        decide
      have hB : rankFn stageY JY (3.2 + ε) ((-1.5) + ε) = 1 := by
        rw [rankY_eq _ _ (by linarith),
            indEss_pos 5 (3.2 + ε) (by linarith),
            indMort_neg_s 3.2 (-1.5) (3.2 + ε) ((-1.5) + ε) (by linarith),
            indMort_neg_s 1.6 0.3 (3.2 + ε) ((-1.5) + ε) (by linarith)]
        decide
      have hC : rankFn stageY JY (3.2 - ε) ((-1.5) - ε) = 1 := by
        rw [rankY_eq _ _ (by linarith),
            indEss_pos 5 (3.2 - ε) (by linarith),
            indMort_neg_t 3.2 (-1.5) (3.2 - ε) ((-1.5) - ε) (by linarith),
            indMort_neg 1.6 0.3 (3.2 - ε) ((-1.5) - ε) (by rintro ⟨h1, h2⟩; linarith)]
        decide
      have hD : rankFn stageY JY (3.2 + ε) ((-1.5) - ε) = 1 := by
        rw [rankY_eq _ _ (by linarith),
            indEss_pos 5 (3.2 + ε) (by linarith),
            indMort_neg_s 3.2 (-1.5) (3.2 + ε) ((-1.5) - ε) (by linarith),
            indMort_neg 1.6 0.3 (3.2 + ε) ((-1.5) - ε) (by rintro ⟨h1, h2⟩; linarith)]
        decide
      rw [hA, hB, hC, hD]
      decide
    · have hA : rankFn stageY JY (3.2 - ε) ((-1.5) + ε) = 3 := by
        rw [rankY_eq _ _ (by linarith),
            indEss_pos 5 (3.2 - ε) (by linarith),
            indMort_pos 3.2 (-1.5) (3.2 - ε) ((-1.5) + ε) (by linarith) (by linarith),
            indMort_pos 1.6 0.3 (3.2 - ε) ((-1.5) + ε) (by linarith) (by linarith)]
        decide
      have hB : rankFn stageY JY (3.2 + ε) ((-1.5) + ε) = 0 := by
        rw [rankY_eq _ _ (by linarith),
            indEss_neg 5 (3.2 + ε) (by linarith),
            indMort_neg_s 3.2 (-1.5) (3.2 + ε) ((-1.5) + ε) (by linarith),
            indMort_neg_s 1.6 0.3 (3.2 + ε) ((-1.5) + ε) (by linarith)]
        decide
      have hC : rankFn stageY JY (3.2 - ε) ((-1.5) - ε) = 1 := by
        rw [rankY_eq _ _ (by linarith),
            indEss_pos 5 (3.2 - ε) (by linarith),
            indMort_neg_t 3.2 (-1.5) (3.2 - ε) ((-1.5) - ε) (by linarith),
            indMort_neg 1.6 0.3 (3.2 - ε) ((-1.5) - ε) (by rintro ⟨h1, h2⟩; linarith)]
        decide
      have hD : rankFn stageY JY (3.2 + ε) ((-1.5) - ε) = 0 := by
        rw [rankY_eq _ _ (by linarith),
            indEss_neg 5 (3.2 + ε) (by linarith),
            indMort_neg_s 3.2 (-1.5) (3.2 + ε) ((-1.5) - ε) (by linarith),
            indMort_neg_s 1.6 0.3 (3.2 + ε) ((-1.5) - ε) (by linarith)]
        decide
      rw [hA, hB, hC, hD]
      decide

theorem multY_16 :
    mult (rankFn stageY JY) (((1.6:ℝ):EReal), ((0.3:ℝ):EReal)) = 1 := by
  rw [mult_coe_coe _ 1.6 0.3 (by norm_num : (0.3:ℝ) < 1.6)]
  refine le_antisymm ?_ (le_iInf fun ε => le_iInf fun hε => ?_)
  · refine iInf_le_of_le 0.3 (iInf_le_of_le ⟨by norm_num, by norm_num⟩ ?_)
    have hA : rankFn stageY JY (1.6 - 0.3) (0.3 + 0.3) = 3 := by
      rw [rankY_eq _ _ (by norm_num),
          indEss_pos 5 (1.6 - 0.3) (by norm_num),
          indMort_pos 3.2 (-1.5) (1.6 - 0.3) (0.3 + 0.3) (by norm_num) (by norm_num),
          indMort_pos 1.6 0.3 (1.6 - 0.3) (0.3 + 0.3) (by norm_num) (by norm_num)]
      decide
    have hB : rankFn stageY JY (1.6 + 0.3) (0.3 + 0.3) = 2 := by
      rw [rankY_eq _ _ (by norm_num),
          indEss_pos 5 (1.6 + 0.3) (by norm_num),
          indMort_pos 3.2 (-1.5) (1.6 + 0.3) (0.3 + 0.3) (by norm_num) (by norm_num),
          indMort_neg_s 1.6 0.3 (1.6 + 0.3) (0.3 + 0.3) (by norm_num)]
      decide
    have hC : rankFn stageY JY (1.6 - 0.3) (0.3 - 0.3) = 2 := by
      rw [rankY_eq _ _ (by norm_num),
          indEss_pos 5 (1.6 - 0.3) (by norm_num),
          indMort_pos 3.2 (-1.5) (1.6 - 0.3) (0.3 - 0.3) (by norm_num) (by norm_num),
          indMort_neg_t 1.6 0.3 (1.6 - 0.3) (0.3 - 0.3) (by norm_num)]
      decide
    have hD : rankFn stageY JY (1.6 + 0.3) (0.3 - 0.3) = 2 := by
      rw [rankY_eq _ _ (by norm_num),
          indEss_pos 5 (1.6 + 0.3) (by norm_num),
          indMort_pos 3.2 (-1.5) (1.6 + 0.3) (0.3 - 0.3) (by norm_num) (by norm_num),
          indMort_neg_s 1.6 0.3 (1.6 + 0.3) (0.3 - 0.3) (by norm_num)]
      decide
    rw [hA, hB, hC, hD]
    decide
  · obtain ⟨hε0, hεw⟩ := Set.mem_Ioo.mp hε
    have hA : rankFn stageY JY (1.6 - ε) (0.3 + ε) = 3 := by
      rw [rankY_eq _ _ (by linarith),
          indEss_pos 5 (1.6 - ε) (by linarith),
          indMort_pos 3.2 (-1.5) (1.6 - ε) (0.3 + ε) (by linarith) (by linarith),
          indMort_pos 1.6 0.3 (1.6 - ε) (0.3 + ε) (by linarith) (by linarith)]
      decide
    have hB : rankFn stageY JY (1.6 + ε) (0.3 + ε) = 2 := by
      rw [rankY_eq _ _ (by linarith),
          indEss_pos 5 (1.6 + ε) (by linarith),
          indMort_pos 3.2 (-1.5) (1.6 + ε) (0.3 + ε) (by linarith) (by linarith),
          indMort_neg_s 1.6 0.3 (1.6 + ε) (0.3 + ε) (by linarith)]
      decide
    have hC : rankFn stageY JY (1.6 - ε) (0.3 - ε) = 2 := by
      rw [rankY_eq _ _ (by linarith),
          indEss_pos 5 (1.6 - ε) (by linarith),
          indMort_pos 3.2 (-1.5) (1.6 - ε) (0.3 - ε) (by linarith) (by linarith),
          indMort_neg_t 1.6 0.3 (1.6 - ε) (0.3 - ε) (by linarith)]
      decide
    have hD : rankFn stageY JY (1.6 + ε) (0.3 - ε) = 2 := by
      rw [rankY_eq _ _ (by linarith),
          indEss_pos 5 (1.6 + ε) (by linarith),
          indMort_pos 3.2 (-1.5) (1.6 + ε) (0.3 - ε) (by linarith) (by linarith),
          indMort_neg_s 1.6 0.3 (1.6 + ε) (0.3 - ε) (by linarith)]
      decide
    rw [hA, hB, hC, hD]
    decide

theorem multY_5 :
    mult (rankFn stageY JY) (((5:ℝ):EReal), (⊥:EReal)) = 1 := by
  rw [mult_coe_bot _ 5]
  refine le_antisymm ?_ (le_iInf fun ε => le_iInf fun hε => le_iInf fun t => le_iInf fun ht => ?_)
  · refine iInf_le_of_le 1 (iInf_le_of_le (show (0:ℝ) < 1 by norm_num) ?_)
    refine iInf_le_of_le 0 (iInf_le_of_le (show (0:ℝ) ≤ 5 - 1 by norm_num) ?_)
    have hA : rankFn stageY JY (5 - 1) 0 = 1 := by
      rw [rankY_eq _ _ (by norm_num),
          indEss_pos 5 (5 - 1) (by norm_num),
          indMort_neg_s 3.2 (-1.5) (5 - 1) 0 (by norm_num),
          indMort_neg_s 1.6 0.3 (5 - 1) 0 (by norm_num)]
      decide
    have hB : rankFn stageY JY (5 + 1) 0 = 0 := by
      rw [rankY_eq _ _ (by norm_num),
          indEss_neg 5 (5 + 1) (by norm_num),
          indMort_neg_s 3.2 (-1.5) (5 + 1) 0 (by norm_num),
          indMort_neg_s 1.6 0.3 (5 + 1) 0 (by norm_num)]
      decide
    rw [hA, hB]
    decide
  · have hA : rankFn stageY JY (5 - ε) t
          = 1 + (if (5 - ε) ≤ 3.2 ∧ (-1.5) < t then (1:ℕ∞) else 0)
            + (if (5 - ε) ≤ 1.6 ∧ 0.3 < t then (1:ℕ∞) else 0) := by
      rw [rankY_eq _ _ ht, indEss_pos 5 (5 - ε) (by linarith)]
      rfl
    have hB : rankFn stageY JY (5 + ε) t = 0 := by
      rw [rankY_eq _ _ (by linarith),
          indEss_neg 5 (5 + ε) (by linarith),
          indMort_neg_s 3.2 (-1.5) (5 + ε) t (by linarith),
          indMort_neg_s 1.6 0.3 (5 + ε) t (by linarith)]
      decide
    rw [hA, hB]
    split_ifs <;> decide

/-! ### Step 6: truncated diagram multiplicities -/

/-- When every corner of the `ε`-window lies at or above `α`, the truncated multiplicity
coincides with the plain one. -/
private lemma multTrunc_above_eq (r : ℝ → ℝ → ℕ∞) (α b d : ℝ) (hbd : d < b)
    (h : ∀ ε ∈ Set.Ioo (0:ℝ) ((b - d) / 2),
      (α ≤ b - ε) ∧ (α ≤ d + ε) ∧ (α ≤ b + ε) ∧ (α ≤ d - ε)) :
    mult (truncRank r α) (((b:ℝ):EReal), ((d:ℝ):EReal)) =
      mult r (((b:ℝ):EReal), ((d:ℝ):EReal)) := by
  have heq : ∀ ε ∈ Set.Ioo (0:ℝ) ((b - d) / 2),
      ((truncRank r α (b - ε) (d + ε) - truncRank r α (b + ε) (d + ε)) -
        (truncRank r α (b - ε) (d - ε) - truncRank r α (b + ε) (d - ε))) =
      ((r (b - ε) (d + ε) - r (b + ε) (d + ε)) - (r (b - ε) (d - ε) - r (b + ε) (d - ε))) := by
    intro ε hε
    obtain ⟨h1, h2, h3, h4⟩ := h ε hε
    rw [trunc_above _ _ _ _ h1 h2, trunc_above _ _ _ _ h3 h2,
        trunc_above _ _ _ _ h1 h4, trunc_above _ _ _ _ h3 h4]
  rw [mult_coe_coe _ b d hbd, mult_coe_coe _ b d hbd]
  refine le_antisymm ?_ ?_
  · refine le_iInf fun ε => le_iInf fun hε => ?_
    exact le_trans (iInf_le_of_le ε (iInf_le_of_le hε le_rfl)) (le_of_eq (heq ε hε))
  · refine le_iInf fun ε => le_iInf fun hε => ?_
    exact le_trans (iInf_le_of_le ε (iInf_le_of_le hε le_rfl)) (le_of_eq (heq ε hε).symm)

theorem multTruncX_42 :
    mult (truncRank (rankFn stageX JX) (-2)) (((4.2:ℝ):EReal), ((0.5:ℝ):EReal)) = 1 := by
  have hbox : ∀ ε ∈ Set.Ioo (0:ℝ) ((4.2 - 0.5) / 2),
      (-2:ℝ) ≤ 4.2 - ε ∧ (-2:ℝ) ≤ 0.5 + ε ∧ (-2:ℝ) ≤ 4.2 + ε ∧ (-2:ℝ) ≤ 0.5 - ε := by
    intro ε hε
    obtain ⟨hε0, hεw⟩ := Set.mem_Ioo.mp hε
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  rw [multTrunc_above_eq (rankFn stageX JX) (-2) 4.2 0.5 (by norm_num) hbox]
  exact multX_42

theorem multTruncY_16 :
    mult (truncRank (rankFn stageY JY) (-2)) (((1.6:ℝ):EReal), ((0.3:ℝ):EReal)) = 1 := by
  have hbox : ∀ ε ∈ Set.Ioo (0:ℝ) ((1.6 - 0.3) / 2),
      (-2:ℝ) ≤ 1.6 - ε ∧ (-2:ℝ) ≤ 0.3 + ε ∧ (-2:ℝ) ≤ 1.6 + ε ∧ (-2:ℝ) ≤ 0.3 - ε := by
    intro ε hε
    obtain ⟨hε0, hεw⟩ := Set.mem_Ioo.mp hε
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  rw [multTrunc_above_eq (rankFn stageY JY) (-2) 1.6 0.3 (by norm_num) hbox]
  exact multY_16

theorem multTruncX_5 :
    mult (truncRank (rankFn stageX JX) (-2)) (((5:ℝ):EReal), ((-2:ℝ):EReal)) = 1 := by
  rw [mult_coe_coe _ 5 (-2) (by norm_num : (-2:ℝ) < 5)]
  refine le_antisymm ?_ (le_iInf fun ε => le_iInf fun hε => ?_)
  · refine iInf_le_of_le 1 (iInf_le_of_le ⟨by norm_num, by norm_num⟩ ?_)
    have hA : truncRank (rankFn stageX JX) (-2) (5 - 1) ((-2) + 1) = 1 := by
      rw [trunc_above _ _ _ _ (by norm_num) (by norm_num),
          rankX_eq _ _ (by norm_num),
          indEss_pos 5 (5 - 1) (by norm_num),
          indMort_neg_t 4.2 0.5 (5 - 1) ((-2) + 1) (by norm_num),
          indMort_neg_s 2.5 (-0.6) (5 - 1) ((-2) + 1) (by norm_num)]
      decide
    have hB : truncRank (rankFn stageX JX) (-2) (5 + 1) ((-2) + 1) = 0 := by
      rw [trunc_above _ _ _ _ (by norm_num) (by norm_num),
          rankX_eq _ _ (by norm_num),
          indEss_neg 5 (5 + 1) (by norm_num),
          indMort_neg_s 4.2 0.5 (5 + 1) ((-2) + 1) (by norm_num),
          indMort_neg_s 2.5 (-0.6) (5 + 1) ((-2) + 1) (by norm_num)]
      decide
    have hC : truncRank (rankFn stageX JX) (-2) (5 - 1) ((-2) - 1) = 0 :=
      truncRank_zero_of_lt _ _ _ _ (by norm_num : ((-2:ℝ) - 1) < -2)
    have hD : truncRank (rankFn stageX JX) (-2) (5 + 1) ((-2) - 1) = 0 :=
      truncRank_zero_of_lt _ _ _ _ (by norm_num : ((-2:ℝ) - 1) < -2)
    rw [hA, hB, hC, hD]
    decide
  · obtain ⟨hε0, hεw⟩ := Set.mem_Ioo.mp hε
    have hA : truncRank (rankFn stageX JX) (-2) (5 - ε) ((-2) + ε)
        = 1 + (if (5 - ε) ≤ 4.2 ∧ 0.5 < (-2) + ε then (1:ℕ∞) else 0)
          + (if (5 - ε) ≤ 2.5 ∧ (-0.6) < (-2) + ε then (1:ℕ∞) else 0) := by
      rw [trunc_above _ _ _ _ (by linarith) (by linarith),
          rankX_eq _ _ (by linarith),
          indEss_pos 5 (5 - ε) (by linarith)]
      rfl
    have hB : truncRank (rankFn stageX JX) (-2) (5 + ε) ((-2) + ε) = 0 := by
      rw [trunc_above _ _ _ _ (by linarith) (by linarith),
          rankX_eq _ _ (by linarith),
          indEss_neg 5 (5 + ε) (by linarith),
          indMort_neg_s 4.2 0.5 (5 + ε) ((-2) + ε) (by linarith),
          indMort_neg_s 2.5 (-0.6) (5 + ε) ((-2) + ε) (by linarith)]
      decide
    have hC : truncRank (rankFn stageX JX) (-2) (5 - ε) ((-2) - ε) = 0 :=
      truncRank_zero_of_lt _ _ _ _ (by linarith : ((-2:ℝ) - ε) < -2)
    have hD : truncRank (rankFn stageX JX) (-2) (5 + ε) ((-2) - ε) = 0 :=
      truncRank_zero_of_lt _ _ _ _ (by linarith : ((-2:ℝ) - ε) < -2)
    rw [hA, hB, hC, hD]
    split_ifs <;> decide

theorem multTruncY_5 :
    mult (truncRank (rankFn stageY JY) (-2)) (((5:ℝ):EReal), ((-2:ℝ):EReal)) = 1 := by
  rw [mult_coe_coe _ 5 (-2) (by norm_num : (-2:ℝ) < 5)]
  refine le_antisymm ?_ (le_iInf fun ε => le_iInf fun hε => ?_)
  · refine iInf_le_of_le 1 (iInf_le_of_le ⟨by norm_num, by norm_num⟩ ?_)
    have hA : truncRank (rankFn stageY JY) (-2) (5 - 1) ((-2) + 1) = 1 := by
      rw [trunc_above _ _ _ _ (by norm_num) (by norm_num),
          rankY_eq _ _ (by norm_num),
          indEss_pos 5 (5 - 1) (by norm_num),
          indMort_neg_s 3.2 (-1.5) (5 - 1) ((-2) + 1) (by norm_num),
          indMort_neg_s 1.6 0.3 (5 - 1) ((-2) + 1) (by norm_num)]
      decide
    have hB : truncRank (rankFn stageY JY) (-2) (5 + 1) ((-2) + 1) = 0 := by
      rw [trunc_above _ _ _ _ (by norm_num) (by norm_num),
          rankY_eq _ _ (by norm_num),
          indEss_neg 5 (5 + 1) (by norm_num),
          indMort_neg_s 3.2 (-1.5) (5 + 1) ((-2) + 1) (by norm_num),
          indMort_neg_s 1.6 0.3 (5 + 1) ((-2) + 1) (by norm_num)]
      decide
    have hC : truncRank (rankFn stageY JY) (-2) (5 - 1) ((-2) - 1) = 0 :=
      truncRank_zero_of_lt _ _ _ _ (by norm_num : ((-2:ℝ) - 1) < -2)
    have hD : truncRank (rankFn stageY JY) (-2) (5 + 1) ((-2) - 1) = 0 :=
      truncRank_zero_of_lt _ _ _ _ (by norm_num : ((-2:ℝ) - 1) < -2)
    rw [hA, hB, hC, hD]
    decide
  · obtain ⟨hε0, hεw⟩ := Set.mem_Ioo.mp hε
    have hA : truncRank (rankFn stageY JY) (-2) (5 - ε) ((-2) + ε)
        = 1 + (if (5 - ε) ≤ 3.2 ∧ (-1.5) < (-2) + ε then (1:ℕ∞) else 0)
          + (if (5 - ε) ≤ 1.6 ∧ 0.3 < (-2) + ε then (1:ℕ∞) else 0) := by
      rw [trunc_above _ _ _ _ (by linarith) (by linarith),
          rankY_eq _ _ (by linarith),
          indEss_pos 5 (5 - ε) (by linarith)]
      rfl
    have hB : truncRank (rankFn stageY JY) (-2) (5 + ε) ((-2) + ε) = 0 := by
      rw [trunc_above _ _ _ _ (by linarith) (by linarith),
          rankY_eq _ _ (by linarith),
          indEss_neg 5 (5 + ε) (by linarith),
          indMort_neg_s 3.2 (-1.5) (5 + ε) ((-2) + ε) (by linarith),
          indMort_neg_s 1.6 0.3 (5 + ε) ((-2) + ε) (by linarith)]
      decide
    have hC : truncRank (rankFn stageY JY) (-2) (5 - ε) ((-2) - ε) = 0 :=
      truncRank_zero_of_lt _ _ _ _ (by linarith : ((-2:ℝ) - ε) < -2)
    have hD : truncRank (rankFn stageY JY) (-2) (5 + ε) ((-2) - ε) = 0 :=
      truncRank_zero_of_lt _ _ _ _ (by linarith : ((-2:ℝ) - ε) < -2)
    rw [hA, hB, hC, hD]
    split_ifs <;> decide

theorem multTruncX_25 :
    mult (truncRank (rankFn stageX JX) (-2)) (((2.5:ℝ):EReal), ((-0.6:ℝ):EReal)) = 1 := by
  rw [mult_coe_coe _ 2.5 (-0.6) (by norm_num : (-0.6:ℝ) < 2.5)]
  refine le_antisymm ?_ (le_iInf fun ε => le_iInf fun hε => ?_)
  · refine iInf_le_of_le 0.5 (iInf_le_of_le ⟨by norm_num, by norm_num⟩ ?_)
    have hA : truncRank (rankFn stageX JX) (-2) (2.5 - 0.5) ((-0.6) + 0.5) = 2 := by
      rw [trunc_above _ _ _ _ (by norm_num) (by norm_num),
          rankX_eq _ _ (by norm_num),
          indEss_pos 5 (2.5 - 0.5) (by norm_num),
          indMort_neg_t 4.2 0.5 (2.5 - 0.5) ((-0.6) + 0.5) (by norm_num),
          indMort_pos 2.5 (-0.6) (2.5 - 0.5) ((-0.6) + 0.5) (by norm_num) (by norm_num)]
      decide
    have hB : truncRank (rankFn stageX JX) (-2) (2.5 + 0.5) ((-0.6) + 0.5) = 1 := by
      rw [trunc_above _ _ _ _ (by norm_num) (by norm_num),
          rankX_eq _ _ (by norm_num),
          indEss_pos 5 (2.5 + 0.5) (by norm_num),
          indMort_neg_t 4.2 0.5 (2.5 + 0.5) ((-0.6) + 0.5) (by norm_num),
          indMort_neg_s 2.5 (-0.6) (2.5 + 0.5) ((-0.6) + 0.5) (by norm_num)]
      decide
    have hC : truncRank (rankFn stageX JX) (-2) (2.5 - 0.5) ((-0.6) - 0.5) = 1 := by
      rw [trunc_above _ _ _ _ (by norm_num) (by norm_num),
          rankX_eq _ _ (by norm_num),
          indEss_pos 5 (2.5 - 0.5) (by norm_num),
          indMort_neg_t 4.2 0.5 (2.5 - 0.5) ((-0.6) - 0.5) (by norm_num),
          indMort_neg_t 2.5 (-0.6) (2.5 - 0.5) ((-0.6) - 0.5) (by norm_num)]
      decide
    have hD : truncRank (rankFn stageX JX) (-2) (2.5 + 0.5) ((-0.6) - 0.5) = 1 := by
      rw [trunc_above _ _ _ _ (by norm_num) (by norm_num),
          rankX_eq _ _ (by norm_num),
          indEss_pos 5 (2.5 + 0.5) (by norm_num),
          indMort_neg_t 4.2 0.5 (2.5 + 0.5) ((-0.6) - 0.5) (by norm_num),
          indMort_neg_s 2.5 (-0.6) (2.5 + 0.5) ((-0.6) - 0.5) (by norm_num)]
      decide
    rw [hA, hB, hC, hD]
    decide
  · obtain ⟨hε0, hεw⟩ := Set.mem_Ioo.mp hε
    by_cases h11 : ε ≤ 1.1
    · have hA : truncRank (rankFn stageX JX) (-2) (2.5 - ε) ((-0.6) + ε) = 2 := by
        rw [trunc_above _ _ _ _ (by linarith) (by linarith),
            rankX_eq _ _ (by linarith),
            indEss_pos 5 (2.5 - ε) (by linarith),
            indMort_neg_t 4.2 0.5 (2.5 - ε) ((-0.6) + ε) (by linarith),
            indMort_pos 2.5 (-0.6) (2.5 - ε) ((-0.6) + ε) (by linarith) (by linarith)]
        decide
      have hB : truncRank (rankFn stageX JX) (-2) (2.5 + ε) ((-0.6) + ε) = 1 := by
        rw [trunc_above _ _ _ _ (by linarith) (by linarith),
            rankX_eq _ _ (by linarith),
            indEss_pos 5 (2.5 + ε) (by linarith),
            indMort_neg_t 4.2 0.5 (2.5 + ε) ((-0.6) + ε) (by linarith),
            indMort_neg_s 2.5 (-0.6) (2.5 + ε) ((-0.6) + ε) (by linarith)]
        decide
      have hC : truncRank (rankFn stageX JX) (-2) (2.5 - ε) ((-0.6) - ε) = 1 := by
        rw [trunc_above _ _ _ _ (by linarith) (by linarith),
            rankX_eq _ _ (by linarith),
            indEss_pos 5 (2.5 - ε) (by linarith),
            indMort_neg_t 4.2 0.5 (2.5 - ε) ((-0.6) - ε) (by linarith),
            indMort_neg_t 2.5 (-0.6) (2.5 - ε) ((-0.6) - ε) (by linarith)]
        decide
      have hD : truncRank (rankFn stageX JX) (-2) (2.5 + ε) ((-0.6) - ε) = 1 := by
        rw [trunc_above _ _ _ _ (by linarith) (by linarith),
            rankX_eq _ _ (by linarith),
            indEss_pos 5 (2.5 + ε) (by linarith),
            indMort_neg_t 4.2 0.5 (2.5 + ε) ((-0.6) - ε) (by linarith),
            indMort_neg_s 2.5 (-0.6) (2.5 + ε) ((-0.6) - ε) (by linarith)]
        decide
      rw [hA, hB, hC, hD]
      decide
    · by_cases h14 : ε ≤ 1.4
      · have hA : truncRank (rankFn stageX JX) (-2) (2.5 - ε) ((-0.6) + ε) = 3 := by
          rw [trunc_above _ _ _ _ (by linarith) (by linarith),
              rankX_eq _ _ (by linarith),
              indEss_pos 5 (2.5 - ε) (by linarith),
              indMort_pos 4.2 0.5 (2.5 - ε) ((-0.6) + ε) (by linarith) (by linarith),
              indMort_pos 2.5 (-0.6) (2.5 - ε) ((-0.6) + ε) (by linarith) (by linarith)]
          decide
        have hB : truncRank (rankFn stageX JX) (-2) (2.5 + ε) ((-0.6) + ε) = 2 := by
          rw [trunc_above _ _ _ _ (by linarith) (by linarith),
              rankX_eq _ _ (by linarith),
              indEss_pos 5 (2.5 + ε) (by linarith),
              indMort_pos 4.2 0.5 (2.5 + ε) ((-0.6) + ε) (by linarith) (by linarith),
              indMort_neg_s 2.5 (-0.6) (2.5 + ε) ((-0.6) + ε) (by linarith)]
          decide
        have hC : truncRank (rankFn stageX JX) (-2) (2.5 - ε) ((-0.6) - ε) = 1 := by
          rw [trunc_above _ _ _ _ (by linarith) (by linarith),
              rankX_eq _ _ (by linarith),
              indEss_pos 5 (2.5 - ε) (by linarith),
              indMort_neg_t 4.2 0.5 (2.5 - ε) ((-0.6) - ε) (by linarith),
              indMort_neg_t 2.5 (-0.6) (2.5 - ε) ((-0.6) - ε) (by linarith)]
          decide
        have hD : truncRank (rankFn stageX JX) (-2) (2.5 + ε) ((-0.6) - ε) = 1 := by
          rw [trunc_above _ _ _ _ (by linarith) (by linarith),
              rankX_eq _ _ (by linarith),
              indEss_pos 5 (2.5 + ε) (by linarith),
              indMort_neg_t 4.2 0.5 (2.5 + ε) ((-0.6) - ε) (by linarith),
              indMort_neg_s 2.5 (-0.6) (2.5 + ε) ((-0.6) - ε) (by linarith)]
          decide
        rw [hA, hB, hC, hD]
        decide
      · have hA : truncRank (rankFn stageX JX) (-2) (2.5 - ε) ((-0.6) + ε) = 3 := by
          rw [trunc_above _ _ _ _ (by linarith) (by linarith),
              rankX_eq _ _ (by linarith),
              indEss_pos 5 (2.5 - ε) (by linarith),
              indMort_pos 4.2 0.5 (2.5 - ε) ((-0.6) + ε) (by linarith) (by linarith),
              indMort_pos 2.5 (-0.6) (2.5 - ε) ((-0.6) + ε) (by linarith) (by linarith)]
          decide
        have hB : truncRank (rankFn stageX JX) (-2) (2.5 + ε) ((-0.6) + ε) = 2 := by
          rw [trunc_above _ _ _ _ (by linarith) (by linarith),
              rankX_eq _ _ (by linarith),
              indEss_pos 5 (2.5 + ε) (by linarith),
              indMort_pos 4.2 0.5 (2.5 + ε) ((-0.6) + ε) (by linarith) (by linarith),
              indMort_neg_s 2.5 (-0.6) (2.5 + ε) ((-0.6) + ε) (by linarith)]
          decide
        have hC : truncRank (rankFn stageX JX) (-2) (2.5 - ε) ((-0.6) - ε) = 0 :=
          truncRank_zero_of_lt _ _ _ _ (by linarith : ((-0.6:ℝ) - ε) < -2)
        have hD : truncRank (rankFn stageX JX) (-2) (2.5 + ε) ((-0.6) - ε) = 0 :=
          truncRank_zero_of_lt _ _ _ _ (by linarith : ((-0.6:ℝ) - ε) < -2)
        rw [hA, hB, hC, hD]
        decide

theorem multTruncY_32 :
    mult (truncRank (rankFn stageY JY) (-2)) (((3.2:ℝ):EReal), ((-1.5:ℝ):EReal)) = 1 := by
  rw [mult_coe_coe _ 3.2 (-1.5) (by norm_num : (-1.5:ℝ) < 3.2)]
  refine le_antisymm ?_ (le_iInf fun ε => le_iInf fun hε => ?_)
  · refine iInf_le_of_le 1 (iInf_le_of_le ⟨by norm_num, by norm_num⟩ ?_)
    have hA : truncRank (rankFn stageY JY) (-2) (3.2 - 1) ((-1.5) + 1) = 2 := by
      rw [trunc_above _ _ _ _ (by norm_num) (by norm_num),
          rankY_eq _ _ (by norm_num),
          indEss_pos 5 (3.2 - 1) (by norm_num),
          indMort_pos 3.2 (-1.5) (3.2 - 1) ((-1.5) + 1) (by norm_num) (by norm_num),
          indMort_neg_s 1.6 0.3 (3.2 - 1) ((-1.5) + 1) (by norm_num)]
      decide
    have hB : truncRank (rankFn stageY JY) (-2) (3.2 + 1) ((-1.5) + 1) = 1 := by
      rw [trunc_above _ _ _ _ (by norm_num) (by norm_num),
          rankY_eq _ _ (by norm_num),
          indEss_pos 5 (3.2 + 1) (by norm_num),
          indMort_neg_s 3.2 (-1.5) (3.2 + 1) ((-1.5) + 1) (by norm_num),
          indMort_neg_s 1.6 0.3 (3.2 + 1) ((-1.5) + 1) (by norm_num)]
      decide
    have hC : truncRank (rankFn stageY JY) (-2) (3.2 - 1) ((-1.5) - 1) = 0 :=
      truncRank_zero_of_lt _ _ _ _ (by norm_num : ((-1.5:ℝ) - 1) < -2)
    have hD : truncRank (rankFn stageY JY) (-2) (3.2 + 1) ((-1.5) - 1) = 0 :=
      truncRank_zero_of_lt _ _ _ _ (by norm_num : ((-1.5:ℝ) - 1) < -2)
    rw [hA, hB, hC, hD]
    decide
  · obtain ⟨hε0, hεw⟩ := Set.mem_Ioo.mp hε
    by_cases h05 : ε ≤ 0.5
    · have hA : truncRank (rankFn stageY JY) (-2) (3.2 - ε) ((-1.5) + ε) = 2 := by
        rw [trunc_above _ _ _ _ (by linarith) (by linarith),
            rankY_eq _ _ (by linarith),
            indEss_pos 5 (3.2 - ε) (by linarith),
            indMort_pos 3.2 (-1.5) (3.2 - ε) ((-1.5) + ε) (by linarith) (by linarith),
            indMort_neg 1.6 0.3 (3.2 - ε) ((-1.5) + ε) (by rintro ⟨h1, h2⟩; linarith)]
        decide
      have hB : truncRank (rankFn stageY JY) (-2) (3.2 + ε) ((-1.5) + ε) = 1 := by
        rw [trunc_above _ _ _ _ (by linarith) (by linarith),
            rankY_eq _ _ (by linarith),
            indEss_pos 5 (3.2 + ε) (by linarith),
            indMort_neg_s 3.2 (-1.5) (3.2 + ε) ((-1.5) + ε) (by linarith),
            indMort_neg_s 1.6 0.3 (3.2 + ε) ((-1.5) + ε) (by linarith)]
        decide
      have hC : truncRank (rankFn stageY JY) (-2) (3.2 - ε) ((-1.5) - ε) = 1 := by
        rw [trunc_above _ _ _ _ (by linarith) (by linarith),
            rankY_eq _ _ (by linarith),
            indEss_pos 5 (3.2 - ε) (by linarith),
            indMort_neg_t 3.2 (-1.5) (3.2 - ε) ((-1.5) - ε) (by linarith),
            indMort_neg 1.6 0.3 (3.2 - ε) ((-1.5) - ε) (by rintro ⟨h1, h2⟩; linarith)]
        decide
      have hD : truncRank (rankFn stageY JY) (-2) (3.2 + ε) ((-1.5) - ε) = 1 := by
        rw [trunc_above _ _ _ _ (by linarith) (by linarith),
            rankY_eq _ _ (by linarith),
            indEss_pos 5 (3.2 + ε) (by linarith),
            indMort_neg_s 3.2 (-1.5) (3.2 + ε) ((-1.5) - ε) (by linarith),
            indMort_neg 1.6 0.3 (3.2 + ε) ((-1.5) - ε) (by rintro ⟨h1, h2⟩; linarith)]
        decide
      rw [hA, hB, hC, hD]
      decide
    · by_cases h18 : ε ≤ 1.8
      · have hA : truncRank (rankFn stageY JY) (-2) (3.2 - ε) ((-1.5) + ε) = 2 := by
          rw [trunc_above _ _ _ _ (by linarith) (by linarith),
              rankY_eq _ _ (by linarith),
              indEss_pos 5 (3.2 - ε) (by linarith),
              indMort_pos 3.2 (-1.5) (3.2 - ε) ((-1.5) + ε) (by linarith) (by linarith),
              indMort_neg 1.6 0.3 (3.2 - ε) ((-1.5) + ε) (by rintro ⟨h1, h2⟩; linarith)]
          decide
        have hB : truncRank (rankFn stageY JY) (-2) (3.2 + ε) ((-1.5) + ε) = 1 := by
          rw [trunc_above _ _ _ _ (by linarith) (by linarith),
              rankY_eq _ _ (by linarith),
              indEss_pos 5 (3.2 + ε) (by linarith),
              indMort_neg_s 3.2 (-1.5) (3.2 + ε) ((-1.5) + ε) (by linarith),
              indMort_neg_s 1.6 0.3 (3.2 + ε) ((-1.5) + ε) (by linarith)]
          decide
        have hC : truncRank (rankFn stageY JY) (-2) (3.2 - ε) ((-1.5) - ε) = 0 :=
          truncRank_zero_of_lt _ _ _ _ (by linarith : ((-1.5:ℝ) - ε) < -2)
        have hD : truncRank (rankFn stageY JY) (-2) (3.2 + ε) ((-1.5) - ε) = 0 :=
          truncRank_zero_of_lt _ _ _ _ (by linarith : ((-1.5:ℝ) - ε) < -2)
        rw [hA, hB, hC, hD]
        decide
      · have hA : truncRank (rankFn stageY JY) (-2) (3.2 - ε) ((-1.5) + ε) = 3 := by
          rw [trunc_above _ _ _ _ (by linarith) (by linarith),
              rankY_eq _ _ (by linarith),
              indEss_pos 5 (3.2 - ε) (by linarith),
              indMort_pos 3.2 (-1.5) (3.2 - ε) ((-1.5) + ε) (by linarith) (by linarith),
              indMort_pos 1.6 0.3 (3.2 - ε) ((-1.5) + ε) (by linarith) (by linarith)]
          decide
        have hB : truncRank (rankFn stageY JY) (-2) (3.2 + ε) ((-1.5) + ε) = 0 := by
          rw [trunc_above _ _ _ _ (by linarith) (by linarith),
              rankY_eq _ _ (by linarith),
              indEss_neg 5 (3.2 + ε) (by linarith),
              indMort_neg_s 3.2 (-1.5) (3.2 + ε) ((-1.5) + ε) (by linarith),
              indMort_neg_s 1.6 0.3 (3.2 + ε) ((-1.5) + ε) (by linarith)]
          decide
        have hC : truncRank (rankFn stageY JY) (-2) (3.2 - ε) ((-1.5) - ε) = 0 :=
          truncRank_zero_of_lt _ _ _ _ (by linarith : ((-1.5:ℝ) - ε) < -2)
        have hD : truncRank (rankFn stageY JY) (-2) (3.2 + ε) ((-1.5) - ε) = 0 :=
          truncRank_zero_of_lt _ _ _ _ (by linarith : ((-1.5:ℝ) - ε) < -2)
        rw [hA, hB, hC, hD]
        decide

/-! ### Step 7: the box-expansion inequality (`hbox`, α = −2, ε = 1) -/

private lemma indEss_anti (β s s' : ℝ) (h : s' ≤ s) : indEss β s ≤ indEss β s' := by
  by_cases hs : s ≤ β
  · rw [indEss_pos β s hs, indEss_pos β s' (h.trans hs)]
  · rw [indEss_neg β s hs]; exact (zero_le : (0:ℕ∞) ≤ _)

private lemma indMort_shift_le (β δ β' δ' s t : ℝ) (hβ : β ≤ β' + 1) (hδ : δ' ≤ δ + 1) :
    indMort β δ s t ≤ indMort β' δ' (s - 1) (t + 1) := by
  by_cases h : s ≤ β ∧ δ < t
  · rw [indMort_pos β δ s t h.1 h.2,
        indMort_pos β' δ' (s - 1) (t + 1) (by linarith [h.1, hβ]) (by linarith [h.2, hδ])]
  · rw [indMort_neg β δ s t h]; exact (zero_le : (0:ℕ∞) ≤ _)

private lemma rankX_le_rankY_shift (s t : ℝ) (hts : t + 2 ≤ s) :
    rankFn stageX JX s t ≤ rankFn stageY JY (s - 1) (t + 1) := by
  rw [rankX_eq s t (by linarith), rankY_eq (s - 1) (t + 1) (by linarith)]
  exact add_le_add (add_le_add (indEss_anti 5 s (s - 1) (by linarith))
      (indMort_shift_le 4.2 0.5 3.2 (-1.5) s t (by linarith) (by linarith)))
      (indMort_shift_le 2.5 (-0.6) 1.6 0.3 s t (by linarith) (by linarith))

private lemma rankY_le_rankX_shift (s t : ℝ) (hts : t + 2 ≤ s) :
    rankFn stageY JY s t ≤ rankFn stageX JX (s - 1) (t + 1) := by
  rw [rankY_eq s t (by linarith), rankX_eq (s - 1) (t + 1) (by linarith)]
  calc indEss 5 s + indMort 3.2 (-1.5) s t + indMort 1.6 0.3 s t
      ≤ indEss 5 (s - 1) + indMort 2.5 (-0.6) (s - 1) (t + 1) + indMort 4.2 0.5 (s - 1) (t + 1) :=
        add_le_add (add_le_add (indEss_anti 5 s (s - 1) (by linarith))
          (indMort_shift_le 3.2 (-1.5) 2.5 (-0.6) s t (by linarith) (by linarith)))
          (indMort_shift_le 1.6 0.3 4.2 0.5 s t (by linarith) (by linarith))
    _ = indEss 5 (s - 1) + indMort 4.2 0.5 (s - 1) (t + 1) + indMort 2.5 (-0.6) (s - 1) (t + 1) := by
        rw [add_right_comm]

theorem hbox_holds : ∀ s t : ℝ, t + 2 * 1 ≤ s →
    truncRank (rankFn stageX JX) (-2) s t ≤ truncRank (rankFn stageY JY) (-2) (s - 1) (t + 1) ∧
    truncRank (rankFn stageY JY) (-2) s t ≤ truncRank (rankFn stageX JX) (-2) (s - 1) (t + 1) := by
  intro s t hts
  have hts' : t + 2 ≤ s := by linarith
  constructor
  · by_cases htr : (-2:ℝ) ≤ s ∧ (-2:ℝ) ≤ t
    · rw [trunc_above _ _ _ _ htr.1 htr.2]
      have h1 : (-2:ℝ) ≤ s - 1 := by linarith [htr.1, htr.2, hts']
      have h2 : (-2:ℝ) ≤ t + 1 := by linarith [htr.2]
      rw [trunc_above _ _ _ _ h1 h2]
      exact rankX_le_rankY_shift s t hts'
    · rw [trunc_below _ _ _ _ htr]; exact (zero_le : (0:ℕ∞) ≤ _)
  · by_cases htr : (-2:ℝ) ≤ s ∧ (-2:ℝ) ≤ t
    · rw [trunc_above _ _ _ _ htr.1 htr.2]
      have h1 : (-2:ℝ) ≤ s - 1 := by linarith [htr.1, htr.2, hts']
      have h2 : (-2:ℝ) ≤ t + 1 := by linarith [htr.2]
      rw [trunc_above _ _ _ _ h1 h2]
      exact rankY_le_rankX_shift s t hts'
    · rw [trunc_below _ _ _ _ htr]; exact (zero_le : (0:ℕ∞) ≤ _)

theorem multTruncY_503 :
    mult (truncRank (rankFn stageY JY) (-2)) (((5:ℝ):EReal), ((0.3:ℝ):EReal)) = 0 := by
  rw [mult_coe_coe _ 5 0.3 (by norm_num : (0.3:ℝ) < 5)]
  refine le_antisymm (iInf_le_of_le 0.1 (iInf_le_of_le ⟨by norm_num, by norm_num⟩ ?_)) (zero_le : (0:ℕ∞) ≤ _)
  have hA : truncRank (rankFn stageY JY) (-2) (5 - 0.1) (0.3 + 0.1) = 1 := by
    rw [trunc_above _ _ _ _ (by norm_num) (by norm_num),
        rankY_eq _ _ (by norm_num),
        indEss_pos 5 (5 - 0.1) (by norm_num),
        indMort_neg_s 3.2 (-1.5) (5 - 0.1) (0.3 + 0.1) (by norm_num),
        indMort_neg_s 1.6 0.3 (5 - 0.1) (0.3 + 0.1) (by norm_num)]
    decide
  have hB : truncRank (rankFn stageY JY) (-2) (5 + 0.1) (0.3 + 0.1) = 0 := by
    rw [trunc_above _ _ _ _ (by norm_num) (by norm_num),
        rankY_eq _ _ (by norm_num),
        indEss_neg 5 (5 + 0.1) (by norm_num),
        indMort_neg_s 3.2 (-1.5) (5 + 0.1) (0.3 + 0.1) (by norm_num),
        indMort_neg_s 1.6 0.3 (5 + 0.1) (0.3 + 0.1) (by norm_num)]
    decide
  have hC : truncRank (rankFn stageY JY) (-2) (5 - 0.1) (0.3 - 0.1) = 1 := by
    rw [trunc_above _ _ _ _ (by norm_num) (by norm_num),
        rankY_eq _ _ (by norm_num),
        indEss_pos 5 (5 - 0.1) (by norm_num),
        indMort_neg_s 3.2 (-1.5) (5 - 0.1) (0.3 - 0.1) (by norm_num),
        indMort_neg_s 1.6 0.3 (5 - 0.1) (0.3 - 0.1) (by norm_num)]
    decide
  have hD : truncRank (rankFn stageY JY) (-2) (5 + 0.1) (0.3 - 0.1) = 0 := by
    rw [trunc_above _ _ _ _ (by norm_num) (by norm_num),
        rankY_eq _ _ (by norm_num),
        indEss_neg 5 (5 + 0.1) (by norm_num),
        indMort_neg_s 3.2 (-1.5) (5 + 0.1) (0.3 - 0.1) (by norm_num),
        indMort_neg_s 1.6 0.3 (5 + 0.1) (0.3 - 0.1) (by norm_num)]
    decide
  rw [hA, hB, hC, hD]
  decide

theorem multTruncY_3203 :
    mult (truncRank (rankFn stageY JY) (-2)) (((3.2:ℝ):EReal), ((0.3:ℝ):EReal)) = 0 := by
  rw [mult_coe_coe _ 3.2 0.3 (by norm_num : (0.3:ℝ) < 3.2)]
  refine le_antisymm (iInf_le_of_le 0.1 (iInf_le_of_le ⟨by norm_num, by norm_num⟩ ?_)) (zero_le : (0:ℕ∞) ≤ _)
  have hA : truncRank (rankFn stageY JY) (-2) (3.2 - 0.1) (0.3 + 0.1) = 2 := by
    rw [trunc_above _ _ _ _ (by norm_num) (by norm_num),
        rankY_eq _ _ (by norm_num),
        indEss_pos 5 (3.2 - 0.1) (by norm_num),
        indMort_pos 3.2 (-1.5) (3.2 - 0.1) (0.3 + 0.1) (by norm_num) (by norm_num),
        indMort_neg_s 1.6 0.3 (3.2 - 0.1) (0.3 + 0.1) (by norm_num)]
    decide
  have hB : truncRank (rankFn stageY JY) (-2) (3.2 + 0.1) (0.3 + 0.1) = 1 := by
    rw [trunc_above _ _ _ _ (by norm_num) (by norm_num),
        rankY_eq _ _ (by norm_num),
        indEss_pos 5 (3.2 + 0.1) (by norm_num),
        indMort_neg_s 3.2 (-1.5) (3.2 + 0.1) (0.3 + 0.1) (by norm_num),
        indMort_neg_s 1.6 0.3 (3.2 + 0.1) (0.3 + 0.1) (by norm_num)]
    decide
  have hC : truncRank (rankFn stageY JY) (-2) (3.2 - 0.1) (0.3 - 0.1) = 2 := by
    rw [trunc_above _ _ _ _ (by norm_num) (by norm_num),
        rankY_eq _ _ (by norm_num),
        indEss_pos 5 (3.2 - 0.1) (by norm_num),
        indMort_pos 3.2 (-1.5) (3.2 - 0.1) (0.3 - 0.1) (by norm_num) (by norm_num),
        indMort_neg_s 1.6 0.3 (3.2 - 0.1) (0.3 - 0.1) (by norm_num)]
    decide
  have hD : truncRank (rankFn stageY JY) (-2) (3.2 + 0.1) (0.3 - 0.1) = 1 := by
    rw [trunc_above _ _ _ _ (by norm_num) (by norm_num),
        rankY_eq _ _ (by norm_num),
        indEss_pos 5 (3.2 + 0.1) (by norm_num),
        indMort_neg_s 3.2 (-1.5) (3.2 + 0.1) (0.3 - 0.1) (by norm_num),
        indMort_neg_s 1.6 0.3 (3.2 + 0.1) (0.3 - 0.1) (by norm_num)]
    decide
  rw [hA, hB, hC, hD]
  decide

/-! ### Step 5: support bounds — threshold-cell congruence infrastructure -/

/-- `indEss` depends only on which side of `β` the argument lies on. -/
private lemma indEss_congr (β s s' : ℝ) (h : s ≤ β ↔ s' ≤ β) : indEss β s = indEss β s' := by
  unfold indEss
  by_cases hs : s ≤ β
  · rw [if_pos hs, if_pos (h.mp hs)]
  · have hs' : ¬ s' ≤ β := fun hc => hs (h.mpr hc)
    rw [if_neg hs, if_neg hs']

/-- `indMort` depends only on which side of `β` the birth argument lies on. -/
private lemma indMort_congr_s (β δ s s' t : ℝ) (h : s ≤ β ↔ s' ≤ β) :
    indMort β δ s t = indMort β δ s' t := by
  unfold indMort
  by_cases hs : s ≤ β
  · have hs' : s' ≤ β := h.mp hs
    by_cases ht : δ < t
    · rw [if_pos ⟨hs, ht⟩, if_pos ⟨hs', ht⟩]
    · rw [if_neg (fun hc => ht hc.2), if_neg (fun hc => ht hc.2)]
  · have hs' : ¬ s' ≤ β := fun hc => hs (h.mpr hc)
    rw [if_neg (fun hc => hs hc.1), if_neg (fun hc => hs' hc.1)]

/-- `indMort` depends only on which side of `δ` the death argument lies on. -/
private lemma indMort_congr_t (β δ s t t' : ℝ) (h : δ < t ↔ δ < t') :
    indMort β δ s t = indMort β δ s t' := by
  unfold indMort
  by_cases ht : δ < t
  · have ht' : δ < t' := h.mp ht
    by_cases hs : s ≤ β
    · rw [if_pos ⟨hs, ht⟩, if_pos ⟨hs, ht'⟩]
    · rw [if_neg (fun hc => hs hc.1), if_neg (fun hc => hs hc.1)]
  · have ht' : ¬ δ < t' := fun hc => ht (h.mpr hc)
    rw [if_neg (fun hc => ht hc.2), if_neg (fun hc => ht' hc.2)]

/-- While `b ± η` stays on one side of the threshold `β ≠ b`, the birth cell is constant. -/
private lemma birth_cell (β b η : ℝ) (hη : 0 ≤ η) (hβ : β ≠ b) (h : η < |β - b|) :
    b - η ≤ β ↔ b + η ≤ β := by
  rcases lt_or_gt_of_ne hβ with hlt | hgt
  · rw [abs_of_neg (by linarith)] at h
    exact ⟨fun hc => absurd hc (by linarith), fun hc => absurd hc (by linarith)⟩
  · rw [abs_of_pos (by linarith)] at h
    exact ⟨fun _ => le_of_lt (by linarith), fun _ => le_of_lt (by linarith)⟩

/-- While `d ± η` stays on one side of the threshold `δ ≠ d`, the death cell is constant. -/
private lemma death_cell (δ d η : ℝ) (hη : 0 ≤ η) (hδ : δ ≠ d) (h : η < |δ - d|) :
    δ < d + η ↔ δ < d - η := by
  rcases lt_or_gt_of_ne hδ with hlt | hgt
  · rw [abs_of_neg (by linarith)] at h
    exact ⟨fun _ => by linarith, fun _ => by linarith⟩
  · rw [abs_of_pos (by linarith)] at h
    exact ⟨fun hc => absurd hc (by linarith), fun hc => absurd hc (by linarith)⟩

private lemma indEss_ne_top (β s : ℝ) : indEss β s ≠ ⊤ := by
  unfold indEss; split <;> simp

private lemma indMort_ne_top (β δ s t : ℝ) : indMort β δ s t ≠ ⊤ := by
  unfold indMort; split <;> simp

private lemma enat_top_sub (x : ℕ∞) (hx : x ≠ ⊤) : (⊤:ℕ∞) - x = ⊤ := by
  obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp hx
  exact ENat.top_sub_natCast n

private lemma enat_top_add (x : ℕ∞) : (⊤:ℕ∞) + x = ⊤ := rfl

/-- Cancellation of a shared finite addend in `ℕ∞` truncated subtraction. -/
private lemma enat_tsub_cancel_right (a b c : ℕ∞) (hc : c ≠ ⊤) : (a + c) - (b + c) = a - b := by
  by_cases ha : a = ⊤
  · by_cases hb : b = ⊤
    · rw [ha, hb, enat_top_add]
    · have hbc : b + c ≠ ⊤ := by
        intro h
        rw [ENat.add_eq_top] at h
        rcases h with h | h
        · exact hb h
        · exact hc h
      rw [ha, enat_top_add, enat_top_sub _ hbc, enat_top_sub _ hb]
  · by_cases hb : b = ⊤
    · rw [hb, enat_top_add, ENat.sub_top, ENat.sub_top]
    · obtain ⟨na, rfl⟩ := ENat.ne_top_iff_exists.mp ha
      obtain ⟨nb, rfl⟩ := ENat.ne_top_iff_exists.mp hb
      obtain ⟨nc, rfl⟩ := ENat.ne_top_iff_exists.mp hc
      have hnat : (na + nc) - (nb + nc) = na - nb := by omega
      rw [← Nat.cast_add, ← Nat.cast_add, ← ENat.natCast_sub, ← ENat.natCast_sub, hnat]

/-- Master bracket lemma: for a rank function of the form
`r s t = indEss β₀ s + indMort β₁ δ₁ s t + indMort β₂ δ₂ s t` (for `t ≤ s`), the four-corner
multiplicity bracket at a real point `(b, d)` vanishes at scale `η` whenever, for each bar,
either the birth window `b ± η` avoids the bar's birth or the death window `d ± η` avoids the
bar's death. -/
private lemma bracket_zero_general (r : ℝ → ℝ → ℕ∞) (β₀ β₁ δ₁ β₂ δ₂ : ℝ)
    (hr : ∀ s t, t ≤ s → r s t = indEss β₀ s + indMort β₁ δ₁ s t + indMort β₂ δ₂ s t)
    (b d η : ℝ) (hη : 0 ≤ η) (hd : d < b) (hηw : η < (b - d) / 2)
    (h1 : (β₁ ≠ b ∧ η < |β₁ - b|) ∨ (δ₁ ≠ d ∧ η < |δ₁ - d|))
    (h2 : (β₂ ≠ b ∧ η < |β₂ - b|) ∨ (δ₂ ≠ d ∧ η < |δ₂ - d|)) :
    ((r (b - η) (d + η) - r (b + η) (d + η)) - (r (b - η) (d - η) - r (b + η) (d - η))) = 0 := by
  have hle1 : d + η ≤ b - η := by linarith
  have hle2 : d + η ≤ b + η := by linarith
  have hle3 : d - η ≤ b - η := by linarith
  have hle4 : d - η ≤ b + η := by linarith
  rw [hr (b - η) (d + η) hle1, hr (b + η) (d + η) hle2,
      hr (b - η) (d - η) hle3, hr (b + η) (d - η) hle4]
  rcases h1 with ⟨hb1, hn1⟩ | ⟨hd1d, hn1d⟩
  · have hc1 : indMort β₁ δ₁ (b + η) (d + η) = indMort β₁ δ₁ (b - η) (d + η) :=
      indMort_congr_s _ _ _ _ _ (birth_cell β₁ b η hη hb1 hn1).symm
    have hc2 : indMort β₁ δ₁ (b + η) (d - η) = indMort β₁ δ₁ (b - η) (d - η) :=
      indMort_congr_s _ _ _ _ _ (birth_cell β₁ b η hη hb1 hn1).symm
    rw [hc1, hc2]
    rcases h2 with ⟨hb2, hn2⟩ | ⟨hd2d, hn2d⟩
    · have hc3 : indMort β₂ δ₂ (b + η) (d + η) = indMort β₂ δ₂ (b - η) (d + η) :=
        indMort_congr_s _ _ _ _ _ (birth_cell β₂ b η hη hb2 hn2).symm
      have hc4 : indMort β₂ δ₂ (b + η) (d - η) = indMort β₂ δ₂ (b - η) (d - η) :=
        indMort_congr_s _ _ _ _ _ (birth_cell β₂ b η hη hb2 hn2).symm
      rw [hc3, hc4]
      rw [enat_tsub_cancel_right
            (indEss β₀ (b - η) + indMort β₁ δ₁ (b - η) (d + η))
            (indEss β₀ (b + η) + indMort β₁ δ₁ (b - η) (d + η))
            (indMort β₂ δ₂ (b - η) (d + η)) (indMort_ne_top _ _ _ _),
        enat_tsub_cancel_right
          (indEss β₀ (b - η)) (indEss β₀ (b + η))
          (indMort β₁ δ₁ (b - η) (d + η)) (indMort_ne_top _ _ _ _),
        enat_tsub_cancel_right
          (indEss β₀ (b - η) + indMort β₁ δ₁ (b - η) (d - η))
          (indEss β₀ (b + η) + indMort β₁ δ₁ (b - η) (d - η))
          (indMort β₂ δ₂ (b - η) (d - η)) (indMort_ne_top _ _ _ _),
        enat_tsub_cancel_right
          (indEss β₀ (b - η)) (indEss β₀ (b + η))
          (indMort β₁ δ₁ (b - η) (d - η)) (indMort_ne_top _ _ _ _)]
      rw [tsub_self]
    · have hd3e : indMort β₂ δ₂ (b - η) (d - η) = indMort β₂ δ₂ (b - η) (d + η) :=
        indMort_congr_t _ _ _ _ _ (death_cell δ₂ d η hη hd2d hn2d).symm
      have hd4e : indMort β₂ δ₂ (b + η) (d - η) = indMort β₂ δ₂ (b + η) (d + η) :=
        indMort_congr_t _ _ _ _ _ (death_cell δ₂ d η hη hd2d hn2d).symm
      rw [hd3e, hd4e]
      rw [add_right_comm (indEss β₀ (b - η)) (indMort β₁ δ₁ (b - η) (d + η)) (indMort β₂ δ₂ (b - η) (d + η)),
        add_right_comm (indEss β₀ (b + η)) (indMort β₁ δ₁ (b - η) (d + η)) (indMort β₂ δ₂ (b + η) (d + η)),
        enat_tsub_cancel_right
          (indEss β₀ (b - η) + indMort β₂ δ₂ (b - η) (d + η))
          (indEss β₀ (b + η) + indMort β₂ δ₂ (b + η) (d + η))
          (indMort β₁ δ₁ (b - η) (d + η)) (indMort_ne_top _ _ _ _),
        add_right_comm (indEss β₀ (b - η)) (indMort β₁ δ₁ (b - η) (d - η)) (indMort β₂ δ₂ (b - η) (d + η)),
        add_right_comm (indEss β₀ (b + η)) (indMort β₁ δ₁ (b - η) (d - η)) (indMort β₂ δ₂ (b + η) (d + η)),
        enat_tsub_cancel_right
          (indEss β₀ (b - η) + indMort β₂ δ₂ (b - η) (d + η))
          (indEss β₀ (b + η) + indMort β₂ δ₂ (b + η) (d + η))
          (indMort β₁ δ₁ (b - η) (d - η)) (indMort_ne_top _ _ _ _)]
      rw [tsub_self]
  · have hd1e : indMort β₁ δ₁ (b - η) (d - η) = indMort β₁ δ₁ (b - η) (d + η) :=
      indMort_congr_t _ _ _ _ _ (death_cell δ₁ d η hη hd1d hn1d).symm
    have hd2e : indMort β₁ δ₁ (b + η) (d - η) = indMort β₁ δ₁ (b + η) (d + η) :=
      indMort_congr_t _ _ _ _ _ (death_cell δ₁ d η hη hd1d hn1d).symm
    rw [hd1e, hd2e]
    rcases h2 with ⟨hb2, hn2⟩ | ⟨hd2d, hn2d⟩
    · have hc3 : indMort β₂ δ₂ (b + η) (d + η) = indMort β₂ δ₂ (b - η) (d + η) :=
        indMort_congr_s _ _ _ _ _ (birth_cell β₂ b η hη hb2 hn2).symm
      have hc4 : indMort β₂ δ₂ (b + η) (d - η) = indMort β₂ δ₂ (b - η) (d - η) :=
        indMort_congr_s _ _ _ _ _ (birth_cell β₂ b η hη hb2 hn2).symm
      rw [hc3, hc4]
      rw [enat_tsub_cancel_right
            (indEss β₀ (b - η) + indMort β₁ δ₁ (b - η) (d + η))
            (indEss β₀ (b + η) + indMort β₁ δ₁ (b + η) (d + η))
            (indMort β₂ δ₂ (b - η) (d + η)) (indMort_ne_top _ _ _ _),
          enat_tsub_cancel_right
            (indEss β₀ (b - η) + indMort β₁ δ₁ (b - η) (d + η))
            (indEss β₀ (b + η) + indMort β₁ δ₁ (b + η) (d + η))
            (indMort β₂ δ₂ (b - η) (d - η)) (indMort_ne_top _ _ _ _)]
      rw [tsub_self]
    · have hd3e : indMort β₂ δ₂ (b - η) (d - η) = indMort β₂ δ₂ (b - η) (d + η) :=
        indMort_congr_t _ _ _ _ _ (death_cell δ₂ d η hη hd2d hn2d).symm
      have hd4e : indMort β₂ δ₂ (b + η) (d - η) = indMort β₂ δ₂ (b + η) (d + η) :=
        indMort_congr_t _ _ _ _ _ (death_cell δ₂ d η hη hd2d hn2d).symm
      rw [hd3e, hd4e]
      rw [tsub_self]

/-! ### Step 5 (cont.): degenerate-case `mult = 0` helpers -/

/-- Any point born at `±∞` has zero multiplicity. -/
private lemma mult_zero_of_born (r : ℝ → ℝ → ℕ∞) (p : EReal × EReal)
    (h : p.1 = ⊥ ∨ p.1 = ⊤) : mult r p = 0 := by
  unfold mult
  rcases h with h | h
  · rw [if_neg (fun hc => hc.1 h)]
  · rw [if_neg (fun hc => hc.2 h)]

/-- A real-born point that dies at `+∞` has zero multiplicity. -/
private lemma mult_coe_top_zero (r : ℝ → ℝ → ℕ∞) (b : ℝ) :
    mult r (((b : ℝ) : EReal), (⊤ : EReal)) = 0 := by
  unfold mult
  rw [if_pos ⟨EReal.coe_ne_bot b, EReal.coe_ne_top b⟩,
      if_neg (bot_ne_top.symm),
      if_neg (fun hc => lt_irrefl (⊤ : EReal) (hc.trans (EReal.coe_lt_top b)))]

/-- A real point on or below the diagonal has zero multiplicity. -/
private lemma mult_coe_coe_le_zero (r : ℝ → ℝ → ℕ∞) (b d : ℝ) (h : b ≤ d) :
    mult r (((b : ℝ) : EReal), ((d : ℝ) : EReal)) = 0 := by
  unfold mult
  rw [if_pos ⟨EReal.coe_ne_bot b, EReal.coe_ne_top b⟩,
      if_neg (EReal.coe_ne_bot d),
      if_neg (fun hc => lt_irrefl d ((EReal.coe_lt_coe_iff.mp hc).trans_le h))]

/-- Master bracket lemma at the truncation floor: for a rank function `r` of three-term
indicator form, the four-corner bracket of `truncRank r α` at a real point `(b, α)` (death
exactly at the truncation level) vanishes at scale `η`, provided the essential birth window
avoids `β₀`, both mortal bars die strictly above `α`, and `η` is small enough to stay below
all three thresholds. -/
private lemma bracket_zero_alpha (r : ℝ → ℝ → ℕ∞) (α β₀ β₁ δ₁ β₂ δ₂ b η : ℝ)
    (hr : ∀ s t, t ≤ s → r s t = indEss β₀ s + indMort β₁ δ₁ s t + indMort β₂ δ₂ s t)
    (hη : 0 < η) (hbα : α < b) (hηw : η < (b - α) / 2)
    (hβ : β₀ ≠ b) (hβw : η < |β₀ - b|)
    (hd1 : α < δ₁) (hη1 : η < δ₁ - α) (hd2 : α < δ₂) (hη2 : η < δ₂ - α) :
    ((truncRank r α (b - η) (α + η) - truncRank r α (b + η) (α + η)) -
      (truncRank r α (b - η) (α - η) - truncRank r α (b + η) (α - η))) = 0 := by
  have hb1 : α ≤ b - η := by linarith
  have hb2 : α ≤ b + η := by linarith
  have ht1 : α ≤ α + η := by linarith
  have ht2 : α - η < α := by linarith
  have hle1 : α + η ≤ b - η := by linarith
  have hle2 : α + η ≤ b + η := by linarith
  have hnd1 : ¬ (δ₁ < α + η) := by linarith
  have hnd2 : ¬ (δ₂ < α + η) := by linarith
  rw [trunc_above r α _ _ hb1 ht1, trunc_above r α _ _ hb2 ht1,
      truncRank_zero_of_lt r α _ _ ht2, truncRank_zero_of_lt r α _ _ ht2,
      hr (b - η) (α + η) hle1, hr (b + η) (α + η) hle2,
      indMort_neg_t β₁ δ₁ (b - η) (α + η) hnd1, indMort_neg_t β₂ δ₂ (b - η) (α + η) hnd2,
      indMort_neg_t β₁ δ₁ (b + η) (α + η) hnd1, indMort_neg_t β₂ δ₂ (b + η) (α + η) hnd2,
      indEss_congr β₀ (b - η) (b + η) (birth_cell β₀ b η hη.le hβ hβw)]
  simp

/-- The α-truncated multiplicity at a real point `(b, d)` with `α ≤ d < b` is zero, provided the
rank `r` has three-term indicator form with essential bar `β₀` and mortal bars `(β₁, δ₁)`,
`(β₂, δ₂)` (both dying strictly above `α`), and the point avoids all three bars. -/
private lemma mult_trunc_eq_zero (r : ℝ → ℝ → ℕ∞) (α β₀ β₁ δ₁ β₂ δ₂ : ℝ)
    (hd1 : α < δ₁) (hd2 : α < δ₂)
    (hr : ∀ s t, t ≤ s → r s t = indEss β₀ s + indMort β₁ δ₁ s t + indMort β₂ δ₂ s t)
    (b d : ℝ) (hbd : d < b) (hda : α ≤ d)
    (h0 : β₀ ≠ b ∨ d ≠ α) (h1 : β₁ ≠ b ∨ d ≠ δ₁) (h2 : β₂ ≠ b ∨ d ≠ δ₂) :
    mult (truncRank r α) (((b : ℝ) : EReal), ((d : ℝ) : EReal)) = 0 := by
  rw [mult_coe_coe (truncRank r α) b d hbd]
  rcases lt_or_eq_of_le hda with hdlt | hde
  · -- Case `α < d`: all four corners lie above `α`.
    set q1 : ℝ := if β₁ = b then |δ₁ - d| else |β₁ - b| with hq1def
    set q2 : ℝ := if β₂ = b then |δ₂ - d| else |β₂ - b| with hq2def
    have hq1pos : 0 < q1 := by
      rw [hq1def]; by_cases hb : β₁ = b
      · rw [if_pos hb]
        rcases h1 with h | h
        · exact absurd hb h
        · exact abs_pos.mpr (sub_ne_zero.mpr (Ne.symm h))
      · rw [if_neg hb]
        exact abs_pos.mpr (sub_ne_zero.mpr hb)
    have hq2pos : 0 < q2 := by
      rw [hq2def]; by_cases hb : β₂ = b
      · rw [if_pos hb]
        rcases h2 with h | h
        · exact absurd hb h
        · exact abs_pos.mpr (sub_ne_zero.mpr (Ne.symm h))
      · rw [if_neg hb]
        exact abs_pos.mpr (sub_ne_zero.mpr hb)
    set M : ℝ := min (min ((b - d) / 2) (d - α)) (min q1 q2) with hMdef
    have hM1 : M ≤ (b - d) / 2 := (min_le_left _ _).trans (min_le_left _ _)
    have hM2 : M ≤ d - α := (min_le_left _ _).trans (min_le_right _ _)
    have hM3 : M ≤ q1 := (min_le_right _ _).trans (min_le_left _ _)
    have hM4 : M ≤ q2 := (min_le_right _ _).trans (min_le_right _ _)
    have hMpos : 0 < M := lt_min (lt_min (by linarith) (by linarith)) (lt_min hq1pos hq2pos)
    set η : ℝ := M / 2 with hηdef
    have hηpos : 0 < η := by linarith
    have hηM : η < M := by linarith
    have hηw : η < (b - d) / 2 := by linarith
    have hh1 : (β₁ ≠ b ∧ η < |β₁ - b|) ∨ (δ₁ ≠ d ∧ η < |δ₁ - d|) := by
      by_cases hb : β₁ = b
      · refine Or.inr ⟨?_, ?_⟩
        · rcases h1 with h | h
          · exact absurd hb h
          · exact h.symm
        · have hq : q1 = |δ₁ - d| := by rw [hq1def, if_pos hb]
          linarith
      · refine Or.inl ⟨hb, ?_⟩
        have hq : q1 = |β₁ - b| := by rw [hq1def, if_neg hb]
        linarith
    have hh2 : (β₂ ≠ b ∧ η < |β₂ - b|) ∨ (δ₂ ≠ d ∧ η < |δ₂ - d|) := by
      by_cases hb : β₂ = b
      · refine Or.inr ⟨?_, ?_⟩
        · rcases h2 with h | h
          · exact absurd hb h
          · exact h.symm
        · have hq : q2 = |δ₂ - d| := by rw [hq2def, if_pos hb]
          linarith
      · refine Or.inl ⟨hb, ?_⟩
        have hq : q2 = |β₂ - b| := by rw [hq2def, if_neg hb]
        linarith
    have hbr : ((truncRank r α (b - η) (d + η) - truncRank r α (b + η) (d + η)) -
        (truncRank r α (b - η) (d - η) - truncRank r α (b + η) (d - η))) = 0 := by
      have hab1 : α ≤ b - η := by linarith
      have hab2 : α ≤ b + η := by linarith
      have had1 : α ≤ d + η := by linarith
      have had2 : α ≤ d - η := by linarith
      rw [trunc_above r α _ _ hab1 had1, trunc_above r α _ _ hab2 had1,
          trunc_above r α _ _ hab1 had2, trunc_above r α _ _ hab2 had2]
      exact bracket_zero_general r β₀ β₁ δ₁ β₂ δ₂ hr b d η hηpos.le hbd hηw hh1 hh2
    refine le_antisymm (iInf_le_of_le η (iInf_le_of_le ⟨hηpos, hηw⟩ hbr.le))
      (zero_le : (0 : ℕ∞) ≤ _)
  · -- Case `d = α`: death exactly at the truncation floor.
    have hβ0 : β₀ ≠ b := by
      rcases h0 with h | h
      · exact h
      · exact (h hde.symm).elim
    set M : ℝ := min (min ((b - d) / 2) (δ₁ - d)) (min (δ₂ - d) |β₀ - b|) with hMdef
    have hM1 : M ≤ (b - d) / 2 := (min_le_left _ _).trans (min_le_left _ _)
    have hM2 : M ≤ δ₁ - d := (min_le_left _ _).trans (min_le_right _ _)
    have hM3 : M ≤ δ₂ - d := (min_le_right _ _).trans (min_le_left _ _)
    have hM4 : M ≤ |β₀ - b| := (min_le_right _ _).trans (min_le_right _ _)
    have hMpos : 0 < M :=
      lt_min (lt_min (by linarith) (by linarith)) (lt_min (by linarith)
        (abs_pos.mpr (sub_ne_zero.mpr hβ0)))
    set η : ℝ := M / 2 with hηdef
    have hηpos : 0 < η := by linarith
    have hηM : η < M := by linarith
    have hηw : η < (b - d) / 2 := by linarith
    have hbr : ((truncRank r α (b - η) (d + η) - truncRank r α (b + η) (d + η)) -
        (truncRank r α (b - η) (d - η) - truncRank r α (b + η) (d - η))) = 0 := by
      rw [← hde]
      exact bracket_zero_alpha r α β₀ β₁ δ₁ β₂ δ₂ b η hr hηpos (by linarith)
        (by linarith) hβ0 (by linarith) hd1 (by linarith) hd2 (by linarith)
    refine le_antisymm (iInf_le_of_le η (iInf_le_of_le ⟨hηpos, hηw⟩ hbr.le))
      (zero_le : (0 : ℕ∞) ≤ _)

/-- Two real-coefficient points of the extended plane are distinct iff a birth or death
coordinate differs (oriented to match `mult_trunc_eq_zero`). -/
private lemma coe_pair_ne_iff (b d bi di : ℝ) :
    (((b : ℝ) : EReal), ((d : ℝ) : EReal)) ≠ (((bi : ℝ) : EReal), ((di : ℝ) : EReal)) ↔
      bi ≠ b ∨ d ≠ di := by
  constructor
  · intro h
    by_cases hb : bi = b
    · refine Or.inr (fun hd => h ?_)
      rw [← hb, ← hd]
    · exact Or.inl hb
  · rintro (hb | hd) h
    · exact hb (EReal.coe_eq_coe_iff.mp (Prod.ext_iff.mp h).1).symm
    · exact hd (EReal.coe_eq_coe_iff.mp (Prod.ext_iff.mp h).2)

/-- Generic truncated-support bound: the `(-2)`-truncated diagram of a rank function with
essential bar `(5, ⊥)` and mortal bars `(bi₁, di₁)`, `(bi₂, di₂)` (both dying above `−2`) is
supported on `{(5,−2), (bi₁,di₁), (bi₂,di₂)}`. -/
private lemma trunc_support_of (r : ℝ → ℝ → ℕ∞) (bi1 di1 bi2 di2 : ℝ)
    (hdi1 : (-2 : ℝ) < di1) (hdi2 : (-2 : ℝ) < di2)
    (hr : ∀ s t, t ≤ s → r s t = indEss 5 s + indMort bi1 di1 s t + indMort bi2 di2 s t)
    (p : EReal × EReal) (hp : mult (truncRank r (-2)) p ≠ 0) :
    p ∈ ({(((5 : ℝ) : EReal), ((-2 : ℝ) : EReal)),
          (((bi1 : ℝ) : EReal), ((di1 : ℝ) : EReal)),
          (((bi2 : ℝ) : EReal), ((di2 : ℝ) : EReal))} : Set (EReal × EReal)) := by
  by_contra hmem
  apply hp
  obtain ⟨x, y⟩ := p
  induction x using EReal.rec with
  | bot => exact mult_zero_of_born _ _ (Or.inl rfl)
  | top => exact mult_zero_of_born _ _ (Or.inr rfl)
  | coe b =>
    induction y using EReal.rec with
    | bot => exact mult_trunc_bot_zero r (-2) b
    | top => exact mult_coe_top_zero _ b
    | coe d =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      push_neg at hmem
      obtain ⟨hne1, hne2, hne3⟩ := hmem
      have h0 := (coe_pair_ne_iff b d 5 (-2)).mp hne1
      have h1 := (coe_pair_ne_iff b d bi1 di1).mp hne2
      have h2 := (coe_pair_ne_iff b d bi2 di2).mp hne3
      by_cases hbd : d < b
      · by_cases hda : d < (-2)
        · exact mult_trunc_lt_zero r (-2) b d hbd hda
        · push_neg at hda
          exact mult_trunc_eq_zero r (-2) 5 bi1 di1 bi2 di2 hdi1 hdi2 hr b d hbd hda h0 h1 h2
      · push_neg at hbd
        exact mult_coe_coe_le_zero _ b d hbd

/-- The `(-2)`-truncated X diagram is supported on `{(5,−2), (4.2,0.5), (2.5,−0.6)}`. -/
theorem truncX_support (p : EReal × EReal)
    (hp : mult (truncRank (rankFn stageX JX) (-2)) p ≠ 0) :
    p ∈ ({(((5 : ℝ) : EReal), ((-2 : ℝ) : EReal)),
          (((4.2 : ℝ) : EReal), ((0.5 : ℝ) : EReal)),
          (((2.5 : ℝ) : EReal), ((-0.6 : ℝ) : EReal))} : Set (EReal × EReal)) :=
  trunc_support_of (rankFn stageX JX) 4.2 0.5 2.5 (-0.6)
    (by norm_num : (-2 : ℝ) < 0.5) (by norm_num : (-2 : ℝ) < (-0.6)) rankX_eq p hp

/-- The `(-2)`-truncated Y diagram is supported on `{(5,−2), (3.2,−1.5), (1.6,0.3)}`. -/
theorem truncY_support (p : EReal × EReal)
    (hp : mult (truncRank (rankFn stageY JY) (-2)) p ≠ 0) :
    p ∈ ({(((5 : ℝ) : EReal), ((-2 : ℝ) : EReal)),
          (((3.2 : ℝ) : EReal), ((-1.5 : ℝ) : EReal)),
          (((1.6 : ℝ) : EReal), ((0.3 : ℝ) : EReal))} : Set (EReal × EReal)) :=
  trunc_support_of (rankFn stageY JY) 3.2 (-1.5) 1.6 0.3
    (by norm_num : (-2 : ℝ) < (-1.5)) (by norm_num : (-2 : ℝ) < 0.3) rankY_eq p hp

/-! ### Step 6: diagram-like and finite-support hypotheses (the stub's `hDiag`/`hFin`) -/

/-- The plain rank multiplicity is a genuine diagram (death strictly below birth off the
diagonal) — direct instance of the general fact. -/
theorem hDiagX : IsDiagramLike (mult (rankFn stageX JX)) := isDiagramLike_mult _
theorem hDiagY : IsDiagramLike (mult (rankFn stageY JY)) := isDiagramLike_mult _

/-- Negation of a `closeE` corner between two real-coefficient points (left conjunct:
the first argument must satisfy `a ≤ b + 1`). -/
private lemma not_closeE_coe_left (a b : ℝ) (h : ¬ (a ≤ b + 1)) :
    ¬ closeE ((a:ℝ):EReal) ((b:ℝ):EReal) 1 := by
  rintro ⟨h1, _⟩
  rw [← EReal.coe_add, EReal.coe_le_coe_iff] at h1
  exact h h1

/-- Negation of a `closeE` corner between two real-coefficient points (right conjunct:
the second argument must satisfy `b ≤ a + 1`). -/
private lemma not_closeE_coe_right (a b : ℝ) (h : ¬ (b ≤ a + 1)) :
    ¬ closeE ((a:ℝ):EReal) ((b:ℝ):EReal) 1 := by
  rintro ⟨_, h2⟩
  rw [← EReal.coe_add, EReal.coe_le_coe_iff] at h2
  exact h h2

/-! ### Step 6 (cont.): plain finite-support bounds (`hFinX`/`hFinY`) -/

/-- A real-born point `(b,d)` with `d < b`, distinct (as a pair) from both mortal bars, has plain
multiplicity zero — the four-corner bracket vanishes by `bracket_zero_general` (the essential-bar
contribution cancels, the mortal cells are congruent). Mirrors `mult_trunc_eq_zero`'s
above-the-floor case at the plain rank. -/
private lemma mult_plain_eq_zero (r : ℝ → ℝ → ℕ∞) (β₀ β₁ δ₁ β₂ δ₂ : ℝ)
    (hr : ∀ s t, t ≤ s → r s t = indEss β₀ s + indMort β₁ δ₁ s t + indMort β₂ δ₂ s t)
    (b d : ℝ) (hbd : d < b)
    (h1 : β₁ ≠ b ∨ d ≠ δ₁) (h2 : β₂ ≠ b ∨ d ≠ δ₂) :
    mult r (((b : ℝ) : EReal), ((d : ℝ) : EReal)) = 0 := by
  rw [mult_coe_coe r b d hbd]
  set q1 : ℝ := if β₁ = b then |δ₁ - d| else |β₁ - b| with hq1def
  set q2 : ℝ := if β₂ = b then |δ₂ - d| else |β₂ - b| with hq2def
  have hq1pos : 0 < q1 := by
    rw [hq1def]; by_cases hb : β₁ = b
    · rw [if_pos hb]
      rcases h1 with h | h
      · exact absurd hb h
      · exact abs_pos.mpr (sub_ne_zero.mpr (Ne.symm h))
    · rw [if_neg hb]
      exact abs_pos.mpr (sub_ne_zero.mpr hb)
  have hq2pos : 0 < q2 := by
    rw [hq2def]; by_cases hb : β₂ = b
    · rw [if_pos hb]
      rcases h2 with h | h
      · exact absurd hb h
      · exact abs_pos.mpr (sub_ne_zero.mpr (Ne.symm h))
    · rw [if_neg hb]
      exact abs_pos.mpr (sub_ne_zero.mpr hb)
  set M : ℝ := min ((b - d) / 2) (min q1 q2) with hMdef
  have hM1 : M ≤ (b - d) / 2 := min_le_left _ _
  have hM3 : M ≤ q1 := (min_le_right _ _).trans (min_le_left _ _)
  have hM4 : M ≤ q2 := (min_le_right _ _).trans (min_le_right _ _)
  have hMpos : 0 < M := lt_min (by linarith) (lt_min hq1pos hq2pos)
  set η : ℝ := M / 2 with hηdef
  have hηpos : 0 < η := by linarith
  have hηM : η < M := by linarith
  have hηw : η < (b - d) / 2 := by linarith
  have hh1 : (β₁ ≠ b ∧ η < |β₁ - b|) ∨ (δ₁ ≠ d ∧ η < |δ₁ - d|) := by
    by_cases hb : β₁ = b
    · refine Or.inr ⟨?_, ?_⟩
      · rcases h1 with h | h
        · exact absurd hb h
        · exact h.symm
      · have hq : q1 = |δ₁ - d| := by rw [hq1def, if_pos hb]
        linarith
    · refine Or.inl ⟨hb, ?_⟩
      have hq : q1 = |β₁ - b| := by rw [hq1def, if_neg hb]
      linarith
  have hh2 : (β₂ ≠ b ∧ η < |β₂ - b|) ∨ (δ₂ ≠ d ∧ η < |δ₂ - d|) := by
    by_cases hb : β₂ = b
    · refine Or.inr ⟨?_, ?_⟩
      · rcases h2 with h | h
        · exact absurd hb h
        · exact h.symm
      · have hq : q2 = |δ₂ - d| := by rw [hq2def, if_pos hb]
        linarith
    · refine Or.inl ⟨hb, ?_⟩
      have hq : q2 = |β₂ - b| := by rw [hq2def, if_neg hb]
      linarith
  have hbr : ((r (b - η) (d + η) - r (b + η) (d + η)) -
      (r (b - η) (d - η) - r (b + η) (d - η))) = 0 :=
    bracket_zero_general r β₀ β₁ δ₁ β₂ δ₂ hr b d η hηpos.le hbd hηw hh1 hh2
  refine le_antisymm (iInf_le_of_le η (iInf_le_of_le ⟨hηpos, hηw⟩ hbr.le))
    (zero_le : (0 : ℕ∞) ≤ _)

/-- The essential bar contributes plain multiplicity only at its own birth: a real-born point
dying at `⊥` whose birth differs from `β₀` has plain multiplicity zero (the essential indicator
cancels across the birth window, and the mortal bars — born at most `β₀` — are inactive in a
window that avoids `β₀`). -/
private lemma mult_coe_bot_zero_of_ne (r : ℝ → ℝ → ℕ∞) (β₀ β₁ δ₁ β₂ δ₂ : ℝ)
    (hβ₁ : β₁ ≤ β₀) (hβ₂ : β₂ ≤ β₀)
    (hr : ∀ s t, t ≤ s → r s t = indEss β₀ s + indMort β₁ δ₁ s t + indMort β₂ δ₂ s t)
    (b : ℝ) (hb : b ≠ β₀) :
    mult r (((b : ℝ) : EReal), (⊥ : EReal)) = 0 := by
  rw [mult_coe_bot r b]
  refine le_antisymm ?_ (le_iInf fun _ => le_iInf fun _ => le_iInf fun _ => le_iInf fun _ =>
    (zero_le : (0 : ℕ∞) ≤ _))
  by_cases hnb : b < β₀
  · -- birth below the essential bar: the essential indicator is `1` at both window ends and the
    -- mortal bars are inactive below all deaths.
    set η : ℝ := (β₀ - b) / 2 with hηdef
    have hηpos : 0 < η := by linarith
    have hb1 : (b - η : ℝ) ≤ β₀ := by linarith
    have hb2 : (b + η : ℝ) ≤ β₀ := by linarith
    set t : ℝ := min (min (b - η) δ₁) δ₂ with htdef
    have htb : t ≤ b - η := (min_le_left _ _).trans (min_le_left _ _)
    have ht1 : t ≤ δ₁ := (min_le_left _ _).trans (min_le_right _ _)
    have ht2 : t ≤ δ₂ := min_le_right _ _
    have hA : r (b - η) t = 1 := by
      rw [hr (b - η) t htb, indEss_pos β₀ (b - η) hb1,
          indMort_neg_t β₁ δ₁ (b - η) t (not_lt.mpr ht1),
          indMort_neg_t β₂ δ₂ (b - η) t (not_lt.mpr ht2)]
      decide
    have hB : r (b + η) t = 1 := by
      have htb2 : t ≤ b + η := htb.trans (by linarith)
      rw [hr (b + η) t htb2, indEss_pos β₀ (b + η) hb2,
          indMort_neg_t β₁ δ₁ (b + η) t (not_lt.mpr ht1),
          indMort_neg_t β₂ δ₂ (b + η) t (not_lt.mpr ht2)]
      decide
    have hzero : r (b - η) t - r (b + η) t = 0 := by rw [hA, hB, tsub_self]
    exact iInf_le_of_le η (iInf_le_of_le hηpos
      (iInf_le_of_le t (iInf_le_of_le htb hzero.le)))
  · -- birth above the essential bar: the whole window lies above `β₀` and every bar.
    rcases lt_or_eq_of_le (not_lt.mp hnb) with hb0 | hb0
    · set η : ℝ := (b - β₀) / 2 with hηdef
      have hηpos : 0 < η := by linarith
      have hb1 : β₀ < b - η := by linarith
      have hb2 : β₀ < b + η := by linarith
      have hA : r (b - η) (b - η) = 0 := by
        rw [hr (b - η) (b - η) le_rfl, indEss_neg β₀ (b - η) (not_le.mpr hb1),
            indMort_neg_s β₁ δ₁ (b - η) (b - η) (not_le.mpr (lt_of_le_of_lt hβ₁ hb1)),
            indMort_neg_s β₂ δ₂ (b - η) (b - η) (not_le.mpr (lt_of_le_of_lt hβ₂ hb1))]
        decide
      have hB : r (b + η) (b - η) = 0 := by
        rw [hr (b + η) (b - η) (by linarith : (b - η : ℝ) ≤ b + η),
            indEss_neg β₀ (b + η) (not_le.mpr hb2),
            indMort_neg_s β₁ δ₁ (b + η) (b - η) (not_le.mpr (lt_of_le_of_lt hβ₁ hb2)),
            indMort_neg_s β₂ δ₂ (b + η) (b - η) (not_le.mpr (lt_of_le_of_lt hβ₂ hb2))]
        decide
      have hzero : r (b - η) (b - η) - r (b + η) (b - η) = 0 := by rw [hA, hB, tsub_self]
      exact iInf_le_of_le η (iInf_le_of_le hηpos
        (iInf_le_of_le (b - η) (iInf_le_of_le le_rfl hzero.le)))
    · exact absurd hb0 (Ne.symm hb)

/-- Generic plain-support bound: the plain diagram of a rank function with essential bar
`(β₀, ⊥)` and mortal bars `(β₁,δ₁)`, `(β₂,δ₂)` (both born at most `β₀`) is supported on
`{(β₀,⊥), (β₁,δ₁), (β₂,δ₂)}`. Mirrors `trunc_support_of` at the plain rank. -/
private lemma plain_support_of (r : ℝ → ℝ → ℕ∞) (β₀ β₁ δ₁ β₂ δ₂ : ℝ)
    (hβ₁ : β₁ ≤ β₀) (hβ₂ : β₂ ≤ β₀)
    (hr : ∀ s t, t ≤ s → r s t = indEss β₀ s + indMort β₁ δ₁ s t + indMort β₂ δ₂ s t)
    (p : EReal × EReal) (hp : mult r p ≠ 0) :
    p ∈ ({(((β₀ : ℝ) : EReal), (⊥ : EReal)),
          (((β₁ : ℝ) : EReal), ((δ₁ : ℝ) : EReal)),
          (((β₂ : ℝ) : EReal), ((δ₂ : ℝ) : EReal))} : Set (EReal × EReal)) := by
  by_contra hmem
  apply hp
  obtain ⟨x, y⟩ := p
  induction x using EReal.rec with
  | bot => exact mult_zero_of_born _ _ (Or.inl rfl)
  | top => exact mult_zero_of_born _ _ (Or.inr rfl)
  | coe b =>
    induction y using EReal.rec with
    | bot =>
      have hbne : b ≠ β₀ := by
        intro hbe
        apply hmem
        rw [hbe]
        exact Set.mem_insert_iff.mpr (Or.inl rfl)
      exact mult_coe_bot_zero_of_ne r β₀ β₁ δ₁ β₂ δ₂ hβ₁ hβ₂ hr b hbne
    | top => exact mult_coe_top_zero _ b
    | coe d =>
      have h1 : β₁ ≠ b ∨ d ≠ δ₁ := by
        by_cases hbb : β₁ = b
        · refine Or.inr ?_
          intro hdd
          apply hmem
          rw [← hbb, hdd]
          exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_insert_iff.mpr (Or.inl rfl)))
        · exact Or.inl hbb
      have h2 : β₂ ≠ b ∨ d ≠ δ₂ := by
        by_cases hbb : β₂ = b
        · refine Or.inr ?_
          intro hdd
          apply hmem
          rw [← hbb, hdd]
          exact Set.mem_insert_iff.mpr
            (Or.inr (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr rfl))))
        · exact Or.inl hbb
      by_cases hbd : d < b
      · exact mult_plain_eq_zero r β₀ β₁ δ₁ β₂ δ₂ hr b d hbd h1 h2
      · exact mult_coe_coe_le_zero _ b d (not_lt.mp hbd)

/-- The plain X diagram is supported on `{(5,⊥), (4.2,0.5), (2.5,−0.6)}`, hence finite. -/
theorem hFinX : {p : EReal × EReal | (mult (rankFn stageX JX)) p ≠ 0}.Finite := by
  have hsub : {p : EReal × EReal | (mult (rankFn stageX JX)) p ≠ 0} ⊆
      ({(((5 : ℝ) : EReal), (⊥ : EReal)),
        (((4.2 : ℝ) : EReal), ((0.5 : ℝ) : EReal)),
        (((2.5 : ℝ) : EReal), ((-0.6 : ℝ) : EReal))} : Set (EReal × EReal)) := by
    intro p hp
    exact plain_support_of (rankFn stageX JX) 5 4.2 0.5 2.5 (-0.6)
      (by norm_num : (4.2 : ℝ) ≤ 5) (by norm_num : (2.5 : ℝ) ≤ 5) rankX_eq p hp
  have hSfin : ({(((5 : ℝ) : EReal), (⊥ : EReal)),
        (((4.2 : ℝ) : EReal), ((0.5 : ℝ) : EReal)),
        (((2.5 : ℝ) : EReal), ((-0.6 : ℝ) : EReal))} : Set (EReal × EReal)).Finite := by
    refine Set.finite_insert.mpr ?_
    refine Set.finite_insert.mpr ?_
    exact Set.finite_singleton _
  exact hSfin.subset hsub

/-- The plain Y diagram is supported on `{(5,⊥), (3.2,−1.5), (1.6,0.3)}`, hence finite. -/
theorem hFinY : {p : EReal × EReal | (mult (rankFn stageY JY)) p ≠ 0}.Finite := by
  have hsub : {p : EReal × EReal | (mult (rankFn stageY JY)) p ≠ 0} ⊆
      ({(((5 : ℝ) : EReal), (⊥ : EReal)),
        (((3.2 : ℝ) : EReal), ((-1.5 : ℝ) : EReal)),
        (((1.6 : ℝ) : EReal), ((0.3 : ℝ) : EReal))} : Set (EReal × EReal)) := by
    intro p hp
    exact plain_support_of (rankFn stageY JY) 5 3.2 (-1.5) 1.6 0.3
      (by norm_num : (3.2 : ℝ) ≤ 5) (by norm_num : (1.6 : ℝ) ≤ 5) rankY_eq p hp
  have hSfin : ({(((5 : ℝ) : EReal), (⊥ : EReal)),
        (((3.2 : ℝ) : EReal), ((-1.5 : ℝ) : EReal)),
        (((1.6 : ℝ) : EReal), ((0.3 : ℝ) : EReal))} : Set (EReal × EReal)).Finite := by
    refine Set.finite_insert.mpr ?_
    refine Set.finite_insert.mpr ?_
    exact Set.finite_singleton _
  exact hSfin.subset hsub

/-! ### Step 8: the witness contradiction -/

/-- No copy of the Y-truncated diagram — off-diagonal or diagonal — is `1`-close to the point
`(4.2, 0.5)`: the off-diagonal support is `{(5,−2),(3.2,−1.5),(1.6,0.3)}`, none of whose points
is `1`-close, and the diagonal is disjoint from the box `[3.2,5.2] × [−0.5,1.5]`. -/
private lemma no_close_partner (c : Copies (mult (truncRank (rankFn stageY JY) (-2))))
    (h1 : closeE ((4.2 : ℝ) : EReal) (pt c).1 1)
    (h2 : closeE ((0.5 : ℝ) : EReal) (pt c).2 1) : False := by
  rcases c with q' | ⟨y1, y2⟩
  · -- off-diagonal copy: `pt c = q'.val.1`, the underlying Y point.
    have hp' : (q'.val.2 : ℕ∞) < mult (truncRank (rankFn stageY JY) (-2)) q'.val.1 := q'.property
    have hne : mult (truncRank (rankFn stageY JY) (-2)) q'.val.1 ≠ 0 := by
      intro h0
      rw [h0] at hp'
      first
        | exact absurd (lt_of_le_of_lt (zero_le ((q'.val.2 : ℕ∞))) hp') (lt_irrefl (0 : ℕ∞))
        | exact absurd hp' (by simp)
    change closeE ((4.2 : ℝ) : EReal) q'.val.1.1 1 at h1
    change closeE ((0.5 : ℝ) : EReal) q'.val.1.2 1 at h2
    rcases Set.mem_insert_iff.mp (truncY_support q'.val.1 hne) with heq | hmem
    · rw [heq] at h1 h2
      exact not_closeE_coe_left 0.5 (-2) (by norm_num) h2
    · rcases Set.mem_insert_iff.mp hmem with heq | hmem
      · rw [heq] at h1 h2
        exact not_closeE_coe_left 0.5 (-1.5) (by norm_num) h2
      · rw [Set.mem_singleton_iff] at hmem
        rw [hmem] at h1 h2
        exact not_closeE_coe_left 4.2 1.6 (by norm_num) h1
  · -- diagonal copy: `pt c = (y1, y1)`, forcing `y1` into two disjoint intervals.
    change closeE ((4.2 : ℝ) : EReal) y1 1 at h1
    change closeE ((0.5 : ℝ) : EReal) y1 1 at h2
    obtain ⟨h1a, h1b⟩ := h1
    obtain ⟨h2a, h2b⟩ := h2
    induction y1 using EReal.rec with
    | bot =>
      rw [EReal.bot_add] at h1a
      exact absurd h1a (not_le.mpr (EReal.bot_lt_coe 4.2))
    | top =>
      rw [← EReal.coe_add] at h2b
      exact absurd h2b (not_le.mpr (EReal.coe_lt_top (0.5 + 1)))
    | coe v =>
      rw [← EReal.coe_add, EReal.coe_le_coe_iff] at h1a
      rw [← EReal.coe_add, EReal.coe_le_coe_iff] at h2b
      linarith

/-- Step 8: the forward closeness clause of the asserted multi-bijection fails at the witness
copy of the X-truncated bar `(4.2, 0.5)`. -/
theorem trunc_closeE_false
    (δ : Copies (mult (truncRank (rankFn stageX JX) (-2))) ≃
         Copies (mult (truncRank (rankFn stageY JY) (-2))))
    (hfwd : ∀ a, closeE (pt a).1 (pt (δ a)).1 1 ∧ closeE (pt a).2 (pt (δ a)).2 1) : False := by
  have hz : ((0 : ℕ) : ℕ∞) < mult (truncRank (rankFn stageX JX) (-2))
      (((4.2 : ℝ) : EReal), ((0.5 : ℝ) : EReal)) := by
    rw [Nat.cast_zero, multTruncX_42]
    first
      | exact zero_lt_one
      | decide
      | simp
  set a : Copies (mult (truncRank (rankFn stageX JX) (-2))) :=
    Sum.inl ⟨⟨(((4.2 : ℝ) : EReal), ((0.5 : ℝ) : EReal)), (0 : ℕ)⟩, hz⟩ with hadef
  obtain ⟨hf1, hf2⟩ := hfwd a
  have hpa1 : (pt a).1 = ((4.2 : ℝ) : EReal) := by rw [hadef]; rfl
  have hpa2 : (pt a).2 = ((0.5 : ℝ) : EReal) := by rw [hadef]; rfl
  rw [hpa1] at hf1
  rw [hpa2] at hf2
  exact no_close_partner (δ a) hf1 hf2

/-! ### Step 9: the falsified published theorem -/

set_option linter.unusedVariables false in
/-- **The published `theorem_4_5_lemma_4_6_corrected_stability_qtame` is FALSE.**

Instantiate its hypothesis list at `ιX = Fin 3`, `stageX`/`JX` (the (5,⊥),(4.2,0.5),(2.5,−0.6)
module) and `ιY = Fin 3`, `stageY`/`JY` (the (5,⊥),(3.2,−1.5),(1.6,0.3) module), with truncation
level `α = −2` and radius `ε = 1`. Every hypothesis is satisfiable here:
`hLawX`/`hLawY` (genuine `FiltrationLaw` modules), `hQX`/`hQY`, `hTameX`/`hTameY`, `hbox`
(the `α = −2`, `ε = 1` box-expansion interleaving), `hDiagX`/`hDiagY`, `hFinX`/`hFinY` — all
proven as named theorems above. Yet the asserted multi-bijection of copies with `ε`-close
control fails: the X-truncated bar `(4.2, 0.5)` has no `1`-close partner among Y's truncated
support `{(5,−2),(3.2,−1.5),(1.6,0.3)}`, nor on the diagonal. Hence rank-level hypotheses do NOT
imply the module-level conclusion. The binder order mirrors the published stub character by
character, with `α := −2` and `ε := 1`. -/
theorem stability_qtame_false
    (hε : (0 : ℝ) ≤ 1)
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    (hQX : ∀ s t : ℝ, rankFn stageX JX s t ≠ ⊤)
    (hQY : ∀ s t : ℝ, rankFn stageY JY s t ≠ ⊤)
    (hTameX : ∃ s₀ : ℝ, ∀ s ≥ s₀, stageX s = ∅)
    (hTameY : ∃ s₀ : ℝ, ∀ s ≥ s₀, stageY s = ∅)
    (hbox : ∀ s t : ℝ, t + 2 * 1 ≤ s →
      truncRank (rankFn stageX JX) (-2) s t ≤ truncRank (rankFn stageY JY) (-2) (s - 1) (t + 1) ∧
      truncRank (rankFn stageY JY) (-2) s t ≤ truncRank (rankFn stageX JX) (-2) (s - 1) (t + 1))
    (hDiagX : IsDiagramLike (mult (rankFn stageX JX)))
    (hDiagY : IsDiagramLike (mult (rankFn stageY JY)))
    (hFinX : {p : EReal × EReal | (mult (rankFn stageX JX)) p ≠ 0}.Finite)
    (hFinY : {p : EReal × EReal | (mult (rankFn stageY JY)) p ≠ 0}.Finite) :
    (∃ δ : Copies (mult (truncRank (rankFn stageX JX) (-2)))
        ≃ Copies (mult (truncRank (rankFn stageY JY) (-2))),
      (∀ a, closeE (pt a).1 (pt (δ a)).1 1 ∧ closeE (pt a).2 (pt (δ a)).2 1) ∧
      (∀ b, closeE (pt (δ.symm b)).1 (pt b).1 1 ∧ closeE (pt (δ.symm b)).2 (pt b).2 1)) →
    False := by
  rintro ⟨δ, hfwd, _⟩
  exact trunc_closeE_false δ hfwd

set_option linter.unusedVariables false in
/-- **Third refutation**: `theorem_4_5_lemma_4_6_corrected_stability_tame` (the `IsTame0`
corrected stability child) is FALSE. Its hypothesis list is the qtame sibling's list WITHOUT
the q-tameness clauses `hQX`/`hQY` — and the instance above satisfies every remaining
hypothesis (including `hTameX`/`hTameY` with `s₀ = 6`, verified as the named `hTameX`/`hTameY`
theorems), while the refutation core `trunc_closeE_false` never uses `hQX`/`hQY`. The same
witness `(4.2, 0.5)` has no 1-close partner in Y's truncated support nor on the diagonal.
Binder order mirrors the published stability_tame stub character by character, with
`α := −2` and `ε := 1`. -/
theorem stability_tame_false
    (hε : (0 : ℝ) ≤ 1)
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    (hTameX : ∃ s₀ : ℝ, ∀ s ≥ s₀, stageX s = ∅)
    (hTameY : ∃ s₀ : ℝ, ∀ s ≥ s₀, stageY s = ∅)
    (hbox : ∀ s t : ℝ, t + 2 * 1 ≤ s →
      truncRank (rankFn stageX JX) (-2) s t ≤ truncRank (rankFn stageY JY) (-2) (s - 1) (t + 1) ∧
      truncRank (rankFn stageY JY) (-2) s t ≤ truncRank (rankFn stageX JX) (-2) (s - 1) (t + 1))
    (hDiagX : IsDiagramLike (mult (rankFn stageX JX)))
    (hDiagY : IsDiagramLike (mult (rankFn stageY JY)))
    (hFinX : {p : EReal × EReal | (mult (rankFn stageX JX)) p ≠ 0}.Finite)
    (hFinY : {p : EReal × EReal | (mult (rankFn stageY JY)) p ≠ 0}.Finite) :
    (∃ δ : Copies (mult (truncRank (rankFn stageX JX) (-2)))
        ≃ Copies (mult (truncRank (rankFn stageY JY) (-2))),
      (∀ a, closeE (pt a).1 (pt (δ a)).1 1 ∧ closeE (pt a).2 (pt (δ a)).2 1) ∧
      (∀ b, closeE (pt (δ.symm b)).1 (pt b).1 1 ∧ closeE (pt (δ.symm b)).2 (pt b).2 1)) →
    False := by
  rintro ⟨δ, hfwd, _⟩
  exact trunc_closeE_false δ hfwd

end

end StabQCE28

/-! ## Platform disproof form (a verified proof of the negation of the target type)

`solution` below proves the negation of the published statement of
`PersistClust.Count.theorem_4_5_lemma_4_6_corrected_stability_qtame` (verbatim binder list and
conclusion, negated). The type variables are fixed at universe 0 (`Type`), the universe of the
explicit counterexample instance: modules over `Fin 3`, truncation level `α = −2`, radius
`ε = 1`. Since the published theorem is universe-polymorphic, refuting its universe-0
restriction refutes it. All hypotheses hold at the instance (the named theorems `hLawX` …
`hFinY` above, including `hQX`/`hQY`, `hTameX`/`hTameY` and the box-expansion `hbox_holds`)
and the asserted multi-bijection is impossible there (`stability_qtame_false`,
`trunc_closeE_false`, `no_close_partner`). -/

open StabQCE28

set_option maxHeartbeats 2000000 in
/-- DISPROOF of `theorem_4_5_lemma_4_6_corrected_stability_qtame`: the negation of its full
published statement (at universe 0, where the explicit two-module counterexample of this file
lives). Every hypothesis holds at the instance — genuine `FiltrationLaw` modules, all
structure ranks finite (`hQX`/`hQY`), stage-tameness at `s₀ = 6` (`hTameX`/`hTameY`), and the
`α = −2`, `ε = 1` box-expansion interleaving of the truncated ranks (`hbox_holds`) — yet the
asserted multi-bijection of truncated copies with `ε`-close control fails: X's truncated bar
`(4.2, 0.5)` has no `1`-close partner among Y's truncated support `{(5, −2), (3.2, −1.5),
(1.6, 0.3)}`, nor on the diagonal (`no_close_partner`, capstone `stability_qtame_false`). -/

theorem solution : ¬ ∀ {ιX : Type} (stageX : ℝ → Set ιX) (JX : ℝ → ιX → ιX → Prop)
    {ιY : Type} (stageY : ℝ → Set ιY) (JY : ℝ → ιY → ιY → Prop)
    (α ε : ℝ) (hε : 0 ≤ ε)
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    (hQX : ∀ s t : ℝ, rankFn stageX JX s t ≠ ⊤)
    (hQY : ∀ s t : ℝ, rankFn stageY JY s t ≠ ⊤)
    (hTameX : ∃ s₀ : ℝ, ∀ s ≥ s₀, stageX s = ∅)
    (hTameY : ∃ s₀ : ℝ, ∀ s ≥ s₀, stageY s = ∅)
    (hbox : ∀ s t : ℝ, t + 2 * ε ≤ s →
      truncRank (rankFn stageX JX) α s t ≤ truncRank (rankFn stageY JY) α (s - ε) (t + ε) ∧
      truncRank (rankFn stageY JY) α s t ≤ truncRank (rankFn stageX JX) α (s - ε) (t + ε))
    (hDiagX : IsDiagramLike (mult (rankFn stageX JX)))
    (hDiagY : IsDiagramLike (mult (rankFn stageY JY)))
    (hFinX : {p : EReal × EReal | (mult (rankFn stageX JX)) p ≠ 0}.Finite)
    (hFinY : {p : EReal × EReal | (mult (rankFn stageY JY)) p ≠ 0}.Finite),
    ∃ δ : Copies (mult (truncRank (rankFn stageX JX) α))
        ≃ Copies (mult (truncRank (rankFn stageY JY) α)),
      (∀ a, closeE (pt a).1 (pt (δ a)).1 ε ∧ closeE (pt a).2 (pt (δ a)).2 ε) ∧
      (∀ b, closeE (pt (δ.symm b)).1 (pt b).1 ε ∧ closeE (pt (δ.symm b)).2 (pt b).2 ε) := by
  intro h
  exact stability_qtame_false zero_le_one hLawX hLawY hQX hQY hTameX hTameY hbox_holds
    hDiagX hDiagY hFinX hFinY
    (h stageX JX stageY JY (-2) 1 zero_le_one hLawX hLawY hQX hQY hTameX hTameY hbox_holds
      hDiagX hDiagY hFinX hFinY)
