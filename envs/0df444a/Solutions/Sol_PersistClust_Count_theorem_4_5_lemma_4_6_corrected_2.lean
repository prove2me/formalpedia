-- Prove2me | solution 2 for PersistClust.Count.theorem_4_5_lemma_4_6_corrected
-- status  : ACCEPTED   (disprove)
-- author  : @fabianroll
-- created : 2026-10-10T08:50:00.639615+00:00
-- url     : https://prove2.me/submissions/d4880aed-c8ae-468e-99ae-c001166d11d3

import Mathlib
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_TruncRank

/-! ## Machine-verified counterexample refuting BOTH
`theorem_4_5_lemma_4_6_corrected_surgery_qtame` and its parent
`theorem_4_5_lemma_4_6_corrected` (α = 0, ε = 1).

Two genuine 3-point merge-tree modules (`FiltrationLaw`) whose α-truncated diagrams are
ε-bijection-equivalent (`hδ`) and whose rank functions satisfy the rank-window interleaving
(`hbx`), with all q-tameness / diagram / finite-support / agreement hypotheses — yet the
asserted multi-bijection `γ` of copies of the ORIGINAL diagrams with ε-close control
(`SatisfiesIIV`) FAILS.

* **X** (values ![20, 10, 0.5]; merge of everything below 0.5): barcode
  `{(10, 0.5)[1], (20, ⊥)[1]}`.
* **Y** (values ![20, 10, −1]; merge of everything below −1): barcode
  `{(10, −1)[1], (20, ⊥)[1]}`.

Root cause: Y's bar `(10, −1)` dies FAR BELOW α = 0. Its truncated copy clamps to the
α-row `(10, 0)` — invisible to `hδ` (which matches it to X's truncated `(10, 0.5)`), and
invisible to `hbx` (whose window `t + 2ε ≤ s, α ≤ t` never probes deaths below α). But the
conclusion's `SatisfiesIIV` demands an ε-close ORIGINAL partner for X's QNE point
`(10, 0.5)`: Y's only candidates — `(10, −1)`, `(20, ⊥)`, and the diagonal — all fail
`closeE` at radius 1. No `γ` exists. The published statements are FALSE. -/

open PersistClust.Count

namespace SurgQCE55

noncomputable section

/-! ### Module X : barcode (20, ⊥), (10, 0.5) -/

/-- Point 0 = the global peak (prominence 20), point 1 = the secondary peak (born 10),
point 2 = the bridge (at level 0.5). -/
def fX : Fin 3 → ℝ := fun i => if i = 0 then 20 else if i = 1 then 10 else 0.5
def stageX (s : ℝ) : Set (Fin 3) := {i | s ≤ fX i}
def JX (t : ℝ) (x y : Fin 3) : Prop :=
  x ∈ stageX t ∧ y ∈ stageX t ∧ (x = y ∨ t ≤ 0.5)

/-! ### Module Y : barcode (20, ⊥), (10, −1) -/

/-- Same shape as X, but the secondary peak's bridge sits at level −1, far below α = 0. -/
def fY : Fin 3 → ℝ := fun i => if i = 0 then 20 else if i = 1 then 10 else -1
def stageY (s : ℝ) : Set (Fin 3) := {i | s ≤ fY i}
def JY (t : ℝ) (x y : Fin 3) : Prop :=
  x ∈ stageY t ∧ y ∈ stageY t ∧ (x = y ∨ t ≤ -1)

lemma fX_zero : fX 0 = 20 := by simp [fX]
lemma fX_one : fX 1 = 10 := by simp [fX]
lemma fX_two : fX 2 = 0.5 := by simp [fX]
lemma fY_zero : fY 0 = 20 := by simp [fY]
lemma fY_one : fY 1 = 10 := by simp [fY]
lemma fY_two : fY 2 = -1 := by simp [fY]

lemma mem_stageX (s : ℝ) (i : Fin 3) : i ∈ stageX s ↔ s ≤ fX i := Iff.rfl
lemma mem_stageY (s : ℝ) (i : Fin 3) : i ∈ stageY s ↔ s ≤ fY i := Iff.rfl

/-! ### Step 1: the two `FiltrationLaw` verifications (genuine modules) -/

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
    rcases hd with rfl | hz
    · exact Or.inl rfl
    · exact Or.inr hz
  · -- trans
    intros t x y z h1 h2
    obtain ⟨hx, hy, h1d⟩ := h1
    obtain ⟨hy2, hz, h2d⟩ := h2
    refine ⟨hx, hz, ?_⟩
    rcases h1d with rfl | hz1
    · exact h2d
    · exact Or.inr hz1
  · -- compat
    intros s t hst x y h
    obtain ⟨hx, hy, hd⟩ := h
    refine ⟨(mem_stageX s x).mpr (hst.trans ((mem_stageX t x).mp hx)),
            (mem_stageX s y).mpr (hst.trans ((mem_stageX t y).mp hy)), ?_⟩
    rcases hd with rfl | hz
    · exact Or.inl rfl
    · exact Or.inr (hst.trans hz)

theorem hLawY : FiltrationLaw stageY JY := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- antitone
    intros s t hst i hi
    exact hst.trans ((mem_stageY t i).mp hi)
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
    rcases hd with rfl | hz
    · exact Or.inl rfl
    · exact Or.inr hz
  · -- trans
    intros t x y z h1 h2
    obtain ⟨hx, hy, h1d⟩ := h1
    obtain ⟨hy2, hz, h2d⟩ := h2
    refine ⟨hx, hz, ?_⟩
    rcases h1d with rfl | hz1
    · exact h2d
    · exact Or.inr hz1
  · -- compat
    intros s t hst x y h
    obtain ⟨hx, hy, hd⟩ := h
    refine ⟨(mem_stageY s x).mpr (hst.trans ((mem_stageY t x).mp hx)),
            (mem_stageY s y).mpr (hst.trans ((mem_stageY t y).mp hy)), ?_⟩
    rcases hd with rfl | hz
    · exact Or.inl rfl
    · exact Or.inr (hst.trans hz)

/-! ### Step 2: rank formulas (for `t ≤ s`) -/

/-- Indicator of the essential bar (born β, never dying): counts the global class. -/
noncomputable def indEss (β : ℝ) (s : ℝ) : ℕ∞ := if s ≤ β then 1 else 0
/-- Indicator of the mortal bar born at β, dying at δ. -/
noncomputable def indMort (β δ : ℝ) (s t : ℝ) : ℕ∞ := if s ≤ β ∧ δ < t then 1 else 0

private lemma indEss_pos (β s : ℝ) (h : s ≤ β) : indEss β s = 1 := by simp [indEss, h]
private lemma indEss_neg (β s : ℝ) (h : ¬ s ≤ β) : indEss β s = 0 := by simp [indEss, h]
private lemma indMort_pos (β δ s t : ℝ) (hs : s ≤ β) (ht : δ < t) :
    indMort β δ s t = 1 := by simp [indMort, hs, ht]
private lemma indMort_neg_s (β δ s t : ℝ) (h : ¬ s ≤ β) : indMort β δ s t = 0 := by
  simp [indMort, h]
private lemma indMort_neg_t (β δ s t : ℝ) (h : ¬ δ < t) : indMort β δ s t = 0 := by
  simp [indMort, h]

/-- The `JX`-class of `x` at time `t`: below the bridge level `0.5` everything merges into
the single class `stageX t`; above it, all classes are singletons. -/
lemma JX_class_eq (t : ℝ) (x : Fin 3) (hx : x ∈ stageX t) :
    {y : Fin 3 | JX t x y} = if t ≤ 0.5 then stageX t else ({x} : Set (Fin 3)) := by
  ext y
  by_cases ht : t ≤ 0.5
  · simp only [if_pos ht, Set.mem_setOf_eq]
    unfold JX
    exact ⟨fun h => h.2.1, fun hy => ⟨hx, hy, Or.inr ht⟩⟩
  · simp only [if_neg ht, Set.mem_setOf_eq, Set.mem_singleton_iff]
    unfold JX
    refine ⟨?_, ?_⟩
    · rintro ⟨_, _, rfl | hz⟩
      · rfl
      · exact (ht hz).elim
    · rintro rfl; exact ⟨hx, hx, Or.inl rfl⟩

/-- The `JY`-class of `x` at time `t` (merge level `−1`). -/
lemma JY_class_eq (t : ℝ) (x : Fin 3) (hx : x ∈ stageY t) :
    {y : Fin 3 | JY t x y} = if t ≤ -1 then stageY t else ({x} : Set (Fin 3)) := by
  ext y
  by_cases ht : t ≤ -1
  · simp only [if_pos ht, Set.mem_setOf_eq]
    unfold JY
    exact ⟨fun h => h.2.1, fun hy => ⟨hx, hy, Or.inr ht⟩⟩
  · simp only [if_neg ht, Set.mem_setOf_eq, Set.mem_singleton_iff]
    unfold JY
    refine ⟨?_, ?_⟩
    · rintro ⟨_, _, rfl | hz⟩
      · rfl
      · exact (ht hz).elim
    · rintro rfl; exact ⟨hx, hx, Or.inl rfl⟩

/-- `stageX s` as an explicit set, by region of `s`. -/
private lemma stageX_eq_01 {s : ℝ} (h05 : ¬ s ≤ 0.5) (h10 : s ≤ 10) :
    stageX s = ({(0:Fin 3),(1:Fin 3)} : Set (Fin 3)) := by
  ext i; fin_cases i <;> simp [mem_stageX, fX_zero, fX_one, fX_two] <;> linarith
private lemma stageX_eq_0 {s : ℝ} (h10 : ¬ s ≤ 10) (h20 : s ≤ 20) :
    stageX s = ({(0:Fin 3)} : Set (Fin 3)) := by
  ext i; fin_cases i <;> simp [mem_stageX, fX_zero, fX_one, fX_two] <;> linarith
private lemma stageX_eq_empty {s : ℝ} (h20 : ¬ s ≤ 20) : stageX s = (∅ : Set (Fin 3)) := by
  ext i; fin_cases i <;> simp [mem_stageX, fX_zero, fX_one, fX_two] <;> linarith

/-- `stageY s` as an explicit set, by region of `s`. -/
private lemma stageY_eq_01 {s : ℝ} (h01 : ¬ s ≤ -1) (h10 : s ≤ 10) :
    stageY s = ({(0:Fin 3),(1:Fin 3)} : Set (Fin 3)) := by
  ext i; fin_cases i <;> simp [mem_stageY, fY_zero, fY_one, fY_two] <;> linarith
private lemma stageY_eq_0 {s : ℝ} (h10 : ¬ s ≤ 10) (h20 : s ≤ 20) :
    stageY s = ({(0:Fin 3)} : Set (Fin 3)) := by
  ext i; fin_cases i <;> simp [mem_stageY, fY_zero, fY_one, fY_two] <;> linarith
private lemma stageY_eq_empty {s : ℝ} (h20 : ¬ s ≤ 20) : stageY s = (∅ : Set (Fin 3)) := by
  ext i; fin_cases i <;> simp [mem_stageY, fY_zero, fY_one, fY_two] <;> linarith

/-- X's rank function: the essential class born at 20 plus the mortal bar `(10, 0.5)`. -/
theorem rankX_eq (s t : ℝ) (hts : t ≤ s) :
    rankFn stageX JX s t = indEss 20 s + indMort 10 0.5 s t := by
  unfold rankFn
  by_cases hle : t ≤ 0.5
  · -- merged region: a single class
    by_cases hs20 : s ≤ 20
    · have himg : (fun x => {y : Fin 3 | JX t x y}) '' stageX s =
          ({(stageX t)} : Set (Set (Fin 3))) := by
        ext c
        simp only [Set.mem_image, Set.mem_singleton_iff]
        refine ⟨?_, ?_⟩
        · rintro ⟨x, hx, hfx⟩
          have hxt : x ∈ stageX t := (mem_stageX t x).mpr (hts.trans ((mem_stageX s x).mp hx))
          rw [JX_class_eq t x hxt, if_pos hle] at hfx
          exact hfx.symm
        · intro h
          refine ⟨0, (mem_stageX s 0).mpr (by rw [fX_zero]; linarith), ?_⟩
          have h0t : (0:Fin 3) ∈ stageX t := (mem_stageX t 0).mpr (by rw [fX_zero]; linarith)
          rw [JX_class_eq t 0 h0t, if_pos hle, h]
      rw [himg, Set.encard_singleton, indEss_pos 20 s hs20,
          indMort_neg_t 10 0.5 s t (not_lt.mpr hle), add_zero]
    · have himg : (fun x => {y : Fin 3 | JX t x y}) '' stageX s = (∅ : Set (Set (Fin 3))) := by
        rw [Set.image_eq_empty, stageX_eq_empty hs20]
      have hs10 : ¬ s ≤ 10 := fun h => hs20 (h.trans (by norm_num))
      rw [himg, Set.encard_empty, indEss_neg 20 s hs20, indMort_neg_s 10 0.5 s t hs10, add_zero]
  · -- singleton region: 0.5 < t
    have ht05 : 0.5 < t := not_le.mp hle
    have hcls : ∀ x ∈ stageX s, {y : Fin 3 | JX t x y} = ({x} : Set (Fin 3)) := by
      intro x hx
      have hxt : x ∈ stageX t := (mem_stageX t x).mpr (hts.trans ((mem_stageX s x).mp hx))
      rw [JX_class_eq t x hxt, if_neg hle]
    have himg : (fun x => {y : Fin 3 | JX t x y}) '' stageX s =
        (fun x => ({x} : Set (Fin 3))) '' stageX s := by
      ext c
      simp only [Set.mem_image]
      refine ⟨?_, ?_⟩
      · rintro ⟨x, hx, hfx⟩; exact ⟨x, hx, (hcls x hx).symm.trans hfx⟩
      · rintro ⟨x, hx, hfx⟩; exact ⟨x, hx, (hcls x hx).trans hfx⟩
    rw [himg]
    have hcard : ((fun x => ({x} : Set (Fin 3))) '' stageX s).encard = (stageX s).encard :=
      Set.InjOn.encard_image (fun a _ b _ hhe => by simpa using hhe)
    rw [hcard]
    by_cases hs10 : s ≤ 10
    · have hs20 : s ≤ 20 := hs10.trans (by norm_num)
      rw [stageX_eq_01 (show ¬ s ≤ 0.5 by linarith) hs10,
          Set.encard_insert_of_notMem (by decide), Set.encard_singleton,
          indEss_pos 20 s hs20, indMort_pos 10 0.5 s t hs10 ht05]
    · by_cases hs20 : s ≤ 20
      · rw [stageX_eq_0 hs10 hs20, Set.encard_singleton,
            indEss_pos 20 s hs20, indMort_neg_s 10 0.5 s t hs10, add_zero]
      · rw [stageX_eq_empty hs20, Set.encard_empty,
            indEss_neg 20 s hs20, indMort_neg_s 10 0.5 s t hs10, add_zero]

/-- Y's rank function: the essential class born at 20 plus the mortal bar `(10, −1)`. -/
theorem rankY_eq (s t : ℝ) (hts : t ≤ s) :
    rankFn stageY JY s t = indEss 20 s + indMort 10 (-1) s t := by
  unfold rankFn
  by_cases hle : t ≤ -1
  · -- merged region: a single class
    by_cases hs20 : s ≤ 20
    · have himg : (fun x => {y : Fin 3 | JY t x y}) '' stageY s =
          ({(stageY t)} : Set (Set (Fin 3))) := by
        ext c
        simp only [Set.mem_image, Set.mem_singleton_iff]
        refine ⟨?_, ?_⟩
        · rintro ⟨x, hx, hfx⟩
          have hxt : x ∈ stageY t := (mem_stageY t x).mpr (hts.trans ((mem_stageY s x).mp hx))
          rw [JY_class_eq t x hxt, if_pos hle] at hfx
          exact hfx.symm
        · intro h
          refine ⟨0, (mem_stageY s 0).mpr (by rw [fY_zero]; linarith), ?_⟩
          have h0t : (0:Fin 3) ∈ stageY t := (mem_stageY t 0).mpr (by rw [fY_zero]; linarith)
          rw [JY_class_eq t 0 h0t, if_pos hle, h]
      rw [himg, Set.encard_singleton, indEss_pos 20 s hs20,
          indMort_neg_t 10 (-1) s t (not_lt.mpr hle), add_zero]
    · have himg : (fun x => {y : Fin 3 | JY t x y}) '' stageY s = (∅ : Set (Set (Fin 3))) := by
        rw [Set.image_eq_empty, stageY_eq_empty hs20]
      have hs10 : ¬ s ≤ 10 := fun h => hs20 (h.trans (by norm_num))
      rw [himg, Set.encard_empty, indEss_neg 20 s hs20, indMort_neg_s 10 (-1) s t hs10, add_zero]
  · -- singleton region: -1 < t
    have ht01 : -1 < t := not_le.mp hle
    have hcls : ∀ x ∈ stageY s, {y : Fin 3 | JY t x y} = ({x} : Set (Fin 3)) := by
      intro x hx
      have hxt : x ∈ stageY t := (mem_stageY t x).mpr (hts.trans ((mem_stageY s x).mp hx))
      rw [JY_class_eq t x hxt, if_neg hle]
    have himg : (fun x => {y : Fin 3 | JY t x y}) '' stageY s =
        (fun x => ({x} : Set (Fin 3))) '' stageY s := by
      ext c
      simp only [Set.mem_image]
      refine ⟨?_, ?_⟩
      · rintro ⟨x, hx, hfx⟩; exact ⟨x, hx, (hcls x hx).symm.trans hfx⟩
      · rintro ⟨x, hx, hfx⟩; exact ⟨x, hx, (hcls x hx).trans hfx⟩
    rw [himg]
    have hcard : ((fun x => ({x} : Set (Fin 3))) '' stageY s).encard = (stageY s).encard :=
      Set.InjOn.encard_image (fun a _ b _ hhe => by simpa using hhe)
    rw [hcard]
    by_cases hs10 : s ≤ 10
    · have hs20 : s ≤ 20 := hs10.trans (by norm_num)
      rw [stageY_eq_01 (show ¬ s ≤ -1 by linarith) hs10,
          Set.encard_insert_of_notMem (by decide), Set.encard_singleton,
          indEss_pos 20 s hs20, indMort_pos 10 (-1) s t hs10 ht01]
    · by_cases hs20 : s ≤ 20
      · rw [stageY_eq_0 hs10 hs20, Set.encard_singleton,
            indEss_pos 20 s hs20, indMort_neg_s 10 (-1) s t hs10, add_zero]
      · rw [stageY_eq_empty hs20, Set.encard_empty,
            indEss_neg 20 s hs20, indMort_neg_s 10 (-1) s t hs10, add_zero]

/-! ### Step 6a: q-tameness (ranks ≠ ⊤) -/

theorem hQX : ∀ s t : ℝ, rankFn stageX JX s t ≠ ⊤ := by
  intro s t
  unfold rankFn
  exact (Set.Finite.encard_lt_top (Set.toFinite _)).ne

theorem hQY : ∀ s t : ℝ, rankFn stageY JY s t ≠ ⊤ := by
  intro s t
  unfold rankFn
  exact (Set.Finite.encard_lt_top (Set.toFinite _)).ne

/-! ### Step 3: the plain diagram multiplicities -/

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

/-- The mortal bar `(10, 0.5)` has multiplicity `1`. -/
theorem multX_10_05 :
    mult (rankFn stageX JX) (((10:ℝ):EReal), ((0.5:ℝ):EReal)) = 1 := by
  rw [mult_coe_coe _ 10 0.5 (by norm_num : (0.5:ℝ) < 10)]
  refine le_antisymm ?_ (le_iInf fun ε => le_iInf fun hε => ?_)
  · refine iInf_le_of_le 1 (iInf_le_of_le ⟨by norm_num, by norm_num⟩ ?_)
    have hA : rankFn stageX JX (10 - 1) (0.5 + 1) = 2 := by
      rw [rankX_eq _ _ (by norm_num),
          indEss_pos 20 (10 - 1) (by norm_num),
          indMort_pos 10 0.5 (10 - 1) (0.5 + 1) (by norm_num) (by norm_num)]
      decide
    have hB : rankFn stageX JX (10 + 1) (0.5 + 1) = 1 := by
      rw [rankX_eq _ _ (by norm_num),
          indEss_pos 20 (10 + 1) (by norm_num),
          indMort_neg_s 10 0.5 (10 + 1) (0.5 + 1) (by norm_num)]
      decide
    have hC : rankFn stageX JX (10 - 1) (0.5 - 1) = 1 := by
      rw [rankX_eq _ _ (by norm_num),
          indEss_pos 20 (10 - 1) (by norm_num),
          indMort_neg_t 10 0.5 (10 - 1) (0.5 - 1) (by norm_num)]
      decide
    have hD : rankFn stageX JX (10 + 1) (0.5 - 1) = 1 := by
      rw [rankX_eq _ _ (by norm_num),
          indEss_pos 20 (10 + 1) (by norm_num),
          indMort_neg_s 10 0.5 (10 + 1) (0.5 - 1) (by norm_num)]
      decide
    rw [hA, hB, hC, hD]; decide
  · obtain ⟨hε0, hεw⟩ := Set.mem_Ioo.mp hε
    have hA : rankFn stageX JX (10 - ε) (0.5 + ε) = 2 := by
      rw [rankX_eq _ _ (by linarith),
          indEss_pos 20 (10 - ε) (by linarith),
          indMort_pos 10 0.5 (10 - ε) (0.5 + ε) (by linarith) (by linarith)]
      decide
    have hB : rankFn stageX JX (10 + ε) (0.5 + ε) = 1 := by
      rw [rankX_eq _ _ (by linarith),
          indEss_pos 20 (10 + ε) (by linarith),
          indMort_neg_s 10 0.5 (10 + ε) (0.5 + ε) (by linarith)]
      decide
    have hC : rankFn stageX JX (10 - ε) (0.5 - ε) = 1 := by
      rw [rankX_eq _ _ (by linarith),
          indEss_pos 20 (10 - ε) (by linarith),
          indMort_neg_t 10 0.5 (10 - ε) (0.5 - ε) (by linarith)]
      decide
    have hD : rankFn stageX JX (10 + ε) (0.5 - ε) = 1 := by
      rw [rankX_eq _ _ (by linarith),
          indEss_pos 20 (10 + ε) (by linarith),
          indMort_neg_s 10 0.5 (10 + ε) (0.5 - ε) (by linarith)]
      decide
    rw [hA, hB, hC, hD]; decide

/-- The essential bar `(20, ⊥)` has multiplicity `1`. -/
theorem multX_20_bot :
    mult (rankFn stageX JX) (((20:ℝ):EReal), (⊥:EReal)) = 1 := by
  rw [mult_coe_bot _ 20]
  refine le_antisymm ?_ (le_iInf fun ε => le_iInf fun hε => le_iInf fun t => le_iInf fun ht => ?_)
  · refine iInf_le_of_le 1 (iInf_le_of_le (show (0:ℝ) < 1 by norm_num) ?_)
    refine iInf_le_of_le 0 (iInf_le_of_le (show (0:ℝ) ≤ 20 - 1 by norm_num) ?_)
    have hA : rankFn stageX JX (20 - 1) 0 = 1 := by
      rw [rankX_eq _ _ (by norm_num),
          indEss_pos 20 (20 - 1) (by norm_num),
          indMort_neg_t 10 0.5 (20 - 1) 0 (by norm_num)]
      decide
    have hB : rankFn stageX JX (20 + 1) 0 = 0 := by
      rw [rankX_eq _ _ (by norm_num),
          indEss_neg 20 (20 + 1) (by norm_num),
          indMort_neg_s 10 0.5 (20 + 1) 0 (by norm_num)]
      decide
    rw [hA, hB]; decide
  · have hA : rankFn stageX JX (20 - ε) t =
        1 + (if (20 - ε) ≤ 10 ∧ 0.5 < t then (1:ℕ∞) else 0) := by
      rw [rankX_eq _ _ ht, indEss_pos 20 (20 - ε) (by linarith)]
      rfl
    have hB : rankFn stageX JX (20 + ε) t = 0 := by
      rw [rankX_eq _ _ (by linarith),
          indEss_neg 20 (20 + ε) (by linarith),
          indMort_neg_s 10 0.5 (20 + ε) t (by linarith)]
      decide
    rw [hA, hB]
    split_ifs <;> decide

/-- The mortal bar `(10, −1)` has multiplicity `1`. -/
theorem multY_10_m1 :
    mult (rankFn stageY JY) (((10:ℝ):EReal), ((-1:ℝ):EReal)) = 1 := by
  rw [mult_coe_coe _ 10 (-1) (by norm_num : (-1:ℝ) < 10)]
  refine le_antisymm ?_ (le_iInf fun ε => le_iInf fun hε => ?_)
  · refine iInf_le_of_le 1 (iInf_le_of_le ⟨by norm_num, by norm_num⟩ ?_)
    have hA : rankFn stageY JY (10 - 1) ((-1) + 1) = 2 := by
      rw [rankY_eq _ _ (by norm_num),
          indEss_pos 20 (10 - 1) (by norm_num),
          indMort_pos 10 (-1) (10 - 1) ((-1) + 1) (by norm_num) (by norm_num)]
      decide
    have hB : rankFn stageY JY (10 + 1) ((-1) + 1) = 1 := by
      rw [rankY_eq _ _ (by norm_num),
          indEss_pos 20 (10 + 1) (by norm_num),
          indMort_neg_s 10 (-1) (10 + 1) ((-1) + 1) (by norm_num)]
      decide
    have hC : rankFn stageY JY (10 - 1) ((-1) - 1) = 1 := by
      rw [rankY_eq _ _ (by norm_num),
          indEss_pos 20 (10 - 1) (by norm_num),
          indMort_neg_t 10 (-1) (10 - 1) ((-1) - 1) (by norm_num)]
      decide
    have hD : rankFn stageY JY (10 + 1) ((-1) - 1) = 1 := by
      rw [rankY_eq _ _ (by norm_num),
          indEss_pos 20 (10 + 1) (by norm_num),
          indMort_neg_s 10 (-1) (10 + 1) ((-1) - 1) (by norm_num)]
      decide
    rw [hA, hB, hC, hD]; decide
  · obtain ⟨hε0, hεw⟩ := Set.mem_Ioo.mp hε
    have hA : rankFn stageY JY (10 - ε) ((-1) + ε) = 2 := by
      rw [rankY_eq _ _ (by linarith),
          indEss_pos 20 (10 - ε) (by linarith),
          indMort_pos 10 (-1) (10 - ε) ((-1) + ε) (by linarith) (by linarith)]
      decide
    have hB : rankFn stageY JY (10 + ε) ((-1) + ε) = 1 := by
      rw [rankY_eq _ _ (by linarith),
          indEss_pos 20 (10 + ε) (by linarith),
          indMort_neg_s 10 (-1) (10 + ε) ((-1) + ε) (by linarith)]
      decide
    have hC : rankFn stageY JY (10 - ε) ((-1) - ε) = 1 := by
      rw [rankY_eq _ _ (by linarith),
          indEss_pos 20 (10 - ε) (by linarith),
          indMort_neg_t 10 (-1) (10 - ε) ((-1) - ε) (by linarith)]
      decide
    have hD : rankFn stageY JY (10 + ε) ((-1) - ε) = 1 := by
      rw [rankY_eq _ _ (by linarith),
          indEss_pos 20 (10 + ε) (by linarith),
          indMort_neg_s 10 (-1) (10 + ε) ((-1) - ε) (by linarith)]
      decide
    rw [hA, hB, hC, hD]; decide

/-- Y's essential bar `(20, ⊥)` has multiplicity `1`. -/
theorem multY_20_bot :
    mult (rankFn stageY JY) (((20:ℝ):EReal), (⊥:EReal)) = 1 := by
  rw [mult_coe_bot _ 20]
  refine le_antisymm ?_ (le_iInf fun ε => le_iInf fun hε => le_iInf fun t => le_iInf fun ht => ?_)
  · refine iInf_le_of_le 1 (iInf_le_of_le (show (0:ℝ) < 1 by norm_num) ?_)
    refine iInf_le_of_le 0 (iInf_le_of_le (show (0:ℝ) ≤ 20 - 1 by norm_num) ?_)
    have hA : rankFn stageY JY (20 - 1) 0 = 1 := by
      rw [rankY_eq _ _ (by norm_num),
          indEss_pos 20 (20 - 1) (by norm_num),
          indMort_neg_s 10 (-1) (20 - 1) 0 (by norm_num)]
      decide
    have hB : rankFn stageY JY (20 + 1) 0 = 0 := by
      rw [rankY_eq _ _ (by norm_num),
          indEss_neg 20 (20 + 1) (by norm_num),
          indMort_neg_s 10 (-1) (20 + 1) 0 (by norm_num)]
      decide
    rw [hA, hB]; decide
  · have hA : rankFn stageY JY (20 - ε) t =
        1 + (if (20 - ε) ≤ 10 ∧ -1 < t then (1:ℕ∞) else 0) := by
      rw [rankY_eq _ _ ht, indEss_pos 20 (20 - ε) (by linarith)]
      rfl
    have hB : rankFn stageY JY (20 + ε) t = 0 := by
      rw [rankY_eq _ _ (by linarith),
          indEss_neg 20 (20 + ε) (by linarith),
          indMort_neg_s 10 (-1) (20 + ε) t (by linarith)]
      decide
    rw [hA, hB]
    split_ifs <;> decide

theorem hDiagX : IsDiagramLike (mult (rankFn stageX JX)) := isDiagramLike_mult _
theorem hDiagY : IsDiagramLike (mult (rankFn stageY JY)) := isDiagramLike_mult _

/-! ### Step 4: the truncated-rank helpers and α-truncated multiplicities (α = 0) -/

private theorem trunc_above (r : ℝ → ℝ → ℕ∞) (a s t : ℝ) (h1 : a ≤ s) (h2 : a ≤ t) :
    truncRank r a s t = r s t := by simp [truncRank, h1, h2]
private theorem trunc_below (r : ℝ → ℝ → ℕ∞) (a s t : ℝ) (h : ¬(a ≤ s ∧ a ≤ t)) :
    truncRank r a s t = 0 := by simp [truncRank, h]
private theorem truncRank_zero_of_lt (r : ℝ → ℝ → ℕ∞) (α s t : ℝ) (ht : t < α) :
    truncRank r α s t = 0 :=
  trunc_below r α s t (fun h => not_le.mpr ht h.2)

/-- Any α-truncated bar dying at `⊥` has zero multiplicity (the truncation floor kills it). -/
private theorem mult_trunc_bot_zero (r : ℝ → ℝ → ℕ∞) (α b : ℝ) :
    mult (truncRank r α) (((b : ℝ) : EReal), (⊥ : EReal)) = 0 := by
  rw [mult_coe_bot]
  refine le_antisymm ?_ (le_iInf fun _ => le_iInf fun _ => le_iInf fun _ =>
    le_iInf fun _ => (zero_le : (0 : ℕ∞) ≤ _))
  have ht0 : min (b - 1) (α - 1) < α := by
    linarith [min_le_right (b - 1) (α - 1), min_le_left (b - 1) (α - 1)]
  have hval : truncRank r α (b - 1) (min (b - 1) (α - 1)) -
      truncRank r α (b + 1) (min (b - 1) (α - 1)) ≤ 0 := by
    rw [truncRank_zero_of_lt r α _ _ ht0, truncRank_zero_of_lt r α _ _ ht0, tsub_self]
  exact iInf_le_of_le 1 (iInf_le_of_le (show (0 : ℝ) < 1 by norm_num)
    (iInf_le_of_le (min (b - 1) (α - 1)) (iInf_le_of_le (min_le_left _ _) hval)))

/-- A bar dying strictly below α has zero α-truncated multiplicity. -/
private theorem mult_trunc_lt_zero (r : ℝ → ℝ → ℕ∞) (α b d : ℝ) (hbd : d < b) (hd : d < α) :
    mult (truncRank r α) (((b : ℝ) : EReal), ((d : ℝ) : EReal)) = 0 := by
  rw [mult_coe_coe _ b d hbd]
  refine le_antisymm ?_ (le_iInf fun _ => le_iInf fun _ => (zero_le : (0 : ℕ∞) ≤ _))
  set η := (min ((b - d) / 2) ((α - d) / 2)) / 2 with hη
  have hbd0 : 0 < (b - d) / 2 := by linarith
  have had0 : 0 < (α - d) / 2 := by linarith
  have hpos : 0 < η := by have : 0 < min ((b - d) / 2) ((α - d) / 2) := lt_min hbd0 had0; linarith
  have hwin : η ∈ Set.Ioo (0 : ℝ) ((b - d) / 2) := by
    refine ⟨hpos, ?_⟩
    have h1 : min ((b - d) / 2) ((α - d) / 2) ≤ (b - d) / 2 := min_le_left _ _
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

/-- The X-truncated bar `(10, 0.5)` survives truncation at α = 0 (multiplicity 1). -/
theorem multTruncX_10_05 :
    mult (truncRank (rankFn stageX JX) 0) (((10:ℝ):EReal), ((0.5:ℝ):EReal)) = 1 := by
  rw [mult_coe_coe _ 10 0.5 (by norm_num)]
  refine le_antisymm ?_ (le_iInf fun ε => le_iInf fun hε => ?_)
  · refine iInf_le_of_le 1 (iInf_le_of_le ⟨by norm_num, by norm_num⟩ ?_)
    have hA : truncRank (rankFn stageX JX) 0 (10 - 1) (0.5 + 1) = 2 := by
      rw [trunc_above _ 0 _ _ (by norm_num) (by norm_num), rankX_eq _ _ (by norm_num),
          indEss_pos 20 (10 - 1) (by norm_num),
          indMort_pos 10 0.5 (10 - 1) (0.5 + 1) (by norm_num) (by norm_num)]
      decide
    have hB : truncRank (rankFn stageX JX) 0 (10 + 1) (0.5 + 1) = 1 := by
      rw [trunc_above _ 0 _ _ (by norm_num) (by norm_num), rankX_eq _ _ (by norm_num),
          indEss_pos 20 (10 + 1) (by norm_num),
          indMort_neg_s 10 0.5 (10 + 1) (0.5 + 1) (by norm_num)]
      decide
    have hC : truncRank (rankFn stageX JX) 0 (10 - 1) (0.5 - 1) = 0 :=
      truncRank_zero_of_lt _ 0 _ _ (by norm_num)
    have hD : truncRank (rankFn stageX JX) 0 (10 + 1) (0.5 - 1) = 0 :=
      truncRank_zero_of_lt _ 0 _ _ (by norm_num)
    rw [hA, hB, hC, hD]; decide
  · obtain ⟨hε0, hεw⟩ := Set.mem_Ioo.mp hε
    have hA : truncRank (rankFn stageX JX) 0 (10 - ε) (0.5 + ε) = 2 := by
      rw [trunc_above _ 0 _ _ (by linarith) (by linarith), rankX_eq _ _ (by linarith),
          indEss_pos 20 (10 - ε) (by linarith),
          indMort_pos 10 0.5 (10 - ε) (0.5 + ε) (by linarith) (by linarith)]
      decide
    have hB : truncRank (rankFn stageX JX) 0 (10 + ε) (0.5 + ε) = 1 := by
      rw [trunc_above _ 0 _ _ (by linarith) (by linarith), rankX_eq _ _ (by linarith),
          indEss_pos 20 (10 + ε) (by linarith),
          indMort_neg_s 10 0.5 (10 + ε) (0.5 + ε) (by linarith)]
      decide
    have hCD : truncRank (rankFn stageX JX) 0 (10 - ε) (0.5 - ε) -
        truncRank (rankFn stageX JX) 0 (10 + ε) (0.5 - ε) = 0 := by
      by_cases h05 : 0 ≤ 0.5 - ε
      · have hC : truncRank (rankFn stageX JX) 0 (10 - ε) (0.5 - ε) = 1 := by
          rw [trunc_above _ 0 _ _ (by linarith) h05, rankX_eq _ _ (by linarith),
              indEss_pos 20 (10 - ε) (by linarith),
              indMort_neg_t 10 0.5 (10 - ε) (0.5 - ε) (by linarith)]
          decide
        have hD : truncRank (rankFn stageX JX) 0 (10 + ε) (0.5 - ε) = 1 := by
          rw [trunc_above _ 0 _ _ (by linarith) h05, rankX_eq _ _ (by linarith),
              indEss_pos 20 (10 + ε) (by linarith),
              indMort_neg_s 10 0.5 (10 + ε) (0.5 - ε) (by linarith)]
          decide
        rw [hC, hD]; decide
      · have hC : truncRank (rankFn stageX JX) 0 (10 - ε) (0.5 - ε) = 0 :=
          truncRank_zero_of_lt _ 0 _ _ (by linarith)
        have hD : truncRank (rankFn stageX JX) 0 (10 + ε) (0.5 - ε) = 0 :=
          truncRank_zero_of_lt _ 0 _ _ (by linarith)
        rw [hC, hD]; decide
    rw [hA, hB, hCD]; decide

/-- The X-truncated essential bar clamps to `(20, 0)` (multiplicity 1). -/
theorem multTruncX_20_0 :
    mult (truncRank (rankFn stageX JX) 0) (((20:ℝ):EReal), ((0:ℝ):EReal)) = 1 := by
  rw [mult_coe_coe _ 20 0 (by norm_num)]
  refine le_antisymm ?_ (le_iInf fun ε => le_iInf fun hε => ?_)
  · refine iInf_le_of_le 1 (iInf_le_of_le ⟨by norm_num, by norm_num⟩ ?_)
    have hA : truncRank (rankFn stageX JX) 0 (20 - 1) (0 + 1) = 1 := by
      rw [trunc_above _ 0 _ _ (by norm_num) (by norm_num), rankX_eq _ _ (by norm_num),
          indEss_pos 20 (20 - 1) (by norm_num),
          indMort_neg_s 10 0.5 (20 - 1) (0 + 1) (by norm_num)]
      decide
    have hB : truncRank (rankFn stageX JX) 0 (20 + 1) (0 + 1) = 0 := by
      rw [trunc_above _ 0 _ _ (by norm_num) (by norm_num), rankX_eq _ _ (by norm_num),
          indEss_neg 20 (20 + 1) (by norm_num),
          indMort_neg_s 10 0.5 (20 + 1) (0 + 1) (by norm_num)]
      decide
    have hC : truncRank (rankFn stageX JX) 0 (20 - 1) (0 - 1) = 0 :=
      truncRank_zero_of_lt _ 0 _ _ (by norm_num)
    have hD : truncRank (rankFn stageX JX) 0 (20 + 1) (0 - 1) = 0 :=
      truncRank_zero_of_lt _ 0 _ _ (by norm_num)
    rw [hA, hB, hC, hD]; decide
  · obtain ⟨hε0, hεw⟩ := Set.mem_Ioo.mp hε
    have hA : truncRank (rankFn stageX JX) 0 (20 - ε) (0 + ε) = 1 := by
      rw [trunc_above _ 0 _ _ (by linarith) (by linarith), rankX_eq _ _ (by linarith),
          indEss_pos 20 (20 - ε) (by linarith),
          indMort_neg_s 10 0.5 (20 - ε) (0 + ε) (by linarith)]
      decide
    have hB : truncRank (rankFn stageX JX) 0 (20 + ε) (0 + ε) = 0 := by
      rw [trunc_above _ 0 _ _ (by linarith) (by linarith), rankX_eq _ _ (by linarith),
          indEss_neg 20 (20 + ε) (by linarith),
          indMort_neg_s 10 0.5 (20 + ε) (0 + ε) (by linarith)]
      decide
    have hC : truncRank (rankFn stageX JX) 0 (20 - ε) (0 - ε) = 0 :=
      truncRank_zero_of_lt _ 0 _ _ (by linarith)
    have hD : truncRank (rankFn stageX JX) 0 (20 + ε) (0 - ε) = 0 :=
      truncRank_zero_of_lt _ 0 _ _ (by linarith)
    rw [hA, hB, hC, hD]; decide

/-- The Y-truncated mortal bar `(10, −1)` clamps to `(10, 0)` (multiplicity 1). -/
theorem multTruncY_10_0 :
    mult (truncRank (rankFn stageY JY) 0) (((10:ℝ):EReal), ((0:ℝ):EReal)) = 1 := by
  rw [mult_coe_coe _ 10 0 (by norm_num)]
  refine le_antisymm ?_ (le_iInf fun ε => le_iInf fun hε => ?_)
  · refine iInf_le_of_le 1 (iInf_le_of_le ⟨by norm_num, by norm_num⟩ ?_)
    have hA : truncRank (rankFn stageY JY) 0 (10 - 1) (0 + 1) = 2 := by
      rw [trunc_above _ 0 _ _ (by norm_num) (by norm_num), rankY_eq _ _ (by norm_num),
          indEss_pos 20 (10 - 1) (by norm_num),
          indMort_pos 10 (-1) (10 - 1) (0 + 1) (by norm_num) (by norm_num)]
      decide
    have hB : truncRank (rankFn stageY JY) 0 (10 + 1) (0 + 1) = 1 := by
      rw [trunc_above _ 0 _ _ (by norm_num) (by norm_num), rankY_eq _ _ (by norm_num),
          indEss_pos 20 (10 + 1) (by norm_num),
          indMort_neg_s 10 (-1) (10 + 1) (0 + 1) (by norm_num)]
      decide
    have hC : truncRank (rankFn stageY JY) 0 (10 - 1) (0 - 1) = 0 :=
      truncRank_zero_of_lt _ 0 _ _ (by norm_num)
    have hD : truncRank (rankFn stageY JY) 0 (10 + 1) (0 - 1) = 0 :=
      truncRank_zero_of_lt _ 0 _ _ (by norm_num)
    rw [hA, hB, hC, hD]; decide
  · obtain ⟨hε0, hεw⟩ := Set.mem_Ioo.mp hε
    have hA : truncRank (rankFn stageY JY) 0 (10 - ε) (0 + ε) = 2 := by
      rw [trunc_above _ 0 _ _ (by linarith) (by linarith), rankY_eq _ _ (by linarith),
          indEss_pos 20 (10 - ε) (by linarith),
          indMort_pos 10 (-1) (10 - ε) (0 + ε) (by linarith) (by linarith)]
      decide
    have hB : truncRank (rankFn stageY JY) 0 (10 + ε) (0 + ε) = 1 := by
      rw [trunc_above _ 0 _ _ (by linarith) (by linarith), rankY_eq _ _ (by linarith),
          indEss_pos 20 (10 + ε) (by linarith),
          indMort_neg_s 10 (-1) (10 + ε) (0 + ε) (by linarith)]
      decide
    have hC : truncRank (rankFn stageY JY) 0 (10 - ε) (0 - ε) = 0 :=
      truncRank_zero_of_lt _ 0 _ _ (by linarith)
    have hD : truncRank (rankFn stageY JY) 0 (10 + ε) (0 - ε) = 0 :=
      truncRank_zero_of_lt _ 0 _ _ (by linarith)
    rw [hA, hB, hC, hD]; decide

/-- The Y-truncated essential bar clamps to `(20, 0)` (multiplicity 1). -/
theorem multTruncY_20_0 :
    mult (truncRank (rankFn stageY JY) 0) (((20:ℝ):EReal), ((0:ℝ):EReal)) = 1 := by
  rw [mult_coe_coe _ 20 0 (by norm_num)]
  refine le_antisymm ?_ (le_iInf fun ε => le_iInf fun hε => ?_)
  · refine iInf_le_of_le 1 (iInf_le_of_le ⟨by norm_num, by norm_num⟩ ?_)
    have hA : truncRank (rankFn stageY JY) 0 (20 - 1) (0 + 1) = 1 := by
      rw [trunc_above _ 0 _ _ (by norm_num) (by norm_num), rankY_eq _ _ (by norm_num),
          indEss_pos 20 (20 - 1) (by norm_num),
          indMort_neg_s 10 (-1) (20 - 1) (0 + 1) (by norm_num)]
      decide
    have hB : truncRank (rankFn stageY JY) 0 (20 + 1) (0 + 1) = 0 := by
      rw [trunc_above _ 0 _ _ (by norm_num) (by norm_num), rankY_eq _ _ (by norm_num),
          indEss_neg 20 (20 + 1) (by norm_num),
          indMort_neg_s 10 (-1) (20 + 1) (0 + 1) (by norm_num)]
      decide
    have hC : truncRank (rankFn stageY JY) 0 (20 - 1) (0 - 1) = 0 :=
      truncRank_zero_of_lt _ 0 _ _ (by norm_num)
    have hD : truncRank (rankFn stageY JY) 0 (20 + 1) (0 - 1) = 0 :=
      truncRank_zero_of_lt _ 0 _ _ (by norm_num)
    rw [hA, hB, hC, hD]; decide
  · obtain ⟨hε0, hεw⟩ := Set.mem_Ioo.mp hε
    have hA : truncRank (rankFn stageY JY) 0 (20 - ε) (0 + ε) = 1 := by
      rw [trunc_above _ 0 _ _ (by linarith) (by linarith), rankY_eq _ _ (by linarith),
          indEss_pos 20 (20 - ε) (by linarith),
          indMort_neg_s 10 (-1) (20 - ε) (0 + ε) (by linarith)]
      decide
    have hB : truncRank (rankFn stageY JY) 0 (20 + ε) (0 + ε) = 0 := by
      rw [trunc_above _ 0 _ _ (by linarith) (by linarith), rankY_eq _ _ (by linarith),
          indEss_neg 20 (20 + ε) (by linarith),
          indMort_neg_s 10 (-1) (20 + ε) (0 + ε) (by linarith)]
      decide
    have hC : truncRank (rankFn stageY JY) 0 (20 - ε) (0 - ε) = 0 :=
      truncRank_zero_of_lt _ 0 _ _ (by linarith)
    have hD : truncRank (rankFn stageY JY) 0 (20 + ε) (0 - ε) = 0 :=
      truncRank_zero_of_lt _ 0 _ _ (by linarith)
    rw [hA, hB, hC, hD]; decide

/-- The off-support point `(10, 0)` is absent from the X-truncated diagram. -/
theorem multTruncX_10_0 :
    mult (truncRank (rankFn stageX JX) 0) (((10:ℝ):EReal), ((0:ℝ):EReal)) = 0 := by
  rw [mult_coe_coe _ 10 0 (by norm_num)]
  refine le_antisymm ?_ (le_iInf fun ε => le_iInf fun hε => (zero_le : (0:ℕ∞) ≤ _))
  · refine iInf_le_of_le 0.25 (iInf_le_of_le ⟨by norm_num, by norm_num⟩ ?_)
    have hA : truncRank (rankFn stageX JX) 0 (10 - 0.25) (0 + 0.25) = 1 := by
      rw [trunc_above _ 0 _ _ (by norm_num) (by norm_num), rankX_eq _ _ (by norm_num),
          indEss_pos 20 (10 - 0.25) (by norm_num),
          indMort_neg_t 10 0.5 (10 - 0.25) (0 + 0.25) (by norm_num)]
      decide
    have hB : truncRank (rankFn stageX JX) 0 (10 + 0.25) (0 + 0.25) = 1 := by
      rw [trunc_above _ 0 _ _ (by norm_num) (by norm_num), rankX_eq _ _ (by norm_num),
          indEss_pos 20 (10 + 0.25) (by norm_num),
          indMort_neg_s 10 0.5 (10 + 0.25) (0 + 0.25) (by norm_num)]
      decide
    have hC : truncRank (rankFn stageX JX) 0 (10 - 0.25) (0 - 0.25) = 0 :=
      truncRank_zero_of_lt _ 0 _ _ (by norm_num)
    have hD : truncRank (rankFn stageX JX) 0 (10 + 0.25) (0 - 0.25) = 0 :=
      truncRank_zero_of_lt _ 0 _ _ (by norm_num)
    rw [hA, hB, hC, hD]; decide

/-! ### Step 5a: support machinery (2-term: one essential + one mortal bar) -/

private lemma indEss_congr (β s s' : ℝ) (h : s ≤ β ↔ s' ≤ β) : indEss β s = indEss β s' := by
  unfold indEss
  by_cases hs : s ≤ β
  · rw [if_pos hs, if_pos (h.mp hs)]
  · have hs' : ¬ s' ≤ β := fun hc => hs (h.mpr hc)
    rw [if_neg hs, if_neg hs']

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

private lemma birth_cell (β b η : ℝ) (hη : 0 ≤ η) (hβ : β ≠ b) (h : η < |β - b|) :
    b - η ≤ β ↔ b + η ≤ β := by
  rcases lt_or_gt_of_ne hβ with hlt | hgt
  · rw [abs_of_neg (by linarith)] at h
    exact ⟨fun hc => absurd hc (by linarith), fun hc => absurd hc (by linarith)⟩
  · rw [abs_of_pos (by linarith)] at h
    exact ⟨fun _ => le_of_lt (by linarith), fun _ => le_of_lt (by linarith)⟩

private lemma death_cell (δ d η : ℝ) (hη : 0 ≤ η) (hδ : δ ≠ d) (h : η < |δ - d|) :
    δ < d + η ↔ δ < d - η := by
  rcases lt_or_gt_of_ne hδ with hlt | hgt
  · rw [abs_of_neg (by linarith)] at h
    exact ⟨fun _ => by linarith, fun _ => by linarith⟩
  · rw [abs_of_pos (by linarith)] at h
    exact ⟨fun hc => absurd hc (by linarith), fun hc => absurd hc (by linarith)⟩

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

/-- Four-corner bracket of a 2-term rank `indEss β₀ + indMort β₁ δ₁` vanishes when the mortal
bar's birth or death cell is constant across the four corners. -/
private lemma bracket_zero_2 (r : ℝ → ℝ → ℕ∞) (β₀ β₁ δ₁ : ℝ)
    (hr : ∀ s t, t ≤ s → r s t = indEss β₀ s + indMort β₁ δ₁ s t)
    (b d η : ℝ) (hη : 0 ≤ η) (hd : d < b) (hηw : η < (b - d) / 2)
    (h1 : (β₁ ≠ b ∧ η < |β₁ - b|) ∨ (δ₁ ≠ d ∧ η < |δ₁ - d|)) :
    ((r (b - η) (d + η) - r (b + η) (d + η)) - (r (b - η) (d - η) - r (b + η) (d - η))) = 0 := by
  have hle1 : d + η ≤ b - η := by linarith
  have hle2 : d + η ≤ b + η := by linarith
  have hle3 : d - η ≤ b - η := by linarith
  have hle4 : d - η ≤ b + η := by linarith
  rw [hr (b - η) (d + η) hle1, hr (b + η) (d + η) hle2,
      hr (b - η) (d - η) hle3, hr (b + η) (d - η) hle4]
  rcases h1 with ⟨hb1, hn1⟩ | ⟨hd1d, hn1d⟩
  · have hbc : b - η ≤ β₁ ↔ b + η ≤ β₁ := birth_cell β₁ b η hη hb1 hn1
    have hc1 : indMort β₁ δ₁ (b + η) (d + η) = indMort β₁ δ₁ (b - η) (d + η) :=
      indMort_congr_s _ _ _ _ _ hbc.symm
    have hc2 : indMort β₁ δ₁ (b + η) (d - η) = indMort β₁ δ₁ (b - η) (d - η) :=
      indMort_congr_s _ _ _ _ _ hbc.symm
    rw [hc1, hc2,
      enat_tsub_cancel_right (indEss β₀ (b - η)) (indEss β₀ (b + η))
        (indMort β₁ δ₁ (b - η) (d + η)) (indMort_ne_top _ _ _ _),
      enat_tsub_cancel_right (indEss β₀ (b - η)) (indEss β₀ (b + η))
        (indMort β₁ δ₁ (b - η) (d - η)) (indMort_ne_top _ _ _ _)]
    rw [tsub_self]
  · have hdc : δ₁ < d + η ↔ δ₁ < d - η := death_cell δ₁ d η hη hd1d hn1d
    have hd3e : indMort β₁ δ₁ (b - η) (d - η) = indMort β₁ δ₁ (b - η) (d + η) :=
      indMort_congr_t _ _ _ _ _ hdc.symm
    have hd4e : indMort β₁ δ₁ (b + η) (d - η) = indMort β₁ δ₁ (b + η) (d + η) :=
      indMort_congr_t _ _ _ _ _ hdc.symm
    rw [hd3e, hd4e, tsub_self]

private lemma mult_zero_of_born (r : ℝ → ℝ → ℕ∞) (p : EReal × EReal)
    (h : p.1 = ⊥ ∨ p.1 = ⊤) : mult r p = 0 := by
  unfold mult
  rcases h with h | h
  · rw [if_neg (fun hc => hc.1 h)]
  · rw [if_neg (fun hc => hc.2 h)]

private lemma mult_coe_top_zero (r : ℝ → ℝ → ℕ∞) (b : ℝ) :
    mult r (((b : ℝ) : EReal), (⊤ : EReal)) = 0 := by
  unfold mult
  rw [if_pos ⟨EReal.coe_ne_bot b, EReal.coe_ne_top b⟩, if_neg (bot_ne_top.symm),
      if_neg (fun hc => lt_irrefl (⊤ : EReal) (hc.trans (EReal.coe_lt_top b)))]

private lemma mult_coe_coe_le_zero (r : ℝ → ℝ → ℕ∞) (b d : ℝ) (h : b ≤ d) :
    mult r (((b : ℝ) : EReal), ((d : ℝ) : EReal)) = 0 := by
  unfold mult
  rw [if_pos ⟨EReal.coe_ne_bot b, EReal.coe_ne_top b⟩, if_neg (EReal.coe_ne_bot d),
      if_neg (fun hc => lt_irrefl d ((EReal.coe_lt_coe_iff.mp hc).trans_le h))]

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

/-- A real point off the single mortal bar has zero plain multiplicity. -/
private lemma mult_plain_eq_zero_2 (r : ℝ → ℝ → ℕ∞) (β₀ β₁ δ₁ : ℝ)
    (hr : ∀ s t, t ≤ s → r s t = indEss β₀ s + indMort β₁ δ₁ s t)
    (b d : ℝ) (hbd : d < b) (hne : β₁ ≠ b ∨ d ≠ δ₁) :
    mult r (((b : ℝ) : EReal), ((d : ℝ) : EReal)) = 0 := by
  rw [mult_coe_coe r b d hbd]
  refine le_antisymm ?_ (le_iInf fun _ => le_iInf fun _ => (zero_le : (0:ℕ∞) ≤ _))
  set q1 : ℝ := if β₁ = b then |δ₁ - d| else |β₁ - b| with hq1def
  have hq1pos : 0 < q1 := by
    rw [hq1def]; by_cases hb : β₁ = b
    · rw [if_pos hb]
      rcases hne with h | h
      · exact absurd hb h
      · exact abs_pos.mpr (sub_ne_zero.mpr (Ne.symm h))
    · rw [if_neg hb]; exact abs_pos.mpr (sub_ne_zero.mpr hb)
  set M : ℝ := min ((b - d) / 2) q1 with hMdef
  have hM1 : M ≤ (b - d) / 2 := min_le_left _ _
  have hM2 : M ≤ q1 := min_le_right _ _
  have hMpos : 0 < M := lt_min (by linarith) hq1pos
  set η : ℝ := M / 2 with hηdef
  have hηpos : 0 < η := by linarith
  have hηw : η < (b - d) / 2 := by linarith
  have hh1 : (β₁ ≠ b ∧ η < |β₁ - b|) ∨ (δ₁ ≠ d ∧ η < |δ₁ - d|) := by
    by_cases hb : β₁ = b
    · refine Or.inr ⟨?_, ?_⟩
      · rcases hne with h | h
        · exact absurd hb h
        · exact h.symm
      · have hq : q1 = |δ₁ - d| := by rw [hq1def, if_pos hb]
        linarith
    · refine Or.inl ⟨hb, ?_⟩
      have hq : q1 = |β₁ - b| := by rw [hq1def, if_neg hb]
      linarith
  have hbr : ((r (b - η) (d + η) - r (b + η) (d + η)) -
      (r (b - η) (d - η) - r (b + η) (d - η))) = 0 :=
    bracket_zero_2 r β₀ β₁ δ₁ hr b d η hηpos.le hbd hηw hh1
  exact iInf_le_of_le η (iInf_le_of_le ⟨hηpos, hηw⟩ hbr.le)

/-- A real-born point dying at `⊥`, not born at the essential birth `β₀`, has zero multiplicity. -/
private lemma mult_coe_bot_zero_of_ne_2 (r : ℝ → ℝ → ℕ∞) (β₀ β₁ δ₁ : ℝ)
    (hr : ∀ s t, t ≤ s → r s t = indEss β₀ s + indMort β₁ δ₁ s t)
    (b : ℝ) (hbne : β₀ ≠ b) :
    mult r (((b : ℝ) : EReal), (⊥ : EReal)) = 0 := by
  rw [mult_coe_bot r b]
  refine le_antisymm ?_ (le_iInf fun _ => le_iInf fun _ => le_iInf fun _ =>
    (zero_le : (0 : ℕ∞) ≤ _))
  set η : ℝ := |β₀ - b| / 2 with hηdef
  have hηpos : 0 < η := by apply div_pos; exact abs_pos.mpr (sub_ne_zero.mpr hbne); norm_num
  have hηw : η < |β₀ - b| := by linarith
  set t : ℝ := min δ₁ (b - η) with htdef
  have ht : t ≤ b - η := min_le_right _ _
  have htt : ¬ δ₁ < t := fun h =>
    lt_irrefl δ₁ (h.trans_le (min_le_left δ₁ (b - η)))
  have hbr : r (b - η) t - r (b + η) t = 0 := by
    have hle1 : t ≤ b - η := ht
    have hle2 : t ≤ b + η := by linarith
    rw [hr (b - η) t hle1, hr (b + η) t hle2,
        indMort_neg_t β₁ δ₁ (b - η) t htt, indMort_neg_t β₁ δ₁ (b + η) t htt,
        indEss_congr β₀ (b - η) (b + η) (birth_cell β₀ b η hηpos.le hbne hηw)]
    simp
  exact iInf_le_of_le η (iInf_le_of_le hηpos (iInf_le_of_le t (iInf_le_of_le ht hbr.le)))

/-- Generic plain-support bound (2-term): support ⊆ `{(β₀,⊥), (β₁,δ₁)}`. -/
private lemma plain_support_of_2 (r : ℝ → ℝ → ℕ∞) (β₀ β₁ δ₁ : ℝ)
    (hr : ∀ s t, t ≤ s → r s t = indEss β₀ s + indMort β₁ δ₁ s t)
    (p : EReal × EReal) (hp : mult r p ≠ 0) :
    p ∈ ({(((β₀ : ℝ) : EReal), (⊥ : EReal)),
          (((β₁ : ℝ) : EReal), ((δ₁ : ℝ) : EReal))} : Set (EReal × EReal)) := by
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
        intro hbe; apply hmem
        rw [hbe]; exact Set.mem_insert_iff.mpr (Or.inl rfl)
      exact mult_coe_bot_zero_of_ne_2 r β₀ β₁ δ₁ hr b hbne.symm
    | top => exact mult_coe_top_zero _ b
    | coe d =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      push_neg at hmem
      obtain ⟨hne1, hne2⟩ := hmem
      have h1 := (coe_pair_ne_iff b d β₁ δ₁).mp hne2
      by_cases hbd : d < b
      · exact mult_plain_eq_zero_2 r β₀ β₁ δ₁ hr b d hbd h1
      · push_neg at hbd; exact mult_coe_coe_le_zero _ b d hbd

/-- The α-truncated multiplicity at a real point `(b, d)` with `α < d` is zero off the mortal bar
(all four corners lie above α, so it reduces to the plain bracket). -/
private lemma mult_trunc_eq_zero_above (r : ℝ → ℝ → ℕ∞) (α β₀ β₁ δ₁ : ℝ)
    (hr : ∀ s t, t ≤ s → r s t = indEss β₀ s + indMort β₁ δ₁ s t)
    (b d : ℝ) (hbd : d < b) (hda : α < d) (h1 : β₁ ≠ b ∨ d ≠ δ₁) :
    mult (truncRank r α) (((b : ℝ) : EReal), ((d : ℝ) : EReal)) = 0 := by
  rw [mult_coe_coe (truncRank r α) b d hbd]
  refine le_antisymm ?_ (le_iInf fun _ => le_iInf fun _ => (zero_le : (0 : ℕ∞) ≤ _))
  set q1 : ℝ := if β₁ = b then |δ₁ - d| else |β₁ - b| with hq1def
  have hq1pos : 0 < q1 := by
    rw [hq1def]; by_cases hb : β₁ = b
    · rw [if_pos hb]
      rcases h1 with h | h
      · exact absurd hb h
      · exact abs_pos.mpr (sub_ne_zero.mpr (Ne.symm h))
    · rw [if_neg hb]; exact abs_pos.mpr (sub_ne_zero.mpr hb)
  set M : ℝ := min (min ((b - d) / 2) (d - α)) q1 with hMdef
  have hM1 : M ≤ (b - d) / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hM2 : M ≤ d - α := (min_le_left _ _).trans (min_le_right _ _)
  have hM3 : M ≤ q1 := min_le_right _ _
  have hMpos : 0 < M := lt_min (lt_min (by linarith) (by linarith)) hq1pos
  set η : ℝ := M / 2 with hηdef
  have hηpos : 0 < η := by linarith
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
  have hbr : ((truncRank r α (b - η) (d + η) - truncRank r α (b + η) (d + η)) -
      (truncRank r α (b - η) (d - η) - truncRank r α (b + η) (d - η))) = 0 := by
    have hab1 : α ≤ b - η := by linarith
    have hab2 : α ≤ b + η := by linarith
    have had1 : α ≤ d + η := by linarith
    have had2 : α ≤ d - η := by linarith
    rw [trunc_above r α _ _ hab1 had1, trunc_above r α _ _ hab2 had1,
        trunc_above r α _ _ hab1 had2, trunc_above r α _ _ hab2 had2]
    exact bracket_zero_2 r β₀ β₁ δ₁ hr b d η hηpos.le hbd hηw hh1
  exact iInf_le_of_le η (iInf_le_of_le ⟨hηpos, hηw⟩ hbr.le)

/-- Bracket at the truncation floor `d = α`, mortal dying ABOVE α (`δ₁ > α`): the mortal is
killed at the `(α + η)` corners, so only the essential birth cell (β₀ ≠ b) matters. -/
private lemma bracket_zero_alpha_2 (r : ℝ → ℝ → ℕ∞) (α β₀ β₁ δ₁ b η : ℝ)
    (hr : ∀ s t, t ≤ s → r s t = indEss β₀ s + indMort β₁ δ₁ s t)
    (hη : 0 < η) (hbα : α < b) (hηw : η < (b - α) / 2)
    (hβ : β₀ ≠ b) (hβw : η < |β₀ - b|) (hd1 : α < δ₁) (hη1 : η < δ₁ - α) :
    ((truncRank r α (b - η) (α + η) - truncRank r α (b + η) (α + η)) -
      (truncRank r α (b - η) (α - η) - truncRank r α (b + η) (α - η))) = 0 := by
  have hb1 : α ≤ b - η := by linarith
  have hb2 : α ≤ b + η := by linarith
  have ht1 : α ≤ α + η := by linarith
  have ht2 : α - η < α := by linarith
  have hle1 : α + η ≤ b - η := by linarith
  have hle2 : α + η ≤ b + η := by linarith
  have hnd1 : ¬ (δ₁ < α + η) := by linarith
  rw [trunc_above r α _ _ hb1 ht1, trunc_above r α _ _ hb2 ht1,
      truncRank_zero_of_lt r α _ _ ht2, truncRank_zero_of_lt r α _ _ ht2,
      hr (b - η) (α + η) hle1, hr (b + η) (α + η) hle2,
      indMort_neg_t β₁ δ₁ (b - η) (α + η) hnd1, indMort_neg_t β₁ δ₁ (b + η) (α + η) hnd1,
      indEss_congr β₀ (b - η) (b + η) (birth_cell β₀ b η hη.le hβ hβw)]
  simp

private lemma mult_trunc_eq_zero_floor (r : ℝ → ℝ → ℕ∞) (α β₀ β₁ δ₁ : ℝ) (hd1 : α < δ₁)
    (hr : ∀ s t, t ≤ s → r s t = indEss β₀ s + indMort β₁ δ₁ s t)
    (b : ℝ) (hbα : α < b) (hb0 : β₀ ≠ b) :
    mult (truncRank r α) (((b : ℝ) : EReal), ((α : ℝ) : EReal)) = 0 := by
  rw [mult_coe_coe (truncRank r α) b α hbα]
  refine le_antisymm ?_ (le_iInf fun _ => le_iInf fun _ => (zero_le : (0 : ℕ∞) ≤ _))
  set M : ℝ := min (min ((b - α) / 2) (δ₁ - α)) |β₀ - b| with hMdef
  have hM1 : M ≤ (b - α) / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hM2 : M ≤ δ₁ - α := (min_le_left _ _).trans (min_le_right _ _)
  have hM3 : M ≤ |β₀ - b| := min_le_right _ _
  have hMpos : 0 < M := lt_min (lt_min (by linarith) (by linarith))
    (abs_pos.mpr (sub_ne_zero.mpr hb0))
  set η : ℝ := M / 2 with hηdef
  have hηpos : 0 < η := by linarith
  have hηw : η < (b - α) / 2 := by linarith
  have hbr : ((truncRank r α (b - η) (α + η) - truncRank r α (b + η) (α + η)) -
      (truncRank r α (b - η) (α - η) - truncRank r α (b + η) (α - η))) = 0 :=
    bracket_zero_alpha_2 r α β₀ β₁ δ₁ b η hr hηpos (by linarith) (by linarith) hb0
      (by linarith) hd1 (by linarith)
  exact iInf_le_of_le η (iInf_le_of_le ⟨hηpos, hηw⟩ hbr.le)

/-- Generic truncated-support bound (2-term, mortal dying ABOVE α): support ⊆ `{(β₀,α), (β₁,δ₁)}`. -/
private lemma trunc_support_of_2 (r : ℝ → ℝ → ℕ∞) (α β₀ β₁ δ₁ : ℝ) (hd1 : α < δ₁)
    (hr : ∀ s t, t ≤ s → r s t = indEss β₀ s + indMort β₁ δ₁ s t)
    (p : EReal × EReal) (hp : mult (truncRank r α) p ≠ 0) :
    p ∈ ({(((β₀ : ℝ) : EReal), ((α : ℝ) : EReal)),
          (((β₁ : ℝ) : EReal), ((δ₁ : ℝ) : EReal))} : Set (EReal × EReal)) := by
  by_contra hmem
  apply hp
  obtain ⟨x, y⟩ := p
  induction x using EReal.rec with
  | bot => exact mult_zero_of_born _ _ (Or.inl rfl)
  | top => exact mult_zero_of_born _ _ (Or.inr rfl)
  | coe b =>
    induction y using EReal.rec with
    | bot => exact mult_trunc_bot_zero r α b
    | top => exact mult_coe_top_zero _ b
    | coe d =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      push_neg at hmem
      obtain ⟨hne1, hne2⟩ := hmem
      have h0 := (coe_pair_ne_iff b d β₀ α).mp hne1
      have h1 := (coe_pair_ne_iff b d β₁ δ₁).mp hne2
      by_cases hbd : d < b
      · by_cases hda : d < α
        · exact mult_trunc_lt_zero r α b d hbd hda
        · push_neg at hda
          rcases lt_or_eq_of_le hda with hdlt | hde
          · exact mult_trunc_eq_zero_above r α β₀ β₁ δ₁ hr b d hbd hdlt h1
          · have hb0 : β₀ ≠ b := by
              rcases h0 with h | h
              · exact h
              · exact (h hde.symm).elim
            rw [← hde]
            exact mult_trunc_eq_zero_floor r α β₀ β₁ δ₁ hd1 hr b (by linarith) hb0
      · push_neg at hbd; exact mult_coe_coe_le_zero _ b d hbd

/-- Bracket at the truncation floor `d = α`, mortal dying BELOW α (`δ₁ < α`): the mortal is
active at the `(α + η)` corners, so BOTH birth cells must be constant (β₀ ≠ b and β₁ ≠ b). -/
private lemma bracket_zero_alpha_below_2 (r : ℝ → ℝ → ℕ∞) (α β₀ β₁ δ₁ b η : ℝ)
    (hr : ∀ s t, t ≤ s → r s t = indEss β₀ s + indMort β₁ δ₁ s t)
    (hη : 0 < η) (hbα : α < b) (hηw : η < (b - α) / 2)
    (hβ0 : β₀ ≠ b) (hβ0w : η < |β₀ - b|)
    (hβ1 : β₁ ≠ b) (hβ1w : η < |β₁ - b|) :
    ((truncRank r α (b - η) (α + η) - truncRank r α (b + η) (α + η)) -
      (truncRank r α (b - η) (α - η) - truncRank r α (b + η) (α - η))) = 0 := by
  have hb1 : α ≤ b - η := by linarith
  have hb2 : α ≤ b + η := by linarith
  have ht1 : α ≤ α + η := by linarith
  have ht2 : α - η < α := by linarith
  have hle1 : α + η ≤ b - η := by linarith
  have hle2 : α + η ≤ b + η := by linarith
  rw [trunc_above r α _ _ hb1 ht1, trunc_above r α _ _ hb2 ht1,
      truncRank_zero_of_lt r α _ _ ht2, truncRank_zero_of_lt r α _ _ ht2,
      hr (b - η) (α + η) hle1, hr (b + η) (α + η) hle2,
      indEss_congr β₀ (b - η) (b + η) (birth_cell β₀ b η hη.le hβ0 hβ0w),
      indMort_congr_s β₁ δ₁ (b - η) (b + η) (α + η) (birth_cell β₁ b η hη.le hβ1 hβ1w)]
  simp

private lemma mult_trunc_eq_zero_clamp (r : ℝ → ℝ → ℕ∞) (α β₀ β₁ δ₁ : ℝ) (hd1 : δ₁ < α)
    (hr : ∀ s t, t ≤ s → r s t = indEss β₀ s + indMort β₁ δ₁ s t)
    (b : ℝ) (hbα : α < b) (hb0 : β₀ ≠ b) (hb1 : β₁ ≠ b) :
    mult (truncRank r α) (((b : ℝ) : EReal), ((α : ℝ) : EReal)) = 0 := by
  rw [mult_coe_coe (truncRank r α) b α hbα]
  refine le_antisymm ?_ (le_iInf fun _ => le_iInf fun _ => (zero_le : (0 : ℕ∞) ≤ _))
  set M : ℝ := min (min ((b - α) / 2) |β₀ - b|) |β₁ - b| with hMdef
  have hM1 : M ≤ (b - α) / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hM2 : M ≤ |β₀ - b| := (min_le_left _ _).trans (min_le_right _ _)
  have hM3 : M ≤ |β₁ - b| := min_le_right _ _
  have hMpos : 0 < M := lt_min (lt_min (by linarith) (abs_pos.mpr (sub_ne_zero.mpr hb0)))
    (abs_pos.mpr (sub_ne_zero.mpr hb1))
  set η : ℝ := M / 2 with hηdef
  have hηpos : 0 < η := by linarith
  have hηw : η < (b - α) / 2 := by linarith
  have hbr : ((truncRank r α (b - η) (α + η) - truncRank r α (b + η) (α + η)) -
      (truncRank r α (b - η) (α - η) - truncRank r α (b + η) (α - η))) = 0 :=
    bracket_zero_alpha_below_2 r α β₀ β₁ δ₁ b η hr hηpos (by linarith) (by linarith) hb0
      (by linarith) hb1 (by linarith)
  exact iInf_le_of_le η (iInf_le_of_le ⟨hηpos, hηw⟩ hbr.le)

/-- Generic truncated-support bound (2-term, mortal dying BELOW α — it CLAMPS to the α-row):
support ⊆ `{(β₀,α), (β₁,α)}`. -/
private lemma trunc_support_clamp_of (r : ℝ → ℝ → ℕ∞) (α β₀ β₁ δ₁ : ℝ) (hd1 : δ₁ < α)
    (hr : ∀ s t, t ≤ s → r s t = indEss β₀ s + indMort β₁ δ₁ s t)
    (p : EReal × EReal) (hp : mult (truncRank r α) p ≠ 0) :
    p ∈ ({(((β₀ : ℝ) : EReal), ((α : ℝ) : EReal)),
          (((β₁ : ℝ) : EReal), ((α : ℝ) : EReal))} : Set (EReal × EReal)) := by
  by_contra hmem
  apply hp
  obtain ⟨x, y⟩ := p
  induction x using EReal.rec with
  | bot => exact mult_zero_of_born _ _ (Or.inl rfl)
  | top => exact mult_zero_of_born _ _ (Or.inr rfl)
  | coe b =>
    induction y using EReal.rec with
    | bot => exact mult_trunc_bot_zero r α b
    | top => exact mult_coe_top_zero _ b
    | coe d =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      push_neg at hmem
      obtain ⟨hne1, hne2⟩ := hmem
      have hb0 : β₀ ≠ b ∨ d ≠ α := (coe_pair_ne_iff b d β₀ α).mp hne1
      have hb1 : β₁ ≠ b ∨ d ≠ α := (coe_pair_ne_iff b d β₁ α).mp hne2
      by_cases hbd : d < b
      · by_cases hda : d < α
        · exact mult_trunc_lt_zero r α b d hbd hda
        · push_neg at hda
          rcases lt_or_eq_of_le hda with hdlt | hde
          · have h1 : β₁ ≠ b ∨ d ≠ δ₁ :=
              Or.inr (ne_of_lt (lt_trans hd1 hdlt)).symm
            exact mult_trunc_eq_zero_above r α β₀ β₁ δ₁ hr b d hbd hdlt h1
          · have hbβ0 : β₀ ≠ b := by
              rcases hb0 with h | h
              · exact h
              · exact (h hde.symm).elim
            have hbβ1 : β₁ ≠ b := by
              rcases hb1 with h | h
              · exact h
              · exact (h hde.symm).elim
            rw [← hde]
            exact mult_trunc_eq_zero_clamp r α β₀ β₁ δ₁ hd1 hr b (by linarith) hbβ0 hbβ1
      · push_neg at hbd; exact mult_coe_coe_le_zero _ b d hbd

/-! ### Step 6: the support, finite-support, and agreement hypotheses -/

/-- The X-truncated diagram (α = 0) is supported on `{(20, 0), (10, 0.5)}`. -/
theorem truncX_support (p : EReal × EReal)
    (hp : mult (truncRank (rankFn stageX JX) 0) p ≠ 0) :
    p ∈ ({(((20 : ℝ) : EReal), ((0 : ℝ) : EReal)),
          (((10 : ℝ) : EReal), ((0.5 : ℝ) : EReal))} : Set (EReal × EReal)) :=
  trunc_support_of_2 (rankFn stageX JX) 0 20 10 0.5 (by norm_num : (0 : ℝ) < 0.5) rankX_eq p hp

/-- The Y-truncated diagram (α = 0) is supported on `{(20, 0), (10, 0)}` (the mortal `(10,−1)`
clamps to the α-row). -/
theorem truncY_support (p : EReal × EReal)
    (hp : mult (truncRank (rankFn stageY JY) 0) p ≠ 0) :
    p ∈ ({(((20 : ℝ) : EReal), ((0 : ℝ) : EReal)),
          (((10 : ℝ) : EReal), ((0 : ℝ) : EReal))} : Set (EReal × EReal)) :=
  trunc_support_clamp_of (rankFn stageY JY) 0 20 10 (-1) (by norm_num : (-1 : ℝ) < 0) rankY_eq p hp

/-- The plain X diagram is supported on `{(20,⊥), (10,0.5)}`, hence finite. -/
theorem hFinX : {p : EReal × EReal | (mult (rankFn stageX JX)) p ≠ 0}.Finite := by
  have hsub : {p : EReal × EReal | (mult (rankFn stageX JX)) p ≠ 0} ⊆
      ({(((20 : ℝ) : EReal), (⊥ : EReal)),
        (((10 : ℝ) : EReal), ((0.5 : ℝ) : EReal))} : Set (EReal × EReal)) := by
    intro p hp
    exact plain_support_of_2 (rankFn stageX JX) 20 10 0.5 rankX_eq p hp
  have hSfin : ({(((20 : ℝ) : EReal), (⊥ : EReal)),
        (((10 : ℝ) : EReal), ((0.5 : ℝ) : EReal))} : Set (EReal × EReal)).Finite :=
    Set.finite_insert.mpr (Set.finite_singleton _)
  exact hSfin.subset hsub

/-- The plain Y diagram is supported on `{(20,⊥), (10,−1)}`, hence finite. -/
theorem hFinY : {p : EReal × EReal | (mult (rankFn stageY JY)) p ≠ 0}.Finite := by
  have hsub : {p : EReal × EReal | (mult (rankFn stageY JY)) p ≠ 0} ⊆
      ({(((20 : ℝ) : EReal), (⊥ : EReal)),
        (((10 : ℝ) : EReal), ((-1 : ℝ) : EReal))} : Set (EReal × EReal)) := by
    intro p hp
    exact plain_support_of_2 (rankFn stageY JY) 20 10 (-1) rankY_eq p hp
  have hSfin : ({(((20 : ℝ) : EReal), (⊥ : EReal)),
        (((10 : ℝ) : EReal), ((-1 : ℝ) : EReal))} : Set (EReal × EReal)).Finite :=
    Set.finite_insert.mpr (Set.finite_singleton _)
  exact hSfin.subset hsub

private lemma coe_not_lt_bot (a : ℝ) : ¬ (((a : ℝ) : EReal) < ⊥) := by
  intro h
  exact EReal.coe_ne_bot a (le_antisymm (le_of_lt h) bot_le)

/-- The agreement hypothesis: on `QNE α` (α = 0) the plain and α-truncated diagrams coincide.
X's only QNE support point is `(10, 0.5)` (plain = truncated = 1); Y has no QNE support points. -/
theorem hAgree : ∀ p ∈ QNE 0,
    mult (rankFn stageX JX) p = mult (truncRank (rankFn stageX JX) 0) p ∧
    mult (rankFn stageY JY) p = mult (truncRank (rankFn stageY JY) 0) p := by
  intro p hp
  refine ⟨?_, ?_⟩
  · by_cases hpX : p = (((10 : ℝ) : EReal), ((0.5 : ℝ) : EReal))
    · rw [hpX, multX_10_05, multTruncX_10_05]
    · have hpx : mult (rankFn stageX JX) p = 0 := by
        by_contra hne
        have hsup := plain_support_of_2 (rankFn stageX JX) 20 10 0.5 rankX_eq p hne
        rcases Set.mem_insert_iff.mp hsup with heq | heq
        · rw [heq] at hp; exact absurd hp.2 (coe_not_lt_bot 0)
        · exact hpX heq
      have hptx : mult (truncRank (rankFn stageX JX) 0) p = 0 := by
        by_contra hne
        have hsup := truncX_support p hne
        rcases Set.mem_insert_iff.mp hsup with heq | heq
        · rw [heq] at hp
          exact absurd (EReal.coe_lt_coe_iff.mp hp.2) (lt_irrefl 0)
        · exact hpX heq
      rw [hpx, hptx]
  · have hpy : mult (rankFn stageY JY) p = 0 := by
      by_contra hne
      have hsup := plain_support_of_2 (rankFn stageY JY) 20 10 (-1) rankY_eq p hne
      rcases Set.mem_insert_iff.mp hsup with heq | heq
      · rw [heq] at hp; exact absurd hp.2 (coe_not_lt_bot 0)
      · rw [heq] at hp
        exact absurd (EReal.coe_lt_coe_iff.mp hp.2) (by linarith : ¬ (0 : ℝ) < -1)
    have hpty : mult (truncRank (rankFn stageY JY) 0) p = 0 := by
      by_contra hne
      have hsup := truncY_support p hne
      rcases Set.mem_insert_iff.mp hsup with heq | heq
      · rw [heq] at hp
        exact absurd (EReal.coe_lt_coe_iff.mp hp.2) (lt_irrefl 0)
      · rw [heq] at hp
        exact absurd (EReal.coe_lt_coe_iff.mp hp.2) (lt_irrefl 0)
    rw [hpy, hpty]

/-! ### Step 5b: the truncated-pair stability bijection δ on the Copies -/

abbrev DX : EReal × EReal → ℕ∞ := mult (truncRank (rankFn stageX JX) 0)
abbrev DY : EReal × EReal → ℕ∞ := mult (truncRank (rankFn stageY JY) 0)
abbrev PX : EReal × EReal := (((10 : ℝ) : EReal), ((0.5 : ℝ) : EReal))
abbrev PY : EReal × EReal := (((10 : ℝ) : EReal), ((0 : ℝ) : EReal))
abbrev QE : EReal × EReal := (((20 : ℝ) : EReal), ((0 : ℝ) : EReal))

private theorem memDX_10_05 : ((0 : ℕ) : ℕ∞) <
    mult (truncRank (rankFn stageX JX) 0) (((10 : ℝ) : EReal), ((0.5 : ℝ) : EReal)) := by
  rw [Nat.cast_zero, multTruncX_10_05]; exact zero_lt_one
private theorem memDX_20_0 : ((0 : ℕ) : ℕ∞) <
    mult (truncRank (rankFn stageX JX) 0) (((20 : ℝ) : EReal), ((0 : ℝ) : EReal)) := by
  rw [Nat.cast_zero, multTruncX_20_0]; exact zero_lt_one
private theorem memDY_10_0 : ((0 : ℕ) : ℕ∞) <
    mult (truncRank (rankFn stageY JY) 0) (((10 : ℝ) : EReal), ((0 : ℝ) : EReal)) := by
  rw [Nat.cast_zero, multTruncY_10_0]; exact zero_lt_one
private theorem memDY_20_0 : ((0 : ℕ) : ℕ∞) <
    mult (truncRank (rankFn stageY JY) 0) (((20 : ℝ) : EReal), ((0 : ℝ) : EReal)) := by
  rw [Nat.cast_zero, multTruncY_20_0]; exact zero_lt_one

/-- `closeE` for real-coefficient points, stated in terms of real inequalities. -/
private lemma closeE_coe_coe (a b r : ℝ) (h1 : a ≤ b + r) (h2 : b ≤ a + r) :
    closeE ((a : ℝ) : EReal) ((b : ℝ) : EReal) r := by
  refine ⟨?_, ?_⟩
  · rw [← EReal.coe_add, EReal.coe_le_coe_iff]; exact h1
  · rw [← EReal.coe_add, EReal.coe_le_coe_iff]; exact h2

private lemma closeE_10_10 : closeE (((10 : ℝ) : EReal)) (((10 : ℝ) : EReal)) 1 :=
  closeE_coe_coe 10 10 1 (by norm_num) (by norm_num)
private lemma closeE_05_0 : closeE (((0.5 : ℝ) : EReal)) (((0 : ℝ) : EReal)) 1 :=
  closeE_coe_coe 0.5 0 1 (by norm_num) (by norm_num)
private lemma closeE_20_20 : closeE (((20 : ℝ) : EReal)) (((20 : ℝ) : EReal)) 1 :=
  closeE_coe_coe 20 20 1 (by norm_num) (by norm_num)
private lemma closeE_0_0 : closeE (((0 : ℝ) : EReal)) (((0 : ℝ) : EReal)) 1 :=
  closeE_coe_coe 0 0 1 (by norm_num) (by norm_num)

/-- Every extended real is `1`-close to itself (`⊥ + 1 = ⊥`, `⊤ + 1 = ⊤`, reals shift by 1). -/
private lemma closeE_self (a : EReal) : closeE a a 1 := by
  have h1ne : (((1 : ℝ) : EReal)) ≠ ⊥ := EReal.coe_ne_bot 1
  constructor
  · induction a using EReal.rec with
    | bot => exact (EReal.bot_add (1 : EReal)).symm.le
    | top => exact (EReal.top_add_of_ne_bot h1ne).symm.le
    | coe v => rw [← EReal.coe_add, EReal.coe_le_coe_iff]; linarith
  · induction a using EReal.rec with
    | bot => exact (EReal.bot_add (1 : EReal)).symm.le
    | top => exact (EReal.top_add_of_ne_bot h1ne).symm.le
    | coe v => rw [← EReal.coe_add, EReal.coe_le_coe_iff]; linarith

/-- Off-diagonal copies of the X-truncated diagram: point in `{QE, PX}` and index 0. -/
private lemma DX_offdiag (q : {q : (EReal × EReal) × ℕ // (q.2 : ℕ∞) < DX q.1}) :
    (q.1.1 = QE ∨ q.1.1 = PX) ∧ q.1.2 = 0 := by
  have hp0 : ((q.1.2 : ℕ) : ℕ∞) < mult (truncRank (rankFn stageX JX) 0) q.1.1 := q.property
  have hq : mult (truncRank (rankFn stageX JX) 0) q.1.1 ≠ 0 := by
    intro h0; rw [h0] at hp0
    exact absurd hp0 (not_lt.mpr (zero_le : (0 : ℕ∞) ≤ (q.1.2 : ℕ∞)))
  rcases Set.mem_insert_iff.mp (truncX_support q.1.1 hq) with hP | hP
  · refine ⟨Or.inl hP, ?_⟩
    rw [hP, multTruncX_20_0] at hp0
    exact Nat.lt_one_iff.mp (ENat.natCast_lt_natCast.mp hp0)
  · refine ⟨Or.inr hP, ?_⟩
    rw [hP, multTruncX_10_05] at hp0
    exact Nat.lt_one_iff.mp (ENat.natCast_lt_natCast.mp hp0)

/-- Off-diagonal copies of the Y-truncated diagram: point in `{QE, PY}` and index 0. -/
private lemma DY_offdiag (q : {q : (EReal × EReal) × ℕ // (q.2 : ℕ∞) < DY q.1}) :
    (q.1.1 = QE ∨ q.1.1 = PY) ∧ q.1.2 = 0 := by
  have hp0 : ((q.1.2 : ℕ) : ℕ∞) < mult (truncRank (rankFn stageY JY) 0) q.1.1 := q.property
  have hq : mult (truncRank (rankFn stageY JY) 0) q.1.1 ≠ 0 := by
    intro h0; rw [h0] at hp0
    exact absurd hp0 (not_lt.mpr (zero_le : (0 : ℕ∞) ≤ (q.1.2 : ℕ∞)))
  rcases Set.mem_insert_iff.mp (truncY_support q.1.1 hq) with hP | hP
  · refine ⟨Or.inl hP, ?_⟩
    rw [hP, multTruncY_20_0] at hp0
    exact Nat.lt_one_iff.mp (ENat.natCast_lt_natCast.mp hp0)
  · refine ⟨Or.inr hP, ?_⟩
    rw [hP, multTruncY_10_0] at hp0
    exact Nat.lt_one_iff.mp (ENat.natCast_lt_natCast.mp hp0)

private lemma PX_ne_QE : PX ≠ QE := by
  intro h; have h2 := congrArg Prod.fst h
  exact absurd h2 (by norm_num [PX, QE] : ¬ (((10 : ℝ) : EReal) = ((20 : ℝ) : EReal)))
private lemma PY_ne_QE : PY ≠ QE := by
  intro h; have h2 := congrArg Prod.fst h
  exact absurd h2 (by norm_num [PY, QE] : ¬ (((10 : ℝ) : EReal) = ((20 : ℝ) : EReal)))

/-- The explicit truncated-pair bijection δ: X's clamped mortal copy `(10,0.5)` ↦ Y's clamped
mortal copy `(10,0)`, the clamped essential `(20,0)` ↦ `(20,0)`, and the diagonal summand
identically. Both directions are `1`-close. -/
theorem hDelta :
    ∃ δ : Copies DX ≃ Copies DY,
        (∀ a, closeE (pt a).1 (pt (δ a)).1 1 ∧ closeE (pt a).2 (pt (δ a)).2 1) ∧
        (∀ b, closeE (pt (δ.symm b)).1 (pt b).1 1 ∧ closeE (pt (δ.symm b)).2 (pt b).2 1) := by
  classical
  let toFun : Copies DX → Copies DY := fun c =>
    match c with
    | Sum.inl q => if q.1.1 = PX then Sum.inl ⟨(PY, 0), memDY_10_0⟩
                   else Sum.inl ⟨(QE, 0), memDY_20_0⟩
    | Sum.inr x => Sum.inr x
  let invFun : Copies DY → Copies DX := fun c =>
    match c with
    | Sum.inl q => if q.1.1 = PY then Sum.inl ⟨(PX, 0), memDX_10_05⟩
                   else Sum.inl ⟨(QE, 0), memDX_20_0⟩
    | Sum.inr x => Sum.inr x
  have hleft : ∀ c, invFun (toFun c) = c := by
    intro c
    match c with
    | Sum.inl q =>
      obtain ⟨hsupp, hz⟩ := DX_offdiag q
      by_cases hP : q.1.1 = PX
      · have hto : toFun (Sum.inl q) = Sum.inl ⟨(PY, 0), memDY_10_0⟩ := by
          simp only [toFun, hP, if_pos]
        rw [hto]
        have hinv : invFun (Sum.inl ⟨(PY, 0), memDY_10_0⟩) = Sum.inl ⟨(PX, 0), memDX_10_05⟩ := by
          simp [invFun]
        rw [hinv]
        apply congrArg Sum.inl
        apply Subtype.ext
        refine Prod.ext_iff.mpr ⟨hP.symm, hz.symm⟩
      · have hQ : q.1.1 = QE := by
          rcases hsupp with h | h
          · exact h
          · exact (hP h).elim
        have hto : toFun (Sum.inl q) = Sum.inl ⟨(QE, 0), memDY_20_0⟩ := by
          simp only [toFun]
          rw [if_neg hP]
        rw [hto]
        have hPYneQE : PY ≠ QE := by
          intro h; have := congrArg Prod.fst h
          simp only [PY, QE] at this; norm_num at this
        have hinv : invFun (Sum.inl ⟨(QE, 0), memDY_20_0⟩) = Sum.inl ⟨(QE, 0), memDX_20_0⟩ := by
          simp only [invFun]
          rw [if_neg (fun h => hPYneQE h.symm)]
        rw [hinv]
        apply congrArg Sum.inl
        apply Subtype.ext
        refine Prod.ext_iff.mpr ⟨hQ.symm, hz.symm⟩
    | Sum.inr x => rfl
  have hright : ∀ c, toFun (invFun c) = c := by
    intro c
    match c with
    | Sum.inl q =>
      obtain ⟨hsupp, hz⟩ := DY_offdiag q
      by_cases hP : q.1.1 = PY
      · have hinv : invFun (Sum.inl q) = Sum.inl ⟨(PX, 0), memDX_10_05⟩ := by
          simp only [invFun]
          rw [if_pos hP]
        rw [hinv]
        have hto : toFun (Sum.inl ⟨(PX, 0), memDX_10_05⟩) = Sum.inl ⟨(PY, 0), memDY_10_0⟩ := by
          simp [toFun]
        rw [hto]
        apply congrArg Sum.inl
        apply Subtype.ext
        refine Prod.ext_iff.mpr ⟨hP.symm, hz.symm⟩
      · have hQ : q.1.1 = QE := by
          rcases hsupp with h | h
          · exact h
          · exact (hP h).elim
        have hinv : invFun (Sum.inl q) = Sum.inl ⟨(QE, 0), memDX_20_0⟩ := by
          simp only [invFun]
          rw [if_neg hP]
        rw [hinv]
        have hQE : QE ≠ PX := Ne.symm PX_ne_QE
        have hto : toFun (Sum.inl ⟨(QE, 0), memDX_20_0⟩) = Sum.inl ⟨(QE, 0), memDY_20_0⟩ := by
          simp only [toFun]
          rw [if_neg hQE]
        rw [hto]
        apply congrArg Sum.inl
        apply Subtype.ext
        refine Prod.ext_iff.mpr ⟨hQ.symm, hz.symm⟩
    | Sum.inr x => rfl
  let δ : Copies DX ≃ Copies DY := Equiv.mk toFun invFun hleft hright
  have hδ : ∀ c, δ c = toFun c := fun c => rfl
  have hδsymm : ∀ c, δ.symm c = invFun c := fun c => rfl
  refine ⟨δ, ?_, ?_⟩
  · intro a
    match a with
    | Sum.inl q =>
      obtain ⟨hsupp, hz⟩ := DX_offdiag q
      rw [hδ]
      rcases hsupp with hQ | hP
      · have hne : q.1.1 ≠ PX := by
          rw [hQ]
          exact fun h => PX_ne_QE h.symm
        have hto : toFun (Sum.inl q) = Sum.inl ⟨(QE, 0), memDY_20_0⟩ := by
          simp only [toFun]
          rw [if_neg hne]
        have hpa : pt (Sum.inl q) = QE := hQ
        have hpb : pt (toFun (Sum.inl q)) = QE := by rw [hto]; rfl
        rw [hpa, hpb]
        exact ⟨closeE_20_20, closeE_0_0⟩
      · have hto : toFun (Sum.inl q) = Sum.inl ⟨(PY, 0), memDY_10_0⟩ := by
          simp only [toFun]
          rw [if_pos hP]
        have hpa : pt (Sum.inl q) = PX := hP
        have hpb : pt (toFun (Sum.inl q)) = PY := by rw [hto]; rfl
        rw [hpa, hpb]
        exact ⟨closeE_10_10, closeE_05_0⟩
    | Sum.inr x =>
      show closeE (pt (Sum.inr x)).1 (pt (toFun (Sum.inr x))).1 1 ∧
           closeE (pt (Sum.inr x)).2 (pt (toFun (Sum.inr x))).2 1
      have hto : toFun (Sum.inr x) = Sum.inr x := rfl
      rw [hto]
      exact ⟨closeE_self x.1, closeE_self x.1⟩
  · intro b
    match b with
    | Sum.inl q =>
      obtain ⟨hsupp, hz⟩ := DY_offdiag q
      rw [hδsymm]
      rcases hsupp with hQ | hP
      · have hne : q.1.1 ≠ PY := by
          rw [hQ]
          exact fun h => PY_ne_QE h.symm
        have hinv : invFun (Sum.inl q) = Sum.inl ⟨(QE, 0), memDX_20_0⟩ := by
          simp only [invFun]
          rw [if_neg hne]
        have hsa : pt (Sum.inl q) = QE := hQ
        have hsb : pt (invFun (Sum.inl q)) = QE := by rw [hinv]; rfl
        rw [hsa, hsb]
        exact ⟨closeE_20_20, closeE_0_0⟩
      · have hinv : invFun (Sum.inl q) = Sum.inl ⟨(PX, 0), memDX_10_05⟩ := by
          simp only [invFun]
          rw [if_pos hP]
        have hsa : pt (Sum.inl q) = PY := hP
        have hsb : pt (invFun (Sum.inl q)) = PX := by rw [hinv]; rfl
        rw [hsa, hsb]
        exact ⟨closeE_10_10, closeE_05_0⟩
    | Sum.inr x =>
      show closeE (pt (invFun (Sum.inr x))).1 (pt (Sum.inr x)).1 1 ∧
           closeE (pt (invFun (Sum.inr x))).2 (pt (Sum.inr x)).2 1
      have hinv : invFun (Sum.inr x) = Sum.inr x := rfl
      rw [hinv]
      exact ⟨closeE_self x.1, closeE_self x.1⟩

/-! ### Step 7: the no-γ core (SatisfiesIIV (i) fails at X's QNE point `(10, 0.5)`) -/

/-- No copy of the Y **plain** diagram — off-diagonal or diagonal — is `1`-close to the point
`(10, 0.5)`: the off-diagonal support is `{(20, ⊥), (10, −1)}` (both fail `closeE`), and no
diagonal point is `1`-close to `(10, 0.5)` either. -/
private lemma no_close_partner (c : Copies (mult (rankFn stageY JY)))
    (h1 : closeE (((10 : ℝ) : EReal)) (pt c).1 1)
    (h2 : closeE (((0.5 : ℝ) : EReal)) (pt c).2 1) : False := by
  rcases c with q | ⟨y1, y2⟩
  · -- off-diagonal copy: `pt c = q.val.1`, a positive-multiplicity point of Y's plain diagram
    have hp' : ((q.val.2 : ℕ) : ℕ∞) < mult (rankFn stageY JY) q.val.1 := q.property
    have hne : mult (rankFn stageY JY) q.val.1 ≠ 0 := by
      intro h0; rw [h0] at hp'
      exact absurd hp' (not_lt.mpr (zero_le : (0 : ℕ∞) ≤ (q.val.2 : ℕ∞)))
    have hmem := plain_support_of_2 (rankFn stageY JY) 20 10 (-1) rankY_eq q.val.1 hne
    change closeE (((10 : ℝ) : EReal)) q.val.1.1 1 at h1
    change closeE (((0.5 : ℝ) : EReal)) q.val.1.2 1 at h2
    rcases Set.mem_insert_iff.mp hmem with heq | hmem2
    · -- `(20, ⊥)`: `closeE 10 20 1` needs `20 ≤ 10 + 1 = 11`, false
      rw [heq] at h1
      dsimp only at h1
      have h := h1.2
      rw [← EReal.coe_add, EReal.coe_le_coe_iff] at h
      exact absurd h (by norm_num : ¬ ((20 : ℝ) ≤ 10 + 1))
    · -- `(10, −1)`: `closeE 0.5 (−1) 1` needs `0.5 ≤ −1 + 1 = 0`, false
      rw [Set.mem_singleton_iff] at hmem2
      rw [hmem2] at h2
      dsimp only at h2
      have h := h2.1
      rw [← EReal.coe_add, EReal.coe_le_coe_iff] at h
      exact absurd h (by norm_num : ¬ ((0.5 : ℝ) ≤ -1 + 1))
  · -- diagonal copy: `pt c = (y1, y1)` forces `y1` into two disjoint intervals
    change closeE (((10 : ℝ) : EReal)) y1 1 at h1
    change closeE (((0.5 : ℝ) : EReal)) y1 1 at h2
    obtain ⟨h1a, h1b⟩ := h1
    obtain ⟨h2a, h2b⟩ := h2
    induction y1 using EReal.rec with
    | bot => rw [EReal.bot_add] at h1a
             exact absurd h1a (not_le.mpr (EReal.bot_lt_coe 10))
    | top => rw [← EReal.coe_add] at h2b
             exact absurd h2b (not_le.mpr (EReal.coe_lt_top (0.5 + 1)))
    | coe v =>
      rw [← EReal.coe_add, EReal.coe_le_coe_iff] at h1a
      rw [← EReal.coe_add, EReal.coe_le_coe_iff] at h2b
      linarith

/-- Step 7: the forward closeness clause of `SatisfiesIIV` (i) fails at the witness copy of
X's QNE bar `(10, 0.5)`: no Y copy is `1`-close to it in both coordinates. -/
theorem surg_closeE_false
    (γ : Copies (mult (rankFn stageX JX)) ≃ Copies (mult (rankFn stageY JY)))
    (h₁ : ∀ a, pt a ∈ QNE 0 → closeE (pt a).1 (pt (γ a)).1 1 ∧ closeE (pt a).2 (pt (γ a)).2 1) :
    False := by
  have hz : ((0 : ℕ) : ℕ∞) <
      mult (rankFn stageX JX) (((10 : ℝ) : EReal), ((0.5 : ℝ) : EReal)) := by
    rw [Nat.cast_zero, multX_10_05]; exact zero_lt_one
  set a : Copies (mult (rankFn stageX JX)) :=
    Sum.inl ⟨⟨(((10 : ℝ) : EReal), ((0.5 : ℝ) : EReal)), (0 : ℕ)⟩, hz⟩ with hadef
  have hne : pt a ∈ QNE 0 := by
    rw [hadef]
    exact ⟨EReal.coe_lt_coe_iff.mpr (by norm_num : (0 : ℝ) < 10),
           EReal.coe_lt_coe_iff.mpr (by norm_num : (0 : ℝ) < 0.5)⟩
  obtain ⟨hf1, hf2⟩ := h₁ a hne
  have hpa1 : (pt a).1 = ((10 : ℝ) : EReal) := by rw [hadef]; rfl
  have hpa2 : (pt a).2 = ((0.5 : ℝ) : EReal) := by rw [hadef]; rfl
  rw [hpa1] at hf1
  rw [hpa2] at hf2
  exact no_close_partner (γ a) hf1 hf2

/-! ### Step 8: the falsified published theorem (surgery_qtame) -/

set_option linter.unusedVariables false in
/-- **The published `theorem_4_5_lemma_4_6_corrected_surgery_qtame` is FALSE.**

Instantiate its binder list at `ιX = Fin 3`, `stageX`/`JX` (the `(20,⊥),(10,0.5)` merge tree)
and `ιY = Fin 3`, `stageY`/`JY` (the `(20,⊥),(10,−1)` merge tree), with `α = 0` and `ε = 1`.
Every hypothesis of the published statement holds here — `hLawX`/`hLawY` (genuine modules),
`hQX`/`hQY`, `hDiagX`/`hDiagY`, `hFinX`/`hFinY`, `hAgree`, and `hδ` (the two α-truncated
diagrams are `1`-bijection-equivalent: `D̃_X = {(10,0.5), (20,0)}` vs `D̃_Y = {(10,0), (20,0)}`,
matched by δ) — yet the asserted conclusion FAILS: Y's bar `(10, −1)` dies far below α = 0, is
invisible to the truncated bijection, and no Y copy is `1`-close to X's QNE point `(10, 0.5)`.
The binder order below mirrors the published stub character by character, with `α := 0`,
`ε := 1`; the conclusion is negated (`SatisfiesIIV` fails, so `∃ γ` is impossible). -/
theorem surgery_qtame_false
    (hε : (0:ℝ) ≤ 1)
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    (hQX : ∀ s t : ℝ, rankFn stageX JX s t ≠ ⊤)
    (hQY : ∀ s t : ℝ, rankFn stageY JY s t ≠ ⊤)
    (hDiagX : IsDiagramLike (mult (rankFn stageX JX)))
    (hDiagY : IsDiagramLike (mult (rankFn stageY JY)))
    (hFinX : {p : EReal × EReal | (mult (rankFn stageX JX)) p ≠ 0}.Finite)
    (hFinY : {p : EReal × EReal | (mult (rankFn stageY JY)) p ≠ 0}.Finite)
    (hAgree : ∀ p ∈ QNE 0, mult (rankFn stageX JX) p = mult (truncRank (rankFn stageX JX) 0) p ∧
                            mult (rankFn stageY JY) p = mult (truncRank (rankFn stageY JY) 0) p)
    (hδ : ∃ δ : Copies (mult (truncRank (rankFn stageX JX) 0))
        ≃ Copies (mult (truncRank (rankFn stageY JY) 0)),
        (∀ a, closeE (pt a).1 (pt (δ a)).1 1 ∧ closeE (pt a).2 (pt (δ a)).2 1) ∧
        (∀ b, closeE (pt (δ.symm b)).1 (pt b).1 1 ∧ closeE (pt (δ.symm b)).2 (pt b).2 1)) :
    (∃ γ : Copies (mult (rankFn stageX JX)) ≃ Copies (mult (rankFn stageY JY)),
      SatisfiesIIV γ 0 1) → False := by
  rintro ⟨γ, h₁, h₂, h₃, h₄⟩
  exact surg_closeE_false γ h₁

/-- The instance-independent capstone: for THIS instance the conclusion of both published
theorems is unsatisfiable (together with the hypothesis theorems `hLawX` … `hDelta` proven
above, this completes the refutation). -/
theorem no_gamma_exists :
    ¬ (∃ γ : Copies (mult (rankFn stageX JX)) ≃ Copies (mult (rankFn stageY JY)),
      SatisfiesIIV γ 0 1) := by
  rintro ⟨γ, h₁, h₂, h₃, h₄⟩
  exact surg_closeE_false γ h₁

/-! ### Step 9: the rank-window interleaving hypothesis (`hbx`) -/

private lemma indEss_le_shift (β s : ℝ) : indEss β s ≤ indEss β (s - 1) := by
  unfold indEss
  by_cases hs : s ≤ β
  · rw [if_pos hs, if_pos (by linarith)]
  · rw [if_neg hs]
    exact zero_le

/-! The window `t + 2ε ≤ s` with `α ≤ t` (α = 0, ε = 1) makes each direction work: the essential
term shifts monotonically (`s ≤ 10 → s − 1 ≤ 10`), and the mortal term shifts because X's
death band `δ' < t + 1` at the HALF-shifted window covers Y's `δ < t` — for direction 2
exactly because `α ≤ t` forces `t + 1 ≥ 1 > 0.5`, the blindness of the rank window to deaths
below α. -/
private lemma indMort_le_shift' (β δ δ' s t : ℝ) (h0 : s ≤ β ∧ δ < t → s - 1 ≤ β ∧ δ' < t + 1) :
    indMort β δ s t ≤ indMort β δ' (s - 1) (t + 1) := by
  unfold indMort
  by_cases hc : s ≤ β ∧ δ < t
  · obtain ⟨h1, h2⟩ := h0 hc
    rw [if_pos hc, if_pos ⟨h1, h2⟩]
  · rw [if_neg hc]
    exact zero_le

/-- The rank-window interleaving (`hbx` at α = 0, ε = 1): the window `t + 2 ≤ s, 0 ≤ t` exactly
excludes every violating corner — Y's bar `(10, −1)` never needs to be matched at a birth `t`
with `t + 1 ≤ 0.5`. -/
theorem hbx_holds : ∀ s t : ℝ, t + 2 * 1 ≤ s → (0:ℝ) ≤ t →
    rankFn stageX JX s t ≤ rankFn stageY JY (s - 1) (t + 1) ∧
    rankFn stageY JY s t ≤ rankFn stageX JX (s - 1) (t + 1) := by
  intro s t hwin ht0
  have hts : t ≤ s := by linarith
  have hts' : t + 1 ≤ s - 1 := by linarith
  rw [rankX_eq s t hts, rankY_eq (s - 1) (t + 1) hts',
      rankY_eq s t hts, rankX_eq (s - 1) (t + 1) hts']
  constructor
  · exact add_le_add (indEss_le_shift 20 s)
      (indMort_le_shift' 10 0.5 (-1) s t (fun h => ⟨by linarith, by linarith⟩))
  · exact add_le_add (indEss_le_shift 20 s)
      (indMort_le_shift' 10 (-1) 0.5 s t (fun h => ⟨by linarith, by linarith⟩))

/-! ### Step 10: the falsified parent theorem (lemma_4_6_corrected) -/

set_option linter.unusedVariables false in
/-- **The published parent `theorem_4_5_lemma_4_6_corrected` is FALSE.**

Same instance (`α = 0`, `ε = 1`), with the RANK-interleaving hypothesis `hbx` instead of the
truncated δ: every hypothesis holds (`hLawX`/`hLawY`, `hbx` via `hbx_holds`, `hDiagX`/`hDiagY`,
`hFinX`/`hFinY`), yet the same conclusion fails for the same reason — Y's bar `(10, −1)`
dying below α is invisible to the rank window, but X's QNE point `(10, 0.5)` demands a
`1`-close ORIGINAL partner among Y's copies, and none exists (`no_close_partner`). -/
theorem lemma_4_6_corrected_false
    (hε : (0:ℝ) ≤ 1)
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    (hbx : ∀ s t : ℝ, t + 2 * 1 ≤ s → (0:ℝ) ≤ t →
      rankFn stageX JX s t ≤ rankFn stageY JY (s - 1) (t + 1) ∧
      rankFn stageY JY s t ≤ rankFn stageX JX (s - 1) (t + 1))
    (hDiagX : IsDiagramLike (mult (rankFn stageX JX)))
    (hDiagY : IsDiagramLike (mult (rankFn stageY JY)))
    (hFinX : {p : EReal × EReal | (mult (rankFn stageX JX)) p ≠ 0}.Finite)
    (hFinY : {p : EReal × EReal | (mult (rankFn stageY JY)) p ≠ 0}.Finite) :
    (∃ γ : Copies (mult (rankFn stageX JX)) ≃ Copies (mult (rankFn stageY JY)),
      SatisfiesIIV γ 0 1) → False := by
  rintro ⟨γ, h₁, h₂, h₃, h₄⟩
  exact surg_closeE_false γ h₁

/-! ### Step 11: the falsified non-qtame surgery sibling -/

set_option linter.unusedVariables false in
/-- **The published non-qtame `theorem_4_5_lemma_4_6_corrected_surgery` is also FALSE.**

Its hypothesis list is the qtame sibling's list WITHOUT the q-tameness clauses `hQX`/`hQY`
— and this instance satisfies every remaining hypothesis (`hLawX`/`hLawY`, `hDiagX`/`hDiagY`,
`hFinX`/`hFinY`, `hAgree`, `hDelta` — all proven as the named theorems above), while the
refutation core `surg_closeE_false` never uses `hQX`/`hQY`. The stub's docstring proposes to
resolve the death-crossing subtlety by choosing the vertical per-birth matching
ε-proximally, "possible because truncation only clamps deaths down to `α`" — this instance
shows that resolution FAILS: Y's only original at birth `10` dies at `−1`, far below the
ε-proximal band, so no vertical matching can be proximal, and X's QNE point `(10, 0.5)` has
no `1`-close partner. Binder order mirrors the non-qtame stub character by character, with
`α := 0`, `ε := 1`. -/
theorem surgery_false
    (hε : (0:ℝ) ≤ 1)
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    (hDiagX : IsDiagramLike (mult (rankFn stageX JX)))
    (hDiagY : IsDiagramLike (mult (rankFn stageY JY)))
    (hFinX : {p : EReal × EReal | (mult (rankFn stageX JX)) p ≠ 0}.Finite)
    (hFinY : {p : EReal × EReal | (mult (rankFn stageY JY)) p ≠ 0}.Finite)
    (hAgree : ∀ p ∈ QNE 0, mult (rankFn stageX JX) p = mult (truncRank (rankFn stageX JX) 0) p ∧
                            mult (rankFn stageY JY) p = mult (truncRank (rankFn stageY JY) 0) p)
    (hδ : ∃ δ : Copies (mult (truncRank (rankFn stageX JX) 0))
        ≃ Copies (mult (truncRank (rankFn stageY JY) 0)),
        (∀ a, closeE (pt a).1 (pt (δ a)).1 1 ∧ closeE (pt a).2 (pt (δ a)).2 1) ∧
        (∀ b, closeE (pt (δ.symm b)).1 (pt b).1 1 ∧ closeE (pt (δ.symm b)).2 (pt b).2 1)) :
    (∃ γ : Copies (mult (rankFn stageX JX)) ≃ Copies (mult (rankFn stageY JY)),
      SatisfiesIIV γ 0 1) → False := by
  rintro ⟨γ, h₁, h₂, h₃, h₄⟩
  exact surg_closeE_false γ h₁

end

end SurgQCE55

/-! ## Platform disproof form (a verified proof of the negation of the target type)

`solution` below proves the negation of the published statement of
`PersistClust.Count.theorem_4_5_lemma_4_6_corrected` (verbatim binder list and conclusion,
negated). The type variables are fixed at universe 0 (`Type`), the universe of the explicit
counterexample instance: modules over `Fin 3`, `α = 0`, `ε = 1`. Since the published theorem
is universe-polymorphic, refuting its universe-0 restriction refutes it. All hypotheses hold
at the instance — including the rank-window interleaving `hbx` (`hbx_holds`) — and the
conclusion is impossible there (`no_gamma_exists`). -/

open SurgQCE55

set_option maxHeartbeats 2000000 in
/-- DISPROOF of `theorem_4_5_lemma_4_6_corrected` (the parent lemma): the negation of its full
published statement (at universe 0, where the explicit two-module counterexample of this file
lives). Every hypothesis holds at the instance — the rank-window inequality `hbx` holds
(`hbx_holds`; the window `t + 2ε ≤ s` with `α ≤ t` keeps it blind to the below-α structure
that distinguishes the modules) — and no multi-bijection `γ` with `SatisfiesIIV γ 0 1`
exists: X's QNE point `(10, 0.5)` has no 1-close partner among Y's copies (`no_gamma_exists`). -/

theorem solution : ¬ ∀ {ιX : Type} (stageX : ℝ → Set ιX) (JX : ℝ → ιX → ιX → Prop)
    {ιY : Type} (stageY : ℝ → Set ιY) (JY : ℝ → ιY → ιY → Prop)
    (α ε : ℝ) (hε : 0 ≤ ε)
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    (hbx : ∀ s t : ℝ, t + 2 * ε ≤ s → α ≤ t →
      rankFn stageX JX s t ≤ rankFn stageY JY (s - ε) (t + ε) ∧
      rankFn stageY JY s t ≤ rankFn stageX JX (s - ε) (t + ε))
    (hDiagX : IsDiagramLike (mult (rankFn stageX JX)))
    (hDiagY : IsDiagramLike (mult (rankFn stageY JY)))
    (hFinX : {p : EReal × EReal | (mult (rankFn stageX JX)) p ≠ 0}.Finite)
    (hFinY : {p : EReal × EReal | (mult (rankFn stageY JY)) p ≠ 0}.Finite),
    ∃ γ : Copies (mult (rankFn stageX JX)) ≃ Copies (mult (rankFn stageY JY)),
      SatisfiesIIV γ α ε := by
  intro h
  exact no_gamma_exists
    (h stageX JX stageY JY 0 1 zero_le_one hLawX hLawY hbx_holds hDiagX hDiagY hFinX hFinY)
