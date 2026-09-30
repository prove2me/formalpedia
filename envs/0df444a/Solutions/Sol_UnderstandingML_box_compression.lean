-- Prove2me | solution 1 for UnderstandingML.box_compression
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-27T05:14:27.899745+00:00
-- url     : https://prove2.me/submissions/b817570f-20fc-4dd2-8cb0-78ee97316d41

import Definitions.Def_UnderstandingML_Compression

open MeasureTheory
open scoped InnerProductSpace

namespace BoxCompressionSol

variable {d : ℕ}

/-- Lower corner of the minimal enclosing box of the positive examples of `T`
(an empty box `[1, 0]` if there are none). -/
noncomputable def lo {k : ℕ} (T : Fin k → (Fin d → ℝ) × Bool) (i : Fin d) : ℝ :=
  open Classical in
  if h : ∃ j, (T j).2 = true then
    (Finset.univ.filter (fun j ↦ (T j).2 = true)).inf'
      (by obtain ⟨j, hj⟩ := h; exact ⟨j, by simp [hj]⟩) (fun j ↦ (T j).1 i)
  else 1

/-- Upper corner of the minimal enclosing box of the positive examples of `T`. -/
noncomputable def hi {k : ℕ} (T : Fin k → (Fin d → ℝ) × Bool) (i : Fin d) : ℝ :=
  open Classical in
  if h : ∃ j, (T j).2 = true then
    (Finset.univ.filter (fun j ↦ (T j).2 = true)).sup'
      (by obtain ⟨j, hj⟩ := h; exact ⟨j, by simp [hj]⟩) (fun j ↦ (T j).1 i)
  else 0

/-- The reconstruction map: the minimal enclosing box of the positive examples. -/
noncomputable def recon {k : ℕ} (T : Fin k → (Fin d → ℝ) × Bool) : (Fin d → ℝ) → Bool :=
  open Classical in
  fun x ↦ decide (∀ i, lo T i ≤ x i ∧ x i ≤ hi T i)

lemma lo_le {k : ℕ} (T : Fin k → (Fin d → ℝ) × Bool) (i : Fin d) (j : Fin k)
    (hj : (T j).2 = true) : lo T i ≤ (T j).1 i := by
  have h : ∃ j, (T j).2 = true := ⟨j, hj⟩
  simp only [lo, h, dite_true]
  exact Finset.inf'_le _ (by simp [hj])

lemma le_hi {k : ℕ} (T : Fin k → (Fin d → ℝ) × Bool) (i : Fin d) (j : Fin k)
    (hj : (T j).2 = true) : (T j).1 i ≤ hi T i := by
  have h : ∃ j, (T j).2 = true := ⟨j, hj⟩
  simp only [hi, h, dite_true]
  exact Finset.le_sup' (fun j ↦ (T j).1 i) (by simp [hj])

lemma le_lo {k : ℕ} (T : Fin k → (Fin d → ℝ) × Bool) (i : Fin d) (c : ℝ)
    (h : ∃ j, (T j).2 = true) (hc : ∀ j, (T j).2 = true → c ≤ (T j).1 i) : c ≤ lo T i := by
  simp only [lo, h, dite_true]
  exact Finset.le_inf' _ _ (fun j hj ↦ hc j (by simpa using hj))

lemma hi_le {k : ℕ} (T : Fin k → (Fin d → ℝ) × Bool) (i : Fin d) (c : ℝ)
    (h : ∃ j, (T j).2 = true) (hc : ∀ j, (T j).2 = true → (T j).1 i ≤ c) : hi T i ≤ c := by
  simp only [hi, h, dite_true]
  exact Finset.sup'_le _ _ (fun j hj ↦ hc j (by simpa using hj))

lemma lo_of_none {k : ℕ} (T : Fin k → (Fin d → ℝ) × Bool) (i : Fin d)
    (h : ¬ ∃ j, (T j).2 = true) : lo T i = 1 := by
  simp [lo, h]

lemma hi_of_none {k : ℕ} (T : Fin k → (Fin d → ℝ) × Bool) (i : Fin d)
    (h : ¬ ∃ j, (T j).2 = true) : hi T i = 0 := by
  simp [hi, h]

/-- Index of a positive example with minimal `i`-th coordinate (or `0` if none). -/
noncomputable def argLo {m : ℕ} (hm : 0 < m) (S : Fin m → (Fin d → ℝ) × Bool) (i : Fin d) :
    Fin m :=
  open Classical in
  if h : ∃ p, (S p).2 = true then
    ((Finset.univ.filter (fun p ↦ (S p).2 = true)).exists_min_image (fun p ↦ (S p).1 i)
      (by obtain ⟨p, hp⟩ := h; exact ⟨p, by simp [hp]⟩)).choose
  else ⟨0, hm⟩

/-- Index of a positive example with maximal `i`-th coordinate (or `0` if none). -/
noncomputable def argHi {m : ℕ} (hm : 0 < m) (S : Fin m → (Fin d → ℝ) × Bool) (i : Fin d) :
    Fin m :=
  open Classical in
  if h : ∃ p, (S p).2 = true then
    ((Finset.univ.filter (fun p ↦ (S p).2 = true)).exists_max_image (fun p ↦ (S p).1 i)
      (by obtain ⟨p, hp⟩ := h; exact ⟨p, by simp [hp]⟩)).choose
  else ⟨0, hm⟩

lemma argLo_spec {m : ℕ} (hm : 0 < m) (S : Fin m → (Fin d → ℝ) × Bool) (i : Fin d)
    (h : ∃ p, (S p).2 = true) :
    (S (argLo hm S i)).2 = true ∧ ∀ p, (S p).2 = true → (S (argLo hm S i)).1 i ≤ (S p).1 i := by
  classical
  simp only [argLo, h, dite_true]
  obtain ⟨p0, hp0⟩ := h
  obtain ⟨hmem, hmin⟩ := ((Finset.univ.filter (fun p ↦ (S p).2 = true)).exists_min_image
    (fun p ↦ (S p).1 i) ⟨p0, by simp [hp0]⟩).choose_spec
  exact ⟨by simpa using hmem, fun p hp ↦ hmin p (by simp [hp])⟩

lemma argHi_spec {m : ℕ} (hm : 0 < m) (S : Fin m → (Fin d → ℝ) × Bool) (i : Fin d)
    (h : ∃ p, (S p).2 = true) :
    (S (argHi hm S i)).2 = true ∧ ∀ p, (S p).2 = true → (S p).1 i ≤ (S (argHi hm S i)).1 i := by
  classical
  simp only [argHi, h, dite_true]
  obtain ⟨p0, hp0⟩ := h
  obtain ⟨hmem, hmax⟩ := ((Finset.univ.filter (fun p ↦ (S p).2 = true)).exists_max_image
    (fun p ↦ (S p).1 i) ⟨p0, by simp [hp0]⟩).choose_spec
  exact ⟨by simpa using hmem, fun p hp ↦ hmax p (by simp [hp])⟩

/-- The selection rule: the first `d` indices are the coordinate-wise minimal positive
examples, the last `d` the coordinate-wise maximal ones. -/
noncomputable def sel {m : ℕ} (hm : 0 < m) (S : Fin m → (Fin d → ℝ) × Bool) :
    Fin (2 * d) → Fin m :=
  fun j ↦ if hj : j.val < d then argLo hm S ⟨j.val, hj⟩
    else argHi hm S ⟨j.val - d, by omega⟩

lemma sel_lo {m : ℕ} (hm : 0 < m) (S : Fin m → (Fin d → ℝ) × Bool) (i : Fin d) :
    sel hm S ⟨i.val, by omega⟩ = argLo hm S i := by
  simp [sel, i.isLt]

lemma sel_hi {m : ℕ} (hm : 0 < m) (S : Fin m → (Fin d → ℝ) × Bool) (i : Fin d) :
    sel hm S ⟨i.val + d, by omega⟩ = argHi hm S i := by
  simp [sel]

end BoxCompressionSol

open UnderstandingML BoxCompressionSol in
theorem solution (d : ℕ) : HasCompressionScheme (boxClass d) (2 * d) := by
  classical
  intro m hm
  refine ⟨sel hm, recon, ?_, ?_⟩
  · intro T
    exact ⟨lo T, hi T, by funext x; simp [recon]⟩
  · rintro h ⟨a, b, rfl⟩ x q
    set S : Fin m → (Fin d → ℝ) × Bool :=
      fun p ↦ (x p, decide (∀ i, a i ≤ x p i ∧ x p i ≤ b i)) with hS
    set T : Fin (2 * d) → (Fin d → ℝ) × Bool := fun j ↦ S (sel hm S j) with hT
    show recon T (x q) = decide (∀ i, a i ≤ x q i ∧ x q i ≤ b i)
    simp only [recon, decide_eq_decide]
    -- every positive entry of `T` lies in the target box
    have hTpos : ∀ j, (T j).2 = true → ∀ i, a i ≤ (T j).1 i ∧ (T j).1 i ≤ b i := by
      intro j hj
      simpa [hT, hS] using hj
    constructor
    · intro hin i
      by_cases hex : ∃ j, (T j).2 = true
      · refine ⟨?_, ?_⟩
        · exact (le_lo T i (a i) hex fun j hj ↦ (hTpos j hj i).1).trans (hin i).1
        · exact (hin i).2.trans (hi_le T i (b i) hex fun j hj ↦ (hTpos j hj i).2)
      · have h1 := (hin i).1
        have h2 := (hin i).2
        rw [lo_of_none T i hex] at h1
        rw [hi_of_none T i hex] at h2
        linarith
    · intro hbox i
      have hq : (S q).2 = true := by simpa [hS] using hbox
      have hexS : ∃ p, (S p).2 = true := ⟨q, hq⟩
      obtain ⟨hlo1, hlo2⟩ := argLo_spec hm S i hexS
      obtain ⟨hhi1, hhi2⟩ := argHi_spec hm S i hexS
      have hTlo : T ⟨i.val, by omega⟩ = S (argLo hm S i) := by
        simp only [hT, sel_lo]
      have hThi : T ⟨i.val + d, by omega⟩ = S (argHi hm S i) := by
        simp only [hT, sel_hi]
      refine ⟨?_, ?_⟩
      · have := lo_le T i ⟨i.val, by omega⟩ (by rw [hTlo]; exact hlo1)
        rw [hTlo] at this
        exact this.trans (hlo2 q hq)
      · have := le_hi T i ⟨i.val + d, by omega⟩ (by rw [hThi]; exact hhi1)
        rw [hThi] at this
        exact (hhi2 q hq).trans this
