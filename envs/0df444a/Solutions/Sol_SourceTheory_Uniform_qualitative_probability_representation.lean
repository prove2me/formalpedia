-- Prove2me | solution 1 for SourceTheory.Uniform.qualitative_probability_representation
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T17:28:03.736537+00:00
-- url     : https://prove2.me/submissions/5c79bd06-5dd5-407c-927a-83d3d9987cee

import Mathlib
import Definitions.Def_SourceTheory_Uniform_Model

set_option linter.unusedSimpArgs false

namespace STUQPAux

open Set SourceTheory.Uniform MeasureTheory

structure Hyp {S : Type*} (𝒮 : Set (Set S)) (W : Set S → ℝ) : Prop where
  alg : IsSetAlgebra 𝒮
  W0 : W ∅ = 0
  W1 : W univ = 1
  mono : ∀ A ∈ 𝒮, ∀ B ∈ 𝒮, B ⊆ A → W B ≤ W A
  add : ∀ E ∈ 𝒮, ∀ F ∈ 𝒮, ∀ H ∈ 𝒮, E ∩ H = ∅ → F ∩ H = ∅ →
    (W F ≤ W E ↔ W (F ∪ H) ≤ W (E ∪ H))
  cr : IsConvexRanged 𝒮 W
  arch : ¬ ∃ E : ℕ → Set S, (∀ i, E i ∈ 𝒮) ∧ Pairwise (fun i j => Disjoint (E i) (E j)) ∧
    (∀ i, 0 < W (E i)) ∧ ∀ i j, W (E i) = W (E j)

variable {S : Type*} {𝒮 : Set (Set S)} {W : Set S → ℝ}

lemma inter_empty_iff' {X Y : Set S} : X ∩ Y = ∅ ↔ ∀ s, s ∈ X → s ∈ Y → False := by
  constructor
  · intro h s h1 h2
    have : s ∈ X ∩ Y := ⟨h1, h2⟩
    rw [h] at this; exact this
  · intro h; ext s; simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    exact fun h1 h2 => h s h1 h2

lemma Hyp.nn (h : Hyp 𝒮 W) {X : Set S} (hX : X ∈ 𝒮) : 0 ≤ W X := by
  have := h.mono X hX ∅ h.alg.empty_mem (empty_subset _)
  rwa [h.W0] at this

lemma Hyp.addlt (h : Hyp 𝒮 W) {X Y Z : Set S} (hX : X ∈ 𝒮) (hY : Y ∈ 𝒮) (hZ : Z ∈ 𝒮)
    (hXZ : X ∩ Z = ∅) (hYZ : Y ∩ Z = ∅) : W Y < W X ↔ W (Y ∪ Z) < W (X ∪ Z) := by
  rw [lt_iff_not_ge, lt_iff_not_ge, h.add Y hY X hX Z hZ hYZ hXZ]

/-- substitution: `A ≼ A'`, `B ≼ B'` with disjoint pairs give `A ∪ B ≼ A' ∪ B'`. -/
lemma Hyp.subst_le (h : Hyp 𝒮 W) {A B A' B' : Set S} (hA : A ∈ 𝒮) (hB : B ∈ 𝒮)
    (hA' : A' ∈ 𝒮) (hB' : B' ∈ 𝒮) (hAB : A ∩ B = ∅) (hAB' : A' ∩ B' = ∅)
    (h1 : W A ≤ W A') (h2 : W B ≤ W B') : W (A ∪ B) ≤ W (A' ∪ B') := by
  have g := h.alg
  rw [inter_empty_iff'] at hAB hAB'
  -- atoms
  set a1 := A ∩ A'
  set a2 := A ∩ B'
  set a3 := A \ (A' ∪ B')
  set b1 := B ∩ A'
  set b2 := B ∩ B'
  set b3 := B \ (A' ∪ B')
  set c1 := A' \ (A ∪ B)
  set c2 := B' \ (A ∪ B)
  have m1 : a1 ∈ 𝒮 := g.inter_mem hA hA'
  have m2 : a2 ∈ 𝒮 := g.inter_mem hA hB'
  have m3 : a3 ∈ 𝒮 := g.sdiff_mem hA (g.union_mem hA' hB')
  have n1 : b1 ∈ 𝒮 := g.inter_mem hB hA'
  have n2 : b2 ∈ 𝒮 := g.inter_mem hB hB'
  have n3 : b3 ∈ 𝒮 := g.sdiff_mem hB (g.union_mem hA' hB')
  have k1 : c1 ∈ 𝒮 := g.sdiff_mem hA' (g.union_mem hA hB)
  have k2 : c2 ∈ 𝒮 := g.sdiff_mem hB' (g.union_mem hA hB)
  -- s1 : a2 ∪ a3 ≼ b1 ∪ c1
  have s1 : W (a2 ∪ a3) ≤ W (b1 ∪ c1) := by
    have e := h.add (b1 ∪ c1) (g.union_mem n1 k1) (a2 ∪ a3) (g.union_mem m2 m3) a1 m1
      (by ext s; simp only [a1, b1, c1, mem_inter_iff, mem_union, mem_sdiff, mem_empty_iff_false, iff_false, mem_compl_iff, not_and, not_or]; have := hAB s; have := hAB' s; tauto)
      (by ext s; simp only [a1, a2, a3, mem_inter_iff, mem_union, mem_sdiff, mem_empty_iff_false, iff_false, mem_compl_iff, not_and, not_or]; have := hAB s; have := hAB' s; tauto)
    have r1 : (a2 ∪ a3) ∪ a1 = A := by
      ext s; simp only [a1, a2, a3, mem_inter_iff, mem_union, mem_sdiff, mem_empty_iff_false, iff_false, mem_compl_iff, not_and, not_or]; have := hAB s; have := hAB' s; tauto
    have r2 : (b1 ∪ c1) ∪ a1 = A' := by
      ext s; simp only [a1, b1, c1, mem_inter_iff, mem_union, mem_sdiff, mem_empty_iff_false, iff_false, mem_compl_iff, not_and, not_or]; have := hAB s; have := hAB' s; tauto
    rw [e, r1, r2]; exact h1
  have s2 : W (b1 ∪ b3) ≤ W (a2 ∪ c2) := by
    have e := h.add (a2 ∪ c2) (g.union_mem m2 k2) (b1 ∪ b3) (g.union_mem n1 n3) b2 n2
      (by ext s; simp only [a2, b2, c2, mem_inter_iff, mem_union, mem_sdiff, mem_empty_iff_false, iff_false, mem_compl_iff, not_and, not_or]; have := hAB s; have := hAB' s; tauto)
      (by ext s; simp only [b1, b2, b3, mem_inter_iff, mem_union, mem_sdiff, mem_empty_iff_false, iff_false, mem_compl_iff, not_and, not_or]; have := hAB s; have := hAB' s; tauto)
    have r1 : (b1 ∪ b3) ∪ b2 = B := by
      ext s; simp only [b1, b2, b3, mem_inter_iff, mem_union, mem_sdiff, mem_empty_iff_false, iff_false, mem_compl_iff, not_and, not_or]; have := hAB s; have := hAB' s; tauto
    have r2 : (a2 ∪ c2) ∪ b2 = B' := by
      ext s; simp only [a2, b2, c2, mem_inter_iff, mem_union, mem_sdiff, mem_empty_iff_false, iff_false, mem_compl_iff, not_and, not_or]; have := hAB s; have := hAB' s; tauto
    rw [e, r1, r2]; exact h2
  -- add b3 to s1, c1 to s2
  have t1 : W ((a2 ∪ a3) ∪ b3) ≤ W ((b1 ∪ c1) ∪ b3) :=
    (h.add (b1 ∪ c1) (g.union_mem n1 k1) (a2 ∪ a3) (g.union_mem m2 m3) b3 n3
      (by ext s; simp only [b1, c1, b3, mem_inter_iff, mem_union, mem_sdiff, mem_empty_iff_false, iff_false, mem_compl_iff, not_and, not_or]; have := hAB s; have := hAB' s; tauto)
      (by ext s; simp only [a2, a3, b3, mem_inter_iff, mem_union, mem_sdiff, mem_empty_iff_false, iff_false, mem_compl_iff, not_and, not_or]; have := hAB s; have := hAB' s; tauto)).1 s1
  have t2 : W ((b1 ∪ b3) ∪ c1) ≤ W ((a2 ∪ c2) ∪ c1) :=
    (h.add (a2 ∪ c2) (g.union_mem m2 k2) (b1 ∪ b3) (g.union_mem n1 n3) c1 k1
      (by ext s; simp only [a2, c2, c1, mem_inter_iff, mem_union, mem_sdiff, mem_empty_iff_false, iff_false, mem_compl_iff, not_and, not_or]; have := hAB s; have := hAB' s; tauto)
      (by ext s; simp only [b1, b3, c1, mem_inter_iff, mem_union, mem_sdiff, mem_empty_iff_false, iff_false, mem_compl_iff, not_and, not_or]; have := hAB s; have := hAB' s; tauto)).1 s2
  have r : (b1 ∪ c1) ∪ b3 = (b1 ∪ b3) ∪ c1 := by ext s; simp only [mem_union]; tauto
  rw [r] at t1
  have t3 := t1.trans t2
  -- cancel a2
  have t4 : W (a3 ∪ b3) ≤ W (c1 ∪ c2) := by
    have e := h.add (c1 ∪ c2) (g.union_mem k1 k2) (a3 ∪ b3) (g.union_mem m3 n3) a2 m2
      (by ext s; simp only [a2, c1, c2, mem_inter_iff, mem_union, mem_sdiff, mem_empty_iff_false, iff_false, mem_compl_iff, not_and, not_or]; have := hAB s; have := hAB' s; tauto)
      (by ext s; simp only [a2, a3, b3, mem_inter_iff, mem_union, mem_sdiff, mem_empty_iff_false, iff_false, mem_compl_iff, not_and, not_or]; have := hAB s; have := hAB' s; tauto)
    have q1 : (a2 ∪ a3) ∪ b3 = (a3 ∪ b3) ∪ a2 := by ext s; simp only [mem_union]; tauto
    have q2 : (a2 ∪ c2) ∪ c1 = (c1 ∪ c2) ∪ a2 := by ext s; simp only [mem_union]; tauto
    rw [e, ← q1, ← q2]; exact t3
  -- add the common part
  have hM : A ∪ B ∈ 𝒮 := g.union_mem hA hB
  have hM' : A' ∪ B' ∈ 𝒮 := g.union_mem hA' hB'
  have q3 : a3 ∪ b3 = (A ∪ B) \ (A' ∪ B') := by
    ext s; simp only [a3, b3, mem_inter_iff, mem_union, mem_sdiff, mem_empty_iff_false, iff_false, mem_compl_iff, not_and, not_or]; tauto
  have q4 : c1 ∪ c2 = (A' ∪ B') \ (A ∪ B) := by
    ext s; simp only [c1, c2, mem_inter_iff, mem_union, mem_sdiff, mem_empty_iff_false, iff_false, mem_compl_iff, not_and, not_or]; tauto
  rw [q3, q4] at t4
  have e := h.add ((A' ∪ B') \ (A ∪ B)) (g.sdiff_mem hM' hM) ((A ∪ B) \ (A' ∪ B'))
    (g.sdiff_mem hM hM') ((A ∪ B) ∩ (A' ∪ B')) (g.inter_mem hM hM')
    (by ext s; simp only [mem_inter_iff, mem_union, mem_sdiff, mem_empty_iff_false, iff_false, mem_compl_iff, not_and, not_or]; tauto) (by ext s; simp only [mem_inter_iff, mem_union, mem_sdiff, mem_empty_iff_false, iff_false, mem_compl_iff, not_and, not_or]; tauto)
  have r1 : ((A ∪ B) \ (A' ∪ B')) ∪ ((A ∪ B) ∩ (A' ∪ B')) = A ∪ B := by
    ext s; simp only [mem_inter_iff, mem_union, mem_sdiff, mem_empty_iff_false, iff_false, mem_compl_iff, not_and, not_or]; tauto
  have r2 : ((A' ∪ B') \ (A ∪ B)) ∪ ((A ∪ B) ∩ (A' ∪ B')) = A' ∪ B' := by
    ext s; simp only [mem_inter_iff, mem_union, mem_sdiff, mem_empty_iff_false, iff_false, mem_compl_iff, not_and, not_or]; tauto
  rw [r1, r2] at e
  exact e.1 t4

lemma Hyp.subst_lt (h : Hyp 𝒮 W) {A B A' B' : Set S} (hA : A ∈ 𝒮) (hB : B ∈ 𝒮)
    (hA' : A' ∈ 𝒮) (hB' : B' ∈ 𝒮) (hAB : A ∩ B = ∅) (hAB' : A' ∩ B' = ∅)
    (h1 : W A ≤ W A') (h2 : W B < W B') : W (A ∪ B) < W (A' ∪ B') := by
  have g := h.alg
  obtain ⟨B'', hB'', -, hsub, hW⟩ := h.cr ∅ g.empty_mem B' hB' (empty_subset _) (W B)
    (by rw [h.W0]; exact h.nn hB) h2.le
  have hAB'' : A' ∩ B'' = ∅ := by
    rw [inter_empty_iff'] at hAB' ⊢; exact fun s a b => hAB' s a (hsub b)
  have l1 := h.subst_le hA hB hA' hB'' hAB hAB'' h1 hW.symm.le
  set Z := B' \ B''
  have hZ : Z ∈ 𝒮 := g.sdiff_mem hB' hB''
  have hZpos : W ∅ < W Z := by
    have e := h.addlt hZ g.empty_mem hB'' (by ext s; simp [Z]) (by simp)
    rw [e]
    have r : Z ∪ B'' = B' := by ext s; simp [Z]; have := @hsub s; tauto
    rw [r, empty_union, hW]; exact h2
  have e := (h.addlt hZ g.empty_mem (g.union_mem hA' hB'')
    (by ext s; simp [Z]; have := @hsub s; rw [inter_empty_iff'] at hAB'; have := hAB' s; tauto)
    (by simp)).1 hZpos
  have r : Z ∪ (A' ∪ B'') = A' ∪ B' := by ext s; simp [Z]; have := @hsub s; tauto
  rw [r, empty_union] at e
  exact l1.trans_lt e

lemma Hyp.subst_eq (h : Hyp 𝒮 W) {A B A' B' : Set S} (hA : A ∈ 𝒮) (hB : B ∈ 𝒮)
    (hA' : A' ∈ 𝒮) (hB' : B' ∈ 𝒮) (hAB : A ∩ B = ∅) (hAB' : A' ∩ B' = ∅)
    (h1 : W A = W A') (h2 : W B = W B') : W (A ∪ B) = W (A' ∪ B') :=
  le_antisymm (h.subst_le hA hB hA' hB' hAB hAB' h1.le h2.le)
    (h.subst_le hA' hB' hA hB hAB' hAB h1.symm.le h2.symm.le)

/-- relative complements reverse the order -/
lemma Hyp.comp_anti (h : Hyp 𝒮 W) {A H H' : Set S} (hA : A ∈ 𝒮) (hH : H ∈ 𝒮) (hH' : H' ∈ 𝒮)
    (hHA : H ⊆ A) (hH'A : H' ⊆ A) (hle : W H ≤ W H') : W (A \ H') ≤ W (A \ H) := by
  have g := h.alg
  have m1 : H' \ H ∈ 𝒮 := g.sdiff_mem hH' hH
  have m2 : H \ H' ∈ 𝒮 := g.sdiff_mem hH hH'
  have e1 := h.add (H' \ H) m1 (H \ H') m2 (H ∩ H') (g.inter_mem hH hH')
    (by ext s; simp only [mem_inter_iff, mem_union, mem_sdiff, mem_empty_iff_false, iff_false, mem_compl_iff, not_and, not_or]; tauto) (by ext s; simp only [mem_inter_iff, mem_union, mem_sdiff, mem_empty_iff_false, iff_false, mem_compl_iff, not_and, not_or]; tauto)
  have r1 : (H \ H') ∪ (H ∩ H') = H := by ext s; simp only [mem_inter_iff, mem_union, mem_sdiff, mem_empty_iff_false, iff_false, mem_compl_iff, not_and, not_or]; tauto
  have r2 : (H' \ H) ∪ (H ∩ H') = H' := by ext s; simp only [mem_inter_iff, mem_union, mem_sdiff, mem_empty_iff_false, iff_false, mem_compl_iff, not_and, not_or]; tauto
  rw [r1, r2] at e1
  have k := e1.2 hle
  have e2 := h.add (H' \ H) m1 (H \ H') m2 (A \ (H ∪ H')) (g.sdiff_mem hA (g.union_mem hH hH'))
    (by ext s; simp only [mem_inter_iff, mem_union, mem_sdiff, mem_empty_iff_false, iff_false, mem_compl_iff, not_and, not_or]; tauto) (by ext s; simp only [mem_inter_iff, mem_union, mem_sdiff, mem_empty_iff_false, iff_false, mem_compl_iff, not_and, not_or]; tauto)
  have r3 : (H \ H') ∪ (A \ (H ∪ H')) = A \ H' := by
    ext s; simp only [mem_inter_iff, mem_union, mem_sdiff, mem_empty_iff_false, iff_false, mem_compl_iff, not_and, not_or]; have := @hHA s; have := @hH'A s; tauto
  have r4 : (H' \ H) ∪ (A \ (H ∪ H')) = A \ H := by
    ext s; simp only [mem_inter_iff, mem_union, mem_sdiff, mem_empty_iff_false, iff_false, mem_compl_iff, not_and, not_or]; have := @hHA s; have := @hH'A s; tauto
  rw [r3, r4] at e2
  exact e2.1 k

lemma Hyp.halving (h : Hyp 𝒮 W) {A : Set S} (hA : A ∈ 𝒮) :
    ∃ H ∈ 𝒮, H ⊆ A ∧ W H = W (A \ H) := by
  have g := h.alg
  set T : Set ℝ := {t | ∃ H ∈ 𝒮, H ⊆ A ∧ W H = t ∧ t ≤ W (A \ H)} with hT
  have h0T : (0 : ℝ) ∈ T := ⟨∅, g.empty_mem, empty_subset _, h.W0, by
    rw [diff_empty]; exact h.nn hA⟩
  have hTne : T.Nonempty := ⟨0, h0T⟩
  have hTbdd : BddAbove T := ⟨W A, by
    rintro t ⟨H, hH, hHA, rfl, -⟩; exact h.mono A hA H hH hHA⟩
  set ts := sSup T
  have hts0 : 0 ≤ ts := le_csSup hTbdd h0T
  have htsA : ts ≤ W A := csSup_le hTne (by
    rintro t ⟨H, hH, hHA, rfl, -⟩; exact h.mono A hA H hH hHA)
  obtain ⟨Hs, hHs, -, hHsA, hWHs⟩ := h.cr ∅ g.empty_mem A hA (empty_subset _) ts
    (by rw [h.W0]; exact hts0) htsA
  refine ⟨Hs, hHs, hHsA, ?_⟩
  have hAHs : A \ Hs ∈ 𝒮 := g.sdiff_mem hA hHs
  have hWAHs : W (A \ Hs) ≤ W A := h.mono A hA _ hAHs diff_subset
  -- a set Y ⊆ A of any weight s ∈ [0, W A], and its complement X = A \ Y
  have pick : ∀ s, 0 ≤ s → s ≤ W A → ∃ Y ∈ 𝒮, Y ⊆ A ∧ W Y = s := by
    intro s hs1 hs2
    obtain ⟨Y, hY, -, hYA, hWY⟩ := h.cr ∅ g.empty_mem A hA (empty_subset _) s
      (by rw [h.W0]; exact hs1) hs2
    exact ⟨Y, hY, hYA, hWY⟩
  have dd : ∀ Y, Y ⊆ A → A \ (A \ Y) = Y := by
    intro Y hY; ext s; simp only [mem_inter_iff, mem_union, mem_sdiff, mem_empty_iff_false, iff_false, mem_compl_iff, not_and, not_or]; have := @hY s; tauto
  rcases lt_trichotomy (W (A \ Hs)) ts with hc | hc | hc
  · exfalso
    set s := (W (A \ Hs) + ts) / 2
    obtain ⟨Y, hY, hYA, hWY⟩ := pick s (by have := h.nn hAHs; simp only [s]; linarith)
      (by simp only [s]; linarith)
    have hX : A \ Y ∈ 𝒮 := g.sdiff_mem hA hY
    have hXlt : W (A \ Y) < W Hs := by
      by_contra hcon; push Not at hcon
      have := h.comp_anti hA hHs hX hHsA diff_subset hcon
      rw [dd Y hYA, hWY] at this
      simp only [s] at this; linarith
    obtain ⟨t2, ⟨H2, hH2, hH2A, rfl, ht2⟩, hlt2⟩ :=
      exists_lt_of_lt_csSup hTne (show max s (W (A \ Y)) < ts by
        rw [max_lt_iff]; constructor
        · simp only [s]; linarith
        · rw [← hWHs]; exact hXlt)
    rw [max_lt_iff] at hlt2
    have := h.comp_anti hA hX hH2 diff_subset hH2A hlt2.2.le
    rw [dd Y hYA, hWY] at this
    linarith [hlt2.1]
  · exact hWHs.trans hc.symm
  · exfalso
    set s := (W (A \ Hs) + ts) / 2
    obtain ⟨Y, hY, hYA, hWY⟩ := pick s (by simp only [s]; linarith)
      (by simp only [s]; linarith)
    have hX : A \ Y ∈ 𝒮 := g.sdiff_mem hA hY
    have hXgt : W Hs < W (A \ Y) := by
      by_contra hcon; push Not at hcon
      have := h.comp_anti hA hX hHs diff_subset hHsA hcon
      rw [dd Y hYA, hWY] at this
      simp only [s] at this; linarith
    set t' := min (W (A \ Y)) s
    have ht'1 : ts < t' := lt_min (hWHs ▸ hXgt) (by simp only [s]; linarith)
    obtain ⟨H', hH', hH'A, hWH'⟩ := pick t' (by linarith)
      ((min_le_right _ _).trans (by simp only [s]; linarith))
    have := h.comp_anti hA hH' hX hH'A diff_subset (hWH' ▸ min_le_left _ _)
    rw [dd Y hYA, hWY] at this
    have hmem : t' ∈ T := ⟨H', hH', hH'A, hWH', (min_le_right _ _).trans this⟩
    have := le_csSup hTbdd hmem
    linarith

section dyadic

variable (𝒮 W) in
open Classical in
noncomputable def half (A : Set S) : Set S :=
  if hh : ∃ H ∈ 𝒮, H ⊆ A ∧ W H = W (A \ H) then hh.choose else ∅

lemma half_subset (A : Set S) : half 𝒮 W A ⊆ A := by
  unfold half; split_ifs with hh
  · exact hh.choose_spec.2.1
  · exact empty_subset _

lemma Hyp.half_mem (h : Hyp 𝒮 W) {A : Set S} (hA : A ∈ 𝒮) : half 𝒮 W A ∈ 𝒮 := by
  have hh := h.halving hA
  unfold half; rw [dif_pos hh]; exact hh.choose_spec.1

lemma Hyp.half_eq (h : Hyp 𝒮 W) {A : Set S} (hA : A ∈ 𝒮) :
    W (half 𝒮 W A) = W (A \ half 𝒮 W A) := by
  have hh := h.halving hA
  unfold half; rw [dif_pos hh]; exact hh.choose_spec.2.2

lemma Hyp.half_resp (h : Hyp 𝒮 W) {X X' : Set S} (hX : X ∈ 𝒮) (hX' : X' ∈ 𝒮)
    (hW : W X = W X') : W (half 𝒮 W X) = W (half 𝒮 W X') := by
  have g := h.alg
  have key : ∀ Y ∈ 𝒮, ∀ Y' ∈ 𝒮, W (half 𝒮 W Y) < W (half 𝒮 W Y') → W Y < W Y' := by
    intro Y hY Y' hY' hlt
    have e1 := h.half_eq hY
    have e2 := h.half_eq hY'
    have := h.subst_lt (h.half_mem hY) (g.sdiff_mem hY (h.half_mem hY)) (h.half_mem hY')
      (g.sdiff_mem hY' (h.half_mem hY')) (by ext s; simp) (by ext s; simp) hlt.le
      (by rw [← e1, ← e2]; exact hlt)
    have r : ∀ Z : Set S, half 𝒮 W Z ∪ (Z \ half 𝒮 W Z) = Z := fun Z => by
      ext s; simp only [mem_union, mem_sdiff]; have := @half_subset S 𝒮 W Z s; tauto
    rwa [r, r] at this
  rcases lt_trichotomy (W (half 𝒮 W X)) (W (half 𝒮 W X')) with c | c | c
  · have := key X hX X' hX' c; linarith
  · exact c
  · have := key X' hX' X hX c; linarith

variable (𝒮 W) in
noncomputable def UU : ℕ → ℕ → Set S
  | 0, m => if m = 0 then ∅ else univ
  | k + 1, m => if m % 2 = 0 then UU k (m / 2) else
      UU k (m / 2) ∪ half 𝒮 W (UU k (m / 2 + 1) \ UU k (m / 2))

lemma UU_even (k j : ℕ) : UU 𝒮 W (k + 1) (2 * j) = UU 𝒮 W k j := by
  have h1 : (2 * j) % 2 = 0 := by omega
  have h2 : (2 * j) / 2 = j := by omega
  simp only [UU, h1, h2, if_true]

lemma UU_odd (k j : ℕ) : UU 𝒮 W (k + 1) (2 * j + 1) =
    UU 𝒮 W k j ∪ half 𝒮 W (UU 𝒮 W k (j + 1) \ UU 𝒮 W k j) := by
  have h1 : (2 * j + 1) % 2 = 1 := by omega
  have h2 : (2 * j + 1) / 2 = j := by omega
  simp only [UU, h1, h2]; simp

lemma parity (m : ℕ) : ∃ j, m = 2 * j ∨ m = 2 * j + 1 := ⟨m / 2, by omega⟩

lemma Hyp.UU_mem (h : Hyp 𝒮 W) : ∀ k m, UU 𝒮 W k m ∈ 𝒮 := by
  intro k
  induction k with
  | zero => intro m; simp only [UU]; split_ifs
            · exact h.alg.empty_mem
            · exact h.alg.univ_mem
  | succ k ih =>
    intro m
    obtain ⟨j, rfl | rfl⟩ := parity m
    · rw [UU_even]; exact ih j
    · rw [UU_odd]
      exact h.alg.union_mem (ih j) (h.half_mem (h.alg.sdiff_mem (ih _) (ih _)))

lemma UU_zero : ∀ k, UU 𝒮 W k 0 = ∅ := by
  intro k
  induction k with
  | zero => simp [UU]
  | succ k ih => have := UU_even (𝒮 := 𝒮) (W := W) k 0; simp only [mul_zero] at this
                 rw [this, ih]

lemma UU_top : ∀ k m, 2 ^ k ≤ m → UU 𝒮 W k m = univ := by
  intro k
  induction k with
  | zero => intro m hm; simp only [UU]; rw [if_neg (by simp at hm; omega)]
  | succ k ih =>
    intro m hm
    obtain ⟨j, rfl | rfl⟩ := parity m
    · rw [UU_even]; exact ih j (by rw [pow_succ] at hm; omega)
    · rw [UU_odd, ih j (by rw [pow_succ] at hm; omega)]; exact univ_union _

lemma UU_succ_sub : ∀ k m, UU 𝒮 W k m ⊆ UU 𝒮 W k (m + 1) := by
  intro k
  induction k with
  | zero => intro m; simp only [UU]; split_ifs <;> simp_all
  | succ k ih =>
    intro m
    obtain ⟨j, rfl | rfl⟩ := parity m
    · rw [UU_even, UU_odd]; exact subset_union_left
    · rw [UU_odd, show 2 * j + 1 + 1 = 2 * (j + 1) by ring, UU_even]
      exact union_subset (ih j) ((half_subset _).trans sdiff_subset)

lemma UU_mono (k : ℕ) {m m' : ℕ} (hm : m ≤ m') : UU 𝒮 W k m ⊆ UU 𝒮 W k m' := by
  have : Monotone (UU 𝒮 W k) := monotone_nat_of_le_succ (fun n => UU_succ_sub k n)
  exact this hm

variable (𝒮 W) in
noncomputable def CC (k i : ℕ) : Set S := UU 𝒮 W k (i + 1) \ UU 𝒮 W k i

lemma Hyp.CC_mem (h : Hyp 𝒮 W) (k i : ℕ) : CC 𝒮 W k i ∈ 𝒮 :=
  h.alg.sdiff_mem (h.UU_mem _ _) (h.UU_mem _ _)

lemma CC_even (k j : ℕ) : CC 𝒮 W (k + 1) (2 * j) = half 𝒮 W (CC 𝒮 W k j) := by
  unfold CC
  rw [UU_odd, UU_even]
  ext s
  have := @half_subset S 𝒮 W (UU 𝒮 W k (j + 1) \ UU 𝒮 W k j) s
  simp only [mem_sdiff, mem_union] at this ⊢
  tauto

lemma CC_odd (k j : ℕ) : CC 𝒮 W (k + 1) (2 * j + 1) = CC 𝒮 W k j \ half 𝒮 W (CC 𝒮 W k j) := by
  unfold CC
  rw [UU_odd, show 2 * j + 1 + 1 = 2 * (j + 1) by ring, UU_even]
  ext s
  simp only [mem_sdiff, mem_union]
  tauto

lemma Hyp.CC_eq (h : Hyp 𝒮 W) : ∀ k, ∀ i < 2 ^ k, W (CC 𝒮 W k i) = W (CC 𝒮 W k 0) := by
  intro k
  induction k with
  | zero => intro i hi; simp at hi; rw [hi]
  | succ k ih =>
    intro i hi
    have h0 : W (CC 𝒮 W (k + 1) 0) = W (half 𝒮 W (CC 𝒮 W k 0)) := by
      have := CC_even (𝒮 := 𝒮) (W := W) k 0; simp only [mul_zero] at this; rw [this]
    rw [h0]
    obtain ⟨j, rfl | rfl⟩ := parity i
    · rw [CC_even]
      exact h.half_resp (h.CC_mem _ _) (h.CC_mem _ _) (ih j (by rw [pow_succ] at hi; omega))
    · rw [CC_odd, ← h.half_eq (h.CC_mem _ _)]
      exact h.half_resp (h.CC_mem _ _) (h.CC_mem _ _) (ih j (by rw [pow_succ] at hi; omega))

lemma Hyp.CC_pos (h : Hyp 𝒮 W) : ∀ k, 0 < W (CC 𝒮 W k 0) := by
  intro k
  induction k with
  | zero =>
    have : CC 𝒮 W 0 0 = univ := by
      unfold CC; rw [UU_zero, UU_top 0 1 (by simp)]; simp
    rw [this, h.W1]; norm_num
  | succ k ih =>
    have e := CC_even (𝒮 := 𝒮) (W := W) k 0
    simp only [mul_zero] at e
    rw [e]
    by_contra hc; push Not at hc
    have hm := h.CC_mem k 0
    have hh := h.half_mem hm
    have := h.subst_le hh (h.alg.sdiff_mem hm hh) h.alg.empty_mem h.alg.empty_mem
      (by ext s; simp) (by simp) (by rw [h.W0]; exact hc)
      (by rw [h.W0, ← h.half_eq hm]; exact hc)
    have r : half 𝒮 W (CC 𝒮 W k 0) ∪ (CC 𝒮 W k 0 \ half 𝒮 W (CC 𝒮 W k 0)) = CC 𝒮 W k 0 := by
      ext s; simp only [mem_union, mem_sdiff]
      have := @half_subset S 𝒮 W (CC 𝒮 W k 0) s; tauto
    rw [r, union_empty, h.W0] at this
    linarith

lemma Hyp.shift (h : Hyp 𝒮 W) (k : ℕ) : ∀ j m, m + j ≤ 2 ^ k →
    W (UU 𝒮 W k (m + j) \ UU 𝒮 W k m) = W (UU 𝒮 W k j) := by
  intro j
  induction j with
  | zero => intro m _; simp [UU_zero]
  | succ j ih =>
    intro m hm
    have g := h.alg
    have e1 : UU 𝒮 W k (m + (j + 1)) \ UU 𝒮 W k m =
        (UU 𝒮 W k (m + j) \ UU 𝒮 W k m) ∪ CC 𝒮 W k (m + j) := by
      unfold CC
      have a := UU_mono (𝒮 := 𝒮) (W := W) k (show m ≤ m + j by omega)
      have b := UU_mono (𝒮 := 𝒮) (W := W) k (show m + j ≤ m + (j + 1) by omega)
      rw [show m + j + 1 = m + (j + 1) by ring]
      ext s; have := @a s; have := @b s; simp only [mem_union, mem_sdiff]; tauto
    have e2 : UU 𝒮 W k (j + 1) = UU 𝒮 W k j ∪ CC 𝒮 W k j := by
      unfold CC
      have b := UU_succ_sub (𝒮 := 𝒮) (W := W) k j
      ext s; have := @b s; simp only [mem_union, mem_sdiff]; tauto
    rw [e1, e2]
    apply h.subst_eq (g.sdiff_mem (h.UU_mem _ _) (h.UU_mem _ _)) (h.CC_mem _ _)
      (h.UU_mem _ _) (h.CC_mem _ _)
    · unfold CC; ext s; simp only [mem_inter_iff, mem_sdiff, mem_empty_iff_false, iff_false]; tauto
    · unfold CC; ext s; simp only [mem_inter_iff, mem_sdiff, mem_empty_iff_false, iff_false]; tauto
    · exact ih m (by omega)
    · rw [h.CC_eq k _ (by omega), h.CC_eq k j (by omega)]

lemma Hyp.UU_lt_succ (h : Hyp 𝒮 W) {k m : ℕ} (hm : m < 2 ^ k) :
    W (UU 𝒮 W k m) < W (UU 𝒮 W k (m + 1)) := by
  have g := h.alg
  have e := (h.addlt (h.CC_mem k m) g.empty_mem (h.UU_mem k m)
    (by unfold CC; ext s; simp only [mem_inter_iff, mem_sdiff, mem_empty_iff_false, iff_false]; tauto)
    (by simp)).1 (by rw [h.W0, h.CC_eq k m hm]; exact h.CC_pos k)
  have r : CC 𝒮 W k m ∪ UU 𝒮 W k m = UU 𝒮 W k (m + 1) := by
    unfold CC
    have b := UU_succ_sub (𝒮 := 𝒮) (W := W) k m
    ext s; have := @b s; simp only [mem_union, mem_sdiff]; tauto
  rwa [empty_union, r] at e

lemma Hyp.UU_lt (h : Hyp 𝒮 W) {k m m' : ℕ} (hmm : m < m') (hm' : m' ≤ 2 ^ k) :
    W (UU 𝒮 W k m) < W (UU 𝒮 W k m') := by
  induction m' with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hmm with c | c
    · exact (ih c (by omega)).trans (h.UU_lt_succ (by omega))
    · rw [c]; exact h.UU_lt_succ (by omega)

end dyadic

section counting

variable (𝒮 W) in
open Classical in
noncomputable def NN (k : ℕ) (t : ℝ) : ℕ := Nat.findGreatest (fun m => W (UU 𝒮 W k m) ≤ t) (2 ^ k)

lemma Hyp.NN_spec (h : Hyp 𝒮 W) {k : ℕ} {t : ℝ} (ht : 0 ≤ t) :
    W (UU 𝒮 W k (NN 𝒮 W k t)) ≤ t := by
  classical
  unfold NN
  exact Nat.findGreatest_spec (P := fun m => W (UU 𝒮 W k m) ≤ t) (m := 0) (Nat.zero_le _) (by rw [UU_zero, h.W0]; exact ht)

lemma NN_le (k : ℕ) (t : ℝ) : NN 𝒮 W k t ≤ 2 ^ k := by
  classical
  unfold NN; exact Nat.findGreatest_le _

lemma NN_great {k m : ℕ} {t : ℝ} (h1 : NN 𝒮 W k t < m) (h2 : m ≤ 2 ^ k) :
    t < W (UU 𝒮 W k m) := by
  classical
  unfold NN at h1
  exact not_le.1 (Nat.findGreatest_is_greatest h1 h2)

lemma le_NN {k m : ℕ} {t : ℝ} (h1 : m ≤ 2 ^ k) (h2 : W (UU 𝒮 W k m) ≤ t) : m ≤ NN 𝒮 W k t := by
  classical
  unfold NN; exact Nat.le_findGreatest h1 h2

lemma NN_mono {k : ℕ} {t t' : ℝ} (htt : t ≤ t') : NN 𝒮 W k t ≤ NN 𝒮 W k t' := by
  classical
  unfold NN; exact Nat.findGreatest_mono_left (fun m hm => hm.trans htt) _

lemma Hyp.NN_lev1 (h : Hyp 𝒮 W) {k : ℕ} {t : ℝ} (ht : 0 ≤ t) :
    2 * NN 𝒮 W k t ≤ NN 𝒮 W (k + 1) t := by
  apply le_NN
  · have := NN_le (𝒮 := 𝒮) (W := W) k t; rw [pow_succ]; omega
  · rw [UU_even]; exact h.NN_spec ht

lemma Hyp.NN_lev2 (h : Hyp 𝒮 W) {k : ℕ} {t : ℝ} (ht : 0 ≤ t) :
    NN 𝒮 W (k + 1) t ≤ 2 * NN 𝒮 W k t + 1 := by
  by_contra hc; push Not at hc
  have hN := NN_le (𝒮 := 𝒮) (W := W) k t
  have hN1 := NN_le (𝒮 := 𝒮) (W := W) (k + 1) t
  have hlt : NN 𝒮 W k t < 2 ^ k := by
    by_contra c; rw [pow_succ] at hN1; omega
  have g := NN_great (𝒮 := 𝒮) (W := W) (Nat.lt_succ_self (NN 𝒮 W k t)) hlt
  have sub : UU 𝒮 W (k + 1) (2 * (NN 𝒮 W k t + 1)) ⊆ UU 𝒮 W (k + 1) (NN 𝒮 W (k + 1) t) :=
    UU_mono _ (by omega)
  rw [UU_even] at sub
  have := h.mono _ (h.UU_mem _ _) _ (h.UU_mem _ _) sub
  have := h.NN_spec (k := k + 1) ht
  linarith

lemma Hyp.NN_lo (h : Hyp 𝒮 W) (k : ℕ) {A B : Set S} (hA : A ∈ 𝒮) (hB : B ∈ 𝒮)
    (hAB : A ∩ B = ∅) :
    NN 𝒮 W k (W A) + NN 𝒮 W k (W B) ≤ NN 𝒮 W k (W (A ∪ B)) := by
  have g := h.alg
  set a := NN 𝒮 W k (W A)
  set b := NN 𝒮 W k (W B)
  have ha := h.NN_spec (k := k) (h.nn hA)
  have hb := h.NN_spec (k := k) (h.nn hB)
  have hbk : b ≤ 2 ^ k := NN_le k _
  have hak : a ≤ 2 ^ k := NN_le k _
  have split : ∀ j, UU 𝒮 W k (a + j) = UU 𝒮 W k a ∪ (UU 𝒮 W k (a + j) \ UU 𝒮 W k a) := by
    intro j
    have := UU_mono (𝒮 := 𝒮) (W := W) k (show a ≤ a + j by omega)
    ext s; have := @this s; simp only [mem_union, mem_sdiff]; tauto
  have disj : ∀ j, UU 𝒮 W k a ∩ (UU 𝒮 W k (a + j) \ UU 𝒮 W k a) = ∅ := by
    intro j; ext s; simp only [mem_inter_iff, mem_sdiff, mem_empty_iff_false, iff_false]; tauto
  by_cases hab : a + b ≤ 2 ^ k
  · apply le_NN hab
    rw [split b]
    exact h.subst_le (h.UU_mem _ _) (g.sdiff_mem (h.UU_mem _ _) (h.UU_mem _ _)) hA hB (disj b)
      hAB ha (by rw [h.shift k b a hab]; exact hb)
  · exfalso
    set j := 2 ^ k - a
    have hj : a + j = 2 ^ k := by omega
    have hlt := h.subst_lt (h.UU_mem _ _) (g.sdiff_mem (h.UU_mem _ _) (h.UU_mem _ _)) hA hB
      (disj j) hAB ha (by
        rw [h.shift k j a (by omega)]
        exact (h.UU_lt (show j < b by omega) hbk).trans_le hb)
    rw [← split j, hj, UU_top k _ le_rfl, h.W1] at hlt
    have := h.mono univ g.univ_mem (A ∪ B) (g.union_mem hA hB) (subset_univ _)
    rw [h.W1] at this
    linarith

lemma Hyp.NN_hi (h : Hyp 𝒮 W) (k : ℕ) {A B : Set S} (hA : A ∈ 𝒮) (hB : B ∈ 𝒮)
    (hAB : A ∩ B = ∅) :
    NN 𝒮 W k (W (A ∪ B)) ≤ NN 𝒮 W k (W A) + NN 𝒮 W k (W B) + 1 := by
  have g := h.alg
  set a := NN 𝒮 W k (W A)
  set b := NN 𝒮 W k (W B)
  have hn := NN_le (𝒮 := 𝒮) (W := W) k (W (A ∪ B))
  by_cases hab : a + b + 2 ≤ 2 ^ k
  · have hA' : W A < W (UU 𝒮 W k (a + 1)) := NN_great (Nat.lt_succ_self _) (by omega)
    have hB' : W B < W (UU 𝒮 W k (b + 1)) := NN_great (Nat.lt_succ_self _) (by omega)
    have split : UU 𝒮 W k (a + 1 + (b + 1)) =
        UU 𝒮 W k (a + 1) ∪ (UU 𝒮 W k (a + 1 + (b + 1)) \ UU 𝒮 W k (a + 1)) := by
      have := UU_mono (𝒮 := 𝒮) (W := W) k (show a + 1 ≤ a + 1 + (b + 1) by omega)
      ext s; have := @this s; simp only [mem_union, mem_sdiff]; tauto
    have hlt := h.subst_lt (A' := UU 𝒮 W k (a + 1))
      (B' := UU 𝒮 W k (a + 1 + (b + 1)) \ UU 𝒮 W k (a + 1))
      hA hB (h.UU_mem _ _) (g.sdiff_mem (h.UU_mem _ _) (h.UU_mem _ _)) hAB
      (by ext s; simp only [mem_inter_iff, mem_sdiff, mem_empty_iff_false, iff_false]; tauto)
      hA'.le (by rw [h.shift k (b + 1) (a + 1) (by omega)]; exact hB')
    rw [← split] at hlt
    by_contra hc; push Not at hc
    have sub := UU_mono (𝒮 := 𝒮) (W := W) k (show a + 1 + (b + 1) ≤ NN 𝒮 W k (W (A ∪ B)) by omega)
    have := h.mono _ (h.UU_mem _ _) _ (h.UU_mem _ _) sub
    have := h.NN_spec (k := k) (h.nn (g.union_mem hA hB))
    linarith
  · omega

end counting

section limit

variable (𝒮 W) in
noncomputable def ff (t : ℝ) : ℝ := ⨆ k : ℕ, (NN 𝒮 W k t : ℝ) / 2 ^ k

lemma term_le_one (k : ℕ) (t : ℝ) : (NN 𝒮 W k t : ℝ) / 2 ^ k ≤ 1 := by
  rw [div_le_one (by positivity)]
  exact_mod_cast NN_le k t

lemma ff_bdd (t : ℝ) : BddAbove (range fun k : ℕ => (NN 𝒮 W k t : ℝ) / 2 ^ k) :=
  ⟨1, by rintro _ ⟨k, rfl⟩; exact term_le_one k t⟩

lemma ff_ge (k : ℕ) (t : ℝ) : (NN 𝒮 W k t : ℝ) / 2 ^ k ≤ ff 𝒮 W t :=
  le_ciSup (ff_bdd t) k

lemma Hyp.iter (h : Hyp 𝒮 W) {t : ℝ} (ht : 0 ≤ t) (k : ℕ) : ∀ d,
    2 ^ d * NN 𝒮 W k t ≤ NN 𝒮 W (k + d) t ∧
      NN 𝒮 W (k + d) t + 1 ≤ 2 ^ d * (NN 𝒮 W k t + 1) := by
  intro d
  induction d with
  | zero => simp
  | succ d ih =>
    have l1 := h.NN_lev1 (k := k + d) ht
    have l2 := h.NN_lev2 (k := k + d) ht
    rw [← add_assoc]
    constructor
    · rw [pow_succ]; nlinarith [ih.1]
    · rw [pow_succ]; nlinarith [ih.2]

lemma Hyp.ff_le (h : Hyp 𝒮 W) {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    ff 𝒮 W t ≤ ((NN 𝒮 W k t : ℝ) + 1) / 2 ^ k := by
  apply ciSup_le
  intro j
  rcases le_total j k with hjk | hkj
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjk
    have := (h.iter ht j d).1
    have c : (2 : ℝ) ^ d * (NN 𝒮 W j t : ℝ) ≤ (NN 𝒮 W (j + d) t : ℝ) := by exact_mod_cast this
    rw [div_le_div_iff₀ (by positivity) (by positivity), pow_add]
    nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) j, pow_pos (two_pos : (0 : ℝ) < 2) d]
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkj
    have := (h.iter ht k d).2
    have c : (NN 𝒮 W (k + d) t : ℝ) + 1 ≤ (2 : ℝ) ^ d * ((NN 𝒮 W k t : ℝ) + 1) := by
      exact_mod_cast this
    rw [div_le_div_iff₀ (by positivity) (by positivity), pow_add]
    nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) k, pow_pos (two_pos : (0 : ℝ) < 2) d]

lemma sandwich {p q c : ℝ} (hk : ∀ k : ℕ, |p - q| ≤ c / 2 ^ k) : p = q := by
  by_contra hne
  have hpos : 0 < |p - q| := abs_pos.2 (sub_ne_zero.2 hne)
  obtain ⟨k, hk'⟩ := exists_nat_gt (c / |p - q|)
  have h2 : (k : ℝ) < 2 ^ k := by exact_mod_cast Nat.lt_two_pow_self
  have := hk k
  rw [le_div_iff₀ (by positivity)] at this
  rw [div_lt_iff₀ hpos] at hk'
  nlinarith

end limit

section arch

lemma UU_one_anti : Antitone (fun k => UU 𝒮 W k 1) := by
  apply antitone_nat_of_succ_le
  intro k
  have := UU_odd (𝒮 := 𝒮) (W := W) k 0
  simp only [mul_zero, zero_add] at this
  rw [this, UU_zero, empty_union]
  exact (half_subset _).trans sdiff_subset

lemma Hyp.arch_step (h : Hyp 𝒮 W) {Z : Set S} (hZ : Z ∈ 𝒮) (hpos : 0 < W Z) :
    ∃ k, W (CC 𝒮 W k 0) ≤ W Z := by
  by_contra hc; push Not at hc
  have ex : ∀ k : ℕ, ∃ E ∈ 𝒮, E ⊆ CC 𝒮 W (k + 1) 1 ∧ W E = W Z := by
    intro k
    obtain ⟨E, hE, -, hsub, hW⟩ := h.cr ∅ h.alg.empty_mem _ (h.CC_mem (k + 1) 1)
      (empty_subset _) (W Z) (by rw [h.W0]; exact hpos.le)
      (by
        rw [h.CC_eq (k + 1) 1 (by have := Nat.one_lt_two_pow (n := k + 1) (by omega); omega)]
        exact (hc (k + 1)).le)
    exact ⟨E, hE, hsub, hW⟩
  choose E hE hsub hW using ex
  have csub : ∀ k, CC 𝒮 W (k + 1) 1 ⊆ UU 𝒮 W k 1 := by
    intro k
    have := UU_even (𝒮 := 𝒮) (W := W) k 1
    simp only [mul_one] at this
    unfold CC; rw [this]; exact sdiff_subset
  have cdisj : ∀ k, Disjoint (CC 𝒮 W (k + 1) 1) (UU 𝒮 W (k + 1) 1) := by
    intro k; unfold CC; exact disjoint_sdiff_left
  have key : ∀ i j, i < j → Disjoint (E i) (E j) := by
    intro i j hij
    have s1 : E j ⊆ UU 𝒮 W (i + 1) 1 :=
      (hsub j).trans ((csub j).trans (UU_one_anti (𝒮 := 𝒮) (W := W) (show i + 1 ≤ j by omega)))
    exact Disjoint.mono (hsub i) s1 (cdisj i)
  apply h.arch
  refine ⟨E, hE, ?_, fun i => by rw [hW]; exact hpos, fun i j => by rw [hW, hW]⟩
  intro i j hij
  rcases lt_or_gt_of_ne hij with c | c
  · exact key i j c
  · exact (key j i c).symm

end arch

section prob

lemma Hyp.Q_bounds (h : Hyp 𝒮 W) {Q : Set S → ℝ} (hQ : IsProbOn 𝒮 Q)
    (hrep : ∀ A ∈ 𝒮, ∀ A' ∈ 𝒮, W A' ≤ W A ↔ Q A' ≤ Q A) {A : Set S} (hA : A ∈ 𝒮) (k : ℕ) :
    (NN 𝒮 W k (W A) : ℝ) / 2 ^ k ≤ Q A ∧ Q A ≤ ((NN 𝒮 W k (W A) : ℝ) + 1) / 2 ^ k := by
  have g := h.alg
  obtain ⟨hQ1, -, hQadd⟩ := hQ
  have hQ0 : Q ∅ = 0 := by
    have := hQadd ∅ g.empty_mem ∅ g.empty_mem (disjoint_empty _)
    rw [union_empty] at this; linarith
  have hcell : ∀ i < 2 ^ k, Q (CC 𝒮 W k i) = Q (CC 𝒮 W k 0) := by
    intro i hi
    have e := h.CC_eq k i hi
    exact le_antisymm ((hrep _ (h.CC_mem k 0) _ (h.CC_mem k i)).1 e.le)
      ((hrep _ (h.CC_mem k i) _ (h.CC_mem k 0)).1 e.ge)
  have hUU : ∀ m ≤ 2 ^ k, Q (UU 𝒮 W k m) = m * Q (CC 𝒮 W k 0) := by
    intro m
    induction m with
    | zero => intro _; rw [UU_zero, hQ0]; simp
    | succ m ih =>
      intro hm
      have r : UU 𝒮 W k (m + 1) = UU 𝒮 W k m ∪ CC 𝒮 W k m := by
        unfold CC
        have b := UU_succ_sub (𝒮 := 𝒮) (W := W) k m
        ext s; have := @b s; simp only [mem_union, mem_sdiff]; tauto
      rw [r, hQadd _ (h.UU_mem _ _) _ (h.CC_mem _ _) (by unfold CC; exact disjoint_sdiff_right),
        ih (by omega), hcell m (by omega)]
      push_cast; ring
  have hc : Q (CC 𝒮 W k 0) = 1 / 2 ^ k := by
    have := hUU (2 ^ k) le_rfl
    rw [UU_top k _ le_rfl, hQ1] at this
    push_cast at this
    field_simp; linarith
  have hUU' : ∀ m ≤ 2 ^ k, Q (UU 𝒮 W k m) = m / 2 ^ k := by
    intro m hm; rw [hUU m hm, hc]; ring
  set N := NN 𝒮 W k (W A)
  have hNk : N ≤ 2 ^ k := NN_le k _
  constructor
  · rw [← hUU' N hNk]
    exact (hrep _ hA _ (h.UU_mem _ _)).1 (h.NN_spec (h.nn hA))
  · by_cases hN : N < 2 ^ k
    · have hlt : W A < W (UU 𝒮 W k (N + 1)) := NN_great (Nat.lt_succ_self _) hN
      have : Q A < Q (UU 𝒮 W k (N + 1)) := by
        by_contra c; push Not at c
        have := (hrep _ hA _ (h.UU_mem _ _)).2 c
        linarith
      rw [hUU' (N + 1) hN] at this
      push_cast at this; exact this.le
    · have hNe : N = 2 ^ k := by omega
      have := (hrep _ g.univ_mem _ hA).1 (h.mono _ g.univ_mem _ hA (subset_univ _))
      rw [hQ1] at this
      rw [hNe]; push_cast
      rw [le_div_iff₀ (by positivity)]
      nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) k]

lemma Hyp.ff_strict (h : Hyp 𝒮 W) {A A' : Set S} (hA : A ∈ 𝒮) (hA' : A' ∈ 𝒮)
    (hlt : W A < W A') : ff 𝒮 W (W A) < ff 𝒮 W (W A') := by
  have g := h.alg
  obtain ⟨A'', hA'', -, hsub, hW⟩ := h.cr ∅ g.empty_mem A' hA' (empty_subset _) (W A)
    (by rw [h.W0]; exact h.nn hA) hlt.le
  set Z := A' \ A''
  have hZ : Z ∈ 𝒮 := g.sdiff_mem hA' hA''
  have hZpos : 0 < W Z := by
    by_contra c; push Not at c
    have e := (h.add ∅ g.empty_mem Z hZ A'' hA'' (by simp) (by ext s; simp [Z])).1
      (by rw [h.W0]; exact c)
    have r : Z ∪ A'' = A' := by ext s; simp only [Z, mem_union, mem_sdiff]; have := @hsub s; tauto
    rw [r, empty_union, hW] at e
    linarith
  obtain ⟨k, hk⟩ := h.arch_step hZ hZpos
  have e2 : UU 𝒮 W (k + 1) 2 = CC 𝒮 W k 0 := by
    have := UU_even (𝒮 := 𝒮) (W := W) k 1
    simp only [mul_one] at this
    rw [this]; unfold CC; rw [UU_zero, diff_empty]
  have hZ2 : 2 ≤ NN 𝒮 W (k + 1) (W Z) := by
    apply le_NN
    · have := Nat.one_lt_two_pow (n := k + 1) (by omega); omega
    · rw [e2]; exact hk
  have lo := h.NN_lo (k + 1) hA'' hZ (by ext s; simp [Z])
  have r : A'' ∪ Z = A' := by ext s; simp only [Z, mem_union, mem_sdiff]; have := @hsub s; tauto
  rw [r, hW] at lo
  have c1 := ff_ge (𝒮 := 𝒮) (W := W) (k + 1) (W A')
  have c2 := h.ff_le (h.nn hA) (k + 1)
  have c3 : ((NN 𝒮 W (k + 1) (W A) : ℝ) + 2) ≤ (NN 𝒮 W (k + 1) (W A') : ℝ) := by
    exact_mod_cast (show NN 𝒮 W (k + 1) (W A) + 2 ≤ NN 𝒮 W (k + 1) (W A') by omega)
  have c4 : ((NN 𝒮 W (k + 1) (W A) : ℝ) + 1) / 2 ^ (k + 1) <
      (NN 𝒮 W (k + 1) (W A') : ℝ) / 2 ^ (k + 1) := by
    apply div_lt_div_of_pos_right _ (by positivity); linarith
  linarith

theorem main (h : Hyp 𝒮 W) :
    ∃ P : Set S → ℝ, IsProbOn 𝒮 P ∧ (∀ A ∈ 𝒮, ∀ A' ∈ 𝒮, W A' ≤ W A ↔ P A' ≤ P A) ∧
      ∀ Q : Set S → ℝ, IsProbOn 𝒮 Q → (∀ A ∈ 𝒮, ∀ A' ∈ 𝒮, W A' ≤ W A ↔ Q A' ≤ Q A) →
        ∀ E ∈ 𝒮, Q E = P E := by
  have g := h.alg
  refine ⟨fun A => ff 𝒮 W (W A), ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · -- P univ = 1
    simp only
    rw [h.W1]
    apply le_antisymm
    · exact ciSup_le fun k => term_le_one k 1
    · have := ff_ge (𝒮 := 𝒮) (W := W) 0 1
      have e : NN 𝒮 W 0 1 = 1 := by
        classical
        unfold NN
        rw [Nat.findGreatest_eq]
        · simp
        · rw [UU_top 0 _ (by simp), h.W1]
      rw [e] at this; simpa using this
  · intro E hE
    exact le_trans (by positivity) (ff_ge (𝒮 := 𝒮) (W := W) 0 (W E))
  · intro E hE F hF hEF
    have hEF' : E ∩ F = ∅ := Set.disjoint_iff_inter_eq_empty.1 hEF
    apply sandwich (c := 2)
    intro k
    have lo := h.NN_lo k hE hF hEF'
    have hi := h.NN_hi k hE hF hEF'
    have lo' : (NN 𝒮 W k (W E) : ℝ) + NN 𝒮 W k (W F) ≤ NN 𝒮 W k (W (E ∪ F)) := by
      exact_mod_cast lo
    have hi' : (NN 𝒮 W k (W (E ∪ F)) : ℝ) ≤ NN 𝒮 W k (W E) + NN 𝒮 W k (W F) + 1 := by
      exact_mod_cast hi
    have a1 := ff_ge (𝒮 := 𝒮) (W := W) k (W (E ∪ F))
    have a2 := h.ff_le (h.nn (g.union_mem hE hF)) k
    have b1 := ff_ge (𝒮 := 𝒮) (W := W) k (W E)
    have b2 := h.ff_le (h.nn hE) k
    have c1 := ff_ge (𝒮 := 𝒮) (W := W) k (W F)
    have c2 := h.ff_le (h.nn hF) k
    have hp : (0 : ℝ) < 2 ^ k := by positivity
    rw [abs_le]
    simp only [add_div] at a2 b2 c2 ⊢
    constructor
    · have : (NN 𝒮 W k (W E) : ℝ) / 2 ^ k + (NN 𝒮 W k (W F) : ℝ) / 2 ^ k ≤
          (NN 𝒮 W k (W (E ∪ F)) : ℝ) / 2 ^ k := by
        rw [← add_div]; exact div_le_div_of_nonneg_right lo' hp.le
      have : (2 / 2 ^ k : ℝ) = 1 / 2 ^ k + 1 / 2 ^ k := by rw [← add_div]; norm_num
      linarith
    · have : (NN 𝒮 W k (W (E ∪ F)) : ℝ) / 2 ^ k ≤
          (NN 𝒮 W k (W E) : ℝ) / 2 ^ k + (NN 𝒮 W k (W F) : ℝ) / 2 ^ k + 1 / 2 ^ k := by
        rw [← add_div, ← add_div]; exact div_le_div_of_nonneg_right hi' hp.le
      have : (2 / 2 ^ k : ℝ) = 1 / 2 ^ k + 1 / 2 ^ k := by rw [← add_div]; norm_num
      linarith
  · intro A hA A' hA'
    constructor
    · intro hle
      apply ciSup_le
      intro k
      exact le_trans (div_le_div_of_nonneg_right (by exact_mod_cast NN_mono hle) (by positivity))
        (ff_ge k (W A))
    · intro hle
      by_contra c; push Not at c
      have := h.ff_strict hA hA' c
      linarith
  · intro Q hQ hrep E hE
    apply sandwich (c := 1)
    intro k
    have q := h.Q_bounds hQ hrep hE k
    have p1 := ff_ge (𝒮 := 𝒮) (W := W) k (W E)
    have p2 := h.ff_le (h.nn hE) k
    rw [abs_le]
    simp only [add_div] at q p2 ⊢
    constructor <;> linarith [q.1, q.2]

end prob

end STUQPAux

open Set MeasureTheory SourceTheory.Uniform in
theorem solution {S : Type*} (𝒮 : Set (Set S)) (W : Set S → ℝ)
    (h𝒮 : IsSetAlgebra 𝒮) (hW0 : W ∅ = 0) (hW1 : W univ = 1)
    (hmono : ∀ A ∈ 𝒮, ∀ B ∈ 𝒮, B ⊆ A → W B ≤ W A)
    (hadd : ∀ E ∈ 𝒮, ∀ F ∈ 𝒮, ∀ H ∈ 𝒮, E ∩ H = ∅ → F ∩ H = ∅ →
      (W F ≤ W E ↔ W (F ∪ H) ≤ W (E ∪ H)))
    (hcr : IsConvexRanged 𝒮 W)
    (harch : ¬ ∃ E : ℕ → Set S, (∀ i, E i ∈ 𝒮) ∧ Pairwise (fun i j => Disjoint (E i) (E j)) ∧
      (∀ i, 0 < W (E i)) ∧ ∀ i j, W (E i) = W (E j)) :
    ∃ P : Set S → ℝ, IsProbOn 𝒮 P ∧ (∀ A ∈ 𝒮, ∀ A' ∈ 𝒮, W A' ≤ W A ↔ P A' ≤ P A) ∧
      ∀ Q : Set S → ℝ, IsProbOn 𝒮 Q → (∀ A ∈ 𝒮, ∀ A' ∈ 𝒮, W A' ≤ W A ↔ Q A' ≤ Q A) →
        ∀ E ∈ 𝒮, Q E = P E :=
  STUQPAux.main ⟨h𝒮, hW0, hW1, hmono, hadd, hcr, harch⟩
