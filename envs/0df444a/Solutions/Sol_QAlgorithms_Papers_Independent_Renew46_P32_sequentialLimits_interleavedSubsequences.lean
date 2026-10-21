-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P32.sequentialLimits_interleavedSubsequences
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T04:15:14.175057+00:00
-- url     : https://prove2.me/submissions/72bac054-4329-4bea-b28a-6d097f1e2b29

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P32

open QAlgorithms.Papers.Independent.Renew46.P32

open Set Filter Topology

universe u v

theorem g66b_alt_tendsto {Y : Type v} {l : Filter Y} (a b : ℕ → Y)
    (ha : Tendsto a atTop l) (hb : Tendsto b atTop l) :
    Tendsto (alternatingSequence a b) atTop l := by
  have hd : Tendsto (fun n : ℕ => n / 2) atTop atTop := Nat.tendsto_div_const_atTop (by norm_num)
  unfold alternatingSequence
  exact Tendsto.if ((ha.comp hd).mono_left inf_le_left) ((hb.comp hd).mono_left inf_le_left)

theorem g66b_alt_even {Y : Type v} (a b : ℕ → Y) (n : ℕ) :
    alternatingSequence a b (2 * n) = a n := by
  simp [alternatingSequence]

theorem g66b_alt_odd {Y : Type v} (a b : ℕ → Y) (n : ℕ) :
    alternatingSequence a b (2 * n + 1) = b n := by
  simp only [alternatingSequence]
  rw [if_neg (by simp)]
  congr 1; omega

theorem g66b_tend_even {Y : Type v} [TopologicalSpace Y] {a b : ℕ → Y} {y : Y}
    (h : Tendsto (alternatingSequence a b) atTop (𝓝 y)) : Tendsto a atTop (𝓝 y) := by
  have h2 : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_id.const_mul_atTop' (by norm_num)
  have := h.comp h2
  simpa [Function.comp_def, g66b_alt_even] using this

theorem g66b_tend_odd {Y : Type v} [TopologicalSpace Y] {a b : ℕ → Y} {y : Y}
    (h : Tendsto (alternatingSequence a b) atTop (𝓝 y)) : Tendsto b atTop (𝓝 y) := by
  have h2 : Tendsto (fun n : ℕ => 2 * n + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => show id n ≤ 2 * n + 1 by simp; omega) tendsto_id
  have := h.comp h2
  simpa [Function.comp_def, g66b_alt_odd] using this

theorem solution
    {X : Type u} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [T2Space X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y]
    (S : Set X) (f : S → Y) (x : X) (hx : x ∈ closure S) :
    (∀ a : ℕ → S, Tendsto (fun n => (a n : X)) atTop (𝓝 x) →
      ∃ y : Y, Tendsto (fun n => f (a n)) atTop (𝓝 y)) ↔
    (∀ a b : ℕ → S,
      Tendsto (fun n => (a n : X)) atTop (𝓝 x) →
      Tendsto (fun n => (b n : X)) atTop (𝓝 x) →
      ∃ i j : ℕ → ℕ, StrictMono i ∧ StrictMono j ∧
        ∃ y : Y, Tendsto (alternatingSequence (fun n => f (a (i n)))
          (fun n => f (b (j n)))) atTop (𝓝 y)) := by
  constructor
  · intro H a b ha hb
    refine ⟨id, id, strictMono_id, strictMono_id, ?_⟩
    obtain ⟨y, hy⟩ := H (alternatingSequence a b) (by
      have := g66b_alt_tendsto (fun n => (a n : X)) (fun n => (b n : X)) ha hb
      convert this using 2 with n
      unfold alternatingSequence; split_ifs <;> rfl)
    refine ⟨y, ?_⟩
    convert hy using 2 with n
    unfold alternatingSequence; split_ifs <;> rfl
  · intro H a ha
    obtain ⟨i0, j0, hi0, -, y0, hy0⟩ := H a a ha ha
    have hy0' := g66b_tend_even hy0
    refine ⟨y0, ?_⟩
    apply tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨i', j', hi', hj', y', hy'⟩ :=
      H (fun n => a (i0 n)) (fun n => a (ns n)) (ha.comp hi0.tendsto_atTop) (ha.comp hns)
    have e1 := g66b_tend_even hy'
    have e2 : Tendsto (fun n => f (a (i0 (i' n)))) atTop (𝓝 y0) :=
      hy0'.comp hi'.tendsto_atTop
    have : y' = y0 := tendsto_nhds_unique e1 e2
    subst this
    exact ⟨j', g66b_tend_odd hy'⟩
