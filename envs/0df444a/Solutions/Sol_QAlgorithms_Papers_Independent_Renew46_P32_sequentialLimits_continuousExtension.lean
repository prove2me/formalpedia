-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P32.sequentialLimits_continuousExtension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T04:15:57.81341+00:00
-- url     : https://prove2.me/submissions/7ae885f7-1753-43a9-a8df-8747147def73

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
    {Y : Type v} [TopologicalSpace Y] [RegularSpace Y] [T2Space Y]
    (D : Set X) (hD : Dense D) (f : D → Y) (hf : Continuous f)
    (hLimits : ∀ (s : ℕ → D) (x : X),
      Tendsto (fun n => (s n : X)) atTop (𝓝 x) →
        ∃ y : Y, Tendsto (fun n => f (s n)) atTop (𝓝 y)) :
    ∃ g : X → Y, Continuous g ∧ ∀ x : D, g x = f x := by
  have hDI : IsDenseInducing (Subtype.val : D → X) := hD.isDenseInducing_val
  have key : ∀ x : X, ∃ y, Tendsto f (comap Subtype.val (𝓝 x)) (𝓝 y) := by
    intro x
    haveI := hDI.comap_nhds_neBot x
    obtain ⟨s0, hs0⟩ := exists_seq_tendsto (comap (Subtype.val : D → X) (𝓝 x))
    have hs0' : Tendsto (fun n => (s0 n : X)) atTop (𝓝 x) := tendsto_comap_iff.mp hs0
    obtain ⟨y, hy⟩ := hLimits s0 x hs0'
    refine ⟨y, tendsto_of_seq_tendsto fun s hs => ?_⟩
    have hs' : Tendsto (fun n => (s n : X)) atTop (𝓝 x) := tendsto_comap_iff.mp hs
    have ht : Tendsto (fun n => ((alternatingSequence s0 s n : D) : X)) atTop (𝓝 x) := by
      have := g66b_alt_tendsto _ _ hs0' hs'
      convert this using 2 with n
      unfold alternatingSequence; split_ifs <;> rfl
    obtain ⟨y', hy'⟩ := hLimits _ x ht
    have hy'' : Tendsto (alternatingSequence (fun n => f (s0 n)) (fun n => f (s n))) atTop
        (𝓝 y') := by
      convert hy' using 2 with n
      unfold alternatingSequence; split_ifs <;> rfl
    have := tendsto_nhds_unique (g66b_tend_even hy'') hy
    subst this
    exact g66b_tend_odd hy''
  exact ⟨hDI.extend f, hDI.continuous_extend key, fun x => hDI.extend_eq hf x⟩
