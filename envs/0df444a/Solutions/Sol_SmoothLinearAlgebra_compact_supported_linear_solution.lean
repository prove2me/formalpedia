-- Prove2me | solution 1 for SmoothLinearAlgebra.compact_supported_linear_solution
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-06T19:16:29.011482+00:00
-- url     : https://prove2.me/submissions/31c4960f-fc4e-4fca-ac46-512e09a6722b

import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Tactic.Linarith

open Set Function
open scoped ContDiff Topology

set_option autoImplicit false

theorem solution {P V W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (A : P → V →L[ℝ] W) (b : P → W)
    (hA : ContDiff ℝ ∞ A) (hb : ContDiff ℝ ∞ b)
    (C : Set P) (hC : IsCompact C) (hi : ∀ p ∈ C, (A p).IsInvertible) :
    ∃ u : P → V, ∃ χ : P → ℝ,
      ContDiff ℝ ∞ u ∧ ContDiff ℝ ∞ χ ∧ HasCompactSupport u ∧
      (∀ p ∈ C, χ p = 1) ∧ (∀ p, A p (u p) = χ p • b p) := by
  let U : Set P := {p | (A p).IsInvertible}
  have hU : IsOpen U := by
    change IsOpen (A ⁻¹' Set.range (fun e : V ≃L[ℝ] W => (e : V →L[ℝ] W)))
    exact ContinuousLinearEquiv.isOpen.preimage hA.continuous
  obtain ⟨L, hL, hCL, hLU⟩ := exists_compact_between hC hU hi
  obtain ⟨f, hfs, hf, hfr⟩ := (isOpen_interior (s := L)).exists_contDiff_support_eq (n := (⊤ : ℕ∞))
  obtain ⟨g, hgs, hg, hgr⟩ := hC.isClosed.isOpen_compl.exists_contDiff_support_eq (n := (⊤ : ℕ∞))
  have hpos : ∀ p, 0 < f p + g p := by
    intro p
    have hf0 := (hfr (mem_range_self p)).1
    have hg0 := (hgr (mem_range_self p)).1
    by_cases hp : p ∈ C
    · have hfne : f p ≠ 0 := by
        rw [← mem_support, hfs]
        exact hCL hp
      exact add_pos_of_pos_of_nonneg (lt_of_le_of_ne hf0 (Ne.symm hfne)) hg0
    · have hgne : g p ≠ 0 := by
        rw [← mem_support, hgs]
        exact hp
      exact add_pos_of_nonneg_of_pos hf0 (lt_of_le_of_ne hg0 (Ne.symm hgne))
  let χ : P → ℝ := fun p => f p / (f p + g p)
  have hχ : ContDiff ℝ ∞ χ := hf.div (hf.add hg) (fun p => (hpos p).ne')
  have hχC : ∀ p ∈ C, χ p = 1 := by
    intro p hp
    have hz : g p = 0 := by
      apply notMem_support.mp
      rwa [hgs, mem_compl_iff, not_not]
    have hne : f p ≠ 0 := by simpa [hz] using (hpos p).ne'
    simp [χ, hz, hne]
  have hsχ : support χ = interior L := by
    have hs : support (fun p => f p + g p) = univ :=
      eq_univ_of_forall (fun p => (hpos p).ne')
    simp only [χ, support_div, hfs, hs, inter_univ]
  have htχ : tsupport χ ⊆ L := by
    rw [tsupport, hsχ]
    exact hL.isClosed.closure_subset_iff.mpr interior_subset
  let u : P → V := fun p => χ p • (A p).inverse (b p)
  have hu : ContDiff ℝ ∞ u := by
    rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hp : p ∈ tsupport χ
    · have hinv : (A p).IsInvertible := hLU (htχ hp)
      exact hχ.contDiffAt.smul
        ((hinv.contDiffAt_map_inverse.comp p hA.contDiffAt).clm_apply hb.contDiffAt)
    · have hz : χ =ᶠ[𝓝 p] (fun _ => 0) := by
        filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hp] with q hq
        exact notMem_support.mp (fun hs => hq (subset_tsupport χ hs))
      apply (show ContDiffAt ℝ ∞ (fun _ : P => (0 : V)) p from contDiffAt_const).congr_of_eventuallyEq
      filter_upwards [hz] with q hq
      simp [u, hq]
  have hsu : tsupport u ⊆ L := by
    apply (closure_mono (support_smul_subset_left χ (fun p => (A p).inverse (b p)))).trans
    exact htχ
  refine ⟨u, χ, hu, hχ, hL.of_isClosed_subset isClosed_closure hsu, hχC, ?_⟩
  intro p
  by_cases hp : (A p).IsInvertible
  · obtain ⟨e, he⟩ := hp
    simp [u, ← he]
  · have hz : χ p = 0 := by
      apply notMem_support.mp
      intro hs
      exact hp (hLU (htχ (subset_tsupport χ hs)))
    simp [u, hz]
