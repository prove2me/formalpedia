-- Prove2me | solution 1 for StochApproxDyn.Lyapunov.subset_and_const_of_isInternallyChainTransitive
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T06:49:57.927282+00:00
-- url     : https://prove2.me/submissions/8ed57314-4ad8-4507-b797-6f7735298a69

import Mathlib
import Definitions.Def_StochApproxDyn_LimitSet_ChainRecurrence
import Definitions.Def_StochApproxDyn_Lyapunov_LyapunovFunction

set_option autoImplicit false

open scoped NNReal

namespace P12db0f23

open StochApproxDyn.LimitSet StochApproxDyn.Lyapunov

theorem V_flow_le {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M) (Λ : Set M) (V : M → ℝ)
    (hV : IsLyapunovFunction Φ Λ V) (x : M) (s : ℝ≥0) : V (Φ s x) ≤ V x := by
  by_cases hx : x ∈ Λ
  · exact (hV.2.2.2.1 x hx s).le
  · have := (hV.2.2.2.2 x hx).antitone (show (0 : ℝ≥0) ≤ s from zero_le)
    simpa [Flow.map_zero_apply] using this

theorem not_lt_on {M : Type*} [MetricSpace M]
    (Φ : Flow ℝ≥0 M) (Λ : Set M) (V : M → ℝ) (hV : IsLyapunovFunction Φ Λ V)
    (hint : interior (V '' Λ) = ∅) (L : Set M) (hL : IsInternallyChainTransitive Φ L)
    (a b : M) (ha : a ∈ L) (hb : b ∈ L) : ¬ V a < V b := by
  intro hab
  obtain ⟨_, hLc, hLi, hch⟩ := hL
  -- pick c ∈ (V a, V b) with c ∉ V '' Λ
  have hc : ∃ c ∈ Set.Ioo (V a) (V b), c ∉ V '' Λ := by
    by_contra hcon
    push Not at hcon
    have hsub : Set.Ioo (V a) (V b) ⊆ interior (V '' Λ) :=
      interior_maximal hcon isOpen_Ioo
    rw [hint] at hsub
    exact (Set.nonempty_Ioo.2 hab).ne_empty (Set.subset_empty_iff.1 hsub)
  obtain ⟨c, ⟨hac, hcb⟩, hcΛ⟩ := hc
  have hVc : Continuous V := hV.2.2.1
  set K : Set M := L ∩ {x | V x ≤ c} with hK
  have hKc : IsCompact K := hLc.inter_right (isClosed_le hVc continuous_const)
  have hΦ1 : Continuous (fun x => Φ 1 x) := Φ.continuous continuous_const continuous_id
  set C : Set M := (fun x => Φ 1 x) '' K ∪ {a} with hC
  have hCc : IsCompact C := (hKc.image hΦ1).union isCompact_singleton
  have hCU : C ⊆ {x | V x < c} := by
    rintro z (⟨y, ⟨hyL, hyc⟩, rfl⟩ | hz)
    · show V (Φ 1 y) < c
      by_cases hy : y ∈ Λ
      · rw [hV.2.2.2.1 y hy 1]
        refine lt_of_le_of_ne hyc ?_
        intro h
        exact hcΛ ⟨y, hy, h⟩
      · have := (hV.2.2.2.2 y hy) (show (0 : ℝ≥0) < 1 from one_pos)
        simp only [Flow.map_zero_apply] at this
        exact lt_of_lt_of_le this hyc
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      exact hac
  obtain ⟨δ, hδ, hthick⟩ :=
    hCc.exists_thickening_subset_open (isOpen_lt hVc continuous_const) hCU
  obtain ⟨k, y, t, hk1, ht, hy0, hstep, hyk⟩ := hch ⟨a, ha⟩ ⟨b, hb⟩ δ hδ 1 one_pos
  have key : ∀ i, i ≤ k → V (y i : M) < c := by
    intro i
    induction i with
    | zero =>
      intro _
      have hmem : ((y 0 : L) : M) ∈ Metric.thickening δ C := by
        rw [Metric.mem_thickening_iff]
        refine ⟨a, Or.inr rfl, ?_⟩
        simpa [Subtype.dist_eq] using hy0
      exact hthick hmem
    | succ i ih =>
      intro hi
      have hik : i < k := Nat.lt_of_succ_le hi
      have hVi := ih hik.le
      have hti := ht i hik
      have hs := hstep i hik
      rw [Subtype.dist_eq] at hs
      have hco : ((restrictSemiflow Φ hLi (t i) (y i) : L) : M) = Φ (t i) (y i) := rfl
      rw [hco] at hs
      have hsplit : Φ (t i) (y i) = Φ 1 (Φ (t i - 1) (y i)) := by
        rw [← Flow.map_add, add_tsub_cancel_of_le hti]
      have hmemK : Φ (t i - 1) (y i) ∈ K := by
        refine ⟨?_, ?_⟩
        · exact (hLi (t i - 1)).subset (Set.mem_image_of_mem _ (y i).2)
        · exact (V_flow_le Φ Λ V hV _ _).trans hVi.le
      have hmemC : Φ (t i) (y i) ∈ C := by
        rw [hsplit]
        exact Or.inl ⟨_, hmemK, rfl⟩
      have hmem : ((y (i + 1) : L) : M) ∈ Metric.thickening δ C := by
        rw [Metric.mem_thickening_iff]
        refine ⟨_, hmemC, ?_⟩
        rw [dist_comm]
        exact hs
      exact hthick hmem
  have := key k le_rfl
  rw [hyk] at this
  exact absurd (lt_trans this hcb) (lt_irrefl _)

end P12db0f23

open NNReal StochApproxDyn.Lyapunov in
theorem solution {M : Type*} [MetricSpace M]
    (Φ : Flow ℝ≥0 M) (Λ : Set M) (V : M → ℝ) (hV : IsLyapunovFunction Φ Λ V)
    (hint : interior (V '' Λ) = ∅) :
    ∀ L : Set M, StochApproxDyn.LimitSet.IsInternallyChainTransitive Φ L →
      L ⊆ Λ ∧ ∃ v : ℝ, ∀ x ∈ L, V x = v := by
  intro L hL
  obtain ⟨⟨x0, hx0⟩, hLc, hLi, hch⟩ := hL
  have hconst : ∀ x ∈ L, V x = V x0 := by
    intro x hx
    exact le_antisymm
      (not_lt.1 (P12db0f23.not_lt_on Φ Λ V hV hint L ⟨⟨x0, hx0⟩, hLc, hLi, hch⟩ x0 x hx0 hx))
      (not_lt.1 (P12db0f23.not_lt_on Φ Λ V hV hint L ⟨⟨x0, hx0⟩, hLc, hLi, hch⟩ x x0 hx hx0))
  refine ⟨?_, V x0, hconst⟩
  intro x hx
  by_contra hxΛ
  have h1 := (hV.2.2.2.2 x hxΛ) (show (0 : ℝ≥0) < 1 from one_pos)
  simp only [Flow.map_zero_apply] at h1
  have hmem : Φ 1 x ∈ L := by
    rw [← hLi 1]
    exact Set.mem_image_of_mem _ hx
  rw [hconst _ hmem, hconst x hx] at h1
  exact lt_irrefl _ h1
