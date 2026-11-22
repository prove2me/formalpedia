-- Prove2me | solution 1 for WeakMFG.Approx.lemma_5_6
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-22T13:51:53.608961+00:00
-- url     : https://prove2.me/submissions/570b85b2-6f98-4dfa-8301-c5c82c6fbca9

import Mathlib

open Filter Topology
open scoped ENNReal

theorem solution {E K : Type*} [TopologicalSpace E] [TopologicalSpace K] [CompactSpace K]
    (G : E × K → ℝ) (x₀ : E) :
    (∀ y : K, ContinuousAt G (x₀, y)) ↔
      (Continuous (fun y : K => G (x₀, y)) ∧
        Tendsto (fun x : E => ⨆ y : K, ENNReal.ofReal |G (x, y) - G (x₀, y)|) (𝓝 x₀) (𝓝 0)) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · -- continuity of the section `y ↦ G (x₀, y)`
      rw [continuous_iff_continuousAt]
      intro y
      have hpath : ContinuousAt (fun y : K => (x₀, y)) y :=
        continuousAt_const.prodMk continuousAt_id
      exact (h y).comp hpath
    · -- uniform deviation tends to zero
      rw [ENNReal.tendsto_nhds_zero]
      intro ε hε
      rcases eq_or_ne ε ⊤ with rfl | hfin
      · exact Eventually.of_forall fun x => le_top
      · have hε0 : ε ≠ 0 := ne_of_gt hε
        have hεpos : 0 < ε.toReal := ENNReal.toReal_pos hε0 hfin
        have hεeq : ENNReal.ofReal ε.toReal = ε := ENNReal.ofReal_toReal hfin
        -- for each `y` a product neighbourhood on which the deviation is `< ε.toReal`
        have hex : ∀ y : K, ∃ V : Set E, ∃ W : Set K,
            V ∈ 𝓝 x₀ ∧ W ∈ 𝓝 y ∧
              ∀ x ∈ V, ∀ y' ∈ W, |G (x, y') - G (x₀, y')| < ε.toReal := by
          intro y
          have hU : ∀ᶠ p : E × K in 𝓝 (x₀, y),
              dist (G p) (G (x₀, y)) < ε.toReal / 2 :=
            (Metric.continuousAt_iff'.mp (h y)) (ε.toReal / 2) (by linarith)
          rw [nhds_prod_eq] at hU
          obtain ⟨V, hV, W, hW, hVW⟩ := Filter.mem_prod_iff.mp hU
          refine ⟨V, W, hV, hW, ?_⟩
          intro x hx y' hy'
          have h1 : dist (G (x, y')) (G (x₀, y)) < ε.toReal / 2 :=
            hVW (Set.mk_mem_prod hx hy')
          have h2 : dist (G (x₀, y')) (G (x₀, y)) < ε.toReal / 2 :=
            hVW (Set.mk_mem_prod (mem_of_mem_nhds hV) hy')
          rw [Real.dist_eq] at h1 h2
          calc |G (x, y') - G (x₀, y')|
              ≤ |G (x, y') - G (x₀, y)| + |G (x₀, y) - G (x₀, y')| := abs_sub_le _ _ _
            _ = |G (x, y') - G (x₀, y)| + |G (x₀, y') - G (x₀, y)| := by
                rw [abs_sub_comm (G (x₀, y)) (G (x₀, y'))]
            _ < ε.toReal := by linarith
        choose V W hVW using hex
        have hVmem : ∀ y : K, V y ∈ 𝓝 x₀ := fun y => (hVW y).1
        have hWmem : ∀ y : K, W y ∈ 𝓝 y := fun y => (hVW y).2.1
        have hbnd : ∀ y : K, ∀ x ∈ V y, ∀ y' ∈ W y,
            |G (x, y') - G (x₀, y')| < ε.toReal := fun y => (hVW y).2.2
        -- finite subcover of the compact `K`
        obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover W (fun y _ => hWmem y)
        have hVt : (⋂ y ∈ t, V y) ∈ 𝓝 x₀ :=
          (Filter.biInter_finset_mem t).mpr fun y _ => hVmem y
        filter_upwards [hVt] with x hx
        have hx' : ∀ y, y ∈ t → x ∈ V y := by
          simpa only [Set.mem_iInter] using hx
        refine iSup_le fun y => ?_
        have hy : y ∈ ⋃ y₀ ∈ t, W y₀ := ht (Set.mem_univ y)
        simp only [Set.mem_iUnion, exists_prop] at hy
        obtain ⟨y₀, hy₀t, hyW⟩ := hy
        calc ENNReal.ofReal |G (x, y) - G (x₀, y)|
            ≤ ENNReal.ofReal ε.toReal :=
              ENNReal.ofReal_le_ofReal (le_of_lt (hbnd y₀ x (hx' y₀ hy₀t) y hyW))
          _ = ε := hεeq
  · -- converse: sup bound plus continuity of the section gives joint continuity
    rintro ⟨hcont, htend⟩ y₀
    rw [Metric.continuousAt_iff']
    intro ε hε
    have hhalf : 0 < ε / 2 := by linarith
    have hx : ∀ᶠ x : E in 𝓝 x₀,
        (⨆ y : K, ENNReal.ofReal |G (x, y) - G (x₀, y)|) ≤ ENNReal.ofReal (ε / 2) :=
      (ENNReal.tendsto_nhds_zero.mp htend) (ENNReal.ofReal (ε / 2))
        (ENNReal.ofReal_pos.mpr hhalf)
    have hy : ∀ᶠ y : K in 𝓝 y₀, dist (G (x₀, y)) (G (x₀, y₀)) < ε / 2 :=
      (Metric.continuousAt_iff'.mp hcont.continuousAt) (ε / 2) hhalf
    rw [nhds_prod_eq]
    refine (hx.prod_mk hy).mono ?_
    rintro ⟨x, y⟩ ⟨hx1, hy1⟩
    rw [Real.dist_eq] at hy1 ⊢
    have h1 : |G (x, y) - G (x₀, y)| ≤ ε / 2 := by
      have h2 : ENNReal.ofReal |G (x, y) - G (x₀, y)| ≤ ENNReal.ofReal (ε / 2) :=
        (le_iSup (fun y' : K => ENNReal.ofReal |G (x, y') - G (x₀, y')|) y).trans hx1
      exact (ENNReal.ofReal_le_ofReal_iff (le_of_lt hhalf)).mp h2
    calc |G (x, y) - G (x₀, y₀)|
        ≤ |G (x, y) - G (x₀, y)| + |G (x₀, y) - G (x₀, y₀)| := abs_sub_le _ _ _
      _ < ε := by linarith
