-- Prove2me | solution 1 for PermanentRollout.permanent_rollout_exists_avoiding_finite_smooth_chart_images
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:02.589874+00:00
-- url     : https://prove2.me/submissions/95c3463d-3a2a-41a6-aa34-6b49f18418fb

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open Set Filter Module
open scoped BigOperators ENNReal
noncomputable section
namespace PermanentRollout
theorem _root_.solution
    {ι E F : Type*} [Finite ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    (f : ι → E → F) (s : ι → Set E)
    (hsmooth : ∀ i x, x ∈ s i → ContDiffAt ℝ 1 (f i) x)
    (hdim : finrank ℝ E < finrank ℝ F) :
    ∃ y : F, ∀ i : ι, y ∉ f i '' s i := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  have hchart (i : ι) :
      dimH (f i '' s i) ≤
        (finrank ℝ E : ENNReal) := by
    calc
      dimH (f i '' s i) ≤ dimH (s i) := by
        apply dimH_image_le_of_locally_lipschitzOn
        intro x hx
        obtain ⟨C, t, ht, hlip⟩ := (hsmooth i x hx).exists_lipschitzOnWith
        exact ⟨C, t, mem_nhdsWithin_of_mem_nhds ht, hlip⟩
      _ ≤ dimH (Set.univ : Set E) :=
        dimH_mono (Set.subset_univ _)
      _ = (finrank ℝ E : ENNReal) :=
        Real.dimH_univ_eq_finrank E
  have hunion :
      dimH (⋃ i, f i '' s i) ≤
        (finrank ℝ E : ENNReal) := by
    rw [dimH_iUnion]
    exact iSup_le hchart
  have hstrict :
      dimH (⋃ i, f i '' s i) <
        (finrank ℝ F : ENNReal) :=
    hunion.trans_lt (by exact_mod_cast hdim)
  have hdense : Dense (⋃ i, f i '' s i)ᶜ :=
    dense_compl_of_dimH_lt_finrank hstrict
  obtain ⟨y, hy⟩ := hdense.nonempty
  refine ⟨y, ?_⟩
  intro i hi
  exact hy (Set.mem_iUnion.mpr ⟨i, hi⟩)
end PermanentRollout
