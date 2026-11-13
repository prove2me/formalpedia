-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P07.basedPaths_loopContractible
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T23:06:53.002199+00:00
-- url     : https://prove2.me/submissions/d6c8652b-8b1a-473e-a99b-cb590c514c32

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P07
import Mathlib.CategoryTheory.Adjunction.Limits
set_option autoImplicit false

open QAlgorithms.Papers.Independent.Intakethird100.P07
noncomputable section

universe u v



open CategoryTheory Topology TopologicalSpace

/-- Example 5.3, PDF p. 20: the displayed rescaling is jointly continuous,
has the required endpoints, and is a path-group endomorphism at each time. -/
theorem solution
    (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G] :
    Continuous (fun p : BasedPaths G × UnitTime => pathRescale p.1 p.2) ∧
    (∀ gamma : BasedPaths G, pathRescale gamma timeZero = basedPathOne) ∧
    (∀ gamma : BasedPaths G, pathRescale gamma timeOne = gamma) ∧
    (∀ (s : UnitTime) (gamma eta : BasedPaths G),
      pathRescale (basedPathMul gamma eta) s =
        basedPathMul (pathRescale gamma s) (pathRescale eta s)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hc : Continuous (fun p : BasedPaths G × UnitTime => (pathRescale p.1 p.2).val) := by
      apply ContinuousMap.continuous_of_continuous_uncurry
      change Continuous (fun p : (BasedPaths G × UnitTime) × UnitTime =>
        p.1.1.val (scaledTime p.1.2 p.2))
      have ht : Continuous (fun p : (BasedPaths G × UnitTime) × UnitTime => scaledTime p.1.2 p.2) := by
        apply Continuous.subtype_mk
        exact (continuous_subtype_val.comp (continuous_snd.comp continuous_fst)).mul
          (continuous_subtype_val.comp continuous_snd)
      exact continuous_eval.comp
        ((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).prodMk ht)
    exact hc.subtype_mk (fun p => (pathRescale p.1 p.2).property)
  · intro gamma
    apply Subtype.ext
    apply ContinuousMap.ext
    intro t
    change gamma.val (scaledTime timeZero t) = 1
    have ht : scaledTime timeZero t = timeZero := by apply Subtype.ext; simp [scaledTime,timeZero]
    rw [ht]
    exact gamma.property
  · intro gamma
    apply Subtype.ext
    apply ContinuousMap.ext
    intro t
    change gamma.val (scaledTime timeOne t) = gamma.val t
    congr 1
    apply Subtype.ext
    simp [scaledTime,timeOne]
  · intro s gamma eta
    apply Subtype.ext
    apply ContinuousMap.ext
    intro t
    rfl
