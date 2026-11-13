-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P07.loopContractible_iff_pathExtensionSplits
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T23:09:46.258819+00:00
-- url     : https://prove2.me/submissions/0d533284-2050-4318-8e11-107338173f08

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P07
import Mathlib.CategoryTheory.Adjunction.Limits
set_option autoImplicit false

open QAlgorithms.Papers.Independent.Intakethird100.P07
noncomputable section

universe u v



open CategoryTheory Topology TopologicalSpace

/-- Remark 5.4, PDF p. 20: the based-path extension splits by a continuous
group-homomorphic section exactly when G is loop contractible. The section
homotopy is phi(g,t)=s(g)(t), and the section from phi is g↦(t↦phi(g,t)). -/
theorem solution
    (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G] :
    LoopContractible G ↔
      ∃ s : C(G, BasedPaths G),
        (∀ g, basedPathEndpoint (s g) = g) ∧
        (∀ g h, s (g * h) = basedPathMul (s g) (s h)) := by
  constructor
  · rintro ⟨phi,hc,h0,h1,hm⟩
    let c : C(G,C(UnitTime,G)) := ContinuousMap.curry ⟨phi,hc⟩
    let s : C(G,BasedPaths G) := ⟨fun g => ⟨c g,h0 g⟩, c.continuous.subtype_mk (fun g => h0 g)⟩
    refine ⟨s,?_,?_⟩
    · intro g
      exact h1 g
    · intro g h
      apply Subtype.ext
      apply ContinuousMap.ext
      intro t
      exact hm t g h
  · rintro ⟨s,he,hm⟩
    let phi : G × UnitTime → G := fun p => (s p.1).val p.2
    refine ⟨phi,?_,?_,?_,?_⟩
    · exact continuous_eval.comp ((continuous_subtype_val.comp (s.continuous.comp continuous_fst)).prodMk continuous_snd)
    · intro g
      exact (s g).property
    · intro g
      exact he g
    · intro t g h
      exact congrArg (fun gamma : BasedPaths G => gamma.val t) (hm g h)
