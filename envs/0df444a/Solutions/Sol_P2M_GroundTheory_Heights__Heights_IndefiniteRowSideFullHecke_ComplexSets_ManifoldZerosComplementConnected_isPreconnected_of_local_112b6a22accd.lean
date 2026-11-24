-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ManifoldZerosComplementConnected_isPreconnected_of_local_112b6a22accd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:11.660727+00:00
-- url     : https://prove2.me/submissions/8cab0b35-24f1-4f50-831a-721c446ac92f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StManifoldZerosComplementConnected
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PManifoldZerosComplementConnected

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter Set
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace ManifoldZerosComplementConnected
theorem _root_.solution {α : Type*} [TopologicalSpace α]
    {X S : Set α} (hX : IsPreconnected X) (hSX : S ⊆ X) (hdense : ∀ x ∈ X, x ∈ closure S)
    (hloc : ∀ x ∈ X, ∃ W, IsOpen W ∧ x ∈ W ∧ IsPreconnected (W ∩ S)) : IsPreconnected S := by
  intro u v hu hv hSuv ⟨a, haS, hau⟩ ⟨b, hbS, hbv⟩
  by_contra hne
  have hne' : ∀ y ∈ S, y ∈ u → y ∈ v → False := fun y hy hyu hyv => hne ⟨y, hy, hyu, hyv⟩
  let P : Set α := {x | ∃ W, IsOpen W ∧ x ∈ W ∧ W ∩ S ⊆ u}
  let Q : Set α := {x | ∃ W, IsOpen W ∧ x ∈ W ∧ W ∩ S ⊆ v}
  have hP : IsOpen P := isOpen_iff_forall_mem_open.mpr fun x ⟨W, hW, hxW, hWS⟩ =>
    ⟨W, fun y hy => ⟨W, hW, hy, hWS⟩, hW, hxW⟩
  have hQ : IsOpen Q := isOpen_iff_forall_mem_open.mpr fun x ⟨W, hW, hxW, hWS⟩ =>
    ⟨W, fun y hy => ⟨W, hW, hy, hWS⟩, hW, hxW⟩
  have hcov : X ⊆ P ∪ Q := by
    intro x hx
    obtain ⟨W, hW, hxW, hWc⟩ := hloc x hx
    by_cases h1 : (W ∩ S ∩ u).Nonempty
    · by_cases h2 : (W ∩ S ∩ v).Nonempty
      · obtain ⟨y, hyWS, hyu, hyv⟩ := hWc u v hu hv (fun y hy => hSuv hy.2) h1 h2
        exact (hne' y hyWS.2 hyu hyv).elim
      · refine Or.inl ⟨W, hW, hxW, fun y hy => ?_⟩
        rcases hSuv hy.2 with h | h
        · exact h
        · exact absurd ⟨y, hy, h⟩ h2
    · refine Or.inr ⟨W, hW, hxW, fun y hy => ?_⟩
      rcases hSuv hy.2 with h | h
      · exact absurd ⟨y, hy, h⟩ h1
      · exact h
  obtain ⟨x, hxX, ⟨W₁, hW₁, hxW₁, hW₁u⟩, ⟨W₂, hW₂, hxW₂, hW₂v⟩⟩ :=
    hX P Q hP hQ hcov ⟨a, hSX haS, u, hu, hau, inter_subset_left⟩
      ⟨b, hSX hbS, v, hv, hbv, inter_subset_left⟩
  obtain ⟨y, ⟨hy₁, hy₂⟩, hyS⟩ := mem_closure_iff.mp (hdense x hxX) _ (hW₁.inter hW₂) ⟨hxW₁, hxW₂⟩
  exact hne' y hyS (hW₁u ⟨hy₁, hyS⟩) (hW₂v ⟨hy₂, hyS⟩)
end ManifoldZerosComplementConnected
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
