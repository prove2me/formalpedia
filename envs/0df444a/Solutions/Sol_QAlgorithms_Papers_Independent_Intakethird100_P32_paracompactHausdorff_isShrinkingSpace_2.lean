-- Prove2me | solution 2 for QAlgorithms.Papers.Independent.Intakethird100.P32.paracompactHausdorff_isShrinkingSpace
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:38:52.779006+00:00
-- url     : https://prove2.me/submissions/060942f2-153a-4d3d-add4-6f94c68c2737

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P32

universe u

open Set Topology

open QAlgorithms.Papers.Independent.Intakethird100.P32 in
theorem solution (X : Type u) [TopologicalSpace X]
    [T2Space X] [ParacompactSpace X] : ShrinkingSpace X := by
  intro A U hU
  obtain ⟨W, Wo, WU, Wlf, WsubU⟩ :=
    precise_refinement U hU.1 (Set.iUnion_eq_univ_iff.2 hU.2)
  obtain ⟨V, VU, Vo, Vc⟩ :=
    exists_iUnion_eq_closure_subset Wo (fun x => Wlf.point_finite x) WU
  exact ⟨V, ⟨Vo, Set.iUnion_eq_univ_iff.1 VU⟩, fun a => (Vc a).trans (WsubU a)⟩
