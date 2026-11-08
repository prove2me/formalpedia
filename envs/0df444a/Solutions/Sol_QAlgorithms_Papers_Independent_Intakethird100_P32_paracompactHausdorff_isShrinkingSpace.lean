-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P32.paracompactHausdorff_isShrinkingSpace
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:38:20.976015+00:00
-- url     : https://prove2.me/submissions/dfa3df64-5138-45cc-a060-9199c84ba784

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
