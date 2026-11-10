-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P87.zeroDescent_bijection
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T01:58:45.451198+00:00
-- url     : https://prove2.me/submissions/fe96b8c2-aed4-481f-8da4-fd6615a12652

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P87

noncomputable section

open scoped ContDiff Manifold

universe u v

open QAlgorithms.Papers.Independent.Intake100.P87 in
theorem solution {Y M G : SmoothManifold.{u}} {T : Type v}
    (pi : SmoothSurjectiveSubmersion Y M) (i : G.carrier → T)
    (hi : Function.Injective i) :
    Function.Bijective (zeroExtract pi i) ∧
    ∀ data : ZeroDescent pi i, ∃! f : M.carrier → G.carrier,
      ∀ y, f (pi.toFun y) = data.val y := by
  have hs := pi.surjective
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro d1 d2 h
    have h2 : d1.val.2 = d2.val.2 := congrArg Subtype.val h
    apply Subtype.ext
    apply Prod.ext
    · funext m
      obtain ⟨y, rfl⟩ := hs m
      rw [d1.property y, d2.property y, h2]
    · exact h2
  · intro d
    refine ⟨⟨(fun m => i (d.val (Classical.choose (hs m))), d.val), ?_⟩, rfl⟩
    intro y
    exact d.property _ _ (Classical.choose_spec (hs (pi.toFun y)))
  · intro d
    refine ⟨fun m => d.val (Classical.choose (hs m)), ?_, ?_⟩
    · intro y
      exact hi (d.property _ _ (Classical.choose_spec (hs (pi.toFun y))))
    · intro g hg
      funext m
      obtain ⟨y, rfl⟩ := hs m
      rw [hg y]
      exact (hi (d.property _ _ (Classical.choose_spec (hs (pi.toFun y))))).symm
