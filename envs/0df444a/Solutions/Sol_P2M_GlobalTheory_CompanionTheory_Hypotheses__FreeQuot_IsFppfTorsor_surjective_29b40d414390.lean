-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_Hypotheses__FreeQuot_IsFppfTorsor_surjective_29b40d414390
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:44:09.94084+00:00
-- url     : https://prove2.me/submissions/04f8c7f1-9781-45a0-b901-de82e0861ba7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomOfFlatQuotientOfAffineKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_RingHomFlatCodescendsAlongFaithfullyFlat
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hypotheses₂
open FreeQuot
open GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot
universe u
variable {S : Scheme.{u}} {G X Y : Over S} [GrpObj G] [ModObj G X] {q : X ⟶ Y}
namespace GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot
namespace IsFppfTorsor
theorem _root_.solution (h : IsFppfTorsor G q) : Surjective q.left := by
  obtain ⟨-, J, U, f, -, hs, hl⟩ := h
  refine ⟨fun y => ?_⟩
  obtain ⟨i, z, rfl⟩ := hs y
  obtain ⟨s, e⟩ := hl i
  exact ⟨s z, by rw [← Scheme.Hom.comp_apply, e]⟩
end IsFppfTorsor
end GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot
