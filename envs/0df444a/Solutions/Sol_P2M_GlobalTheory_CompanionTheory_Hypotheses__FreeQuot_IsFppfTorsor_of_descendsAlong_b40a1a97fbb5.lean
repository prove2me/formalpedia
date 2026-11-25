-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_Hypotheses__FreeQuot_IsFppfTorsor_of_descendsAlong_b40a1a97fbb5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:59:41.408385+00:00
-- url     : https://prove2.me/submissions/fccf2e6a-a3d0-4bac-92ea-2ebc7c9da561

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
set_option backward.isDefEq.respectTransparency.types false
namespace GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot
namespace IsFppfTorsor
theorem _root_.solution (h : IsFppfTorsor G q) (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] [IsZariskiLocalAtTarget P]
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)] (hG : P G.hom) : P q.left := by
  obtain ⟨hp, J, U, f, hf, hs, hl⟩ := h
  choose s hl using hl
  have hp' : IsPullback (γ[G, X] : G ⊗ X ⟶ X).left (snd G X).left q.left q.left := hp.map (Over.forget S)
  have h1 : P (snd G X).left := MorphismProperty.pullback_snd (P := P) G.hom X.hom hG
  have e : Sigma.desc s ≫ q.left = Sigma.desc f := by
    ext i; simp [hl]
  have hq := (IsPullback.of_hasPullback (snd G X).left (Sigma.desc s)).flip.paste_vert hp'.flip
  rw [e] at hq
  have := fun i => (hf i).1
  have := fun i => (hf i).2
  refine MorphismProperty.of_isPullback_of_descendsAlong (P := P)
    (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) hq ⟨⟨⟨fun y => ?_⟩, ?_⟩, ?_⟩
    (MorphismProperty.pullback_snd _ _ h1)
  · obtain ⟨i, z, rfl⟩ := hs y
    exact ⟨Sigma.ι U i z, by rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]⟩
  · exact IsZariskiLocalAtSource.sigmaDesc fun i => inferInstance
  · exact IsZariskiLocalAtSource.sigmaDesc fun i => inferInstance
end IsFppfTorsor
end GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot
