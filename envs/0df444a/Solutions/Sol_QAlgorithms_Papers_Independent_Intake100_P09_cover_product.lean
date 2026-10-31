-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P09.cover_product
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-31T00:30:55.320876+00:00
-- url     : https://prove2.me/submissions/16b5247c-4c24-43f4-8ae0-010306e8acf9

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P09

set_option autoImplicit false
open QAlgorithms.Papers.Independent.Intake100.P09
open scoped Manifold ContDiff
universe u
noncomputable section

private def firstProjection (M N : SmoothManifold.{u}) :
    SmoothMap (smoothProduct M N) M := ⟨Prod.fst, contMDiff_fst⟩

private def secondProjection (M N : SmoothManifold.{u}) :
    SmoothMap (smoothProduct M N) N := ⟨Prod.snd, contMDiff_snd⟩

private def productRightPullback {Y M : SmoothManifold.{u}}
    (f : SmoothMap Y M) (Z : SmoothManifold.{u}) :
    SmoothPullback f (firstProjection M Z) where
  object := smoothProduct Y Z
  first := firstProjection Y Z
  second := smoothProductMap f (smoothIdentity Z)
  commutes := by
    apply ContMDiffMap.ext
    intro x
    rfl
  universal := by
    intro T a b hab
    let l : SmoothMap T (smoothProduct Y Z) :=
      a.prodMk ((secondProjection M Z).comp b)
    refine ⟨l, ⟨?_, ?_⟩, ?_⟩
    · apply ContMDiffMap.ext
      intro x
      rfl
    · apply ContMDiffMap.ext
      intro x
      apply Prod.ext
      · exact congrArg (fun m => m x) hab
      · rfl
    · intro l' hl'
      apply ContMDiffMap.ext
      intro x
      apply Prod.ext
      · exact congrArg (fun m => m x) hl'.1
      · exact congrArg (fun m => (m x).2) hl'.2

private def productLeftPullback {Y M : SmoothManifold.{u}}
    (f : SmoothMap Y M) (Z : SmoothManifold.{u}) :
    SmoothPullback f (secondProjection Z M) where
  object := smoothProduct Z Y
  first := secondProjection Z Y
  second := smoothProductMap (smoothIdentity Z) f
  commutes := by
    apply ContMDiffMap.ext
    intro x
    rfl
  universal := by
    intro T a b hab
    let l : SmoothMap T (smoothProduct Z Y) :=
      ((firstProjection Z M).comp b).prodMk a
    refine ⟨l, ⟨?_, ?_⟩, ?_⟩
    · apply ContMDiffMap.ext
      intro x
      rfl
    · apply ContMDiffMap.ext
      intro x
      apply Prod.ext
      · rfl
      · exact congrArg (fun m => m x) hab
    · intro l' hl'
      apply ContMDiffMap.ext
      intro x
      apply Prod.ext
      · exact congrArg (fun m => (m x).1) hl'.2
      · exact congrArg (fun m => m x) hl'.1

theorem solution (tau : CoverPretopology.{u})
    {Y M Yother Mother : SmoothManifold.{u}}
    (pi : SmoothMap Y M) (piOther : SmoothMap Yother Mother)
    (hpi : tau.covers pi) (hpiOther : tau.covers piOther) :
    tau.covers (smoothProductMap pi piOther) := by
  have hr := tau.pullback_mem pi (firstProjection M Yother)
    (productRightPullback pi Yother) hpi
  have hl := tau.pullback_mem piOther (secondProjection M Mother)
    (productLeftPullback piOther M) hpiOther
  have hc := tau.composition_mem _ _ hr hl
  have he : (smoothProductMap (smoothIdentity M) piOther).comp
      (smoothProductMap pi (smoothIdentity Yother)) = smoothProductMap pi piOther := by
    apply ContMDiffMap.ext
    intro x
    rfl
  change tau.covers ((smoothProductMap (smoothIdentity M) piOther).comp
    (smoothProductMap pi (smoothIdentity Yother))) at hc
  rwa [he] at hc

#print axioms solution
