-- Prove2me | solution 1 for P2M_FunctorialResolution_Blowup_comap_ker_subscheme__comp_0b937eab6fcc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:25.642774+00:00
-- url     : https://prove2.me/submissions/17f4df02-eb9f-40bc-832b-79dc9135187f

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
namespace FunctorialResolution.Blowup
noncomputable section
private theorem isClosedImmersion_lift_comp {X Y Z : Scheme.{u}} (f : X ⟶ Z) [IsClosedImmersion f] (g : Y ⟶ Z)
    (h : Scheme.Hom.ker f ≤ Scheme.Hom.ker g) : IsClosedImmersion.lift f g h ≫ f = g := by
  simp
private theorem ker_le_ker_pullbackFst {X Y W Z : Scheme.{u}} (f : X ⟶ Y) [Mono f] (g : Z ⟶ Y)
    (ι : W ⟶ X) (m : Z ⟶ W) (hfac : m ≫ ι ≫ f = g) :
    Scheme.Hom.ker ι ≤ Scheme.Hom.ker (pullback.fst f g) := by
  have hu : pullback.snd f g ≫ m ≫ ι = pullback.fst f g := by
    rw [← cancel_mono f]
    simp only [Category.assoc]
    rw [hfac, pullback.condition]
  rw [← hu]
  exact le_trans (Scheme.Hom.le_ker_comp m ι)
    (Scheme.Hom.le_ker_comp (pullback.snd f g) (m ≫ ι))
end
end FunctorialResolution.Blowup
end

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open FunctorialResolution FunctorialResolution.Blowup
noncomputable section
namespace FunctorialResolution.Blowup
theorem _root_.solution {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] (I : X.IdealSheafData) :
    ((I.subschemeι ≫ f).ker).comap f = I := by
  rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι]
  refine le_antisymm (Scheme.IdealSheafData.comap_map_le I f) ?_
  have hle : Scheme.Hom.ker (I.subschemeι ≫ f) ≤ Scheme.Hom.ker (I.map f).subschemeι :=
    le_of_eq (by
      rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.Hom.ker_comp,
        Scheme.IdealSheafData.ker_subschemeι])
  have hcomap : (I.map f).comap f =
      Scheme.Hom.ker (pullback.fst f (I.map f).subschemeι) := rfl
  rw [hcomap]
  refine le_trans (le_of_eq (Scheme.IdealSheafData.ker_subschemeι I).symm) ?_
  exact ker_le_ker_pullbackFst f (I.map f).subschemeι I.subschemeι
    (IsClosedImmersion.lift (I.subschemeι ≫ f) (I.map f).subschemeι hle)
    (isClosedImmersion_lift_comp (I.subschemeι ≫ f) (I.map f).subschemeι hle)
end FunctorialResolution.Blowup
