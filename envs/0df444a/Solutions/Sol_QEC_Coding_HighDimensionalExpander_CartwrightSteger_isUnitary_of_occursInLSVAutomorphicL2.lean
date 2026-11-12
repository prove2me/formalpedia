-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.isUnitary_of_occursInLSVAutomorphicL2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T18:56:33.844638+00:00
-- url     : https://prove2.me/submissions/26d8d41e-c0ae-49bc-97b4-56567d40d0cf

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_PrefixHeckeCompatibility
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_QuotientL2
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_RamanujanCriterion
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_lsvRightRegularRepresentation_isUnitary


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open QEC.Coding.HighDimensionalExpander.SphericalHecke
universe u
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat)
    {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (sigma : Representation ℂ
      (HeckeGroup (BaseField P) r.matrixRank) V)
    (hoccurs : OccursInLSVAutomorphicL2 P r level sigma) :
    IsUnitary sigma := by
  rcases hoccurs with ⟨U, hUclosed, e, hintertwines⟩
  intro g v w
  have hv := hintertwines g v
  have hw := hintertwines g w
  calc
    inner ℂ (sigma g v) (sigma g w) =
        inner ℂ (e (sigma g v)) (e (sigma g w)) :=
      (e.inner_map_map (sigma g v) (sigma g w)).symm
    _ = inner ℂ
        (((e (sigma g v) : U.toSubmodule) :
          LSVAutomorphicL2 P r level))
        (((e (sigma g w) : U.toSubmodule) :
          LSVAutomorphicL2 P r level)) := rfl
    _ = inner ℂ
        (lsvRightRegularRepresentation P r level g
          (((e v : U.toSubmodule) :
            LSVAutomorphicL2 P r level)))
        (lsvRightRegularRepresentation P r level g
          (((e w : U.toSubmodule) :
            LSVAutomorphicL2 P r level))) := by
      rw [hv, hw]
    _ = inner ℂ
        (((e v : U.toSubmodule) : LSVAutomorphicL2 P r level))
        (((e w : U.toSubmodule) : LSVAutomorphicL2 P r level)) :=
      lsvRightRegularRepresentation_isUnitary P r level g _ _
    _ = inner ℂ (e v) (e w) := rfl
    _ = inner ℂ v w := e.inner_map_map v w
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
