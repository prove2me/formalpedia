-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.torsor_pullback
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:43:18.837879+00:00
-- url     : https://prove2.me/submissions/015d93bf-10bd-42af-aa01-b31c37484f5a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_OneCHyp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
namespace ReciprocityTheory.ChartRestriction.G.H1
theorem _root_.solution {S : Scheme.{0}} {T G B : Over S} [GrpObj T] [GrpObj G] [GrpObj B] (i : T ⟶ G) (q : G ⟶ B)
    [IsMonHom q] (h : IsPullback i (toUnit _) q η[B]) : IsPullback ((fst T G ≫ i) * snd T G) (snd T G) q q := by
  have hi : i ≫ q = 1 := h.w
  have : Mono i := h.flip.mono_snd_of_mono
  refine IsPullback.of_isLimit' ⟨by rw [MonObj.mul_comp, Category.assoc, hi, MonObj.comp_one, _root_.one_mul]⟩
    (PullbackCone.IsLimit.mk _ (fun s => lift (h.lift (s.fst * s.snd⁻¹) (toUnit _) (by
      rw [MonObj.mul_comp, GrpObj.inv_comp, s.condition, mul_inv_cancel]; rfl)) s.snd) (fun s => ?_) (fun s => lift_snd _ _)
      (fun s m h₁ h₂ => ?_))
  · rw [MonObj.comp_mul, lift_fst_assoc, h.lift_fst, lift_snd, inv_mul_cancel_right]
  · apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst, ← cancel_mono i, h.lift_fst, ← h₁, ← h₂, MonObj.comp_mul, mul_inv_cancel_right, Category.assoc]
    · rw [lift_snd, h₂]
end ReciprocityTheory.ChartRestriction.G.H1
