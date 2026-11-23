-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.dim_base
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:00.431825+00:00
-- url     : https://prove2.me/submissions/52ae0544-ba29-48ac-a372-c515f9be7f2a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_OneCHyp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_dim_unique

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
theorem _root_.solution {X S X' S' : Scheme.{0}} {f : X ⟶ S} {f' : X' ⟶ S'} {a : X' ⟶ X} {b : S' ⟶ S} (h : IsPullback a f' f b)
    {n m : ℕ} {W : X.Opens} (hW : SmoothOfRelativeDimension n (W.ι ≫ f)) (hm : SmoothOfRelativeDimension m f') (x : X')
    (hx : a x ∈ W) : n = m := by
  have h₁ : SmoothOfRelativeDimension n ((a ⁻¹ᵁ W).ι ≫ f') := (smoothOfRelativeDimension_isStableUnderBaseChange n).of_isPullback
    ((isPullback_morphismRestrict a W).paste_vert h) hW
  have h₂ : SmoothOfRelativeDimension (0 + m) ((a ⁻¹ᵁ W).ι ≫ f') := inferInstance
  exact (dim_unique _ h₁ h₂ ⟨x, hx⟩).trans (zero_add m)
end ReciprocityTheory.ChartRestriction.G.H1
