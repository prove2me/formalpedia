-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.exists_dim
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:54:18.690858+00:00
-- url     : https://prove2.me/submissions/34a2af29-757b-4fa5-aa63-c5bfc1954405

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
theorem _root_.solution {X Y : Scheme.{0}} (f : X ⟶ Y) [Smooth f] (x : X) :
    ∃ (n : ℕ) (W : X.Opens), x ∈ W ∧ SmoothOfRelativeDimension n (W.ι ≫ f) := by
  obtain ⟨U, hU, V, hV, hx, e, h⟩ := Smooth.exists_isStandardSmooth f x
  have : Nonempty V := ⟨⟨x, hx⟩⟩
  let _ := (f.appLE U V e).hom.toAlgebra
  have : Algebra.IsStandardSmooth Γ(Y, U) Γ(X, V) := h
  obtain ⟨_, _, _, _, ⟨P⟩⟩ := this
  have h' : RingHom.IsStandardSmoothOfRelativeDimension P.dimension (f.appLE U V e).hom := ⟨_, _, _, ‹_›, P, rfl⟩
  have : IsAffine U := hU
  have : IsAffine V := hV
  have : SmoothOfRelativeDimension P.dimension (f.resLE U V e) :=
    (HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension P.dimension)).2
      (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
        ((RingHom.isStandardSmoothOfRelativeDimension_respectsIso.arrow_mk_iso_iff (arrowResLEAppIso f U V e)).2 h'))
  refine ⟨P.dimension + 0, V, hx, ?_⟩
  rw [← Scheme.Hom.resLE_comp_ι f e]; infer_instance
end ReciprocityTheory.ChartRestriction.G.H1
