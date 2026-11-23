-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht.isUnit_single_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:53:30.812015+00:00
-- url     : https://prove2.me/submissions/5ee66edf-110a-453d-a793-d97e20fa1838

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_SplitTori_SplitTorusIsCommMonObjSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsaRos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj MonObj TensorProduct
open AddMonoidAlgebra
open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
namespace ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
theorem _root_.solution {R A : Type*} [CommRing R] [AddCommGroup A] (a : A) :
    IsUnit (single a (1 : R)) := by
  first
  | exact ⟨⟨single a 1, single (-a) 1, by simp [single_mul_single, AddMonoidAlgebra.one_def],
      by simp [single_mul_single, AddMonoidAlgebra.one_def]⟩, rfl⟩
  | exact isUnit_of_mul_eq_one _ (single (-a) 1)
      (by rw [single_mul_single, add_neg_cancel, mul_one, AddMonoidAlgebra.one_def])
end ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
