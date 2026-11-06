-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.completedIntegralIdeleSubgroup_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:43:49.84707+00:00
-- url     : https://prove2.me/submissions/9a3ae3f2-c195-4a6e-9020-acdb10836b74

import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.RestrictedProduct.Units
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_CompletedGlobalAdele
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_CompletedGlobalIdele

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open Filter
open scoped RestrictedProduct WithZero
noncomputable section
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution
    {S T : Finset (GlobalPlace k F)} (hST : S ⊆ T) :
    completedIntegralIdeleSubgroup (k := k) (F := F) S ≤
      completedIntegralIdeleSubgroup (k := k) (F := F) T := by
  intro x hx P hPT
  exact hx P fun hPS ↦ hPT (hST hPS)
end QEC.Coding.AlgebraicGeometry.GlobalPlace
