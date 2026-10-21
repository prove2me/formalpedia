-- Prove2me | solution 1 for WeilConjectures.Bridge.genusFF_eq_one_of_isElliptic
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-10-20T15:16:36.07836+00:00
-- url     : https://prove2.me/submissions/4c7b3189-ba84-4708-989f-b81191c2beb1

import Mathlib
import Definitions.Def_WeilConjectures_RiemannRochFLT
import Theorems.Thm_WeierstrassCurve_Affine_genus_eq_one
import Theorems.Thm_WeilConjectures_Bridge_genusFF_eq_genus
import Theorems.Thm_AlgebraicCurve_eq_genusFF_of_forall_ell_sub_ell_eq
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_isSeparable
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
open scoped WithZero
open MonoidWithZeroHom
open WeilConjectures.Bridge
open scoped Polynomial RatFunc
variable {k : Type*} [Field k] [PerfectField k] (W : WeierstrassCurve.Affine k) [W.IsElliptic]
  (K : Type*) [Field K] [Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]
  [Algebra k[X] K] [IsScalarTower k[X] W.CoordinateRing K]
  [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
  [FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]
  [Algebra k K] [IsScalarTower k k[X] K] [FunctionField.IsFullConstantField k K]
include W
namespace WeilConjectures.Bridge
theorem _root_.solution : AlgebraicCurve.genusFF k K = 1 := by
  rw [genusFF_eq_genus k K]
  exact WeierstrassCurve.Affine.genus_eq_one W K
end WeilConjectures.Bridge
