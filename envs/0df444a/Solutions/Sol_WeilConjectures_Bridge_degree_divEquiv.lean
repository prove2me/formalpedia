-- Prove2me | solution 1 for WeilConjectures.Bridge.degree_divEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-10-20T14:38:22.994925+00:00
-- url     : https://prove2.me/submissions/e80f2af3-027a-4962-9f34-b4cb36a7b93c

import Mathlib
import Definitions.Def_WeilConjectures_RiemannRochFLT
import Theorems.Thm_AlgebraicCurve_eq_genusFF_of_forall_ell_sub_ell_eq
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_isSeparable
/-
Contains code from riemann-roch-function-fields
(https://github.com/vaca22/riemann-roch-function-fields, commit dbca5bee),
Copyright (c) 2026 Guanghao Li, released under the Apache License 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
Modified: ported to Lean v4.33.1 / Mathlib 0df444a (module headers converted, some proofs
adapted to this Mathlib, a few names qualified, `picTorsor` omitted; statements unchanged), then
split into prove2.me definitions and theorems, with comments removed.
-/
set_option linter.style.haveILetI false
section
section
open scoped nonZeroDivisors Polynomial RatFunc WithZero
noncomputable section
namespace FunctionField
open Chart
variable (k K : Type*) [Field k] [Field K]
  [Algebra k K] [Algebra k[X] K] [Algebra k⟮X⟯ K]
  [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K]
attribute [local instance] FunctionField.instDecidableEqRatFuncCoordinateFreeDivisor
namespace Place
attribute [local instance] FunctionField.Place.finiteVspTower
attribute [local instance] FunctionField.Place.infiniteVspTower
end Place
namespace Divisor
omit [Algebra k[X] K] [Algebra k⟮X⟯ K] [IsScalarTower k k[X] K]
    [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K]
    [Algebra.IsSeparable k⟮X⟯ K] in
theorem deg_formula (D : Divisor k K) :
    deg k K D = D.sum fun v n => n * (v.degree : ℤ) := rfl
end Divisor
end FunctionField
end
end
end
section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
open scoped WithZero
open MonoidWithZeroHom
noncomputable section
namespace WeilConjectures.Bridge
section Valuations
variable {k K : Type*} [Field k] [Field K] [Algebra k K]
namespace FLTPlace
variable (v : AlgebraicCurve.Place k K)
end FLTPlace
end Valuations
section Places
variable (k K : Type*) [Field k] [Field K] [Algebra k K]
variable {k K}
theorem placeEquiv_deg (w : FunctionField.Place k K) :
    (placeEquiv k K w).deg = w.degree := rfl
end Places
section Divisors
variable (k K : Type*) [Field k] [Field K] [Algebra k K]
variable {k K}
end Divisors
section Hypotheses
open scoped Polynomial RatFunc IntermediateField
variable (k K : Type*) [Field k] [Field K] [Algebra k K] [Algebra k[X] K] [Algebra k⟮X⟯ K]
  [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K]
attribute [local instance] WeilConjectures.Bridge.instIsScalarTowerRatFunc
end Hypotheses
section Genus
open scoped Polynomial RatFunc
variable (k K : Type*) [Field k] [Field K] [Algebra k K] [Algebra k[X] K] [Algebra k⟮X⟯ K]
  [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K] [FunctionField.IsFullConstantField k K]
end Genus
section Weierstrass
open scoped Polynomial RatFunc
variable {k : Type*} [Field k] [PerfectField k] (W : WeierstrassCurve.Affine k) [W.IsElliptic]
  (K : Type*) [Field K] [Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]
  [Algebra k[X] K] [IsScalarTower k[X] W.CoordinateRing K]
  [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
  [FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]
  [Algebra k K] [IsScalarTower k k[X] K] [FunctionField.IsFullConstantField k K]
end Weierstrass
end WeilConjectures.Bridge
end
end
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
open scoped WithZero
open MonoidWithZeroHom
open WeilConjectures.Bridge
variable (k K : Type*) [Field k] [Field K] [Algebra k K]
variable {k K}
namespace WeilConjectures.Bridge
theorem _root_.solution (D : FunctionField.Divisor k K) :
    AlgebraicCurve.Divisor.degree (divEquiv k K D) = FunctionField.Divisor.deg k K D := by
  classical
  rw [FunctionField.Divisor.deg_formula, AlgebraicCurve.Divisor.degree, Finsupp.liftAddHom_apply,
    divEquiv, Finsupp.domCongr_apply, Finsupp.equivMapDomain_eq_mapDomain,
    Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by simp [add_mul])]
  simp [placeEquiv_deg]
end WeilConjectures.Bridge
