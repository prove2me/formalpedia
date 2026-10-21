-- Prove2me | solution 1 for WeilConjectures.Bridge.genusFF_eq_genus
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-10-20T15:11:16.013261+00:00
-- url     : https://prove2.me/submissions/6424f616-0a53-4503-bd55-78ec9f8441c1

import Mathlib
import Definitions.Def_WeilConjectures_RiemannRochFLT
import Theorems.Thm_FunctionField_exists_isCanonical
import Theorems.Thm_FunctionField_riemann_roch
import Theorems.Thm_WeilConjectures_Bridge_degree_divEquiv
import Theorems.Thm_WeilConjectures_Bridge_ell_divEquiv
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
variable (k K : Type*) [Field k] [Field K] [Algebra k K]
namespace memRRspace
variable {k K} {D : Divisor k K}
end memRRspace
variable [Algebra k[X] K] [Algebra k⟮X⟯ K]
  [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K] [_root_.FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K] [IsFullConstantField k K]
omit [IsFullConstantField k K] in
theorem memRRspace_equivChart (D : Divisor k K) (f : K) :
    memRRspace k K D f ↔
      Chart.memRRspace k K ((divisorEquivChart k K).symm D) f := by
  constructor
  · intro hf w
    have hv := hf (chartToPlace k K w)
    rw [placeValuation_eq] at hv
    simpa [divisorEquivChart, Finsupp.domCongr_apply] using hv
  · intro hf v
    let w := (chartToPlace k K).symm v
    have hw := hf w
    rw [← placeValuation_eq] at hw
    simpa [w, divisorEquivChart, Finsupp.domCongr_apply] using hw
omit [IsFullConstantField k K] in
theorem RRspace_eq_chart (D : Divisor k K) :
    RRspace k K D = Chart.RRspace k K ((divisorEquivChart k K).symm D) := by
  ext f
  exact memRRspace_equivChart k K D f
omit [IsFullConstantField k K] in
theorem ell_eq_chart (D : Divisor k K) :
    ell k K D = Chart.ell k K ((divisorEquivChart k K).symm D) := by
  rw [ell, Chart.ell, RRspace_eq_chart k K D]
section Canonical
variable {W : Divisor k K} (hW : IsCanonical k K W)
include hW
end Canonical
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
theorem isCurveOver : AlgebraicCurve.IsCurveOver k K :=
  AlgebraicCurve.isCurveOver_of_transcendental_of_isSeparable k K (xK k K) (transcendental_xK k K)
    inferInstance inferInstance
theorem essFiniteType : Algebra.EssFiniteType k K := by
  have : Algebra.EssFiniteType k[X] k⟮X⟯ :=
    Algebra.EssFiniteType.of_isLocalization k⟮X⟯ (nonZeroDivisors k[X])
  have : Algebra.EssFiniteType k k⟮X⟯ := Algebra.EssFiniteType.comp k k[X] k⟮X⟯
  exact Algebra.EssFiniteType.comp k k⟮X⟯ K
end Hypotheses
section Genus
open scoped Polynomial RatFunc
variable (k K : Type*) [Field k] [Field K] [Algebra k K] [Algebra k[X] K] [Algebra k⟮X⟯ K]
  [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K] [FunctionField.IsFullConstantField k K]
theorem rr_ell_zero : FunctionField.ell k K 0 = 1 := by
  rw [FunctionField.ell_eq_chart, map_zero]
  exact FunctionField.Chart.ell_zero k K
theorem flt_ell_zero : AlgebraicCurve.ell (0 : AlgebraicCurve.Divisor k K) = 1 := by
  rw [← map_zero (divEquiv k K), ell_divEquiv, rr_ell_zero]
theorem constantsAreBase : AlgebraicCurve.ConstantsAreBase k K := by
  have h0 := flt_ell_zero k K
  have : FiniteDimensional k (AlgebraicCurve.LSpace (0 : AlgebraicCurve.Divisor k K)) :=
    Module.finite_of_finrank_pos (by change 0 < AlgebraicCurve.ell _; rw [h0]; exact Nat.one_pos)
  unfold AlgebraicCurve.ConstantsAreBase
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨c, rfl⟩
    exact AlgebraicCurve.algebraMap_mem_lSpace_zero c
  · rw [LinearMap.finrank_range_of_inj (f := Algebra.linearMap k K) (algebraMap k K).injective,
      Module.finrank_self]
    exact h0.symm
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
open scoped Polynomial RatFunc
variable (k K : Type*) [Field k] [Field K] [Algebra k K] [Algebra k[X] K] [Algebra k⟮X⟯ K]
  [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K] [FunctionField.IsFullConstantField k K]
namespace WeilConjectures.Bridge
theorem _root_.solution [PerfectField k] :
    AlgebraicCurve.genusFF k K = FunctionField.genus k K := by
  haveI := isCurveOver k K
  haveI := essFiniteType k K
  obtain ⟨W, hW⟩ := FunctionField.exists_isCanonical k K
  symm
  refine AlgebraicCurve.eq_genusFF_of_forall_ell_sub_ell_eq (constantsAreBase k K)
    (Kc := divEquiv k K W) fun D => ?_
  obtain ⟨D', rfl⟩ := (divEquiv k K).surjective D
  rw [← map_sub, ell_divEquiv, ell_divEquiv, degree_divEquiv,
    FunctionField.riemann_roch k K hW D']
  ring
end WeilConjectures.Bridge
