-- Prove2me | solution 1 for WeilConjectures.Bridge.ell_divEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-10-20T14:40:03.640818+00:00
-- url     : https://prove2.me/submissions/08229638-8c35-4110-81c0-a0b02b69a020

import Mathlib
import Definitions.Def_WeilConjectures_RiemannRochFLT
import Theorems.Thm_AlgebraicCurve_eq_genusFF_of_forall_ell_sub_ell_eq
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_isSeparable
set_option linter.style.haveILetI false
section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
open scoped WithZero
open MonoidWithZeroHom
noncomputable section
namespace WeilConjectures.Bridge
section Valuations
variable {k K : Type*} [Field k] [Field K] [Algebra k K]
theorem rrPlace_valuation_eq (w : FunctionField.Place k K) (q : Valuation K ℤᵐ⁰)
    [q.IsRankOneDiscrete] (hV : q.valuationSubring = w.toValuationSubring)
    (hsurj : Function.Surjective q) : w.valuation = q := by
  obtain ⟨V, hne, htriv, hdisc⟩ := w
  dsimp only at hV
  subst hV
  let h := Valuation.isEquiv_valuation_valuationSubring q
  let e : ValueGroup₀ (.ofClass q.valuationSubring.valuation) ≃*o ℤᵐ⁰ :=
    h.orderMonoidIso.symm.trans (Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt q)
  have hnorm : (⟨q.valuationSubring, hne, htriv, hdisc⟩ :
      FunctionField.Place k K).normalization = e :=
    FunctionField.orderMonoidIso_withZeroMulInt_unique _ _
  ext x
  change (FunctionField.Place.normalization ⟨q.valuationSubring, hne, htriv, hdisc⟩)
      (q.valuationSubring.valuation.restrict x) = q x
  rw [hnorm]
  change (Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt q)
      (h.orderMonoidIso.symm (q.valuationSubring.valuation.restrict x)) = q x
  rw [show h.orderMonoidIso.symm (q.valuationSubring.valuation.restrict x) = q.restrict x from
    h.orderMonoidIso.symm_apply_eq.mpr (h.orderMonoidIso_spec x).symm]
  exact Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective
    hsurj x
namespace FLTPlace
variable (v : AlgebraicCurve.Place k K)
theorem adicValuation_surjective : Function.Surjective v.adicValuation :=
  v.heightOneSpectrum.valuation_surjective K
end FLTPlace
end Valuations
section Places
variable (k K : Type*) [Field k] [Field K] [Algebra k K]
variable {k K}
theorem placeEquiv_adicValuation (w : FunctionField.Place k K) :
    (placeEquiv k K w).adicValuation = w.valuation :=
  (rrPlace_valuation_eq w _ (FLTPlace.adicValuation_valuationSubring (placeEquiv k K w))
    (FLTPlace.adicValuation_surjective _)).symm
end Places
section Divisors
variable (k K : Type*) [Field k] [Field K] [Algebra k K]
variable {k K}
@[simp]
theorem divEquiv_apply_placeEquiv (D : FunctionField.Divisor k K) (w : FunctionField.Place k K) :
    divEquiv k K D (placeEquiv k K w) = D w := by
  simp [divEquiv, Finsupp.domCongr_apply]
theorem lSpace_divEquiv (D : FunctionField.Divisor k K) :
    AlgebraicCurve.LSpace (divEquiv k K D) = FunctionField.RRspace k K D := by
  ext f
  rw [AlgebraicCurve.mem_lSpace_iff]
  change _ ↔ ∀ w : FunctionField.Place k K, w.valuation f ≤ WithZero.exp (D w)
  rw [← (placeEquiv k K).forall_congr_right]
  simp only [placeEquiv_adicValuation, divEquiv_apply_placeEquiv]
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
    AlgebraicCurve.ell (divEquiv k K D) = FunctionField.ell k K D := by
  rw [AlgebraicCurve.ell, lSpace_divEquiv]
  rfl
end WeilConjectures.Bridge
