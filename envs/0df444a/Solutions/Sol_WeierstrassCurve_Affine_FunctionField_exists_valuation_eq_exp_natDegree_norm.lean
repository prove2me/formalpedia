-- Prove2me | solution 1 for WeierstrassCurve.Affine.FunctionField.exists_valuation_eq_exp_natDegree_norm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/31b75c61-a07e-5933-8990-f5c3d40254e1

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.Valuation.ExtendToLocalization
import Mathlib.RingTheory.Norm.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_FunctionField_exists_valuation_eq_exp_natDegree_norm

open scoped Polynomial.Bivariate WithZero nonZeroDivisors
p2m_open "Polynomial Polynomial.Bivariate.Polynomial"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine mk Affine.FunctionField toAffine Affine.Point"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "CoordinateRing FunctionField Point CoordinateRing.basis"
p2m_open "WeierstrassCurve.Affine WeierstrassCurve"

variable {K : Type*} [Field K] (W : Affine K)

namespace CoordinateRing
p2m_export "WeierstrassCurve.Affine.CoordinateRing" "mk degree_norm_smul_basis exists_smul_basis_eq"
p2m_open "WeierstrassCurve.Affine.CoordinateRing"

lemma norm_ne_zero {f : W.CoordinateRing} (hf : f ≠ 0) : Algebra.norm K[X] f ≠ 0 :=
  (Algebra.norm_ne_zero_iff_of_basis (CoordinateRing.basis W)).mpr hf

open scoped Classical in

noncomputable def valuationInftyDef (f : W.CoordinateRing) : ℤᵐ⁰ :=
  if f = 0 then 0 else WithZero.exp ((Algebra.norm K[X] f).natDegree : ℤ)

lemma degree_norm_add_le (f g : W.CoordinateRing) :
    (Algebra.norm K[X] (f + g)).degree ≤
      max (Algebra.norm K[X] f).degree (Algebra.norm K[X] g).degree := by
  obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq f
  obtain ⟨p', q', rfl⟩ := exists_smul_basis_eq g
  have : p • (1 : W.CoordinateRing) + q • mk W Y + (p' • 1 + q' • mk W Y) =
      (p + p') • 1 + (q + q') • mk W Y := by
    rw [add_smul, add_smul]; abel
  rw [this, degree_norm_smul_basis, degree_norm_smul_basis, degree_norm_smul_basis]
  refine max_le ?_ ?_
  · rcases le_max_iff.mp (degree_add_le p p') with h | h
    · exact le_max_of_le_left (le_max_of_le_left (nsmul_le_nsmul_right h 2))
    · exact le_max_of_le_right (le_max_of_le_left (nsmul_le_nsmul_right h 2))
  · rcases le_max_iff.mp (degree_add_le q q') with h | h
    · exact le_max_of_le_left (le_max_of_le_right
        (add_le_add_left (nsmul_le_nsmul_right h 2) 3))
    · exact le_max_of_le_right (le_max_of_le_right
        (add_le_add_left (nsmul_le_nsmul_right h 2) 3))

noncomputable def valuationInftyInt : Valuation W.CoordinateRing ℤᵐ⁰ where
  toFun := valuationInftyDef W
  map_zero' := if_pos rfl
  map_one' := by
    simp [valuationInftyDef]
  map_mul' f g := by
    classical
    by_cases hf : f = 0
    · simp [valuationInftyDef, hf]
    by_cases hg : g = 0
    · simp [valuationInftyDef, hg]
    simp only [valuationInftyDef, if_neg hf, if_neg hg, if_neg (mul_ne_zero hf hg), map_mul,
      natDegree_mul (norm_ne_zero W hf) (norm_ne_zero W hg), Nat.cast_add, WithZero.exp_add]
  map_add_le_max' f g := by
    classical
    by_cases hfg : f + g = 0
    · simp [valuationInftyDef, hfg]
    by_cases hf : f = 0
    · simp [valuationInftyDef, hf]
    by_cases hg : g = 0
    · simp [valuationInftyDef, hg]
    simp only [valuationInftyDef, if_neg hf, if_neg hg, if_neg hfg, le_max_iff,
      WithZero.exp_le_exp, Nat.cast_le]
    have h := degree_norm_add_le W f g
    rw [degree_eq_natDegree (norm_ne_zero W hfg), degree_eq_natDegree (norm_ne_zero W hf),
      degree_eq_natDegree (norm_ne_zero W hg)] at h
    rcases le_max_iff.mp h with h | h
    · exact Or.inl (by exact_mod_cast h)
    · exact Or.inr (by exact_mod_cast h)

lemma valuationInftyInt_apply (f : W.CoordinateRing) :
    valuationInftyInt W f = valuationInftyDef W f := rfl

lemma nonZeroDivisors_le_supp_primeCompl :
    W.CoordinateRing⁰ ≤ (valuationInftyInt W).supp.primeCompl := fun _ hs => by
  simp [valuationInftyInt_apply, valuationInftyDef, nonZeroDivisors.ne_zero hs]

end CoordinateRing

noncomputable def valuationInfty : Valuation W.FunctionField ℤᵐ⁰ :=
  (CoordinateRing.valuationInftyInt W).extendToLocalization
    (CoordinateRing.nonZeroDivisors_le_supp_primeCompl W) W.FunctionField

lemma valuationInfty_algebraMap (f : W.CoordinateRing) :
    valuationInfty W (algebraMap W.CoordinateRing W.FunctionField f) =
      CoordinateRing.valuationInftyDef W f :=
  Valuation.extendToLocalization_apply_map_apply ..

lemma valuationInfty_algebraMap_of_ne_zero {f : W.CoordinateRing} (hf : f ≠ 0) :
    valuationInfty W (algebraMap W.CoordinateRing W.FunctionField f) =
      WithZero.exp ((Algebra.norm K[X] f).natDegree : ℤ) := by
  rw [valuationInfty_algebraMap, CoordinateRing.valuationInftyDef, if_neg hf]

end WeierstrassCurve.Affine

theorem solution {K : Type*} [Field K] (W : WeierstrassCurve K) : ∃ v : Valuation W.toAffine.FunctionField (WithZero (Multiplicative ℤ)), ∀ f : W.toAffine.CoordinateRing, f ≠ 0 → v (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField f) = WithZero.exp ((Algebra.norm (Polynomial K) f).natDegree : ℤ) :=
  ⟨WeierstrassCurve.Affine.valuationInfty W.toAffine, fun _ hf =>
    WeierstrassCurve.Affine.valuationInfty_algebraMap_of_ne_zero W.toAffine hf⟩

end S_WeierstrassCurve_Affine_FunctionField_exists_valuation_eq_exp_natDegree_norm
end P2MW
export P2MW.S_WeierstrassCurve_Affine_FunctionField_exists_valuation_eq_exp_natDegree_norm (solution)
