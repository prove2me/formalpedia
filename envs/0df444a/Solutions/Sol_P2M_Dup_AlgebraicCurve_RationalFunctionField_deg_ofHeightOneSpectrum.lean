-- Prove2me | solution 1 for P2M.Dup.AlgebraicCurve.RationalFunctionField.deg_ofHeightOneSpectrum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/25afb3a3-646e-530e-9ea5-650c775aa3e1

import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.AdjoinRoot
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_adicValuation_le_one
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_maximalIdeal_iff_adicValuation_lt_one
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_isEquiv_adicValuation_ofHeightOneSpectrum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RationalFunctionField_deg_ofHeightOneSpectrum
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_deg_ofHeightOneSpectrum.AlgebraicCurve"
open IsDedekindDomain WithZero IsLocalRing
open scoped Polynomial

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.deg Place.ofHeightOneSpectrum Place.mem_iff_adicValuation_le_one Place.mem_maximalIdeal_iff_adicValuation_lt_one Place.isEquiv_adicValuation_ofHeightOneSpectrum"
namespace RationalFunctionField
p2m_open "AlgebraicCurve"

namespace WFf
variable (K : Type*) [Field K]

theorem algebraMap_mem_ofHeightOneSpectrum (w : HeightOneSpectrum K[X]) (q : K[X]) :
    algebraMap K[X] (RatFunc K) q ∈
      (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).toValuationSubring :=
  (Place.mem_iff_adicValuation_le_one _).mpr
    ((Place.isEquiv_adicValuation_ofHeightOneSpectrum (K := K)
      (F := RatFunc K) w).le_one_iff_le_one.mp (w.valuation_le_one q))

def residueOfHeightOneSpectrum (w : HeightOneSpectrum K[X]) :
    K[X] →+* (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ResidueField :=
  (IsLocalRing.residue _).comp
    ((algebraMap K[X] (RatFunc K)).codRestrict
      (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).toValuationSubring.toSubring
      (algebraMap_mem_ofHeightOneSpectrum K w))

theorem residueOfHeightOneSpectrum_apply (w : HeightOneSpectrum K[X]) (q : K[X]) :
    residueOfHeightOneSpectrum K w q = IsLocalRing.residue _
      ⟨algebraMap K[X] (RatFunc K) q, algebraMap_mem_ofHeightOneSpectrum K w q⟩ := rfl

theorem ker_residueOfHeightOneSpectrum (w : HeightOneSpectrum K[X]) :
    RingHom.ker (residueOfHeightOneSpectrum K w) = w.asIdeal := by
  ext q
  rw [RingHom.mem_ker, residueOfHeightOneSpectrum_apply, IsLocalRing.residue_eq_zero_iff,
    Place.mem_maximalIdeal_iff_adicValuation_lt_one,
    ← (Place.isEquiv_adicValuation_ofHeightOneSpectrum (K := K)
      (F := RatFunc K) w).lt_one_iff_lt_one]
  exact HeightOneSpectrum.valuation_lt_one_iff_mem w q

theorem surjective_residueOfHeightOneSpectrum (w : HeightOneSpectrum K[X]) :
    Function.Surjective (residueOfHeightOneSpectrum K w) := by
  intro y
  obtain ⟨⟨x, hx⟩, rfl⟩ := IsLocalRing.residue_surjective y
  have hxval : w.valuation (RatFunc K) x ≤ 1 :=
    (Place.isEquiv_adicValuation_ofHeightOneSpectrum (K := K)
      (F := RatFunc K) w).le_one_iff_le_one.mpr ((Place.mem_iff_adicValuation_le_one _).mp hx)
  have hden_ne : algebraMap K[X] (RatFunc K) x.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr x.denom_ne_zero
  have hmul : x * algebraMap K[X] (RatFunc K) x.denom = algebraMap K[X] (RatFunc K) x.num :=
    ((div_eq_iff hden_ne).mp x.num_div_denom).symm
  have hden : x.denom ∉ w.asIdeal := by
    intro hd
    have hnum : x.num ∉ w.asIdeal := by
      intro hn
      refine w.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr ?_)
      obtain ⟨a, b, hab⟩ := RatFunc.isCoprime_num_denom x
      exact hab ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ hn) (Ideal.mul_mem_left _ _ hd)
    have h1 : w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) x.num) = 1 :=
      (HeightOneSpectrum.valuation_eq_one_iff_notMem w).mpr hnum
    refine absurd h1 (ne_of_lt ?_)
    calc w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) x.num)
        = w.valuation (RatFunc K) x
            * w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) x.denom) := by
          rw [← map_mul, hmul]
      _ ≤ w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) x.denom) :=
          mul_le_of_le_one_left' hxval
      _ < 1 := (HeightOneSpectrum.valuation_lt_one_iff_mem w x.denom).mpr hd
  have hmax : w.asIdeal.IsMaximal := IsPrime.to_maximal_ideal w.ne_bot
  obtain ⟨t, ht⟩ : ∃ t : K[X], x.denom * t - 1 ∈ w.asIdeal := by
    obtain ⟨b, c, hc, hbc⟩ := hmax.exists_inv hden
    refine ⟨b, ?_⟩
    rw [show x.denom * b - 1 = -c by linear_combination hbc]
    exact neg_mem hc
  refine ⟨x.num * t, ?_⟩
  rw [residueOfHeightOneSpectrum_apply, ← sub_eq_zero, ← map_sub,
    IsLocalRing.residue_eq_zero_iff, Place.mem_maximalIdeal_iff_adicValuation_lt_one]
  show (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).adicValuation
    (algebraMap K[X] (RatFunc K) (x.num * t) - x) < 1
  rw [← (Place.isEquiv_adicValuation_ofHeightOneSpectrum (K := K)
      (F := RatFunc K) w).lt_one_iff_lt_one]
  have key : algebraMap K[X] (RatFunc K) (x.num * t) - x
      = x * algebraMap K[X] (RatFunc K) (x.denom * t - 1) := by
    rw [map_sub, map_mul, map_mul, map_one, mul_sub, mul_one, ← mul_assoc, hmul]
  rw [key, map_mul]
  calc w.valuation (RatFunc K) x
        * w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) (x.denom * t - 1))
      ≤ w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) (x.denom * t - 1)) :=
        mul_le_of_le_one_left' hxval
    _ < 1 := (HeightOneSpectrum.valuation_lt_one_iff_mem w _).mpr ht

def residueFieldEquivOfHeightOneSpectrum (w : HeightOneSpectrum K[X]) :
    (K[X] ⧸ w.asIdeal) ≃ₐ[K]
      (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ResidueField := by
  refine AlgEquiv.ofRingEquiv (f := (Ideal.quotEquivOfEq
    (ker_residueOfHeightOneSpectrum K w).symm).trans
    (RingHom.quotientKerEquivOfSurjective (surjective_residueOfHeightOneSpectrum K w))) ?_
  intro a
  rw [show (algebraMap K (K[X] ⧸ w.asIdeal)) a
      = Ideal.Quotient.mk w.asIdeal (algebraMap K K[X] a) from rfl]
  rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk, residueOfHeightOneSpectrum_apply]
  exact congrArg (IsLocalRing.residue _)
    (Subtype.ext (IsScalarTower.algebraMap_apply K K[X] (RatFunc K) a).symm)

end WFf

end AlgebraicCurve.RationalFunctionField

end

theorem solution (K : Type*) [Field K] {w : IsDedekindDomain.HeightOneSpectrum (Polynomial K)} {p : Polynomial K} (hw : w.asIdeal = Ideal.span {p}) : (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).deg = p.natDegree := by
  rw [Place.deg, ← (AlgebraicCurve.RationalFunctionField.WFf.residueFieldEquivOfHeightOneSpectrum K
    w).toLinearEquiv.finrank_eq, hw]
  exact finrank_quotient_span_eq_natDegree

end S_AlgebraicCurve_RationalFunctionField_deg_ofHeightOneSpectrum
end P2MW
export P2MW.S_AlgebraicCurve_RationalFunctionField_deg_ofHeightOneSpectrum (solution)
