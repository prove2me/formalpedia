-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.exists_ratFunc_eq_sum_simpleFractions_of_squarefree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:46:30.851635+00:00
-- url     : https://prove2.me/submissions/1aaf8162-06d3-45ce-b4e2-7879860fe07e

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Polynomial.PartialFractions
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_SimplePoleDenominator
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_SquarefreePartialFraction
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_rationalAdicPolynomialToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_none
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_some
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply



set_option autoImplicit false
open scoped BigOperators Polynomial RatFunc
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.Differential
open UniqueFactorizationMonoid
variable {k : Type*} [Field k]
namespace QEC.Coding.AlgebraicGeometry.Differential
theorem _root_.solution
    (f : RatFunc k)
    (hdegree : f.num.degree < f.denom.degree)
    (hsquarefree : Squarefree f.denom) :
    ∃ (s : Finset k[X]) (r : k[X] → k[X]),
      (∀ q ∈ s, q.Monic ∧ Irreducible q ∧ (r q).degree < q.degree) ∧
        f = ∑ q ∈ s,
          algebraMap k[X] (RatFunc k) (r q) /
            algebraMap k[X] (RatFunc k) q := by
  classical
  let factors : Multiset k[X] := normalizedFactors f.denom
  let s : Finset k[X] := factors.toFinset
  have hfactorsNodup : factors.Nodup := by
    exact (squarefree_iff_nodup_normalizedFactors
      (RatFunc.denom_ne_zero f)).mp hsquarefree
  have hfactorsProd : factors.prod = f.denom := by
    dsimp only [factors]
    rw [UniqueFactorizationMonoid.prod_normalizedFactors_eq
      (RatFunc.denom_ne_zero f)]
    exact (RatFunc.monic_denom f).normalize_eq_self
  have hsProd : (∏ q ∈ s, q) = f.denom := by
    calc
      (∏ q ∈ s, q) = s.val.prod := (Finset.prod_val s).symm
      _ = factors.prod := by
        simp only [s, Multiset.toFinset_val, hfactorsNodup.dedup]
      _ = f.denom := hfactorsProd
  have hfactorData (q : k[X]) (hq : q ∈ s) :
      q.Monic ∧ Irreducible q := by
    have hqFactors : q ∈ normalizedFactors f.denom := by
      simpa only [s, factors, Multiset.mem_toFinset] using hq
    have hdata :=
      (Polynomial.mem_normalizedFactors_iff
        (p := q) (RatFunc.denom_ne_zero f)).mp hqFactors
    exact ⟨hdata.2.1, hdata.1⟩
  have hmonic (q : k[X]) (hq : q ∈ s) : q.Monic :=
    (hfactorData q hq).1
  have hpairwise : Set.Pairwise (↑s : Set k[X])
      (fun q r => IsCoprime q r) := by
    intro q hq r hr hqr
    change q ∈ s at hq
    change r ∈ s at hr
    have hqFactors : q ∈ normalizedFactors f.denom := by
      simpa only [s, factors, Multiset.mem_toFinset] using hq
    have hrFactors : r ∈ normalizedFactors f.denom := by
      simpa only [s, factors, Multiset.mem_toFinset] using hr
    have hqIrreducible : Irreducible q :=
      UniqueFactorizationMonoid.irreducible_of_normalized_factor q hqFactors
    apply hqIrreducible.coprime_iff_not_dvd.mpr
    intro hqDvdR
    apply hqr
    exact UniqueFactorizationMonoid.normalizedFactors_eq_of_dvd f.denom
      q hqFactors r hrFactors hqDvdR
  obtain ⟨quo, rem, hremDegree, hpolynomial⟩ :=
    Polynomial.eq_quo_mul_prod_add_sum_rem_mul_prod
      f.num hmonic hpairwise
  let remainderSum : k[X] :=
    ∑ q ∈ s, rem q * ∏ t ∈ s.erase q, t
  have hprodMonic : (∏ q ∈ s, q).Monic :=
    Polynomial.monic_prod_of_monic s (fun q : k[X] => q) hmonic
  have htermDegree (q : k[X]) (hq : q ∈ s) :
      (rem q * ∏ t ∈ s.erase q, t).degree < (∏ t ∈ s, t).degree := by
    rw [← Finset.mul_prod_erase s (fun t : k[X] => t) hq,
      mul_comm q, (hmonic q hq).degree_mul]
    refine (Polynomial.degree_mul_le (rem q) (∏ t ∈ s.erase q, t)).trans_lt ?_
    have hotherMonic : (∏ t ∈ s.erase q, t).Monic :=
      Polynomial.monic_prod_of_monic (s.erase q) (fun t : k[X] => t)
        (fun t ht => hmonic t (Finset.mem_of_mem_erase ht))
    have hotherDegree : (∏ t ∈ s.erase q, t).degree ≠ ⊥ := by
      rw [Polynomial.degree_ne_bot]
      exact hotherMonic.ne_zero
    rw [add_comm, WithBot.add_lt_add_iff_left hotherDegree]
    exact hremDegree q hq
  have hremainderDegree :
      remainderSum.degree < (∏ q ∈ s, q).degree := by
    dsimp only [remainderSum]
    refine (Polynomial.degree_sum_le s
      (fun q => rem q * ∏ t ∈ s.erase q, t)).trans_lt ?_
    refine (Finset.sup_lt_iff ?_).mpr ?_
    · rw [bot_lt_iff_ne_bot, Polynomial.degree_ne_bot]
      exact hprodMonic.ne_zero
    · intro q hq
      exact htermDegree q hq
  have hnumDegree : f.num.degree < (∏ q ∈ s, q).degree := by
    rw [hsProd]
    exact hdegree
  have hquoMul :
      quo * (∏ q ∈ s, q) = f.num - remainderSum := by
    calc
      quo * (∏ q ∈ s, q) =
          (quo * (∏ q ∈ s, q) + remainderSum) - remainderSum := by
            ring
      _ = f.num - remainderSum := by
        rw [← hpolynomial]
  have hquoMulDegree :
      (quo * (∏ q ∈ s, q)).degree < (∏ q ∈ s, q).degree := by
    rw [hquoMul]
    exact (Polynomial.degree_sub_le f.num remainderSum).trans_lt
      (max_lt hnumDegree hremainderDegree)
  have hquo : quo = 0 := by
    by_contra hquoNe
    exact (hprodMonic.not_dvd_of_degree_lt
      (mul_ne_zero hquoNe hprodMonic.ne_zero) hquoMulDegree)
        (dvd_mul_left (∏ q ∈ s, q) quo)
  refine ⟨s, rem, ?_, ?_⟩
  · intro q hq
    exact ⟨(hfactorData q hq).1, (hfactorData q hq).2, hremDegree q hq⟩
  · calc
      f = algebraMap k[X] (RatFunc k) f.num /
          algebraMap k[X] (RatFunc k) f.denom :=
        (RatFunc.num_div_denom f).symm
      _ = algebraMap k[X] (RatFunc k) remainderSum /
          algebraMap k[X] (RatFunc k) (∏ q ∈ s, q) := by
        rw [← hsProd, hpolynomial, hquo, zero_mul, zero_add]
      _ = ∑ q ∈ s,
          algebraMap k[X] (RatFunc k) (rem q) /
            algebraMap k[X] (RatFunc k) q := by
        dsimp only [remainderSum]
        rw [map_sum, Finset.sum_div]
        refine Finset.sum_congr rfl ?_
        intro q hq
        have hotherMonic : (∏ t ∈ s.erase q, t).Monic :=
          Polynomial.monic_prod_of_monic (s.erase q) (fun t : k[X] => t)
            (fun t ht => hmonic t (Finset.mem_of_mem_erase ht))
        have hqMapNe : algebraMap k[X] (RatFunc k) q ≠ 0 :=
          RatFunc.algebraMap_ne_zero (hmonic q hq).ne_zero
        have hotherMapNe :
            algebraMap k[X] (RatFunc k) (∏ t ∈ s.erase q, t) ≠ 0 :=
          RatFunc.algebraMap_ne_zero hotherMonic.ne_zero
        rw [map_mul, map_prod,
          ← Finset.mul_prod_erase s (fun t : k[X] => t) hq, map_mul]
        field_simp [hqMapNe, hotherMapNe]
        rw [map_prod]
end QEC.Coding.AlgebraicGeometry.Differential
