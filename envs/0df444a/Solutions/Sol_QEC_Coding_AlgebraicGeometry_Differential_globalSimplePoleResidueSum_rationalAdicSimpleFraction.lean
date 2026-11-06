-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.globalSimplePoleResidueSum_rationalAdicSimpleFraction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:47:41.949054+00:00
-- url     : https://prove2.me/submissions/70bdac51-fa23-4a9d-8502-d8b7cb81336d

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicSimpleFractionResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_InfinitySimpleFractionResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_SimpleFractionGlobalResidue
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicSimpleFractionAtSimplePole
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalInfinitySimpleFractionAtSimplePole
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_globalSimplePoleResidue_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleTraceResidue_rationalAdicSimpleFraction
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleTraceResidue_rationalInfinitySimpleFraction
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicPolynomial_monic
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
open scoped Polynomial RatFunc
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.Differential
open FunctionFieldDifferential
variable {k : Type*} [Field k] [Finite k]
namespace QEC.Coding.AlgebraicGeometry.Differential
theorem _root_.solution
    (q : IsDedekindDomain.HeightOneSpectrum k[X]) (b : k[X])
    (hb : b.degree < (GlobalPlace.rationalAdicPolynomial q).degree) :
    globalSimplePoleResidueSum (k := k) (F := RatFunc k)
        ((rationalAdicSimpleFractionAtSimplePole q b :
          simplePoleDifferentialLattice (GlobalPlace.rationalAdic q)) :
            Differential k (RatFunc k))
        (rationalAdicSimpleFraction_isGlobalSimplePole q b hb) = 0 := by
  classical
  let omega : Differential k (RatFunc k) :=
    (rationalAdicSimpleFractionAtSimplePole q b :
      simplePoleDifferentialLattice (GlobalPlace.rationalAdic q))
  let homega : IsGlobalSimplePole (k := k) (F := RatFunc k) omega :=
    rationalAdicSimpleFraction_isGlobalSimplePole q b hb
  let c : k := b.coeff ((GlobalPlace.rationalAdicPolynomial q).natDegree - 1)
  let Pq : GlobalPlace k (RatFunc k) := GlobalPlace.rationalAdic q
  let Pinf : GlobalPlace k (RatFunc k) := GlobalPlace.rationalInfinity k
  have hne : Pq ≠ Pinf := by
    intro h
    have hoption : (some q : Option
        (IsDedekindDomain.HeightOneSpectrum k[X])) = none := by
      apply (GlobalPlace.rationalPlaceEquiv (k := k)).injective
      simpa only [Pq, Pinf, GlobalPlace.rationalPlaceEquiv_apply_some,
        GlobalPlace.rationalPlaceEquiv_apply_none] using h
    exact Option.some_ne_none q hoption
  have hat_q :
      globalSimplePoleResidue (k := k) (F := RatFunc k) omega homega Pq = c := by
    rw [globalSimplePoleResidue_apply]
    exact simplePoleTraceResidue_rationalAdicSimpleFraction q b hb
  have hat_infinity :
      globalSimplePoleResidue (k := k) (F := RatFunc k) omega homega Pinf = -c := by
    rw [globalSimplePoleResidue_apply]
    have hrepresentative : omega =
        (rationalInfinitySimpleFractionAtSimplePole
          (GlobalPlace.rationalAdicPolynomial q) b
          (GlobalPlace.rationalAdicPolynomial_monic q) hb :
            Differential k (RatFunc k)) := by
      dsimp only [omega]
      rw [coe_rationalAdicSimpleFractionAtSimplePole,
        coe_rationalInfinitySimpleFractionAtSimplePole]
    change simplePoleTraceResidue (k := k) (F := RatFunc k)
      Pinf omega (homega Pinf) = -c
    have hlocal : (⟨omega, homega Pinf⟩ : simplePoleDifferentialLattice Pinf) =
        rationalInfinitySimpleFractionAtSimplePole
          (GlobalPlace.rationalAdicPolynomial q) b
          (GlobalPlace.rationalAdicPolynomial_monic q) hb :=
      Subtype.ext hrepresentative
    have htrace := congrArg
      (fun w : simplePoleDifferentialLattice Pinf =>
        simplePoleTraceResidue (k := k) (F := RatFunc k) Pinf w w.property) hlocal
    exact htrace.trans (simplePoleTraceResidue_rationalInfinitySimpleFraction
      (GlobalPlace.rationalAdicPolynomial q) b
      (GlobalPlace.rationalAdicPolynomial_monic q) hb)
  have haway (p : IsDedekindDomain.HeightOneSpectrum k[X]) (hpq : p ≠ q) :
      globalSimplePoleResidue (k := k) (F := RatFunc k) omega homega
          (GlobalPlace.rationalAdic p) = 0 := by
    rw [globalSimplePoleResidue_apply]
    apply simplePoleTraceResidue_eq_zero_of_mem_localDifferentialLattice
      (k := k) (F := RatFunc k)
    exact rationalAdicSimpleFraction_mem_localDifferentialLattice_of_ne
      p q hpq b
  have hresidue :
      globalSimplePoleResidue (k := k) (F := RatFunc k) omega homega =
        Finsupp.single Pq c + Finsupp.single Pinf (-c) := by
    ext P
    obtain ⟨place, rfl⟩ :=
      (GlobalPlace.rationalPlaceEquiv (k := k)).surjective P
    cases place with
    | none =>
        simpa only [GlobalPlace.rationalPlaceEquiv_apply_none, Pinf,
          Finsupp.add_apply, Finsupp.single_apply, hne, if_false, if_true,
          zero_add] using hat_infinity
    | some p =>
        rw [GlobalPlace.rationalPlaceEquiv_apply_some]
        by_cases hpq : p = q
        · subst p
          simpa only [Pq, Finsupp.add_apply, Finsupp.single_apply,
            hne.symm, if_false, if_true, add_zero] using hat_q
        · have hp_ne_q : GlobalPlace.rationalAdic p ≠ Pq := by
            intro h
            apply hpq
            have hoption : (some p : Option
                (IsDedekindDomain.HeightOneSpectrum k[X])) = some q := by
              apply (GlobalPlace.rationalPlaceEquiv (k := k)).injective
              simpa only [Pq, GlobalPlace.rationalPlaceEquiv_apply_some] using h
            exact Option.some.inj hoption
          have hp_ne_inf : GlobalPlace.rationalAdic p ≠ Pinf := by
            intro h
            have hoption : (some p : Option
                (IsDedekindDomain.HeightOneSpectrum k[X])) = none := by
              apply (GlobalPlace.rationalPlaceEquiv (k := k)).injective
              simpa only [Pinf, GlobalPlace.rationalPlaceEquiv_apply_some,
                GlobalPlace.rationalPlaceEquiv_apply_none] using h
            exact Option.some_ne_none p hoption
          simpa only [Finsupp.add_apply, Finsupp.single_apply, hp_ne_q.symm,
            hp_ne_inf.symm, if_false, zero_add] using haway p hpq
  change (globalSimplePoleResidue (k := k) (F := RatFunc k)
    omega homega).sum (fun _ residue => residue) = 0
  rw [hresidue]
  rw [Finsupp.sum_single_add_single Pq Pinf c (-c)
    (fun _ residue => residue) hne (fun _ => rfl)]
  simp
end QEC.Coding.AlgebraicGeometry.Differential
