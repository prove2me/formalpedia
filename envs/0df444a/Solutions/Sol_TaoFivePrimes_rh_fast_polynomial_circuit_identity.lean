-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_polynomial_circuit_identity
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T10:44:57.499192+00:00
-- url     : https://prove2.me/submissions/2971c3c5-8839-4216-aeda-35e8d5aa5a6f

import Definitions.Def_TaoFivePrimes_RHFastPolynomialCircuitSemantics
import Definitions.Def_TaoFivePrimes_RHFastGaussianWindowFourier
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
open Complex Polynomial Finset
namespace RHFastCircuitIdentityProof
open RHFastPolynomialCircuit
local notation "ev" => RHFastPolynomialCircuitSemantics.polynomial
noncomputable def inputs (T:Nat):List ℂ :=
 [RHFastGaussianWindow.center T,(RHFastGaussianWindow.center T)⁻¹,
  Complex.log (RHFastGaussianWindow.center T),(Real.pi:ℂ),(RHFastGaussianWindow.omega T:ℂ)]
lemma sum_fold (zs:List ℂ) (es:List Expr) (a:Expr) :
 ev zs (es.foldl Expr.add a)=ev zs a+(es.map (ev zs)).sum := by
 induction es generalizing a with
 | nil=>simp
 | cons x xs ih=>
  simp only [List.foldl_cons,ih,RHFastPolynomialCircuitSemantics.polynomial,List.map_cons,List.sum_cons]
  ring
lemma sum_ev (zs:List ℂ) (es:List Expr) : ev zs (RHFastPolynomialCircuit.sum es)=(es.map (ev zs)).sum := by
 simpa only [RHFastPolynomialCircuit.sum,RHFastPolynomialCircuitSemantics.polynomial,zero_add] using sum_fold zs es .zero
lemma increment (T:Nat) : ev (inputs T) RHFastPolynomialCircuit.increment=RHFastGaussianWindow.deltaPolynomial T := by
 unfold RHFastPolynomialCircuit.increment
 simp only [RHFastPolynomialCircuitSemantics.polynomial,sum_ev,List.map_map]
 norm_num [List.range_succ,List.map_append,List.map_cons,List.map_nil,List.sum_append,List.sum_cons,List.sum_nil,
  RHFastPolynomialCircuitSemantics.polynomial,RHFastPolynomialCircuit.sub,RHFastPolynomialCircuit.neg,
  inputs,RHFastComplexPoly.entry,RHFastGaussianWindow.deltaPolynomial,Finset.sum_range_succ,
  map_add,map_sub,map_mul,map_pow,map_neg,sum_ev]
 ring
lemma approximation (T:Nat) : ev (inputs T) RHFastPolynomialCircuit.approximation=RHFastGaussianWindow.proxyPolynomial T := by
 unfold RHFastPolynomialCircuit.approximation
 rw [sum_ev]
 norm_num only [List.range_succ,List.range_zero,List.map_append,List.map_cons,List.map_nil,List.sum_append,List.sum_cons,List.sum_nil]
 simp only [RHFastPolynomialCircuitSemantics.polynomial,increment]
 norm_num [RHFastGaussianWindow.proxyPolynomial,Finset.sum_range_succ,Nat.factorial]
 <;> ring
end RHFastCircuitIdentityProof

theorem solution (T:Nat) :
 let zs:List ℂ:=[RHFastGaussianWindow.center T,(RHFastGaussianWindow.center T)⁻¹,
  Complex.log (RHFastGaussianWindow.center T),(Real.pi:ℂ),(RHFastGaussianWindow.omega T:ℂ)]
 RHFastPolynomialCircuitSemantics.polynomial zs RHFastPolynomialCircuit.approximation=RHFastGaussianWindow.proxyPolynomial T :=
 RHFastCircuitIdentityProof.approximation T
#print axioms solution
