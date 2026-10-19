-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_setup_soundness
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T13:31:19.315009+00:00
-- url     : https://prove2.me/submissions/e61c8480-65ca-4071-a552-378f7aaea6f2

import Definitions.Def_TaoFivePrimes_RHFastWindow256Setup
import Definitions.Def_TaoFivePrimes_RHBatch01New256Common
import Definitions.Def_TaoFivePrimes_RHFastBallFrequencyChecker256
import Definitions.Def_TaoFivePrimes_RHFastPolynomialCircuitSemantics
import Definitions.Def_TaoFivePrimes_RHFastGaussianWindowFourier
import Definitions.Def_TaoFivePrimes_RHFastComplexBallSemantics
import Theorems.Thm_TaoFivePrimes_rh_batch01_new256_setup_arithmetic
import Theorems.Thm_TaoFivePrimes_rh_fast_center_scalar_seed_soundness
import Theorems.Thm_TaoFivePrimes_rh_fast_log_center_seed_soundness
import Theorems.Thm_TaoFivePrimes_rh_fast_pi_root_ball_seeds
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_rescale_anchor
import Theorems.Thm_TaoFivePrimes_rh_fresh16_anchor_soundness
import Theorems.Thm_TaoFivePrimes_rh_fast_polynomial_circuit_soundness
import Theorems.Thm_TaoFivePrimes_rh_fast_polynomial_circuit_identity
import Theorems.Thm_TaoFivePrimes_rh_fast_moment_factor_ball_soundness256
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.NormNum
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
open Complex Finset Polynomial
namespace RHBatch01New256RHFastSetup256SoundnessProof
open RHFastBallArithmetic RHFastBallSemantics RHFastComplexPoly
lemma entry_none (xs:List ℂ) (k:Nat) (hk:xs.length≤k) : entry xs k=0 := by
 simp only [entry,List.getElem?_eq_none hk,Option.getD_none]
lemma entry_tabulate (f:Nat→ℂ) (n k:Nat) (hk:k<n) :
 entry ((List.range n).map f) k=f k := by
 simp only [entry,List.getElem?_map,List.getElem?_range hk,Option.map_some,Option.getD_some]
lemma coeff_polynomial (xs:List ℂ) (k:Nat) : (polynomial xs).coeff k=entry xs k := by
 unfold polynomial
 rw [Polynomial.finsetSum_coeff]
 simp only [Polynomial.coeff_C_mul_X_pow]
 by_cases hk:k<xs.length
 · simpa only [Finset.sum_ite_eq,Finset.mem_range,if_pos hk]
 · rw [entry_none xs k (by omega)]
   simpa only [Finset.sum_ite_eq,Finset.mem_range,if_neg hk]
lemma zero_mem (D:Nat) : encloses D zero (0:ℂ) := by simp [encloses,value,zero]
lemma entry_mem (D:Nat) {xs:List Ball} {us:List ℂ}
 (h:List.Forall₂ (encloses D) xs us) (i:Nat) :
 encloses D (RHFastBallPoly.entry xs i) (RHFastComplexPoly.entry us i) := by
 induction h generalizing i with
 | nil=>simpa [RHFastBallPoly.entry,RHFastComplexPoly.entry] using zero_mem D
 | cons ha ht ih=>
  cases i with
  | zero=>simpa [RHFastBallPoly.entry,RHFastComplexPoly.entry] using ha
  | succ i=>simpa [RHFastBallPoly.entry,RHFastComplexPoly.entry] using ih i

local notation "D" => RHFastWindow256Setup.D
local notation "T" => (3289999808:Nat)
noncomputable def zs:List ℂ :=
 [RHFastGaussianWindow.center T,(RHFastGaussianWindow.center T)⁻¹,
  Complex.log (RHFastGaussianWindow.center T),(Real.pi:ℂ),(RHFastGaussianWindow.omega T:ℂ)]
lemma constants :
 encloses D RHBatch01New256Common.anchor (RHFastGaussianWindow.anchor T) ∧
 encloses D RHBatch01New256Common.pi (Real.pi:ℂ) ∧
 encloses D RHBatch01New256Common.root ((Real.sqrt (2*Real.pi):ℝ):ℂ) ∧
 encloses D RHBatch01New256Common.omega ((RHFastGaussianWindow.omega T:ℝ):ℂ) := by
 rcases TaoFivePrimes.rh_batch01_new256_setup_arithmetic with ⟨hin,hq,hpi,hroot,homega,hf,ha⟩
 have hlift:=TaoFivePrimes.rh_fast_window256_rescale_anchor.1
 have hs:=TaoFivePrimes.rh_fast_center_scalar_seed_soundness T (by norm_num) (by norm_num)
 refine ⟨?_,?_,?_,?_⟩
 · rw [ha]
   exact hlift _ _ (TaoFivePrimes.rh_fresh16_anchor_soundness T)
 · rw [hpi]
   exact hlift _ _ TaoFivePrimes.rh_fast_pi_root_ball_seeds.1
 · rw [hroot]
   exact hlift _ _ TaoFivePrimes.rh_fast_pi_root_ball_seeds.2
 · rw [homega]
   exact hlift _ _ hs.2.1
lemma inputs_mem : List.Forall₂ (encloses D) RHBatch01New256Common.inputs zs := by
 rw [TaoFivePrimes.rh_batch01_new256_setup_arithmetic.1]
 unfold RHFastWindow256Setup.inputs zs
 have hlift:=TaoFivePrimes.rh_fast_window256_rescale_anchor.1
 have hs:=TaoFivePrimes.rh_fast_center_scalar_seed_soundness T (by norm_num) (by norm_num)
 have hl:=TaoFivePrimes.rh_fast_log_center_seed_soundness T (by norm_num) (by norm_num)
 exact List.Forall₂.cons (hlift _ _ hs.2.2.1)
  (List.Forall₂.cons (hlift _ _ hs.2.2.2)
  (List.Forall₂.cons (hlift _ _ hl)
  (List.Forall₂.cons constants.2.1
  (List.Forall₂.cons constants.2.2.2 List.Forall₂.nil))))
lemma coefficient_mem (d:Nat) :
 encloses D (RHFastBallFrequencyChecker256.entry RHBatch01New256Common.qs d)
  ((RHFastGaussianWindow.proxyPolynomial T).coeff d) := by
 have h:=TaoFivePrimes.rh_fast_polynomial_circuit_soundness D (by norm_num [RHFastWindow256Setup.D])
  RHBatch01New256Common.inputs zs inputs_mem RHFastPolynomialCircuit.approximation
 have hp:polynomial (RHFastPolynomialCircuitSemantics.evaluate zs RHFastPolynomialCircuit.approximation)=
  RHFastGaussianWindow.proxyPolynomial T := h.2.trans (TaoFivePrimes.rh_fast_polynomial_circuit_identity T)
 have hq:List.Forall₂ (encloses D) RHBatch01New256Common.qs
  (RHFastPolynomialCircuitSemantics.evaluate zs RHFastPolynomialCircuit.approximation) := by
  rw [TaoFivePrimes.rh_batch01_new256_setup_arithmetic.2.1,RHFastWindow256Setup.coefficients,
   ←TaoFivePrimes.rh_batch01_new256_setup_arithmetic.1]
  exact h.1
 have he:=entry_mem D hq d
 rw [←coeff_polynomial,hp] at he
 exact he
lemma factor_mem (k:Nat) (hk:k<24) :
 encloses D (RHFastBallFrequencyChecker256.entry RHBatch01New256Common.factors k)
  (((-Real.pi:ℝ):ℂ)^k/(k.factorial:ℂ)) := by
 have hf:=TaoFivePrimes.rh_batch01_new256_setup_arithmetic.2.2.2.2.2.1
 rw [hf]
 simp only [RHFastWindow256Setup.factors,RHFastBallFrequencyChecker256.entry,
  List.getElem?_map,List.getElem?_range hk,Option.map_some,Option.getD_some]
 exact TaoFivePrimes.rh_fast_moment_factor_ball_soundness256 RHBatch01New256Common.pi constants.2.1 k
end RHBatch01New256RHFastSetup256SoundnessProof

theorem solution :
 RHFastBallSemantics.encloses RHFastWindow256Setup.D RHBatch01New256Common.anchor (RHFastGaussianWindow.anchor 3289999808) ∧
 RHFastBallSemantics.encloses RHFastWindow256Setup.D RHBatch01New256Common.pi (Real.pi:ℂ) ∧
 RHFastBallSemantics.encloses RHFastWindow256Setup.D RHBatch01New256Common.root ((Real.sqrt (2*Real.pi):ℝ):ℂ) ∧
 RHFastBallSemantics.encloses RHFastWindow256Setup.D RHBatch01New256Common.omega ((RHFastGaussianWindow.omega 3289999808:ℝ):ℂ) ∧
 (∀d:Nat,RHFastBallSemantics.encloses RHFastWindow256Setup.D (RHFastBallFrequencyChecker256.entry RHBatch01New256Common.qs d)
  ((RHFastGaussianWindow.proxyPolynomial 3289999808).coeff d)) ∧
 (∀k:Nat,k<24→RHFastBallSemantics.encloses RHFastWindow256Setup.D (RHFastBallFrequencyChecker256.entry RHBatch01New256Common.factors k)
  (((-Real.pi:ℝ):ℂ)^k/(k.factorial:ℂ))) :=
 ⟨RHBatch01New256RHFastSetup256SoundnessProof.constants.1,RHBatch01New256RHFastSetup256SoundnessProof.constants.2.1,
  RHBatch01New256RHFastSetup256SoundnessProof.constants.2.2.1,RHBatch01New256RHFastSetup256SoundnessProof.constants.2.2.2,
  RHBatch01New256RHFastSetup256SoundnessProof.coefficient_mem,RHBatch01New256RHFastSetup256SoundnessProof.factor_mem⟩
#print axioms solution
