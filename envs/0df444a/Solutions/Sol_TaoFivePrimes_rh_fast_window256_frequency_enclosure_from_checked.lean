-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_window256_frequency_enclosure_from_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T11:20:03.155463+00:00
-- url     : https://prove2.me/submissions/ec85cdca-de9e-41f8-9d07-10df4b13ad70

import Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
import Definitions.Def_TaoFivePrimes_RHFastWindow256Setup
import Definitions.Def_TaoFivePrimes_RHFastGaussianWindowFourier
import Definitions.Def_TaoFivePrimes_RHHighGammaFourierTable
import Definitions.Def_TaoFivePrimes_RHHighSamplingFunctions
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_setup_soundness
import Theorems.Thm_TaoFivePrimes_rh_fast_frequency_checker_soundness256
import Theorems.Thm_TaoFivePrimes_rh_fast_window256_packed_reference_lookup
import Theorems.Thm_TaoFivePrimes_rh_fast_actual_center_formula_error
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
open Complex
open scoped FourierTransform
namespace RHFastFrequencyEnclosure256Proof
lemma pair_bound (p:Int×Int) (h:p.1.natAbs+p.2.natAbs≤65536*2^85) :
 ‖((p.1:ℂ)+(p.2:ℂ)*I)/(2:ℂ)^85‖≤65536 := by
 rw [norm_div,Complex.norm_pow,Complex.norm_ofNat]
 apply (div_le_iff₀ (by positivity:(0:ℝ)<2^85)).mpr
 have hn:‖(p.1:ℂ)+(p.2:ℂ)*I‖≤(p.1.natAbs:ℝ)+(p.2.natAbs:ℝ) := by
  apply (norm_add_le _ _).trans
  simp only [norm_mul,norm_I,mul_one,←norm_natAbs p.1,←norm_natAbs p.2,Complex.norm_natCast]
  rfl
 apply hn.trans
 exact_mod_cast h
lemma reference (k j:Nat) (hk:k<24) (hj:j<1954) :
 let p:=((RHFastWindow256CompactReference.references j)[k]?).getD (0,0)
 ((p.1:ℂ)+(p.2:ℂ)*I)/(2:ℂ)^85=RHHighGammaFourierTable.value k j := by
 simp only [RHFastWindow256CompactReference.references,List.getElem?_map,List.getElem?_range hk,Option.map_some,Option.getD_some]
 rw [TaoFivePrimes.rh_fast_window256_packed_reference_lookup k j hk (by omega)]
 rfl
lemma enclosed (k j:Nat) (hk:k<24) (hj:j<1954)
 (hchecked:RHFastWindow256CompactReference.checked j=true) :
 ‖𝓕 (RHHighSamplingFunctions.moment 3289999936 k) ((j:ℝ)/512)-RHHighGammaFourierTable.value k j‖≤1/10^15 ∧
 ‖𝓕 (RHHighSamplingFunctions.moment 3289999936 k) ((j:ℝ)/512)‖≤65537 := by
 simp only [RHFastWindow256CompactReference.checked,Bool.and_eq_true] at hchecked
 rcases hchecked with ⟨hv,hr⟩
 have hs:=TaoFivePrimes.rh_fast_window256_setup_soundness
 have he:=TaoFivePrimes.rh_fast_frequency_checker_soundness256 3289999936 j
  RHFastWindow256Common.anchor RHFastWindow256Common.pi RHFastWindow256Common.root RHFastWindow256Common.omega
  RHFastWindow256Common.qs RHFastWindow256Common.factors
  (RHFastBallFrequencyProgram256.hermites RHFastWindow256Common.pi RHFastWindow256Common.omega j)
  (RHFastBallFrequencyProgram256.exponentials RHFastWindow256Common.pi RHFastWindow256Common.omega j)
  (RHFastBallFrequencyProgram256.squares RHFastWindow256Common.pi RHFastWindow256Common.omega j)
  (RHFastWindow256CompactReference.references j)
  hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 (fun d hd=>hs.2.2.2.2.1 d) hs.2.2.2.2.2 hv k hk
 rw [reference k j hk hj] at he
 have ha:=TaoFivePrimes.rh_fast_actual_center_formula_error 3289999936 (by norm_num) (by norm_num) k ((j:ℝ)/512)
 have herror:‖𝓕 (RHHighSamplingFunctions.moment 3289999936 k) ((j:ℝ)/512)-RHHighGammaFourierTable.value k j‖≤1/10^15 := by
  have ht:=norm_sub_le_norm_sub_add_norm_sub
   (𝓕 (RHHighSamplingFunctions.moment 3289999936 k) ((j:ℝ)/512))
   (RHFastGaussianWindow.fourierFormula 3289999936 k ((j:ℝ)/512)) (RHHighGammaFourierTable.value k j)
  exact (ht.trans (add_le_add ha he)).trans (by norm_num)
 have hmag:‖RHHighGammaFourierTable.value k j‖≤65536 := by
  rw [←reference k j hk hj]
  apply pair_bound
  have hm:(RHFastWindow256CompactReference.signed k j)∈RHFastWindow256CompactReference.references j := by
   exact List.mem_map.mpr ⟨k,List.mem_range.mpr hk,rfl⟩
  have hb:=List.all_eq_true.mp hr _ hm
  have hb':(RHFastWindow256CompactReference.signed k j).1.natAbs+
   (RHFastWindow256CompactReference.signed k j).2.natAbs≤65536*2^85 := of_decide_eq_true hb
  simpa only [RHFastWindow256CompactReference.references,List.getElem?_map,List.getElem?_range hk,Option.map_some,Option.getD_some] using hb'
 refine ⟨herror,?_⟩
 have ht:=norm_le_norm_sub_add (𝓕 (RHHighSamplingFunctions.moment 3289999936 k) ((j:ℝ)/512)) (RHHighGammaFourierTable.value k j)
 exact (ht.trans (add_le_add herror hmag)).trans (by norm_num)
end RHFastFrequencyEnclosure256Proof

theorem solution (k j:Nat) (hk:k<24) (hj:j<1954)
 (hchecked:RHFastWindow256CompactReference.checked j=true) :
 ‖𝓕 (RHHighSamplingFunctions.moment 3289999936 k) ((j:ℝ)/512)-RHHighGammaFourierTable.value k j‖≤1/10^15 ∧
 ‖𝓕 (RHHighSamplingFunctions.moment 3289999936 k) ((j:ℝ)/512)‖≤65537 :=
 RHFastFrequencyEnclosure256Proof.enclosed k j hk hj hchecked
#print axioms solution
