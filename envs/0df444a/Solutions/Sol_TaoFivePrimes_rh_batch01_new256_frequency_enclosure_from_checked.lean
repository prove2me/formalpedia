-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_new256_frequency_enclosure_from_checked
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T16:06:41.303775+00:00
-- url     : https://prove2.me/submissions/0b173a17-ae97-4342-81e1-20386e0a21cd

import Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
import Definitions.Def_TaoFivePrimes_RHFastWindow256Setup
import Definitions.Def_TaoFivePrimes_RHFastGaussianWindowFourier
import Definitions.Def_TaoFivePrimes_RHBatch01GammaFourierTable
import Definitions.Def_TaoFivePrimes_RHHighSamplingFunctions
import Theorems.Thm_TaoFivePrimes_rh_batch01_new256_setup_soundness
import Theorems.Thm_TaoFivePrimes_rh_fast_frequency_checker_soundness256
import Theorems.Thm_TaoFivePrimes_rh_batch01_new256_packed_reference_lookup
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
namespace RHBatch01New256RHFastFrequencyEnclosure256Proof
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
 let p:=((RHBatch01New256CompactReference.references j)[k]?).getD (0,0)
 ((p.1:ℂ)+(p.2:ℂ)*I)/(2:ℂ)^85=RHBatch01GammaFourierTable.value k j := by
 simp only [RHBatch01New256CompactReference.references,List.getElem?_map,List.getElem?_range hk,Option.map_some,Option.getD_some]
 rw [TaoFivePrimes.rh_batch01_new256_packed_reference_lookup k j hk (by omega)]
 rfl
lemma enclosed (k j:Nat) (hk:k<24) (hj:j<1954)
 (hchecked:RHBatch01New256CompactReference.checked j=true) :
 ‖𝓕 (RHHighSamplingFunctions.moment 3289999808 k) ((j:ℝ)/512)-RHBatch01GammaFourierTable.value k j‖≤1/10^15 ∧
 ‖𝓕 (RHHighSamplingFunctions.moment 3289999808 k) ((j:ℝ)/512)‖≤65537 := by
 simp only [RHBatch01New256CompactReference.checked,Bool.and_eq_true] at hchecked
 rcases hchecked with ⟨hv,hr⟩
 have hs:=TaoFivePrimes.rh_batch01_new256_setup_soundness
 have he:=TaoFivePrimes.rh_fast_frequency_checker_soundness256 3289999808 j
  RHBatch01New256Common.anchor RHBatch01New256Common.pi RHBatch01New256Common.root RHBatch01New256Common.omega
  RHBatch01New256Common.qs RHBatch01New256Common.factors
  (RHFastBallFrequencyProgram256.hermites RHBatch01New256Common.pi RHBatch01New256Common.omega j)
  (RHFastBallFrequencyProgram256.exponentials RHBatch01New256Common.pi RHBatch01New256Common.omega j)
  (RHFastBallFrequencyProgram256.squares RHBatch01New256Common.pi RHBatch01New256Common.omega j)
  (RHBatch01New256CompactReference.references j)
  hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 (fun d hd=>hs.2.2.2.2.1 d) hs.2.2.2.2.2 hv k hk
 rw [reference k j hk hj] at he
 have ha:=TaoFivePrimes.rh_fast_actual_center_formula_error 3289999808 (by norm_num) (by norm_num) k ((j:ℝ)/512)
 have herror:‖𝓕 (RHHighSamplingFunctions.moment 3289999808 k) ((j:ℝ)/512)-RHBatch01GammaFourierTable.value k j‖≤1/10^15 := by
  have ht:=norm_sub_le_norm_sub_add_norm_sub
   (𝓕 (RHHighSamplingFunctions.moment 3289999808 k) ((j:ℝ)/512))
   (RHFastGaussianWindow.fourierFormula 3289999808 k ((j:ℝ)/512)) (RHBatch01GammaFourierTable.value k j)
  exact (ht.trans (add_le_add ha he)).trans (by norm_num)
 have hmag:‖RHBatch01GammaFourierTable.value k j‖≤65536 := by
  rw [←reference k j hk hj]
  apply pair_bound
  have hm:(RHBatch01New256CompactReference.signed k j)∈RHBatch01New256CompactReference.references j := by
   exact List.mem_map.mpr ⟨k,List.mem_range.mpr hk,rfl⟩
  have hb:=List.all_eq_true.mp hr _ hm
  have hb':(RHBatch01New256CompactReference.signed k j).1.natAbs+
   (RHBatch01New256CompactReference.signed k j).2.natAbs≤65536*2^85 := of_decide_eq_true hb
  simpa only [RHBatch01New256CompactReference.references,List.getElem?_map,List.getElem?_range hk,Option.map_some,Option.getD_some] using hb'
 refine ⟨herror,?_⟩
 have ht:=norm_le_norm_sub_add (𝓕 (RHHighSamplingFunctions.moment 3289999808 k) ((j:ℝ)/512)) (RHBatch01GammaFourierTable.value k j)
 exact (ht.trans (add_le_add herror hmag)).trans (by norm_num)
end RHBatch01New256RHFastFrequencyEnclosure256Proof

theorem solution (k j:Nat) (hk:k<24) (hj:j<1954)
 (hchecked:RHBatch01New256CompactReference.checked j=true) :
 ‖𝓕 (RHHighSamplingFunctions.moment 3289999808 k) ((j:ℝ)/512)-RHBatch01GammaFourierTable.value k j‖≤1/10^15 ∧
 ‖𝓕 (RHHighSamplingFunctions.moment 3289999808 k) ((j:ℝ)/512)‖≤65537 :=
 RHBatch01New256RHFastFrequencyEnclosure256Proof.enclosed k j hk hj hchecked
#print axioms solution
