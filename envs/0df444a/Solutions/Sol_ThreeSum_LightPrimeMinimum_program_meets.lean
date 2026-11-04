-- Prove2me | solution 1 for ThreeSum.LightPrimeMinimum.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:17:21.868282+00:00
-- url     : https://prove2.me/submissions/144ea6a5-d3de-472a-a3b2-4e3762881dd6

import Definitions.Def_Submission_ThreeSum_LightWeightedScore
import Definitions.Def_Submission_ThreeSum_LightMinimum
import Definitions.Def_Submission_ThreeSum_LightPrimeMinimum
import Theorems.Thm_ThreeSum_LightPrimeMinimum_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Theorems.Thm_ThreeSum_LightCyclic_program_procs
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Theorems.Thm_ThreeSum_LightKaratsuba_program_procs
import Definitions.Def_WeightedCache3SUM_Alias_3252ff1ef14149f2
import Definitions.Def_WeightedCache3SUM_Alias_e1d95931a2ead3e4
import Theorems.Thm_ThreeSum_LightModuloCounts_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_03cdb09d18890d4e
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e
import Definitions.Def_WeightedCache3SUM_Alias_280261ae8ac7fab5


set_option autoImplicit false
open ThreeSum ThreeSum.LightPrimeMinimum
open Light WeightedScore
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightPrimeMinimum
theorem _root_.solution
    {μ : ℕ → ℤ} {a b c nA nB nC q N aux s free maxMod U : ℕ}
    (primes : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hq : 0 < q) (hs : 0 < s)
    (ha : a+nA ≤ free) (hb : b+nB ≤ free) (hc : c+nC ≤ free)
    (haux : aux+s ≤ free)
    (hnA : nA ≤ N) (hnB : nB ≤ N) (hnC : nC ≤ N)
    (hspace : LightWeightedScore.space free maxMod N U ≤ lim.space)
    (hword : (LightWeightedScore.word maxMod N s U : ℤ) ≤ lim.word)
    (hd : d+Nat.clog 2 maxMod+5 ≤ lim.depth)
    (hA : ∀ i < nA, |μ (a+i)| ≤ (U : ℤ))
    (hB : ∀ i < nB, |μ (b+i)| ≤ (U : ℤ))
    (hC : ∀ i < nC, |μ (c+i)| ≤ (U : ℤ))
    (hread : ∀ i < s, μ (aux+i) = (primes i : ℤ))
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i = primes j → i = j)
    (hproduct : ∀ i < s, ∀ j < s, q*primes i*primes j ≤ maxMod) :
    Meets lim program 0 d [a,b,c,nA,nB,nC,q,N,aux,s,free] μ
      (time maxMod nA nB nC s U)
      (fun r μ' => r = (chosenPrime primes s q nA nB nC
        (fun j => μ (a+j)) (fun j => μ (b+j)) (fun j => μ (c+j)) : ℤ) ∧
          Kept μ μ' free) :=
  program_procs.meets primes hw hq hs ha hb hc haux hnA hnB hnC hspace hword hd
    hA hB hC hread hprime hinj hproduct
end ThreeSum.LightPrimeMinimum
