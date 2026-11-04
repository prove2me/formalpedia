-- Prove2me | solution 1 for ThreeSum.LightWeightedScore.Procs.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:03:30.423086+00:00
-- url     : https://prove2.me/submissions/a536f846-1e57-400b-93a9-1ce963d21037

import Definitions.Def_Submission_ThreeSum_WeightedScore
import Definitions.Def_Submission_ThreeSum_ModuloRuntime
import Definitions.Def_Submission_ThreeSum_LightWeightedScore
import Definitions.Def_WeightedCache3SUM_Alias_fde51d4fdceec766
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono
import Theorems.Thm_Light_Seg_congr
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_congr
import Theorems.Thm_ThreeSum_ModuloRuntime_meets_bounded
import Theorems.Thm_ThreeSum_WeightedScore_count_congr


set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedScore
open Light WeightedModuli WeightedScore LightResidues
variable {lim : Limits} {P : Program} {d : ℕ}
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace ThreeSum.LightWeightedScore
namespace Procs
theorem _root_.solution {pMain : ℕ} (C : Procs P pMain)
    {μ : ℕ → ℤ} {a b c nA nB nC q N aux s free maxMod U : ℕ}
    (primes : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hq : 0 < q) (hqmax : q ≤ maxMod)
    (ha : a+nA ≤ free) (hb : b+nB ≤ free) (hc : c+nC ≤ free)
    (haux : aux+s ≤ free)
    (hnA : nA ≤ N) (hnB : nB ≤ N) (hnC : nC ≤ N)
    (hspace : space free maxMod N U ≤ lim.space)
    (hword : (word maxMod N s U : ℤ) ≤ lim.word)
    (hd : d+Nat.clog 2 maxMod+4 ≤ lim.depth)
    (hA : ∀ i < nA, |μ (a+i)| ≤ (U : ℤ))
    (hB : ∀ i < nB, |μ (b+i)| ≤ (U : ℤ))
    (hC : ∀ i < nC, |μ (c+i)| ≤ (U : ℤ))
    (hread : ∀ i < s, μ (aux+i) = (primes i : ℤ))
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i = primes j → i = j)
    (hproduct : ∀ i < s, q*primes i ≤ maxMod) :
    Meets lim P pMain d [a,b,c,nA,nB,nC,q,N,aux,s,free] μ
      (runtimeTime maxMod nA nB nC s U)
      (fun r μ' => r = (score primes s q nA nB nC
        (fun j => μ (a+j)) (fun j => μ (b+j)) (fun j => μ (c+j)) : ℤ) ∧
          Kept μ μ' free) := by
  have hcountSpace : LightModuloCounts.space free maxMod N U ≤ lim.space :=
    (Nat.le_max_left _ _).trans hspace
  have hjointSpace : free+(Nat.log 2 (maxMod+1)+2) ≤ lim.space :=
    (Nat.le_max_right _ _).trans hspace
  have hN : N ≤ lim.space := by
    unfold LightModuloCounts.space at hcountSpace
    omega
  have hcountWord : (LightModuloCounts.word maxMod N U : ℤ) ≤ lim.word := by
    have hh : LightModuloCounts.word maxMod N U ≤ word maxMod N s U := by
      unfold word
      omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hscoreWord : ((s+1)*N^3+8*maxMod+16 : ℕ) ≤ lim.word := by
    have hh : (s+1)*N^3+8*maxMod+16 ≤ word maxMod N s U := by
      unfold word
      omega
    exact (Int.ofNat_le.mpr hh).trans hword
  apply meets_of_count_backend C.main C.joint C.count.emod primes hw (by omega)
    hq hqmax ha hb hc haux hN hnA hnB hnC hjointSpace hscoreWord
    hread hprime hinj hproduct
  intro ν p hkept hp hpmax
  have hAν : ∀ i < nA, |ν (a+i)| ≤ (U : ℤ) := by
    intro i hi
    rw [hkept _ (by omega)]
    exact hA i hi
  have hBν : ∀ i < nB, |ν (b+i)| ≤ (U : ℤ) := by
    intro i hi
    rw [hkept _ (by omega)]
    exact hB i hi
  have hCν : ∀ i < nC, |ν (c+i)| ≤ (U : ℤ) := by
    intro i hi
    rw [hkept _ (by omega)]
    exact hC i hi
  apply (ModuloRuntime.meets_bounded (d := d+1) C.count hw hp hpmax ha hb hc
    hnA hnB hnC hcountSpace hcountWord (by omega) hAν hBν hCν).mono le_rfl
  intro r ν' ⟨hr,hkeep⟩
  refine ⟨hr.trans ?_,hkeep⟩
  congr 1
  exact WeightedScore.count_congr (fun i hi => hkept _ (by omega))
    (fun i hi => hkept _ (by omega)) (fun i hi => hkept _ (by omega))
end Procs
end ThreeSum.LightWeightedScore
