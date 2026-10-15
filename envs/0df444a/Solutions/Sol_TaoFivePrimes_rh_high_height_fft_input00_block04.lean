-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_fft_input00_block04
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T02:51:52.797644+00:00
-- url     : https://prove2.me/submissions/d0ed6485-28a6-4b35-9b1d-922b8f05aa7e

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHHighFFTMomentBlock04
import Definitions.Def_TaoFivePrimes_RHHighFFTInputR00
import Definitions.Def_TaoFivePrimes_RHHighFFTInputI00
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace RHHighFFTInput00Block04
noncomputable def expected (i : Nat) : Int×Int := (let r:Nat:=(((RHHighFFTInputR00.rows[(8192+i)/512]?).getD [])[(8192+i)%512]?).getD 0
   let v:Nat:=(((RHHighFFTInputI00.rows[(8192+i)/512]?).getD [])[(8192+i)%512]?).getD 0
   ((r:Int)-2^166,(v:Int)-2^166))
noncomputable def check (start : Nat) : Bool := (List.range 64).all (fun j => decide (RHHighFFTArithmeticBase.raw (RHHighFFTMomentBlock04.word (start+j)) 0 (8192+start+j)=expected (start+j)))
lemma sound (c j : Nat) (hj:j<64) (h:check (64*c)=true) :
    RHHighFFTArithmeticBase.raw (RHHighFFTMomentBlock04.word (64*c+j)) 0 (8192+64*c+j)=expected (64*c+j) := by
  exact of_decide_eq_true ((List.all_eq_true.mp h) j (List.mem_range.mpr hj))
theorem checked00 : check 0=true := by decide +kernel
theorem checked01 : check 64=true := by decide +kernel
theorem checked02 : check 128=true := by decide +kernel
theorem checked03 : check 192=true := by decide +kernel
theorem checked04 : check 256=true := by decide +kernel
theorem checked05 : check 320=true := by decide +kernel
theorem checked06 : check 384=true := by decide +kernel
theorem checked07 : check 448=true := by decide +kernel
theorem checked08 : check 512=true := by decide +kernel
theorem checked09 : check 576=true := by decide +kernel
theorem checked10 : check 640=true := by decide +kernel
theorem checked11 : check 704=true := by decide +kernel
theorem checked12 : check 768=true := by decide +kernel
theorem checked13 : check 832=true := by decide +kernel
theorem checked14 : check 896=true := by decide +kernel
theorem checked15 : check 960=true := by decide +kernel
theorem checked16 : check 1024=true := by decide +kernel
theorem checked17 : check 1088=true := by decide +kernel
theorem checked18 : check 1152=true := by decide +kernel
theorem checked19 : check 1216=true := by decide +kernel
theorem checked20 : check 1280=true := by decide +kernel
theorem checked21 : check 1344=true := by decide +kernel
theorem checked22 : check 1408=true := by decide +kernel
theorem checked23 : check 1472=true := by decide +kernel
theorem checked24 : check 1536=true := by decide +kernel
theorem checked25 : check 1600=true := by decide +kernel
theorem checked26 : check 1664=true := by decide +kernel
theorem checked27 : check 1728=true := by decide +kernel
theorem checked28 : check 1792=true := by decide +kernel
theorem checked29 : check 1856=true := by decide +kernel
theorem checked30 : check 1920=true := by decide +kernel
theorem checked31 : check 1984=true := by decide +kernel
lemma all_checks (c : Nat) (hc:c<32) : check (64*c)=true := by
  interval_cases c
  · exact checked00
  · exact checked01
  · exact checked02
  · exact checked03
  · exact checked04
  · exact checked05
  · exact checked06
  · exact checked07
  · exact checked08
  · exact checked09
  · exact checked10
  · exact checked11
  · exact checked12
  · exact checked13
  · exact checked14
  · exact checked15
  · exact checked16
  · exact checked17
  · exact checked18
  · exact checked19
  · exact checked20
  · exact checked21
  · exact checked22
  · exact checked23
  · exact checked24
  · exact checked25
  · exact checked26
  · exact checked27
  · exact checked28
  · exact checked29
  · exact checked30
  · exact checked31
end RHHighFFTInput00Block04
theorem solution :
  ∀ i : Nat, i<2048 → RHHighFFTArithmeticBase.raw (RHHighFFTMomentBlock04.word i) 0 (8192+i)=(let r:Nat:=(((RHHighFFTInputR00.rows[(8192+i)/512]?).getD [])[(8192+i)%512]?).getD 0
   let v:Nat:=(((RHHighFFTInputI00.rows[(8192+i)/512]?).getD [])[(8192+i)%512]?).getD 0
   ((r:Int)-2^166,(v:Int)-2^166)) := by
  intro i hi
  change RHHighFFTArithmeticBase.raw (RHHighFFTMomentBlock04.word i) 0 (8192+i)=RHHighFFTInput00Block04.expected i
  have h:64*(i/64)+i%64=i := by omega
  have hh := RHHighFFTInput00Block04.sound (i/64) (i%64) (Nat.mod_lt _ (by decide))
    (RHHighFFTInput00Block04.all_checks (i/64) (by omega))
  simpa only [h,Nat.add_assoc] using hh
