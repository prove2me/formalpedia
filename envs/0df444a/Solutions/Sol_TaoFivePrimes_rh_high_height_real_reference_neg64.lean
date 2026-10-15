-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_real_reference_neg64
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T08:56:11.933557+00:00
-- url     : https://prove2.me/submissions/517f03b2-4d76-4498-9809-f9d203b8f6a6

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighContourCoefficient
import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Definitions.Def_TaoFivePrimes_RHHighRealSpectrumNeg64
namespace RHHighRealReferenceNeg64
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
noncomputable def condition (m : Nat) (positive : Bool) : Bool :=
 let p:=RHHighContourVector.coefficient RHHighRealSpectrumNeg64.rows.flatten positive m
 let q:=RHHighContourCoefficientData.mul (RHHighContourCoefficientData.inputCoefficient m positive)
   (RHHighContourUnit.pair (RHHighContourCoefficientData.rootIndex ⟨0,by decide⟩ positive m))
 decide (p=(q.1/(2:Int)^48,q.2/(2:Int)^48) ∧ |p.1|+|p.2|≤(2:Int)^80)
theorem check00 : (List.range 16).all (fun i=>condition (0+i+1) false && condition (0+i+1) true)=true := by decide +kernel
theorem check01 : (List.range 16).all (fun i=>condition (16+i+1) false && condition (16+i+1) true)=true := by decide +kernel
theorem check02 : (List.range 16).all (fun i=>condition (32+i+1) false && condition (32+i+1) true)=true := by decide +kernel
theorem check03 : (List.range 16).all (fun i=>condition (48+i+1) false && condition (48+i+1) true)=true := by decide +kernel
theorem check04 : (List.range 16).all (fun i=>condition (64+i+1) false && condition (64+i+1) true)=true := by decide +kernel
theorem check05 : (List.range 16).all (fun i=>condition (80+i+1) false && condition (80+i+1) true)=true := by decide +kernel
theorem check06 : (List.range 16).all (fun i=>condition (96+i+1) false && condition (96+i+1) true)=true := by decide +kernel
theorem check07 : (List.range 16).all (fun i=>condition (112+i+1) false && condition (112+i+1) true)=true := by decide +kernel
theorem check08 : (List.range 16).all (fun i=>condition (128+i+1) false && condition (128+i+1) true)=true := by decide +kernel
theorem check09 : (List.range 16).all (fun i=>condition (144+i+1) false && condition (144+i+1) true)=true := by decide +kernel
theorem check10 : (List.range 16).all (fun i=>condition (160+i+1) false && condition (160+i+1) true)=true := by decide +kernel
theorem check11 : (List.range 16).all (fun i=>condition (176+i+1) false && condition (176+i+1) true)=true := by decide +kernel
theorem check12 : (List.range 16).all (fun i=>condition (192+i+1) false && condition (192+i+1) true)=true := by decide +kernel
theorem check13 : (List.range 16).all (fun i=>condition (208+i+1) false && condition (208+i+1) true)=true := by decide +kernel
theorem check14 : (List.range 16).all (fun i=>condition (224+i+1) false && condition (224+i+1) true)=true := by decide +kernel
theorem check15 : (List.range 16).all (fun i=>condition (240+i+1) false && condition (240+i+1) true)=true := by decide +kernel
theorem check16 : (List.range 16).all (fun i=>condition (256+i+1) false && condition (256+i+1) true)=true := by decide +kernel
theorem check17 : (List.range 16).all (fun i=>condition (272+i+1) false && condition (272+i+1) true)=true := by decide +kernel
theorem check18 : (List.range 16).all (fun i=>condition (288+i+1) false && condition (288+i+1) true)=true := by decide +kernel
theorem check19 : (List.range 16).all (fun i=>condition (304+i+1) false && condition (304+i+1) true)=true := by decide +kernel
theorem check20 : (List.range 16).all (fun i=>condition (320+i+1) false && condition (320+i+1) true)=true := by decide +kernel
theorem check21 : (List.range 16).all (fun i=>condition (336+i+1) false && condition (336+i+1) true)=true := by decide +kernel
theorem check22 : (List.range 16).all (fun i=>condition (352+i+1) false && condition (352+i+1) true)=true := by decide +kernel
theorem check23 : (List.range 16).all (fun i=>condition (368+i+1) false && condition (368+i+1) true)=true := by decide +kernel
theorem check24 : (List.range 16).all (fun i=>condition (384+i+1) false && condition (384+i+1) true)=true := by decide +kernel
theorem check25 : (List.range 16).all (fun i=>condition (400+i+1) false && condition (400+i+1) true)=true := by decide +kernel
theorem check26 : (List.range 16).all (fun i=>condition (416+i+1) false && condition (416+i+1) true)=true := by decide +kernel
theorem check27 : (List.range 16).all (fun i=>condition (432+i+1) false && condition (432+i+1) true)=true := by decide +kernel
theorem check28 : (List.range 16).all (fun i=>condition (448+i+1) false && condition (448+i+1) true)=true := by decide +kernel
theorem check29 : (List.range 16).all (fun i=>condition (464+i+1) false && condition (464+i+1) true)=true := by decide +kernel
theorem check30 : (List.range 16).all (fun i=>condition (480+i+1) false && condition (480+i+1) true)=true := by decide +kernel
theorem check31 : (List.range 16).all (fun i=>condition (496+i+1) false && condition (496+i+1) true)=true := by decide +kernel
theorem check32 : (List.range 16).all (fun i=>condition (512+i+1) false && condition (512+i+1) true)=true := by decide +kernel
theorem check33 : (List.range 16).all (fun i=>condition (528+i+1) false && condition (528+i+1) true)=true := by decide +kernel
theorem check34 : (List.range 16).all (fun i=>condition (544+i+1) false && condition (544+i+1) true)=true := by decide +kernel
theorem check35 : (List.range 16).all (fun i=>condition (560+i+1) false && condition (560+i+1) true)=true := by decide +kernel
theorem check36 : (List.range 16).all (fun i=>condition (576+i+1) false && condition (576+i+1) true)=true := by decide +kernel
theorem check37 : (List.range 16).all (fun i=>condition (592+i+1) false && condition (592+i+1) true)=true := by decide +kernel
theorem check38 : (List.range 16).all (fun i=>condition (608+i+1) false && condition (608+i+1) true)=true := by decide +kernel
theorem check39 : (List.range 16).all (fun i=>condition (624+i+1) false && condition (624+i+1) true)=true := by decide +kernel
theorem check40 : (List.range 16).all (fun i=>condition (640+i+1) false && condition (640+i+1) true)=true := by decide +kernel
theorem check41 : (List.range 16).all (fun i=>condition (656+i+1) false && condition (656+i+1) true)=true := by decide +kernel
theorem check42 : (List.range 16).all (fun i=>condition (672+i+1) false && condition (672+i+1) true)=true := by decide +kernel
theorem check43 : (List.range 16).all (fun i=>condition (688+i+1) false && condition (688+i+1) true)=true := by decide +kernel
theorem check44 : (List.range 16).all (fun i=>condition (704+i+1) false && condition (704+i+1) true)=true := by decide +kernel
theorem check45 : (List.range 16).all (fun i=>condition (720+i+1) false && condition (720+i+1) true)=true := by decide +kernel
theorem check46 : (List.range 16).all (fun i=>condition (736+i+1) false && condition (736+i+1) true)=true := by decide +kernel
theorem check47 : (List.range 16).all (fun i=>condition (752+i+1) false && condition (752+i+1) true)=true := by decide +kernel
theorem check48 : (List.range 16).all (fun i=>condition (768+i+1) false && condition (768+i+1) true)=true := by decide +kernel
theorem check49 : (List.range 16).all (fun i=>condition (784+i+1) false && condition (784+i+1) true)=true := by decide +kernel
theorem check50 : (List.range 16).all (fun i=>condition (800+i+1) false && condition (800+i+1) true)=true := by decide +kernel
theorem check51 : (List.range 16).all (fun i=>condition (816+i+1) false && condition (816+i+1) true)=true := by decide +kernel
theorem check52 : (List.range 16).all (fun i=>condition (832+i+1) false && condition (832+i+1) true)=true := by decide +kernel
theorem check53 : (List.range 16).all (fun i=>condition (848+i+1) false && condition (848+i+1) true)=true := by decide +kernel
theorem check54 : (List.range 16).all (fun i=>condition (864+i+1) false && condition (864+i+1) true)=true := by decide +kernel
theorem check55 : (List.range 16).all (fun i=>condition (880+i+1) false && condition (880+i+1) true)=true := by decide +kernel
theorem check56 : (List.range 16).all (fun i=>condition (896+i+1) false && condition (896+i+1) true)=true := by decide +kernel
theorem check57 : (List.range 16).all (fun i=>condition (912+i+1) false && condition (912+i+1) true)=true := by decide +kernel
theorem check58 : (List.range 16).all (fun i=>condition (928+i+1) false && condition (928+i+1) true)=true := by decide +kernel
theorem check59 : (List.range 16).all (fun i=>condition (944+i+1) false && condition (944+i+1) true)=true := by decide +kernel
theorem check60 : (List.range 16).all (fun i=>condition (960+i+1) false && condition (960+i+1) true)=true := by decide +kernel
theorem check61 : (List.range 16).all (fun i=>condition (976+i+1) false && condition (976+i+1) true)=true := by decide +kernel
theorem check62 : (List.range 16).all (fun i=>condition (992+i+1) false && condition (992+i+1) true)=true := by decide +kernel
theorem check63 : (List.range 16).all (fun i=>condition (1008+i+1) false && condition (1008+i+1) true)=true := by decide +kernel
lemma all_checked (b : Nat) (hb:b<64) : (List.range 16).all (fun i=>condition (16*b+i+1) false && condition (16*b+i+1) true)=true := by
 interval_cases b
 · exact check00
 · exact check01
 · exact check02
 · exact check03
 · exact check04
 · exact check05
 · exact check06
 · exact check07
 · exact check08
 · exact check09
 · exact check10
 · exact check11
 · exact check12
 · exact check13
 · exact check14
 · exact check15
 · exact check16
 · exact check17
 · exact check18
 · exact check19
 · exact check20
 · exact check21
 · exact check22
 · exact check23
 · exact check24
 · exact check25
 · exact check26
 · exact check27
 · exact check28
 · exact check29
 · exact check30
 · exact check31
 · exact check32
 · exact check33
 · exact check34
 · exact check35
 · exact check36
 · exact check37
 · exact check38
 · exact check39
 · exact check40
 · exact check41
 · exact check42
 · exact check43
 · exact check44
 · exact check45
 · exact check46
 · exact check47
 · exact check48
 · exact check49
 · exact check50
 · exact check51
 · exact check52
 · exact check53
 · exact check54
 · exact check55
 · exact check56
 · exact check57
 · exact check58
 · exact check59
 · exact check60
 · exact check61
 · exact check62
 · exact check63
end RHHighRealReferenceNeg64
theorem solution :
 (RHHighRealSpectrumNeg64.rows.flatten[0]?).getD 0=RHHighFourierPolynomial.word 0 ∧
 ∀m:Nat,1 ≤ m ∧ m≤1024 → ∀positive:Bool,
  let p:=RHHighContourVector.coefficient RHHighRealSpectrumNeg64.rows.flatten positive m
  let q:=RHHighContourCoefficientData.mul (RHHighContourCoefficientData.inputCoefficient m positive)
    (RHHighContourUnit.pair (RHHighContourCoefficientData.rootIndex ⟨0,by decide⟩ positive m))
  p=(q.1/(2:Int)^48,q.2/(2:Int)^48) ∧ |p.1|+|p.2|≤(2:Int)^80 := by
 constructor
 · decide +kernel
 intro m hm positive
 let b:=(m-1)/16
 let i:=(m-1)%16
 have hb:b<64:=by dsimp[b];omega
 have hi:i<16:=by dsimp[i];omega
 have he:16*b+i+1=m:=by dsimp[b,i];omega
 have h:=(List.all_eq_true.mp (RHHighRealReferenceNeg64.all_checked b hb)) i (List.mem_range.mpr hi)
 rw[he] at h
 simp only[Bool.and_eq_true] at h
 cases positive
 · exact decide_eq_true_eq.mp h.1
 · exact decide_eq_true_eq.mp h.2
