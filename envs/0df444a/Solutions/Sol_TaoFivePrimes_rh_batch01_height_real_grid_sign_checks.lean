-- Prove2me | solution 1 for TaoFivePrimes.rh_batch01_height_real_grid_sign_checks
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-16T17:49:51.780892+00:00
-- url     : https://prove2.me/submissions/d3dc8517-0dba-4b7e-908e-f91b2a835487

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01RealGrid
import Definitions.Def_TaoFivePrimes_RHBatch01HeightBracketInterface
namespace RHBatch01RealGridChecks
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RHBatch01ListChunks
lemma all_from_64 {α : Type*} (xs : List α) (P : α→Bool)
 (h:∀b:Nat,64*b<xs.length → ((xs.drop (64*b)).take 64).all P=true) : xs.all P=true := by
 apply List.all_eq_true.mpr
 intro x hx
 obtain ⟨i,hi,rfl⟩:=List.mem_iff_getElem.mp hx
 let b:=i/64
 let j:=i%64
 have he:64*b+j=i:=by dsimp[b,j];omega
 have hb:64*b<xs.length:=by omega
 have hj:j<64:=by dsimp[j];omega
 have hj':j<((xs.drop (64*b)).take 64).length := by
  simp only[List.length_take,List.length_drop]
  omega
 have hh:=(List.all_eq_true.mp (h b hb)) (((xs.drop (64*b)).take 64)[j]) (List.getElem_mem hj')
 have hv:(((xs.drop (64*b)).take 64)[j])=xs[i] := by
  simp only[List.getElem_take,List.getElem_drop]
  congr 1
 rw[hv] at hh
 exact hh
end RHBatch01ListChunks
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
noncomputable def xs := RHBatch01HeightBracketInterface.leaves RHBatch01HeightBracketData.certificate
noncomputable def condition (p : RHBatch01HeightBracketData.Bracket) : Bool := decide (p.l<4096 ∧ p.r<4096 ∧ 2^80≤10^8*(RHBatch01RealGrid.value p.l).natAbs ∧ 2^80≤10^8*(RHBatch01RealGrid.value p.r).natAbs ∧ RHBatch01RealGrid.value p.l*RHBatch01RealGrid.value p.r<0)
theorem length_checked : xs.length=409 := by decide +kernel
theorem checked00 : ((xs.drop 0).take 64).all condition=true := by decide +kernel
theorem checked01 : ((xs.drop 64).take 64).all condition=true := by decide +kernel
theorem checked02 : ((xs.drop 128).take 64).all condition=true := by decide +kernel
theorem checked03 : ((xs.drop 192).take 64).all condition=true := by decide +kernel
theorem checked04 : ((xs.drop 256).take 64).all condition=true := by decide +kernel
theorem checked05 : ((xs.drop 320).take 64).all condition=true := by decide +kernel
theorem checked06 : ((xs.drop 384).take 64).all condition=true := by decide +kernel
lemma all_checked (b : Nat) (hb:64*b<xs.length) : ((xs.drop (64*b)).take 64).all condition=true := by
 rw[length_checked] at hb
 have hb7:b<7:=by omega
 interval_cases b
 · exact checked00
 · exact checked01
 · exact checked02
 · exact checked03
 · exact checked04
 · exact checked05
 · exact checked06
end RHBatch01RealGridChecks
theorem solution :
 (RHBatch01HeightBracketInterface.leaves RHBatch01HeightBracketData.certificate).all
  (fun p=>decide (p.l<4096 ∧ p.r<4096 ∧ 2^80≤10^8*(RHBatch01RealGrid.value p.l).natAbs ∧ 2^80≤10^8*(RHBatch01RealGrid.value p.r).natAbs ∧ RHBatch01RealGrid.value p.l*RHBatch01RealGrid.value p.r<0))=true := by
 change (RHBatch01RealGridChecks.xs.all RHBatch01RealGridChecks.condition)=true
 exact
  RHBatch01RealGridChecks.RHBatch01ListChunks.all_from_64 RHBatch01RealGridChecks.xs
   RHBatch01RealGridChecks.condition RHBatch01RealGridChecks.all_checked
#print axioms solution
