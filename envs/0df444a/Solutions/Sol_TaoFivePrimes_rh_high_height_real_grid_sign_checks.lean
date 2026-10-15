-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_real_grid_sign_checks
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T08:48:56.490209+00:00
-- url     : https://prove2.me/submissions/af8e5695-244b-4fef-9761-c9a1fab00a8f

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighRealGrid
import Definitions.Def_TaoFivePrimes_RHHighHeightBracketInterface
namespace RHHighRealGridChecks
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RHHighListChunks
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
end RHHighListChunks
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
noncomputable def xs := RHHighHeightBracketInterface.leaves RHHighHeightBracketData.certificate
noncomputable def condition (p : RHHighHeightBracketData.Bracket) : Bool := decide (p.l<4096 ∧ p.r<4096 ∧ 2^80≤10^8*(RHHighRealGrid.value p.l).natAbs ∧ 2^80≤10^8*(RHHighRealGrid.value p.r).natAbs ∧ RHHighRealGrid.value p.l*RHHighRealGrid.value p.r<0)
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
end RHHighRealGridChecks
theorem solution :
 (RHHighHeightBracketInterface.leaves RHHighHeightBracketData.certificate).all
  (fun p=>decide (p.l<4096 ∧ p.r<4096 ∧ 2^80≤10^8*(RHHighRealGrid.value p.l).natAbs ∧ 2^80≤10^8*(RHHighRealGrid.value p.r).natAbs ∧ RHHighRealGrid.value p.l*RHHighRealGrid.value p.r<0))=true := by
 change (RHHighRealGridChecks.xs.all RHHighRealGridChecks.condition)=true
 exact
  RHHighRealGridChecks.RHHighListChunks.all_from_64 RHHighRealGridChecks.xs
   RHHighRealGridChecks.condition RHHighRealGridChecks.all_checked
