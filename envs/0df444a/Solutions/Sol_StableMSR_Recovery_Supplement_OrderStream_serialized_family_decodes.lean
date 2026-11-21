-- Prove2me | solution 1 for StableMSR.Recovery.Supplement.OrderStream.serialized_family_decodes
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-20T18:11:57.382224+00:00
-- url     : https://prove2.me/submissions/36d4c659-9b50-411b-9b05-4ad39b414bc1

import Definitions.Def_StableMSR_PolynomialOrderStream
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.Compiler.BoundedSum
open Polynomial
open StableMSR.Recovery.Supplement StableMSR.Recovery.Supplement.OrderStream
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
open scoped Classical
private lemma cast_list (l : List ℕ) :
    (l : List ℤ)=l.map (fun x : ℕ=>(x:ℤ)) := by
  induction l with
  | nil => rfl
  | cons x l ih => exact congrArg (List.cons (x:ℤ)) ih

theorem solution (m : ℕ) (s : MinSumFPT.State) (h : ∀j < span m,s.imem (-1-(j:ℤ))=(word m j:ℤ)) :
    MinSumFPT.outputSets s=family m := by
  have root : s.imem (-1)=(count m:ℤ) := by simpa [word] using h 0 (by simp [span])
  let pos (r : ℕ) : ℤ := -2-(r:ℤ)*(m+1)
  have size (r : ℕ) (hr : r < count m) : s.imem (pos r)=(m:ℤ) := by
    have bound : 1+r*(m+1) < span m := by unfold span;gcongr
    have eq := h (1+r*(m+1)) bound
    have addr : (-1:ℤ)-((1+r*(m+1):ℕ):ℤ)=pos r := by dsimp [pos];push_cast;ring
    rw [addr] at eq
    simpa [word,Nat.add_comm 1] using eq
  have item (r j : ℕ) (hr : r < count m) (hj : j < m) : s.imem (pos r-1-(j:ℤ))=(atRank m r j:ℤ) := by
    have lt : j+1 < m+1 := by omega
    let u := r*(m+1)+(j+1)
    have un : u < (r+1)*(m+1) := by dsimp [u];rw [Nat.succ_mul];omega
    have up := Nat.mul_le_mul_right (m+1) (Nat.succ_le_of_lt hr)
    change (r+1)*(m+1) ≤ count m*(m+1) at up
    have bound : u+1 < span m := by unfold span;omega
    have eu : (u%(m+1))=j+1 := by simp [u,Nat.add_mod,Nat.mod_eq_of_lt lt]
    have ed : u/(m+1)=r := by
      dsimp [u];rw [Nat.add_comm,Nat.add_mul_div_right _ _ (by omega : 0 < m+1),Nat.div_eq_of_lt lt,Nat.zero_add]
    have eq := h (u+1) bound
    have addr : (-1:ℤ)-((u+1:ℕ):ℤ)=pos r-1-j := by dsimp [u,pos];push_cast;ring
    rw [addr] at eq
    simpa [word,eu,ed] using eq
  have finishLoop (N r : ℕ) (eq : r+N=count m) :
      MinSumFPT.readSets s.imem N (pos r)=(List.range N).map (fun i=>row m (r+i)) := by
    induction N generalizing r with
    | zero => rfl
    | succ N ih =>
      have hr : r < count m := by omega
      have first : MinSumFPT.readSet s.imem (pos r)=row m r := by
        simp only [MinSumFPT.readSet,size r hr,Int.toNat_natCast,row,cast_list,List.map_map]
        apply List.map_congr_left
        intro j hj;exact item r j hr (List.mem_range.mp hj)
      have next : pos r-1-(m:ℤ)=pos (r+1) := by unfold pos;push_cast;ring
      simp only [MinSumFPT.readSets,first,size r hr,Int.toNat_natCast,next,
        ih (r+1) (by omega),List.range_succ_eq_map,List.map_cons,List.map_map,Nat.add_zero]
      apply congrArg (List.cons (row m r))
      apply List.map_congr_left
      intro i hi
      exact congrArg (row m) (show (r+1)+i=r+(i+1) by omega)
  simpa only [MinSumFPT.outputSets,root,Int.toNat_natCast,pos,Nat.cast_zero,zero_mul,sub_zero,Nat.zero_add,family] using finishLoop (count m) 0 (by simp)

