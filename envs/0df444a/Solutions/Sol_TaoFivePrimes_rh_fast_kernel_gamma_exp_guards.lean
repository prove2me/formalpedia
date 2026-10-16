-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_kernel_gamma_exp_guards
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T20:01:23.812408+00:00
-- url     : https://prove2.me/submissions/9556114d-ce8f-46e5-ada7-245b21a2deff

import Mathlib.Tactic.Ring
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.Range
import Lean.Elab.Tactic.Omega
import Definitions.Def_TaoFivePrimes_RHFastKernelGammaArithmetic
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 1000000
namespace RHFastKernelUniformExp
open RHFastKernelGammaArithmetic RHFastKernelLogData RHFastKernelGenericExpHorner
noncomputable def Q : Nat := 8222838654177922817725562880000000*D^31
lemma horner_dominate (c x : Nat) (as bs : List Nat)
    (h : List.Forall₂ (fun a b => c*a≤b) as bs) : c*horner as x≤horner bs x := by
  induction h with
  | nil => simp [horner]
  | @cons a b as bs hab htail ih =>
    change c*(a+x*horner as x)≤b+x*horner bs x
    calc
      c*(a+x*horner as x)=c*a+x*(c*horner as x) := by ring
      _ ≤ b+x*horner bs x := Nat.add_le_add hab (Nat.mul_le_mul_left x ih)
lemma head_le (a x : Nat) (cs : List Nat) : a≤horner (a::cs) x := by
  change a≤a+x*horner cs x
  exact Nat.le_add_right a (x*horner cs x)
lemma horner_cons (a x : Nat) (cs : List Nat) : horner (a::cs) x=a+x*horner cs x := rfl
lemma positive_sub_scaled (A B q : Nat) (hq : 0<q) (hhead : q≤A) (hsmall : 2*B≤A) :
    0<(A-B)*D/q := by
  apply Nat.div_pos ?_ hq
  have h2 : A≤2*(A-B) := by omega
  calc
    q≤A := hhead
    _ ≤ 2*(A-B) := h2
    _ = (A-B)*2 := by ring
    _ ≤ (A-B)*D := Nat.mul_le_mul_left _ (by decide +kernel : 2≤D)
lemma le_of_double_le {A B : Nat} (h : 2*B≤A) : B≤A := by omega
lemma sub_head_bound (q X Y : Nat) (h : X≤Y) : q+X-Y≤q := by omega
lemma fold_bound (a n : Nat) (ha : a≤D) :
    (List.range n).foldl (fun z _ => z*z/D) a≤D := by
  induction n with
  | zero => simpa using ha
  | succ n ih =>
    rw [List.range_succ,List.foldl_append]
    change ((List.range n).foldl (fun z _ => z*z/D) a)*
      ((List.range n).foldl (fun z _ => z*z/D) a)/D≤D
    apply Nat.div_le_of_le_mul
    exact Nat.mul_le_mul ih ih
end RHFastKernelUniformExp

open RHFastKernelGammaArithmetic RHFastKernelLogData RHFastKernelGenericExpHorner RHFastKernelUniformExp

theorem solution (d : Nat) (hd : 2*d≤D) :
    0<RHFastKernelNegativeExp.seed D d ∧ RHFastKernelNegativeExp.seed D d≤D ∧
    ∀ n : Nat, (List.range n).foldl (fun z _ => z*z/D) (RHFastKernelNegativeExp.seed D d)≤D := by
  have hd' : d≤D := by omega
  have hq : 0<Q := by decide +kernel
  have he : List.Forall₂ (fun a b => D*a≤b) (RHFastKernelNegativeExp.en D) (RHFastKernelNegativeExp.ep D) := by decide +kernel
  have heDom := horner_dominate D (d^2) _ _ he
  have he2 : 2*(d*horner (RHFastKernelNegativeExp.en D) (d^2))≤horner (RHFastKernelNegativeExp.ep D) (d^2) := by
    calc
      2*(d*horner (RHFastKernelNegativeExp.en D) (d^2))=(2*d)*horner (RHFastKernelNegativeExp.en D) (d^2) := by rw [Nat.mul_assoc]
      _ ≤ D*horner (RHFastKernelNegativeExp.en D) (d^2) := Nat.mul_le_mul_right _ hd
      _ ≤ horner (RHFastKernelNegativeExp.ep D) (d^2) := heDom
  have heHead : Q≤horner (RHFastKernelNegativeExp.ep D) (d^2) := by
    exact head_le Q (d^2) (RHFastKernelNegativeExp.ep D).tail
  have hePos : 0<RHFastKernelNegativeExp.seed D d := by
    change 0<(horner (RHFastKernelNegativeExp.ep D) (d^2)-d*horner (RHFastKernelNegativeExp.en D) (d^2))*D/Q
    exact positive_sub_scaled _ _ _ hq heHead he2
  have ht : List.Forall₂ (fun a b => D*a≤b) ((RHFastKernelNegativeExp.ep D).tail++[0]) (RHFastKernelNegativeExp.en D) := by decide +kernel
  have htDom := horner_dominate D (d^2) _ _ ht
  have htDom' : D*horner (RHFastKernelNegativeExp.ep D).tail (d^2)≤horner (RHFastKernelNegativeExp.en D) (d^2) := by
    simpa only [horner,List.foldr_append,List.foldr_cons,List.foldr_nil,mul_zero,add_zero] using htDom
  have htSmall : d*horner (RHFastKernelNegativeExp.ep D).tail (d^2)≤horner (RHFastKernelNegativeExp.en D) (d^2) :=
    (Nat.mul_le_mul_right _ hd').trans htDom'
  have htProd : d^2*horner (RHFastKernelNegativeExp.ep D).tail (d^2)≤d*horner (RHFastKernelNegativeExp.en D) (d^2) := by
    simpa only [pow_two,Nat.mul_assoc] using Nat.mul_le_mul_left d htSmall
  have heDecomp : horner (RHFastKernelNegativeExp.ep D) (d^2)=Q+d^2*horner (RHFastKernelNegativeExp.ep D).tail (d^2) := by
    exact horner_cons Q (d^2) (RHFastKernelNegativeExp.ep D).tail
  have heNum : horner (RHFastKernelNegativeExp.ep D) (d^2)-d*horner (RHFastKernelNegativeExp.en D) (d^2)≤Q := by
    calc
      horner (RHFastKernelNegativeExp.ep D) (d^2)-d*horner (RHFastKernelNegativeExp.en D) (d^2) =
          (Q+d^2*horner (RHFastKernelNegativeExp.ep D).tail (d^2))-d*horner (RHFastKernelNegativeExp.en D) (d^2) :=
        congrArg (fun x : Nat => x-d*horner (RHFastKernelNegativeExp.en D) (d^2)) heDecomp
      _ ≤ Q := sub_head_bound _ _ _ htProd
  have heBound : RHFastKernelNegativeExp.seed D d≤D := by
    change (horner (RHFastKernelNegativeExp.ep D) (d^2)-d*horner (RHFastKernelNegativeExp.en D) (d^2))*D/Q≤D
    exact Nat.div_le_of_le_mul (m := (horner (RHFastKernelNegativeExp.ep D) (d^2)-d*horner (RHFastKernelNegativeExp.en D) (d^2))*D) (k := Q) (n := D) (Nat.mul_le_mul_right D heNum)
  exact ⟨hePos,heBound,fun n => fold_bound _ n heBound⟩
#print axioms solution
