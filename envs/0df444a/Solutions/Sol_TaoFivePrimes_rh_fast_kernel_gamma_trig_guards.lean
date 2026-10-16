-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_kernel_gamma_trig_guards
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T19:44:12.920227+00:00
-- url     : https://prove2.me/submissions/a918e2a1-f4a4-46fa-bc4a-3d1ae29f6a16

import Mathlib.Tactic.Ring
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.Range
import Lean.Elab.Tactic.Omega
import Definitions.Def_TaoFivePrimes_RHFastKernelGammaArithmetic
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 1000000
namespace RHFastKernelUniformPolynomials
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
end RHFastKernelUniformPolynomials

open RHFastKernelGammaArithmetic RHFastKernelLogData RHFastKernelGenericExpHorner RHFastKernelUniformPolynomials

theorem solution (d : Nat) (hd : 2*d≤D) :
    d^2*horner (cn D) (d^4)≤horner (cp D) (d^4) ∧
    d^2*horner (sn D) (d^4)≤horner (sp D) (d^4) ∧ 0<(phaseCS d).1 := by
  have hd' : d≤D := by omega
  have hsq : d^2≤D^2 := Nat.pow_le_pow_left hd' 2
  have hq : 0<Q := by decide +kernel
  have hc : List.Forall₂ (fun a b => (2*D^2)*a≤b) (cn D) (cp D) := by decide +kernel
  have hcDom := horner_dominate (2*D^2) (d^4) _ _ hc
  have hc2 : 2*(d^2*horner (cn D) (d^4))≤horner (cp D) (d^4) := by
    calc
      2*(d^2*horner (cn D) (d^4))=(2*d^2)*horner (cn D) (d^4) := by rw [Nat.mul_assoc]
      _ ≤ (2*D^2)*horner (cn D) (d^4) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hsq)
      _ ≤ horner (cp D) (d^4) := hcDom
  have hs : List.Forall₂ (fun a b => (6*D^2)*a≤b) (sn D) (sp D) := by decide +kernel
  have hsDom := horner_dominate (6*D^2) (d^4) _ _ hs
  have hsBound : d^2*horner (sn D) (d^4)≤horner (sp D) (d^4) := by
    calc
      d^2*horner (sn D) (d^4)≤(6*D^2)*horner (sn D) (d^4) :=
        Nat.mul_le_mul_right _ (hsq.trans (by decide +kernel : D^2≤6*D^2))
      _ ≤ horner (sp D) (d^4) := hsDom
  have hcHead : Q≤horner (cp D) (d^4) := by
    exact head_le Q (d^4) (cp D).tail
  have hcPos : 0<(phaseCS d).1 := by
    change 0<(horner (cp D) (d^4)-d^2*horner (cn D) (d^4))*D/Q
    exact positive_sub_scaled _ _ _ hq hcHead hc2
  exact ⟨le_of_double_le hc2,hsBound,hcPos⟩
#print axioms solution
