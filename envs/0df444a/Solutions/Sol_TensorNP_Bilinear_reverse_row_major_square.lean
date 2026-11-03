-- Prove2me | solution 1 for TensorNP.Bilinear.reverse_row_major_square
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-02T12:19:42.387903+00:00
-- url     : https://prove2.me/submissions/a56ed92e-f3cb-4457-85c5-82d6c3474245

import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.List.OfFn
import Lean.Elab.Tactic.Omega

private lemma reverse_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) :
    (List.ofFn f).reverse = List.ofFn (fun k => f k.rev) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.length_reverse, List.length_ofFn] at hi
    simp only [List.getElem_reverse, List.length_ofFn, List.getElem_ofFn]
    congr 1
    apply Fin.ext
    simp only [Fin.val_mk, Fin.val_rev]
    omega

private lemma decode_rev {v : ℕ} (k : Fin (v*v)) :
    finProdFinEquiv.symm k.rev =
      ((finProdFinEquiv.symm k).1.rev, (finProdFinEquiv.symm k).2.rev) := by
  apply finProdFinEquiv.injective
  rw [Equiv.apply_symm_apply]
  apply Fin.ext
  have hfirst := (finProdFinEquiv.symm k).1.isLt
  have hsecond := (finProdFinEquiv.symm k).2.isLt
  have heq := congrArg Fin.val (finProdFinEquiv.apply_symm_apply k)
  change (finProdFinEquiv.symm k).2.val + v * (finProdFinEquiv.symm k).1.val = k.val at heq
  change v*v - (k.val + 1) =
    (v - ((finProdFinEquiv.symm k).2.val + 1)) +
      v * (v - ((finProdFinEquiv.symm k).1.val + 1))
  have hfirst' : (finProdFinEquiv.symm k).1.val + 1 ≤ v := hfirst
  have hsecond' : (finProdFinEquiv.symm k).2.val + 1 ≤ v := hsecond
  simp only [Nat.mul_sub_left_distrib, Nat.mul_add, Nat.mul_one]
  have hmul : v * ((finProdFinEquiv.symm k).1.val + 1) ≤ v * v := Nat.mul_le_mul_left v hfirst'
  simp only [Nat.mul_add, Nat.mul_one] at hmul
  omega

theorem solution {α : Type*} {v : ℕ} (m : Fin v → Fin v → α) :
    (List.ofFn (fun k : Fin (v*v) ↦
      m (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)).reverse =
    List.ofFn (fun k : Fin (v*v) ↦
      m (finProdFinEquiv.symm k).1.rev (finProdFinEquiv.symm k).2.rev) := by
  rw [reverse_ofFn]
  congr 1
  funext k
  rw [decode_rev]

#print axioms solution
