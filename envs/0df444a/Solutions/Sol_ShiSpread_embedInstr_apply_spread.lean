-- Prove2me | solution 1 for ShiSpread.embedInstr_apply_spread
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-11T08:15:22.109157+00:00
-- url     : https://prove2.me/submissions/d1a6d687-fd84-472a-9330-1f42254252e4

import Definitions.Def_ShiSpread_Core

set_option autoImplicit false

section
open ShiSpread ShiEmbed ShiShallow

theorem solution {m n : ℕ} (e : Fin m → Fin n) (he : Function.Injective e)
    (g : Instr m) (ψ : QState m) :
    Instr.apply (embedInstr e he g) (spread e ψ) = spread e (Instr.apply g ψ) := by
  have hpos : ∀ (χ : QState m) (z : Bits n),
      (∀ l : Fin n, OffImage e l → z l = false) → spread e χ z = χ (restrict e z) := by
    intro χ z h
    unfold spread
    rw [if_pos h]
  have hneg : ∀ (χ : QState m) (z : Bits n),
      ¬(∀ l : Fin n, OffImage e l → z l = false) → spread e χ z = 0 := by
    intro χ z h
    unfold spread
    rw [if_neg h]
  have hupd : ∀ (z : Bits n) (k : Fin m) (b : Bool) (l : Fin n), OffImage e l →
      Function.update z (e k) b l = z l := by
    intro z k b l hl
    have hl' : ∀ i : Fin m, e i ≠ l := hl
    exact Function.update_of_ne (fun hh => hl' k hh.symm) b z
  have hcond : ∀ (z : Bits n) (k : Fin m) (b : Bool),
      (∀ l : Fin n, OffImage e l → Function.update z (e k) b l = false)
        ↔ (∀ l : Fin n, OffImage e l → z l = false) := by
    intro z k b
    constructor
    · intro h l hl
      rw [← hupd z k b l hl]
      exact h l hl
    · intro h l hl
      rw [hupd z k b l hl]
      exact h l hl
  have hres : ∀ (z : Bits n) (k : Fin m) (b : Bool),
      restrict e (Function.update z (e k) b) = Function.update (restrict e z) k b := by
    intro z k b
    funext j
    show Function.update z (e k) b (e j) = Function.update (restrict e z) k b j
    by_cases hjk : j = k
    · subst hjk
      simp
    · have hne : e j ≠ e k := fun h => hjk (he h)
      rw [Function.update_of_ne hne b z]
      exact (Function.update_of_ne hjk b (restrict e z)).symm
  have hspU_pos : ∀ (χ : QState m) (z : Bits n) (k : Fin m) (b : Bool),
      (∀ l : Fin n, OffImage e l → z l = false) →
      spread e χ (Function.update z (e k) b) = χ (Function.update (restrict e z) k b) := by
    intro χ z k b h
    rw [hpos χ (Function.update z (e k) b) ((hcond z k b).mpr h), hres z k b]
  have hspU_neg : ∀ (χ : QState m) (z : Bits n) (k : Fin m) (b : Bool),
      ¬(∀ l : Fin n, OffImage e l → z l = false) →
      spread e χ (Function.update z (e k) b) = 0 := by
    intro χ z k b h
    exact hneg χ (Function.update z (e k) b) (fun hh => h ((hcond z k b).mp hh))
  have key1 : ∀ (U : Matrix Bool Bool ℂ) (i : Fin m),
      apply1 U (e i) (spread e ψ) = spread e (apply1 U i ψ) := by
    intro U i
    funext y
    have hL : apply1 U (e i) (spread e ψ) y
        = ∑ b : Bool, U (y (e i)) b * spread e ψ (Function.update y (e i) b) := rfl
    have hR : apply1 U i ψ (restrict e y)
        = ∑ b : Bool, U (y (e i)) b * ψ (Function.update (restrict e y) i b) := rfl
    rw [hL]
    by_cases hy : ∀ l : Fin n, OffImage e l → y l = false
    · rw [hpos (apply1 U i ψ) y hy, hR]
      exact Finset.sum_congr rfl fun b _ => by rw [hspU_pos ψ y i b hy]
    · rw [hneg (apply1 U i ψ) y hy]
      exact Finset.sum_eq_zero fun b _ => by rw [hspU_neg ψ y i b hy, mul_zero]
  have key2 : ∀ (i j : Fin m) (hij : i ≠ j),
      cnotState (e i) (e j) (fun h => hij (he h)) (spread e ψ)
        = spread e (cnotState i j hij ψ) := by
    intro i j hij
    funext y
    have hL : cnotState (e i) (e j) (fun h => hij (he h)) (spread e ψ) y
        = spread e ψ (Function.update y (e j) (xor (y (e j)) (y (e i)))) := rfl
    have hR : cnotState i j hij ψ (restrict e y)
        = ψ (Function.update (restrict e y) j (xor (y (e j)) (y (e i)))) := rfl
    rw [hL]
    by_cases hy : ∀ l : Fin n, OffImage e l → y l = false
    · rw [hspU_pos ψ y j (xor (y (e j)) (y (e i))) hy,
        hpos (cnotState i j hij ψ) y hy, hR]
    · rw [hspU_neg ψ y j (xor (y (e j)) (y (e i))) hy,
        hneg (cnotState i j hij ψ) y hy]
  cases g with
  | h i => exact key1 hMat i
  | s i => exact key1 sMat i
  | t i => exact key1 tMat i
  | x i => exact key1 xMat i
  | cnot i j hij => exact key2 i j hij

end
