-- Prove2me | solution 1 for ShiTensor.runLayered_embed_three_blocks
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-14T04:45:40.429899+00:00
-- url     : https://prove2.me/submissions/0b565a39-ea58-4c5c-b3b0-e6727aafc6d6

import Definitions.Def_ShiTensor_Core
import Definitions.Def_ShiEmbed_Core

set_option autoImplicit false

open ShiShallow ShiTensor

/-!
# Three disjoint circuit blocks act independently on a three-fold product state

Register split LEFT-nested as `(m + p) + q`, with the three inclusions

* `Fin.castAdd q ∘ Fin.castAdd p : Fin m → Fin (m + p + q)`
* `Fin.castAdd q ∘ Fin.natAdd  m : Fin p → Fin (m + p + q)`
* `Fin.natAdd (m + p)           : Fin q → Fin (m + p + q)`

The proof is assembly: `List.foldl_append` splits the concatenated circuit into three
sequential runs, functoriality of `embedCirc` peels each two-step inclusion into an outer and
an inner one, and the two binary block lemmas (re-proved below, since imports of accepted
theorems are not available here) do all the semantic work.  No new disjointness argument is
needed: "block `i` does not disturb the other two factors" is exactly the content of the
binary lemmas.
-/

/-! ## Part 1: the `Fin.castAdd` binary block lemma -/

private theorem shiTri_cast_leftBits_update {m p : ℕ} (y : Bits (m + p)) (i : Fin m)
    (b : Bool) :
    leftBits (Function.update y (Fin.castAdd p i) b) = Function.update (leftBits y) i b := by
  funext k
  simp only [leftBits]
  by_cases hki : k = i
  · subst hki
    rw [Function.update_self, Function.update_self]
  · have hne : Fin.castAdd p k ≠ Fin.castAdd p i := by
      intro hc
      apply hki
      have h2 := congrArg Fin.val hc
      rw [Fin.val_castAdd, Fin.val_castAdd] at h2
      exact Fin.ext h2
    rw [Function.update_of_ne hne, Function.update_of_ne hki]
    rfl

private theorem shiTri_cast_rightBits_update {m p : ℕ} (y : Bits (m + p)) (i : Fin m)
    (b : Bool) :
    rightBits (Function.update y (Fin.castAdd p i) b) = rightBits y := by
  funext k
  simp only [rightBits]
  have hne : Fin.natAdd m k ≠ Fin.castAdd p i := by
    intro hc
    have h2 := congrArg Fin.val hc
    rw [Fin.val_natAdd, Fin.val_castAdd] at h2
    have hi := i.isLt
    omega
  rw [Function.update_of_ne hne]

private theorem shiTri_cast_apply1 {m p : ℕ} (U : Matrix Bool Bool ℂ) (i : Fin m)
    (ψ : QState m) (φ : QState p) :
    apply1 U (Fin.castAdd p i) (tensor ψ φ) = tensor (apply1 U i ψ) φ := by
  funext x
  have hx : x (Fin.castAdd p i) = leftBits x i := rfl
  simp only [apply1, tensor, hx, shiTri_cast_leftBits_update, shiTri_cast_rightBits_update]
  simp only [← mul_assoc]
  rw [← Finset.sum_mul]

private theorem shiTri_cast_cnotState {m p : ℕ} (i j : Fin m) (hij : i ≠ j)
    (hij' : Fin.castAdd p i ≠ Fin.castAdd p j) (ψ : QState m) (φ : QState p) :
    cnotState (Fin.castAdd p i) (Fin.castAdd p j) hij' (tensor ψ φ)
      = tensor (cnotState i j hij ψ) φ := by
  funext x
  simp only [cnotState, tensor]
  rw [shiTri_cast_leftBits_update, shiTri_cast_rightBits_update]
  rfl

private theorem shiTri_cast_instrApply {m p : ℕ} (g : Instr m)
    (ψ : QState m) (φ : QState p) :
    Instr.apply (ShiEmbed.embedInstr (Fin.castAdd p) (Fin.castAdd_injective m p) g) (tensor ψ φ)
      = tensor (Instr.apply g ψ) φ := by
  cases g with
  | h i => exact shiTri_cast_apply1 hMat i ψ φ
  | s i => exact shiTri_cast_apply1 sMat i ψ φ
  | t i => exact shiTri_cast_apply1 tMat i ψ φ
  | x i => exact shiTri_cast_apply1 xMat i ψ φ
  | cnot i j hij =>
      exact shiTri_cast_cnotState i j hij
        (fun h => hij (Fin.castAdd_injective m p h)) ψ φ

private theorem shiTri_cast_runLayer {m p : ℕ} (l : List (Instr m))
    (ψ : QState m) (φ : QState p) :
    runLayer (ShiEmbed.embedLayer (Fin.castAdd p) (Fin.castAdd_injective m p) l) (tensor ψ φ)
      = tensor (runLayer l ψ) φ := by
  induction l generalizing ψ with
  | nil => rfl
  | cons g l' ih =>
      show runLayer (ShiEmbed.embedLayer (Fin.castAdd p) (Fin.castAdd_injective m p) l')
              (Instr.apply
                (ShiEmbed.embedInstr (Fin.castAdd p) (Fin.castAdd_injective m p) g) (tensor ψ φ))
          = tensor (runLayer l' (Instr.apply g ψ)) φ
      rw [shiTri_cast_instrApply]
      exact ih (Instr.apply g ψ)

private theorem shiTri_cast_runLayered {m p : ℕ} (c : Layered m) (ψ : QState m) (φ : QState p) :
    runLayered (ShiEmbed.embedCirc (Fin.castAdd p) (Fin.castAdd_injective m p) c) (tensor ψ φ)
      = tensor (runLayered c ψ) φ := by
  induction c generalizing ψ with
  | nil => rfl
  | cons l c' ih =>
      show runLayered (ShiEmbed.embedCirc (Fin.castAdd p) (Fin.castAdd_injective m p) c')
              (runLayer
                (ShiEmbed.embedLayer (Fin.castAdd p) (Fin.castAdd_injective m p) l) (tensor ψ φ))
          = tensor (runLayered c' (runLayer l ψ)) φ
      rw [shiTri_cast_runLayer]
      exact ih (runLayer l ψ)

/-! ## Part 2: the `Fin.natAdd` binary block lemma -/

private theorem shiTri_nat_rightBits_update {m p : ℕ} (y : Bits (m + p)) (j : Fin p)
    (b : Bool) :
    rightBits (Function.update y (Fin.natAdd m j) b) = Function.update (rightBits y) j b := by
  funext k
  simp only [rightBits]
  by_cases hkj : k = j
  · subst hkj
    rw [Function.update_self, Function.update_self]
  · have hne : Fin.natAdd m k ≠ Fin.natAdd m j := by
      intro hc
      apply hkj
      have h2 := congrArg Fin.val hc
      rw [Fin.val_natAdd, Fin.val_natAdd] at h2
      exact Fin.ext (by omega)
    rw [Function.update_of_ne hne, Function.update_of_ne hkj]
    rfl

private theorem shiTri_nat_leftBits_update {m p : ℕ} (y : Bits (m + p)) (j : Fin p)
    (b : Bool) :
    leftBits (Function.update y (Fin.natAdd m j) b) = leftBits y := by
  funext k
  simp only [leftBits]
  have hne : Fin.castAdd p k ≠ Fin.natAdd m j := by
    intro hc
    have h2 := congrArg Fin.val hc
    rw [Fin.val_castAdd, Fin.val_natAdd] at h2
    have hk := k.isLt
    omega
  rw [Function.update_of_ne hne]

private theorem shiTri_nat_apply1 {m p : ℕ} (U : Matrix Bool Bool ℂ) (j : Fin p)
    (ψ : QState m) (φ : QState p) :
    apply1 U (Fin.natAdd m j) (tensor ψ φ) = tensor ψ (apply1 U j φ) := by
  funext x
  have hx : x (Fin.natAdd m j) = rightBits x j := rfl
  simp only [apply1, tensor, hx, shiTri_nat_leftBits_update, shiTri_nat_rightBits_update]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro b _
  ring

private theorem shiTri_nat_cnotState {m p : ℕ} (i j : Fin p) (hij : i ≠ j)
    (hij' : Fin.natAdd m i ≠ Fin.natAdd m j) (ψ : QState m) (φ : QState p) :
    cnotState (Fin.natAdd m i) (Fin.natAdd m j) hij' (tensor ψ φ)
      = tensor ψ (cnotState i j hij φ) := by
  funext x
  simp only [cnotState, tensor]
  rw [shiTri_nat_leftBits_update, shiTri_nat_rightBits_update]
  rfl

private theorem shiTri_nat_instrApply {m p : ℕ} (g : Instr p)
    (ψ : QState m) (φ : QState p) :
    Instr.apply (ShiEmbed.embedInstr (Fin.natAdd m) (Fin.natAdd_injective p m) g) (tensor ψ φ)
      = tensor ψ (Instr.apply g φ) := by
  cases g with
  | h j => exact shiTri_nat_apply1 hMat j ψ φ
  | s j => exact shiTri_nat_apply1 sMat j ψ φ
  | t j => exact shiTri_nat_apply1 tMat j ψ φ
  | x j => exact shiTri_nat_apply1 xMat j ψ φ
  | cnot i j hij =>
      exact shiTri_nat_cnotState i j hij
        (fun h => hij (Fin.natAdd_injective p m h)) ψ φ

private theorem shiTri_nat_runLayer {m p : ℕ} (l : List (Instr p))
    (ψ : QState m) (φ : QState p) :
    runLayer (ShiEmbed.embedLayer (Fin.natAdd m) (Fin.natAdd_injective p m) l) (tensor ψ φ)
      = tensor ψ (runLayer l φ) := by
  induction l generalizing φ with
  | nil => rfl
  | cons g l' ih =>
      show runLayer (ShiEmbed.embedLayer (Fin.natAdd m) (Fin.natAdd_injective p m) l')
              (Instr.apply
                (ShiEmbed.embedInstr (Fin.natAdd m) (Fin.natAdd_injective p m) g) (tensor ψ φ))
          = tensor ψ (runLayer l' (Instr.apply g φ))
      rw [shiTri_nat_instrApply]
      exact ih (Instr.apply g φ)

private theorem shiTri_nat_runLayered {m p : ℕ} (c : Layered p) (ψ : QState m) (φ : QState p) :
    runLayered (ShiEmbed.embedCirc (Fin.natAdd m) (Fin.natAdd_injective p m) c) (tensor ψ φ)
      = tensor ψ (runLayered c φ) := by
  induction c generalizing φ with
  | nil => rfl
  | cons l c' ih =>
      show runLayered (ShiEmbed.embedCirc (Fin.natAdd m) (Fin.natAdd_injective p m) c')
              (runLayer
                (ShiEmbed.embedLayer (Fin.natAdd m) (Fin.natAdd_injective p m) l) (tensor ψ φ))
          = tensor ψ (runLayered c' (runLayer l φ))
      rw [shiTri_nat_runLayer]
      exact ih (runLayer l φ)

/-! ## Part 3: structural laws -- functoriality of `embedCirc`, and `runLayered` on `++` -/

private theorem shiTri_embedInstr_comp {m n k : ℕ}
    (e : Fin m → Fin n) (he : Function.Injective e)
    (f : Fin n → Fin k) (hf : Function.Injective f)
    (hfe : Function.Injective (f ∘ e)) :
    ShiEmbed.embedInstr (f ∘ e) hfe
      = ShiEmbed.embedInstr f hf ∘ ShiEmbed.embedInstr e he := by
  funext a
  cases a <;> rfl

private theorem shiTri_embedLayer_comp {m n k : ℕ}
    (e : Fin m → Fin n) (he : Function.Injective e)
    (f : Fin n → Fin k) (hf : Function.Injective f)
    (hfe : Function.Injective (f ∘ e)) :
    ShiEmbed.embedLayer (f ∘ e) hfe
      = ShiEmbed.embedLayer f hf ∘ ShiEmbed.embedLayer e he := by
  funext l
  show List.map (ShiEmbed.embedInstr (f ∘ e) hfe) l
      = List.map (ShiEmbed.embedInstr f hf) (List.map (ShiEmbed.embedInstr e he) l)
  rw [List.map_map, shiTri_embedInstr_comp e he f hf hfe]

private theorem shiTri_embedCirc_comp {m n k : ℕ}
    (e : Fin m → Fin n) (he : Function.Injective e)
    (f : Fin n → Fin k) (hf : Function.Injective f)
    (hfe : Function.Injective (f ∘ e)) (c : Layered m) :
    ShiEmbed.embedCirc (f ∘ e) hfe c
      = ShiEmbed.embedCirc f hf (ShiEmbed.embedCirc e he c) := by
  show List.map (ShiEmbed.embedLayer (f ∘ e) hfe) c
      = List.map (ShiEmbed.embedLayer f hf) (List.map (ShiEmbed.embedLayer e he) c)
  rw [List.map_map, shiTri_embedLayer_comp e he f hf hfe]

private theorem shiTri_runLayered_append {n : ℕ} (c c' : Layered n) (ψ : QState n) :
    runLayered (c ++ c') ψ = runLayered c' (runLayered c ψ) := by
  first
    | (simp only [runLayered, List.foldl_append]; done)
    | (simp [runLayered]; done)

/-! ## Part 4: the three-block theorem -/

theorem solution {m p q : ℕ} (c1 : Layered m) (c2 : Layered p) (c3 : Layered q)
    (ψ1 : QState m) (ψ2 : QState p) (ψ3 : QState q) :
    runLayered
        (ShiEmbed.embedCirc
            ((Fin.castAdd q : Fin (m + p) → Fin (m + p + q)) ∘
              (Fin.castAdd p : Fin m → Fin (m + p)))
            ((Fin.castAdd_injective (m + p) q).comp (Fin.castAdd_injective m p)) c1
          ++ ShiEmbed.embedCirc
            ((Fin.castAdd q : Fin (m + p) → Fin (m + p + q)) ∘
              (Fin.natAdd m : Fin p → Fin (m + p)))
            ((Fin.castAdd_injective (m + p) q).comp (Fin.natAdd_injective p m)) c2
          ++ ShiEmbed.embedCirc (Fin.natAdd (m + p) : Fin q → Fin (m + p + q))
            (Fin.natAdd_injective q (m + p)) c3)
        (tensor (tensor ψ1 ψ2) ψ3)
      = tensor (tensor (runLayered c1 ψ1) (runLayered c2 ψ2)) (runLayered c3 ψ3) := by
  have e1 := shiTri_embedCirc_comp
    (Fin.castAdd p : Fin m → Fin (m + p)) (Fin.castAdd_injective m p)
    (Fin.castAdd q : Fin (m + p) → Fin (m + p + q)) (Fin.castAdd_injective (m + p) q)
    ((Fin.castAdd_injective (m + p) q).comp (Fin.castAdd_injective m p)) c1
  have e2 := shiTri_embedCirc_comp
    (Fin.natAdd m : Fin p → Fin (m + p)) (Fin.natAdd_injective p m)
    (Fin.castAdd q : Fin (m + p) → Fin (m + p + q)) (Fin.castAdd_injective (m + p) q)
    ((Fin.castAdd_injective (m + p) q).comp (Fin.natAdd_injective p m)) c2
  first
    | (rw [shiTri_runLayered_append, shiTri_runLayered_append, e1, e2,
          shiTri_cast_runLayered, shiTri_cast_runLayered, shiTri_cast_runLayered,
          shiTri_nat_runLayered, shiTri_nat_runLayered]
       done)
    | (rw [shiTri_runLayered_append, shiTri_runLayered_append, e1, e2,
          shiTri_cast_runLayered, shiTri_cast_runLayered, shiTri_cast_runLayered,
          shiTri_nat_runLayered, shiTri_nat_runLayered]
       rfl
       done)
    | (simp only [shiTri_runLayered_append, e1, e2,
          shiTri_cast_runLayered, shiTri_nat_runLayered]
       done)
