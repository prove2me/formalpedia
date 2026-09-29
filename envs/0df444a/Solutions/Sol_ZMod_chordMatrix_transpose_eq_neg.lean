-- Prove2me | solution 1 for ZMod.chordMatrix_transpose_eq_neg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/ad5466d2-a0b3-5c69-85d2-e2794cb74bee

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ZMod_chordMatrix_transpose_eq_neg

namespace SolChord

variable {N : ℕ} [NeZero N]

private lemma val_sub_cases {a b : ZMod N} (hab : a ≠ b) :
    (a - b).val = if b.val ≤ a.val then a.val - b.val else N + a.val - b.val := by
  rcases le_or_gt b.val a.val with h | h
  · simp only [h, if_true, ZMod.val_sub h]
  · simp only [not_le.mpr h, if_false]
    have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
    have hrw : a - b = -(b - a) := by ring
    rw [hrw, ZMod.neg_val, if_neg hba, ZMod.val_sub (le_of_lt h)]
    have hal : a.val < N := ZMod.val_lt _
    omega

private def σ (a b k : ZMod N) : ℤ :=
  if k ≠ a ∧ (k - a).val < (b - a).val then 1 else 0

omit [NeZero N] in
private lemma σ_shift (a b k c : ZMod N) : σ (a + c) (b + c) (k + c) = σ a b k := by
  unfold σ; congr 1; simp only [ne_eq, add_right_cancel_iff, add_sub_add_right_eq_sub]

omit [NeZero N] in
private lemma σ_sub (a b k : ZMod N) : σ a b k = σ 0 (b - a) (k - a) := by
  have := σ_shift (N := N) 0 (b - a) (k - a) a
  simp only [zero_add, sub_add_cancel] at this; exact this

private lemma σ_antisymm_four {x y z w : ZMod N}
    (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) :
    σ x y z - σ x y w + σ z w x - σ z w y = 0 := by

  rw [σ_sub x y z, σ_sub x y w, σ_sub z w x, σ_sub z w y]
  set Y := y - x with hYdef; set Z := z - x with hZdef; set W := w - x with hWdef
  have hY : Y ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  have hZ : Z ≠ 0 := sub_ne_zero.mpr (Ne.symm hxz)
  have hW : W ≠ 0 := sub_ne_zero.mpr (Ne.symm hxw)
  have hYZ : Y ≠ Z := fun h => hyz (by rw [hYdef, hZdef] at h; exact sub_left_injective h)
  have hYW : Y ≠ W := fun h => hyw (by rw [hYdef, hWdef] at h; exact sub_left_injective h)
  have hZW : Z ≠ W := fun h => hzw (by rw [hZdef, hWdef] at h; exact sub_left_injective h)

  have hwz : w - z = W - Z := by rw [hWdef, hZdef]; ring
  have hxz' : x - z = -Z := by rw [hZdef]; ring
  have hyz' : y - z = Y - Z := by rw [hYdef, hZdef]; ring
  rw [hwz, hxz', hyz']

  unfold σ
  simp only [ne_eq, hZ, not_false_eq_true, true_and, hW, sub_zero,
    neg_eq_zero, sub_eq_zero]
  have hYZ' : ¬(Y = Z) := hYZ
  simp only [hYZ', not_false_eq_true, true_and]

  rw [ZMod.neg_val, if_neg hZ,
    val_sub_cases (a := W) (b := Z) hZW.symm,
    val_sub_cases (a := Y) (b := Z) hYZ]
  have hYlt := ZMod.val_lt Y; have hZlt := ZMod.val_lt Z; have hWlt := ZMod.val_lt W
  have hY1 : 1 ≤ Y.val := Nat.one_le_iff_ne_zero.mpr ((ZMod.val_eq_zero Y).not.mpr hY)
  have hZ1 : 1 ≤ Z.val := Nat.one_le_iff_ne_zero.mpr ((ZMod.val_eq_zero Z).not.mpr hZ)
  have hW1 : 1 ≤ W.val := Nat.one_le_iff_ne_zero.mpr ((ZMod.val_eq_zero W).not.mpr hW)
  have hYZv : Y.val ≠ Z.val := fun h => hYZ (ZMod.val_injective _ h)
  have hYWv : Y.val ≠ W.val := fun h => hYW (ZMod.val_injective _ h)
  have hZWv : Z.val ≠ W.val := fun h => hZW (ZMod.val_injective _ h)
  split_ifs <;> omega

end SolChord

open SolChord in

theorem solution {m : ℕ} [NeZero m]
    (a b : Fin m → ZMod (2 * m))
    (hdist : Function.Injective (fun p : Fin m × Bool => bif p.2 then a p.1 else b p.1)) :
    let P : Matrix (Fin m) (Fin m) ℤ := fun i j =>
      (if a j ≠ a i ∧ (a j - a i).val < (b i - a i).val then (1 : ℤ) else 0) -
      (if b j ≠ a i ∧ (b j - a i).val < (b i - a i).val then (1 : ℤ) else 0)
    P.transpose = -P := by
  intro P
  haveI : NeZero (2 * m) := ⟨Nat.mul_ne_zero two_ne_zero (NeZero.ne m)⟩
  have hd : ∀ (p q : Fin m × Bool), p ≠ q →
      (bif p.2 then a p.1 else b p.1) ≠ (bif q.2 then a q.1 else b q.1) :=
    fun p q h heq => h (hdist heq)
  have haa : ∀ i j, i ≠ j → a i ≠ a j := fun i j h =>
    hd (i, true) (j, true) (by simp [h])
  have hab : ∀ i j, a i ≠ b j := fun i j =>
    hd (i, true) (j, false) (by simp)
  have hbb : ∀ i j, i ≠ j → b i ≠ b j := fun i j h =>
    hd (i, false) (j, false) (by simp [h])
  funext i j
  simp only [Matrix.transpose_apply, Matrix.neg_apply, P]
  by_cases hij : i = j
  · subst hij
    simp only [ne_eq, not_true_eq_false, false_and, if_false, sub_self,
      lt_irrefl, and_false, neg_zero]
  · have key : σ (a i) (b i) (a j) - σ (a i) (b i) (b j) +
        σ (a j) (b j) (a i) - σ (a j) (b j) (b i) = 0 :=
      σ_antisymm_four (N := 2 * m) (hab i i) (haa i j hij) (hab i j)
        (hab j i).symm (hbb i j hij) (hab j j)
    unfold σ at key
    linarith

end S_ZMod_chordMatrix_transpose_eq_neg
end P2MW
export P2MW.S_ZMod_chordMatrix_transpose_eq_neg (solution)
