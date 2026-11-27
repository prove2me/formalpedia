-- Prove2me | solution 1 for UnaryQuadraticKKT.Hardness.unary_cls_reduction_eventually
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T04:10:05.616636+00:00
-- url     : https://prove2.me/submissions/225b11d7-e21d-49bd-b43e-edb0f1fae12a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UnaryQuadraticKKT_Hardness_Output
import Definitions.Def_LinearChoresCLS_EpsKKT
import Theorems.Thm_LinearChoresCLS_unary_to_epsQKKT_reduction
import Theorems.Thm_LinearChoresCLS_epsQKKT_cls_reduction_eventually
import Theorems.Thm_ConstrSOSP_searchReduces_trans

set_option autoImplicit false

namespace UQE
open CookPvsNP

section tm
variable {Γ : Type} (M : TM Γ)

theorem step_tape_len (c : Cfg Γ M.Q) :
    (M.step c).left.length + (M.step c).right.length ≤ c.left.length + c.right.length + 1 := by
  unfold TM.step
  split
  · exact Nat.le_add_right _ _
  · obtain ⟨q', s', h⟩ := M.δ c.state c.head
    cases h with
    | right =>
        simp only [List.length_cons, List.length_tail]
        cases c.right with
        | nil => simp
        | cons b r => simp; omega
    | left =>
        cases c.left with
        | nil => simp
        | cons a x' => simp; omega

theorem run_tape_len (n : ℕ) (c : Cfg Γ M.Q) :
    (M.run n c).left.length + (M.run n c).right.length ≤ n + c.left.length + c.right.length := by
  induction n generalizing c with
  | zero => simp [TM.run]
  | succ n ih =>
      have hrun : M.run (Nat.succ n) c = M.step (M.run n c) := by
        show M.step^[Nat.succ n] c = M.step (M.step^[n] c)
        exact Function.iterate_succ_apply' M.step n c
      rw [hrun]
      have hstep := step_tape_len M (M.run n c)
      have ih' := ih c
      omega

theorem output_length_le (n : ℕ) (w : List Γ) :
    (M.output (M.run n (M.init w))).length ≤ n + w.length + 1 := by
  have hdrop : ∀ c : Cfg Γ M.Q, ((c.head :: c.right).reverse.dropWhile Option.isNone).length
      ≤ 1 + c.right.length := by
    intro c
    have h := List.length_dropWhile_le Option.isNone (c.head :: c.right).reverse
    have h' : (c.head :: c.right).reverse.length = c.right.length + 1 := by
      simp only [List.length_reverse, List.length_cons]
    omega
  have hout : ∀ c : Cfg Γ M.Q, (M.output c).length ≤ 1 + c.right.length := by
    intro c
    have h2 := hdrop c
    simpa [TM.output, add_comm] using h2
  have hinit : (M.init w).left.length + (M.init w).right.length ≤ w.length := by
    simp [TM.init]
  have hrun := run_tape_len M n (M.init w)
  have hc := hout (M.run n (M.init w))
  omega

end tm

theorem polytime_len_le {A B : Type} {f : List A → List B} (hf : PolyTimeComputable f) :
    ∃ k : ℕ, ∀ x, (f x).length ≤ x.length ^ k + k + x.length + 1 := by
  obtain ⟨Γ, _, ι₁, ι₂, M, k, hM⟩ := hf
  refine ⟨k, fun x => ?_⟩
  have h := (hM x).2
  have hl := output_length_le M (x.length ^ k + k) (x.map ι₁)
  rw [h] at hl
  simpa using hl

theorem poly_bound (h : Polynomial ℕ) : ∃ k : ℕ, ∀ s : ℕ, h.eval s ≤ (s + 1) ^ k + k := by
  refine ⟨h.natDegree + h.eval 1, fun s => ?_⟩
  have h1 : h.eval s ≤ h.eval 1 * (s + 1) ^ h.natDegree := by
    rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range, Finset.sum_mul]
    refine Finset.sum_le_sum (fun i hi => ?_)
    simp only [one_pow, mul_one]
    have hi' : i ≤ h.natDegree := by simpa [Nat.lt_succ_iff] using hi
    exact Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (Nat.le_succ s) i).trans
      (Nat.pow_le_pow_right (Nat.succ_pos s) hi'))
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs; simp at h1 ⊢; omega
  · have h3 : h.eval 1 ≤ (s + 1) ^ h.eval 1 :=
      (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left (by omega) _)
    calc h.eval s ≤ h.eval 1 * (s + 1) ^ h.natDegree := h1
      _ ≤ (s + 1) ^ h.eval 1 * (s + 1) ^ h.natDegree := Nat.mul_le_mul_right _ h3
      _ = (s + 1) ^ (h.natDegree + h.eval 1) := by rw [← pow_add, Nat.add_comm (h.eval 1)]
      _ ≤ _ := Nat.le_add_right _ _

open Polynomial in
theorem poly_le (kf kg K : ℕ) : ∃ b : ℕ, ∀ x : ℕ,
    (x + 1 + ((x ^ kf + kf + x + 1 + 1) ^ K + K)) ^ kg + kg + (x + 1 + ((x ^ kf + kf + x + 1 + 1) ^ K + K)) + 1 ≤
      (x + 1) ^ b + b := by
  set q : Polynomial ℕ := X + 1 + ((X ^ kf + C kf + X + 1 + 1) ^ K + C K)
  set h : Polynomial ℕ := q ^ kg + C kg + q + 1
  obtain ⟨b, hb⟩ := poly_bound h
  refine ⟨b, fun x => ?_⟩
  have := hb x
  simpa [h, q] using this

end UQE

open NetworkEquilibriumCLS.LinearNash UnaryQuadraticKKT.Hardness in
theorem solution : ∃ K : ℕ, ∀ b : ℕ, K ≤ b → SearchReduces (bounded unarySearch b) clsSearch := by
  obtain ⟨f, g, hf, hg, hred⟩ := LinearChoresCLS.unary_to_epsQKKT_reduction
  obtain ⟨K, hK⟩ := LinearChoresCLS.epsQKKT_cls_reduction_eventually
  obtain ⟨kf, hkf⟩ := UQE.polytime_len_le hf
  obtain ⟨kg, hkg⟩ := UQE.polytime_len_le hg
  obtain ⟨b0, hb0⟩ := UQE.poly_le kf kg K
  refine ⟨b0, fun b hb => ConstrSOSP.searchReduces_trans _ _ _ ?_ (hK K le_rfl)⟩
  refine ⟨f, g, hf, hg, fun s hs => ⟨(hred s hs).1, fun t ht => ⟨(hred s hs).2 t ht.1, ?_⟩⟩⟩
  have ht2 := ht.2
  have h1 := hkf s
  have h2 := hkg (s.map (some ∘ Sum.inl) ++ none :: t.map (some ∘ Sum.inr))
  simp only [List.length_append, List.length_map, List.length_cons] at h2
  set x := s.length
  have ht3 : t.length ≤ (x ^ kf + kf + x + 1 + 1) ^ K + K := by
    refine ht2.trans (Nat.add_le_add_right (Nat.pow_le_pow_left (by omega) K) K)
  have hm : x + (t.length + 1) ≤ x + 1 + ((x ^ kf + kf + x + 1 + 1) ^ K + K) := by omega
  have h3 : (x + (t.length + 1)) ^ kg ≤ (x + 1 + ((x ^ kf + kf + x + 1 + 1) ^ K + K)) ^ kg :=
    Nat.pow_le_pow_left hm kg
  have h4 := hb0 x
  have h5 : (x + 1) ^ b0 + b0 ≤ (x + 1) ^ b + b :=
    Nat.add_le_add (Nat.pow_le_pow_right (by omega) hb) hb
  omega
