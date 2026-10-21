-- Prove2me | solution 1 for TokenQueue.ProductForm.eq_5_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T07:45:39.026272+00:00
-- url     : https://prove2.me/submissions/74bdba4d-1b03-427f-9579-37a5520b6ff1

import Mathlib
import Definitions.Def_TokenQueue_ProductForm_Model

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace TQLib

open TokenQueue.ProductForm Finset

theorem prod_fin_eq_mapIdx {α β : Type} [CommMonoid β] (l : List α) (F : ℕ → α → β) :
    ∏ j : Fin l.length, F j (l.get j) = (l.mapIdx F).prod := by
  rw [List.mapIdx_eq_ofFn, List.prod_ofFn]

theorem prod_fin_append_single {α β : Type} [CommMonoid β] (l : List α) (a : α)
    (F : ℕ → α → β) :
    ∏ j : Fin (l ++ [a]).length, F j ((l ++ [a]).get j) =
      (∏ j : Fin l.length, F j (l.get j)) * F l.length a := by
  rw [prod_fin_eq_mapIdx, prod_fin_eq_mapIdx, List.mapIdx_append]
  simp

theorem prod_fin_congr_len {α β : Type} [CommMonoid β] (l : List α) (F G : ℕ → α → β)
    (h : ∀ j (hj : j < l.length), F j (l.get ⟨j, hj⟩) = G j (l.get ⟨j, hj⟩)) :
    ∏ j : Fin l.length, F j (l.get j) = ∏ j : Fin l.length, G j (l.get j) := by
  apply Finset.prod_congr rfl
  intro j _
  exact h j j.2

variable {C T : Type} [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T]

theorem toks_append (x y : List (T × ℕ)) : toks (x ++ y) = toks x ++ toks y := by
  simp [toks]

theorem toks_length (x : List (T × ℕ)) : (toks x).length = x.length := by simp [toks]

theorem kfun_nil (P : Params C T) : kfun P [] = 0 := by simp [kfun]

theorem kfun_append_single (P : Params C T) (l : List T) (a : T) :
    kfun P (l ++ [a]) = kfun P l + P.s (l ++ [a]) := by
  unfold kfun
  rw [List.length_append, List.length_singleton, Finset.sum_range_succ]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    simp only [mem_range] at hj
    rw [List.take_append_of_le_length (by omega)]
  · rw [List.take_of_length_le (by simp)]

theorem piLam_nil (P : Params C T) : piLam P [] = 1 := by simp [piLam]

theorem piK_nil (P : Params C T) : piK P [] = 1 := by simp [piK]

theorem piLam_append_single (P : Params C T) (l : List T) (a : T) :
    piLam P (l ++ [a]) = piLam P l * lamTok P l.toFinset a := by
  unfold piLam
  rw [prod_fin_append_single (F := fun j b => lamTok P ((l ++ [a]).take j).toFinset b)]
  congr 1
  · apply Finset.prod_congr rfl
    intro j _
    rw [List.take_append_of_le_length (by have := j.2; omega)]
  · simp

theorem piK_append_single (P : Params C T) (l : List T) (a : T) :
    piK P (l ++ [a]) = piK P l * kfun P (l ++ [a]) := by
  unfold piK
  rw [prod_fin_append_single (F := fun j _ => kfun P ((l ++ [a]).take (j + 1)))]
  congr 1
  · apply Finset.prod_congr rfl
    intro j _
    rw [List.take_append_of_le_length (by have := j.2; omega)]
  · rw [List.take_of_length_le (by simp)]

theorem modLast_nil (f : ℕ → ℕ) : modLast f ([] : List (T × ℕ)) = [] := rfl

theorem modLast_append_single (f : ℕ → ℕ) (l : List (T × ℕ)) (t : T) (n : ℕ) :
    modLast f (l ++ [(t, n)]) = l ++ [(t, f n)] := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    cases l with
    | nil => rfl
    | cons q l' =>
      show modLast f (p :: q :: (l' ++ [(t, n)])) = _
      rw [modLast, ← List.cons_append, ih]; rfl

theorem modLast_eq (f : ℕ → ℕ) (l : List (T × ℕ)) (hl : l ≠ []) :
    modLast f l = l.dropLast ++ [((l.getLast hl).1, f (l.getLast hl).2)] := by
  conv_lhs => rw [← List.dropLast_append_getLast hl]
  rw [modLast_append_single]

theorem toks_modLast (f : ℕ → ℕ) (l : List (T × ℕ)) : toks (modLast f l) = toks l := by
  rcases eq_or_ne l [] with rfl | hl
  · rfl
  · conv_rhs => rw [← List.dropLast_append_getLast hl]
    rw [modLast_eq f l hl, toks_append, toks_append]; rfl

theorem length_modLast (f : ℕ → ℕ) (l : List (T × ℕ)) : (modLast f l).length = l.length := by
  rw [← toks_length, toks_modLast, toks_length]

theorem phi_append (x y : List (T × ℕ)) : phi (x ++ y) = phi x + phi y := by
  simp [phi]; ring

theorem phi_single (t : T) (n : ℕ) : phi [(t, n)] = 1 + n := by simp [phi]

theorem prodEta_succ (P : Params C T) (m : ℕ) :
    ∏ j ∈ Icc 1 (m + 1), (P.eta j)⁻¹ = (∏ j ∈ Icc 1 m, (P.eta j)⁻¹) * (P.eta (m + 1))⁻¹ := by
  exact Finset.prod_Icc_succ_top (by omega) _

theorem alphaProd_append_single (P : Params C T) (y : List (T × ℕ)) (t : T) (n : ℕ) :
    ∏ j : Fin (y ++ [(t, n)]).length,
        alpha P ((toks (y ++ [(t, n)])).take (j + 1)) ^ ((y ++ [(t, n)]).get j).2 =
      (∏ j : Fin y.length, alpha P ((toks y).take (j + 1)) ^ (y.get j).2) *
        alpha P (toks y ++ [t]) ^ n := by
  have h := prod_fin_append_single y (t, n)
    (fun j p => alpha P ((toks (y ++ [(t, n)])).take (j + 1)) ^ p.2)
  simp only at h
  rw [h]
  congr 1
  · apply Finset.prod_congr rfl
    intro j _
    rw [toks_append, List.take_append_of_le_length (by rw [toks_length]; have := j.2; omega)]
  · rw [toks_append, List.take_of_length_le (by simp [toks_length])]
    rfl

theorem weightL_nil (P : Params C T) : weightL P [] = 1 := by
  unfold weightL
  rw [show toks ([] : List (T × ℕ)) = [] from rfl, piLam_nil, piK_nil]
  simp [phi]

/-- Adding one customer to the last portion. -/
theorem weightL_succ_last (P : Params C T) (y : List (T × ℕ)) (t : T) (n : ℕ) :
    weightL P (y ++ [(t, n + 1)]) =
      weightL P (y ++ [(t, n)]) * alpha P (toks y ++ [t]) *
        (P.eta (phi (y ++ [(t, n)]) + 1))⁻¹ := by
  unfold weightL
  rw [alphaProd_append_single, alphaProd_append_single]
  have htk : toks (y ++ [(t, n + 1)]) = toks (y ++ [(t, n)]) := by simp [toks]
  have hphi : phi (y ++ [(t, n + 1)]) = phi (y ++ [(t, n)]) + 1 := by
    simp [phi_append, phi_single]; ring
  rw [htk, hphi, prodEta_succ, pow_succ]
  ring

/-- Appending a new token with an empty portion. -/
theorem weightL_append_new (P : Params C T) (y : List (T × ℕ)) (t : T) :
    weightL P (y ++ [(t, 0)]) =
      weightL P y * (lamTok P (toks y).toFinset t / kfun P (toks y ++ [t])) *
        (P.eta (phi y + 1))⁻¹ := by
  unfold weightL
  rw [alphaProd_append_single]
  have htk : toks (y ++ [(t, 0)]) = toks y ++ [t] := by simp [toks]
  have hphi : phi (y ++ [(t, 0)]) = phi y + 1 := by
    simp [phi_append, phi_single]
  rw [htk, hphi, prodEta_succ, piLam_append_single, piK_append_single, pow_zero]
  rw [mul_div_mul_comm]
  ring

end TQLib

open TQLib TokenQueue.ProductForm Finset

namespace TQLib

variable {C T : Type} [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T]

theorem take_succ_split (x : List (T × ℕ)) (k : ℕ) (hk : k < x.length) :
    x.take (k + 1) = x.take k ++ [(x[k].1, x[k].2)] := by
  rw [← List.take_append_getElem hk]

theorem nAt_succ (x : List (T × ℕ)) (k : ℕ) (hk : k < x.length) : nAt x (k + 1) = x[k].2 := by
  simp [nAt, List.getD_eq_getElem?_getD, hk]

theorem nAt_zero (x : List (T × ℕ)) : nAt x 0 = 0 := by simp [nAt]

theorem phi_modLast_take_sub (x : List (T × ℕ)) (k n : ℕ) (hk : k ≤ x.length)
    (hn : n ≤ nAt x k) : phi (modLast (· - n) (x.take k)) + n = phi (x.take k) := by
  cases k with
  | zero => simp [nAt_zero] at hn; subst hn; simp [modLast_nil]
  | succ k =>
    rw [nAt_succ x k (by omega)] at hn
    rw [take_succ_split x k (by omega), modLast_append_single, phi_append, phi_append,
      phi_single, phi_single]
    omega

theorem phi_modLast_add (l : List (T × ℕ)) (c : ℕ) (hl : l ≠ []) :
    phi (modLast (· + c) l) = phi l + c := by
  rw [modLast_eq _ l hl]
  conv_rhs => rw [← List.dropLast_append_getLast hl]
  rw [phi_append, phi_append, phi_single, phi_single]
  omega

theorem toks_take (x : List (T × ℕ)) (k : ℕ) : toks (x.take k) = pre x k := by
  simp [toks, pre, List.map_take]

theorem muTok_insert (P : Params C T) (A B : List (T × ℕ)) (t : T) (n : ℕ) (m : ℕ)
    (hA : A.length = m) :
    muTok P (A ++ (t, n) :: B) m = P.eta (phi (A ++ (t, n) :: B)) * P.s (toks A ++ [t]) := by
  unfold muTok
  congr 2
  rw [toks_append, List.take_append, toks_length, hA, List.take_of_length_le (by rw [toks_length]; omega)]
  simp [toks]

theorem kfun_diff (P : Params C T) (l : List T) (t : T) :
    P.s (l ++ [t]) = kfun P (l ++ [t]) - kfun P l := by
  rw [kfun_append_single]; ring

end TQLib

theorem solution {C T : Type} [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T]
    (P : Params C T) (x : State T) :
    (∀ t : T, t ∉ toks x.1 → ∀ k ≤ x.1.length, ∀ n ≤ nAt x.1 k,
      phi (release x.1 k n t) = phi x.1 + 1 ∧
      muTok P (release x.1 k n t) k =
        P.eta (phi x.1 + 1) * (kfun P (pre x.1 k ++ [t]) - kfun P (pre x.1 k))) ∧
    (∀ j : Fin x.1.length, ∀ k ≤ j.val, ∀ n ≤ nAt x.1 k,
      phi (shift x.1 (j.val + 1) k n (x.1.get j).1) = phi x.1 + 1 ∧
      muTok P (shift x.1 (j.val + 1) k n (x.1.get j).1) k =
        P.eta (phi x.1 + 1) * (kfun P (pre x.1 k ++ [(x.1.get j).1]) - kfun P (pre x.1 k))) := by
  obtain ⟨x, -⟩ := x
  simp only
  constructor
  · intro t _ k hk n hn
    have hphi : phi (release x k n t) = phi x + 1 := by
      unfold release
      rw [phi_append, ← List.singleton_append, phi_append, phi_single]
      have := phi_modLast_take_sub x k n hk hn
      have hx : phi x = phi (x.take k) + phi (x.drop k) := by
        rw [← phi_append, List.take_append_drop]
      omega
    refine ⟨hphi, ?_⟩
    rw [← hphi]
    unfold release
    rw [muTok_insert P _ _ t n k (by rw [length_modLast]; simp; omega), toks_modLast, toks_take,
      kfun_diff]
  · intro j k hk n hn
    have hj := j.2
    have hlen := hk
    by_cases hkj : k + 1 < j.val + 1
    · -- general shift: k < j
      have hphi : phi (shift x (j.val + 1) k n (x.get j).1) = phi x + 1 := by
        unfold shift
        rw [if_pos hkj]
        simp only [Nat.add_sub_cancel]
        have hM : (x.take j.val).drop k ≠ [] := by
          apply List.ne_nil_of_length_pos; simp; omega
        rw [phi_append, phi_append, ← List.singleton_append, phi_append, phi_single,
          phi_modLast_add _ _ hM]
        have h1 := phi_modLast_take_sub x k n (by omega) hn
        have hx : phi x = phi (x.take k) + phi ((x.take j.val).drop k) + phi [x[j.val]] +
            phi (x.drop (j.val + 1)) := by
          rw [← phi_append, ← phi_append, ← phi_append]
          have e1 : x.take k ++ (x.take j.val).drop k = x.take j.val := by
            rw [show x.take k = (x.take j.val).take k by rw [List.take_take]; congr 1; omega]
            exact List.take_append_drop _ _
          rw [e1, List.take_append_getElem, List.take_append_drop]
        have hn' : nAt x (j.val + 1) = x[j.val].2 := nAt_succ x j.val hj
        have hs : phi [x[j.val]] = 1 + x[j.val].2 := by simp [phi]
        omega
      refine ⟨hphi, ?_⟩
      rw [← hphi]
      unfold shift
      rw [if_pos hkj, List.append_assoc, List.cons_append]
      rw [muTok_insert P _ _ _ n k (by rw [length_modLast]; simp; omega), toks_modLast, toks_take,
        kfun_diff]
    · have hkj' : j.val = k := by omega
      have hk' : k < x.length := by omega
      rw [hkj']
      have hphi : phi (shift x (k + 1) k n (x.get j).1) = phi x + 1 := by
        unfold shift
        rw [if_neg (lt_irrefl _)]
        rw [phi_append, ← List.singleton_append, phi_append, phi_single]
        have h1 := phi_modLast_take_sub x k n (by omega) hn
        have hx : phi x = phi (x.take k) + phi [x[k]] + phi (x.drop (k + 1)) := by
          rw [← phi_append, ← phi_append, List.take_append_getElem, List.take_append_drop]
        have hn' : nAt x (k + 1) = x[k].2 := nAt_succ x k hk'
        have hs : phi [x[k]] = 1 + x[k].2 := by simp [phi]
        omega
      refine ⟨hphi, ?_⟩
      rw [← hphi]
      unfold shift
      rw [if_neg (lt_irrefl _)]
      rw [muTok_insert P _ _ _ _ k (by rw [length_modLast]; simp; omega), toks_modLast, toks_take,
        kfun_diff]
