-- Prove2me | solution 1 for TokenQueue.ProductForm.pi_k_rearrangement
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T07:43:25.941653+00:00
-- url     : https://prove2.me/submissions/d2f719c7-55cd-4125-bbaf-eb98d3c6816c

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

theorem piK_range (P : Params C T) (l : List T) :
    piK P l = ∏ m ∈ range l.length, kfun P (l.take (m + 1)) := by
  unfold piK
  exact Fin.prod_univ_eq_prod_range (fun m => kfun P (l.take (m + 1))) l.length

theorem pik_rearr (P : Params C T) (h2 : Condition2 P) (hk : KPos P) (l : List T) (t : T)
    (hl : (t :: l).Nodup) (k : ℕ) (hki : k ≤ l.length) :
    piK P (l.take k ++ t :: l.drop k) =
      kfun P (l.take k ++ [t]) * piK P l *
        ∏ j ∈ Icc (k + 1) l.length, kfun P (l.take j ++ [t]) / kfun P (l.take j) := by
  set L := l.take k ++ t :: l.drop k with hL
  have hLlen : L.length = l.length + 1 := by
    simp [hL]; omega
  have hLperm : L.Perm (t :: l) := by
    have := List.perm_middle (a := t) (l₁ := l.take k) (l₂ := l.drop k)
    rwa [List.take_append_drop] at this
  have hLnd : L.Nodup := hLperm.nodup_iff.mpr hl
  have hlnd : l.Nodup := (List.nodup_cons.mp hl).2
  have hk' : (l.take k).length = k := by simp; omega
  rw [piK_range, piK_range, hLlen]
  rw [← Finset.prod_range_mul_prod_Ico _ (by omega : k + 1 ≤ l.length + 1),
    Finset.prod_range_succ]
  rw [← Finset.prod_range_mul_prod_Ico _ hki]
  -- the first k factors agree
  have hA : ∏ m ∈ range k, kfun P (L.take (m + 1)) = ∏ m ∈ range k, kfun P (l.take (m + 1)) := by
    apply Finset.prod_congr rfl
    intro m hm
    simp only [mem_range] at hm
    rw [hL, List.take_append_of_le_length (by rw [hk']; omega)]
    rw [List.take_take]; congr 2; omega
  have hB : kfun P (L.take (k + 1)) = kfun P (l.take k ++ [t]) := by
    rw [hL, List.take_append, hk', List.take_of_length_le (by omega)]
    simp
  -- factors after position k: rearrangement by Condition 2
  have hC : ∏ m ∈ Ico (k + 1) (l.length + 1), kfun P (L.take (m + 1)) =
      ∏ m ∈ Ico k l.length, kfun P (l.take (m + 1) ++ [t]) := by
    rw [← Finset.prod_Ico_add' (fun m => kfun P (L.take (m + 1))) k l.length 1]
    apply Finset.prod_congr rfl
    intro m hm
    simp only [mem_Ico] at hm
    apply h2
    · exact hLnd.sublist (List.take_sublist _ _)
    · rw [hL, List.take_append, hk', List.take_of_length_le (by omega)]
      rw [show m + 1 + 1 - k = (m + 1 - k) + 1 by omega, List.take_succ_cons]
      have e : l.take (m + 1) = l.take k ++ (l.drop k).take (m + 1 - k) := by
        rw [← List.take_add]; congr 1; omega
      rw [e]
      exact List.perm_middle.trans (List.perm_append_singleton _ _).symm
  -- the quotient product telescopes against the tail of `piK l`
  have hD : (∏ m ∈ Ico k l.length, kfun P (l.take (m + 1))) *
      ∏ j ∈ Icc (k + 1) l.length, kfun P (l.take j ++ [t]) / kfun P (l.take j) =
      ∏ m ∈ Ico k l.length, kfun P (l.take (m + 1) ++ [t]) := by
    rw [← Finset.Ico_add_one_right_eq_Icc,
      ← Finset.prod_Ico_add' (fun j => kfun P (l.take j ++ [t]) / kfun P (l.take j)) k l.length 1,
      ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro m hm
    simp only [mem_Ico] at hm
    have hpos : 0 < kfun P (l.take (m + 1)) := by
      apply hk
      · exact hlnd.sublist (List.take_sublist _ _)
      · apply List.ne_nil_of_length_pos
        rw [List.length_take]; omega
    field_simp
  rw [hA, hB, hC, ← hD]
  ring

end TQLib

theorem solution {C T : Type} [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T]
    (P : Params C T) (h2 : Condition2 P) (hk : KPos P) (l : List T) (t : T)
    (hl : (t :: l).Nodup) (k : ℕ) (hki : k ≤ l.length) :
    piK P (l.take k ++ t :: l.drop k) =
      kfun P (l.take k ++ [t]) * piK P l *
        ∏ j ∈ Icc (k + 1) l.length, kfun P (l.take j ++ [t]) / kfun P (l.take j) :=
  pik_rearr P h2 hk l t hl k hki
