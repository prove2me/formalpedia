-- Prove2me | solution 1 for TokenQueue.ProductForm.eq_9
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T07:39:38.226226+00:00
-- url     : https://prove2.me/submissions/c3295b52-6f9a-4864-9359-89c17ab16a7b

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

theorem solution {C T : Type} [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T]
    (P : Params C T) (hS : P.Standing) (hk : KPos P) :
    lamTot P * weightL P [] = ∑ t, muTok P [(t, 0)] 0 * weightL P [(t, 0)] := by
  obtain ⟨-, hne, -, hz, h1, -, heta⟩ := hS
  have hw0 : weightL P [] = 1 := weightL_nil P
  have hterm : ∀ t, muTok P [(t, 0)] 0 * weightL P [(t, 0)] = lamTok P ∅ t := by
    intro t
    have hkt : 0 < kfun P [t] := hk [t] (List.nodup_singleton t) (by simp)
    have hks : kfun P [t] = P.s [t] := by simp [kfun]
    have he : 0 < P.eta 1 := heta 1 le_rfl
    have hw := weightL_append_new P [] t
    simp only [List.nil_append] at hw
    rw [hw, hw0]
    simp only [muTok, toks, phi, List.map_cons, List.map_nil, List.length_cons, List.length_nil,
      List.sum_cons, List.sum_nil, List.toFinset_nil, List.nil_append, List.take_succ_cons,
      List.take_zero]
    rw [hks] at hkt ⊢
    simp only [Nat.add_zero, zero_add]
    field_simp
  rw [hw0, mul_one, Finset.sum_congr rfl (fun t _ => hterm t)]
  -- eq (1) with S = ∅, and λ_{U(∅)} = 0
  have key : lamTot P - lamU P ∅ = ∑ t ∈ univ \ ∅, lamTok P ∅ t := by
    unfold lamTot lamU lamTok
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun c => P.tok c ⊆ ∅)
      (fun c => P.lam c * ∑ t ∈ univ \ ∅, P.assign c ∅ t)]
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun c => P.tok c ⊆ ∅) (fun c => P.lam c)]
    have hA : ∀ c ∈ univ.filter (fun c => P.tok c ⊆ ∅),
        P.lam c * ∑ t ∈ univ \ ∅, P.assign c ∅ t = 0 := by
      intro c hc
      simp only [mem_filter, mem_univ, true_and] at hc
      rw [Finset.sum_eq_zero, mul_zero]
      intro t _
      apply hz
      simp only [mem_sdiff, not_and, not_not]
      intro ht; exact hc ht
    have hB : ∀ c ∈ univ.filter (fun c => ¬ P.tok c ⊆ ∅),
        P.lam c * ∑ t ∈ univ \ ∅, P.assign c ∅ t = P.lam c := by
      intro c hc
      simp only [mem_filter, mem_univ, true_and] at hc
      have hne' : (P.tok c \ ∅).Nonempty := by
        rw [Finset.sdiff_nonempty]; exact hc
      have := h1 c ∅ hne'
      rw [Finset.sum_subset (s₁ := P.tok c \ ∅) (s₂ := univ \ ∅)] at this
      · rw [this, mul_one]
      · intro t ht; simp only [mem_sdiff, mem_univ, true_and] at ht ⊢; exact ht.2
      · intro t _ ht; exact hz c ∅ t ht
    rw [Finset.sum_congr rfl hA, Finset.sum_congr rfl hB]
    simp
  have hU : lamU P ∅ = 0 := by
    unfold lamU
    apply Finset.sum_eq_zero
    intro c hc
    simp only [mem_filter, mem_univ, true_and, Finset.subset_empty] at hc
    exact absurd hc (hne c).ne_empty
  rw [hU, sub_zero] at key
  rw [key]; simp
