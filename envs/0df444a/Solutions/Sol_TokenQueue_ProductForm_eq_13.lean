-- Prove2me | solution 1 for TokenQueue.ProductForm.eq_13
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T08:13:52.817605+00:00
-- url     : https://prove2.me/submissions/5ab59952-9af9-4832-a7c0-a2b6d21700b6

import Theorems.Thm_TokenQueue_ProductForm_pi_k_rearrangement
import Theorems.Thm_TokenQueue_ProductForm_eq_29
import Theorems.Thm_TokenQueue_ProductForm_eq_5_7
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


theorem mu_eq (P : Params C T) (x : List (T × ℕ)) :
    mu P x = P.eta (phi x) * kfun P (toks x) := by
  unfold mu muTok kfun
  rw [Finset.mul_sum]
  simp [toks]

theorem lamTok_nonneg (P : Params C T) (hS : P.Standing) (S : Finset T) (t : T) :
    0 ≤ lamTok P S t := by
  unfold lamTok
  exact Finset.sum_nonneg fun c _ => mul_nonneg (hS.1 c).le (hS.2.2.1 c S t)

theorem lamU_nonneg (P : Params C T) (hS : P.Standing) (S : Finset T) : 0 ≤ lamU P S := by
  unfold lamU
  exact Finset.sum_nonneg fun c _ => (hS.1 c).le

theorem lamU_le (P : Params C T) (hS : P.Standing) (S : Finset T) : lamU P S ≤ lamTot P := by
  unfold lamU lamTot
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun c _ _ => (hS.1 c).le)

theorem assign_le_one (P : Params C T) (hS : P.Standing) (c : C) (S : Finset T) (t : T) :
    P.assign c S t ≤ 1 := by
  obtain ⟨-, -, h0, hz, h1, -, -⟩ := hS
  by_cases ht : t ∈ P.tok c \ S
  · have hne : (P.tok c \ S).Nonempty := ⟨t, ht⟩
    rw [← h1 c S hne]
    exact Finset.single_le_sum (fun u _ => h0 c S u) ht
  · rw [hz c S t ht]; exact zero_le_one

theorem lamTok_le (P : Params C T) (hS : P.Standing) (S : Finset T) (t : T) :
    lamTok P S t ≤ lamTot P := by
  unfold lamTok lamTot
  apply Finset.sum_le_sum
  intro c _
  calc P.lam c * P.assign c S t ≤ P.lam c * 1 :=
        mul_le_mul_of_nonneg_left (assign_le_one P hS c S t) (hS.1 c).le
    _ = P.lam c := mul_one _

theorem kfun_nonneg (P : Params C T) (hS : P.Standing) (l : List T) : 0 ≤ kfun P l := by
  unfold kfun
  exact Finset.sum_nonneg fun j _ => hS.2.2.2.2.2.1 _

theorem piLam_nonneg (P : Params C T) (hS : P.Standing) (l : List T) : 0 ≤ piLam P l := by
  unfold piLam
  exact Finset.prod_nonneg fun j _ => lamTok_nonneg P hS _ _

theorem piK_nonneg (P : Params C T) (hS : P.Standing) (l : List T) : 0 ≤ piK P l := by
  unfold piK
  exact Finset.prod_nonneg fun j _ => kfun_nonneg P hS _

theorem weightL_nonneg (P : Params C T) (hS : P.Standing) (x : List (T × ℕ)) :
    0 ≤ weightL P x := by
  unfold weightL
  apply mul_nonneg
  apply mul_nonneg
  · exact div_nonneg (piLam_nonneg P hS _) (piK_nonneg P hS _)
  · exact Finset.prod_nonneg fun j _ => pow_nonneg
      (div_nonneg (lamU_nonneg P hS _) (kfun_nonneg P hS _)) _
  · exact Finset.prod_nonneg fun j hj => inv_nonneg.mpr
      (hS.2.2.2.2.2.2 j (Finset.mem_Icc.mp hj).1).le

theorem kfun_pos_prefix (P : Params C T) (hk : KPos P) (l : List T) (hl : l.Nodup) (m : ℕ)
    (hm : m < l.length) : 0 < kfun P (l.take (m + 1)) := by
  apply hk
  · exact hl.sublist (List.take_sublist _ _)
  · apply List.ne_nil_of_length_pos; rw [List.length_take]; omega

theorem piK_pos (P : Params C T) (hk : KPos P) (l : List T) (hl : l.Nodup) : 0 < piK P l := by
  unfold piK
  exact Finset.prod_pos fun j _ => kfun_pos_prefix P hk l hl j j.2

end TQLib

open TQLib TokenQueue.ProductForm Finset

namespace TQLib

variable {C T : Type} [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T]

noncomputable def AP (P : Params C T) (y : List (T × ℕ)) : ℝ :=
  ∏ j : Fin y.length, alpha P ((toks y).take (j + 1)) ^ (y.get j).2

theorem weightL_AP (P : Params C T) (y : List (T × ℕ)) :
    weightL P y = piLam P (toks y) / piK P (toks y) * AP P y *
      ∏ j ∈ Icc 1 (phi y), (P.eta j)⁻¹ := rfl

theorem AP_append (P : Params C T) (Y Z : List (T × ℕ)) :
    AP P (Y ++ Z) = AP P Y *
      ∏ j ∈ range Z.length, alpha P (toks Y ++ (toks Z).take (j + 1)) ^ nAt Z (j + 1) := by
  unfold AP
  have h := prod_fin_eq_mapIdx (Y ++ Z) (fun j p => alpha P ((toks (Y ++ Z)).take (j + 1)) ^ p.2)
  rw [h, List.mapIdx_append, List.prod_append]
  congr 1
  · have h' := prod_fin_eq_mapIdx Y (fun j p => alpha P ((toks Y).take (j + 1)) ^ p.2)
    rw [h']
    congr 1
    apply List.ext_getElem (by simp)
    intro m h1 h2
    have hm : m + 1 ≤ (toks Y).length := by rw [toks_length]; simp at h1; omega
    simp only [List.getElem_mapIdx, toks_append, List.take_append_of_le_length hm]
  · have h' := prod_fin_eq_mapIdx Z
      (fun j p => alpha P ((toks (Y ++ Z)).take (j + Y.length + 1)) ^ p.2)
    rw [← h', ← Fin.prod_univ_eq_prod_range
      (fun j => alpha P (toks Y ++ (toks Z).take (j + 1)) ^ nAt Z (j + 1))]
    apply Finset.prod_congr rfl
    intro j _
    rw [nAt_succ Z j j.2, toks_append, List.take_append, toks_length,
      List.take_of_length_le (by rw [toks_length]; omega)]
    simp only [List.get_eq_getElem]
    rw [show (j : ℕ) + Y.length + 1 - Y.length = j + 1 by omega]

theorem nAt_drop (x : List (T × ℕ)) (k j : ℕ) : nAt (x.drop k) (j + 1) = nAt x (k + j + 1) := by
  simp [nAt, List.getD_eq_getElem?_getD, List.map_drop, List.getElem?_drop]

theorem toks_drop (x : List (T × ℕ)) (k : ℕ) : toks (x.drop k) = (toks x).drop k := by
  simp [toks, List.map_drop]

theorem AP_nil (P : Params C T) : AP P [] = 1 := by simp [AP]

theorem AP_append_single (P : Params C T) (y : List (T × ℕ)) (t : T) (n : ℕ) :
    AP P (y ++ [(t, n)]) = AP P y * alpha P (toks y ++ [t]) ^ n :=
  alphaProd_append_single P y t n

theorem AP_take_succ (P : Params C T) (x : List (T × ℕ)) (k : ℕ) (hk : k < x.length) :
    AP P (x.take (k + 1)) = AP P (x.take k) * alpha P ((toks x).take (k + 1)) ^ nAt x (k + 1) := by
  rw [take_succ_split x k hk, AP_append_single, nAt_succ x k hk, toks_take]
  congr 1
  rw [← List.take_append_getElem (by rw [toks_length]; exact hk)]
  simp [toks, pre]

theorem prod_Icc_eq_range {β : Type} [CommMonoid β] (f : ℕ → β) (k i : ℕ) :
    ∏ m ∈ Icc (k + 1) i, f m = ∏ j ∈ range (i - k), f (k + j + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range]
  rw [show i + 1 - (k + 1) = i - k by omega]
  apply Finset.prod_congr rfl
  intro j _
  congr 1; omega

theorem lamU_mono (P : Params C T) (hS : P.Standing) {S S' : Finset T} (h : S ⊆ S') :
    lamU P S ≤ lamU P S' := by
  unfold lamU
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact hc.trans h
  · intro c _ _; exact (hS.1 c).le

theorem key_ratio (U UT K KT : ℝ) (hU : 0 ≤ U) (hUT : U ≤ UT) :
    U / UT * (UT / KT) = U / KT := by
  rcases eq_or_lt_of_le (hU.trans hUT) with h | h
  · have : U = 0 := le_antisymm (h ▸ hUT) hU
    subst this; rw [← h]; simp
  · field_simp

theorem toFinset_append_single (l : List T) (t : T) :
    (l ++ [t]).toFinset = insert t l.toFinset := by
  ext a; simp [or_comm]

theorem alpha_perm (P : Params C T) (h2 : Condition2 P) {L L' : List T} (hnd : L.Nodup)
    (hp : L.Perm L') : alpha P L = alpha P L' := by
  unfold alpha
  rw [h2 L L' hnd hp, List.toFinset_eq_of_perm _ _ hp]

end TQLib

namespace TQLib

variable {C T : Type} [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T]

theorem final_alg13 (η KTk Kk bk Qb Λ lt HR aTk Q2 E Q1 Pi Hx Q3 Q4 : ℝ) (n : ℕ)
    (hη : η ≠ 0) (hKT : KTk ≠ 0) (hQ1 : Q1 ≠ 0) (hPi : Pi ≠ 0)
    (hH : bk ^ n * HR * aTk ^ n = Hx * (Kk / KTk) ^ n) (hQ : Qb * Q2 = Q1 * Q3 * Q4) :
    η * (KTk - Kk) * (bk ^ n * Qb) * (Λ * lt / (KTk * Pi * Q1) * (HR * aTk ^ n * Q2) * (E * η⁻¹))
      = lt * (Λ / Pi * (Hx * Q3) * E) * ((KTk - Kk) / KTk * Q4 * (Kk / KTk) ^ n) := by
  have e : η * (KTk - Kk) * (bk ^ n * Qb) *
      (Λ * lt / (KTk * Pi * Q1) * (HR * aTk ^ n * Q2) * (E * η⁻¹)) =
      (KTk - Kk) * Λ * lt * E * (KTk⁻¹ * Pi⁻¹ * Q1⁻¹) * (bk ^ n * HR * aTk ^ n) * (Qb * Q2) *
        (η * η⁻¹) := by
    rw [div_eq_mul_inv, mul_inv, mul_inv]; ring
  rw [e, hH, hQ, mul_inv_cancel₀ hη]
  have h1 := inv_mul_cancel₀ hQ1
  rw [div_eq_mul_inv Λ Pi, div_eq_mul_inv (KTk - Kk) KTk]
  linear_combination ((KTk - Kk) * Λ * lt * E * KTk⁻¹ * Pi⁻¹ * (Hx * (Kk / KTk) ^ n) * Q3 * Q4) * h1

theorem eq13_term (P : Params C T) (hS : P.Standing) (h1 : Condition1 P) (h2 : Condition2 P)
    (hk : KPos P) (xs : List (T × ℕ)) (hxs : (xs.map Prod.fst).Nodup) (t : T)
    (ht : t ∉ toks xs) (k : ℕ) (hki : k ≤ xs.length) (n : ℕ) (hn : n ≤ nAt xs k) :
    muTok P (release xs k n t) k * rfac P xs k n t * weightL P (release xs k n t) =
      lamTok P (toks xs).toFinset t * weightL P xs *
        ((kfun P ((toks xs).take k ++ [t]) - kfun P ((toks xs).take k)) /
            kfun P ((toks xs).take k ++ [t]) *
          (∏ j ∈ Icc (k + 1) (toks xs).length,
            (kfun P ((toks xs).take j) / kfun P ((toks xs).take j ++ [t])) ^ (nAt xs j + 1)) *
          (kfun P ((toks xs).take k) / kfun P ((toks xs).take k ++ [t])) ^ n) := by
  have e57 := (TokenQueue.ProductForm.eq_5_7 P ⟨xs, hxs⟩).1 t ht k hki n hn
  simp only at e57
  obtain ⟨hphi, hmu⟩ := e57
  set l := toks xs with hl
  have hlnd : l.Nodup := hxs
  have htl : (t :: l).Nodup := List.nodup_cons.mpr ⟨ht, hlnd⟩
  have hll : l.length = xs.length := toks_length xs
  set R := release xs k n t with hR
  have htR : toks R = l.take k ++ t :: l.drop k := by
    rw [hR]; unfold release
    rw [toks_append, toks_modLast, toks_take]
    simp [toks, pre, hl, List.map_drop]
  have hLperm : (l.take k ++ t :: l.drop k).Perm (l ++ [t]) := by
    have := List.perm_middle (a := t) (l₁ := l.take k) (l₂ := l.drop k)
    rw [List.take_append_drop] at this
    exact this.trans (List.perm_append_singleton t l).symm
  have hLnd : (l.take k ++ t :: l.drop k).Nodup :=
    hLperm.nodup_iff.mpr ((List.perm_append_singleton t l).nodup_iff.mpr htl)
  -- the factors of the weight of `R`
  have hpl : piLam P (toks R) = piLam P l * lamTok P l.toFinset t := by
    rw [htR, h1 _ _ hLnd hLperm, piLam_append_single]
  have hpk : piK P (toks R) = kfun P (l.take k ++ [t]) * piK P l *
      ∏ j ∈ Icc (k + 1) l.length, kfun P (l.take j ++ [t]) / kfun P (l.take j) := by
    rw [htR]
    exact TokenQueue.ProductForm.pi_k_rearrangement P h2 hk l t htl k (by omega)
  -- alpha-products
  set aT : ℕ → ℝ := fun m => alpha P (l.take m ++ [t]) with haT
  set a : ℕ → ℝ := fun m => alpha P (l.take m) with ha
  have hAR : AP P R = AP P (modLast (· - n) (xs.take k)) * aT k ^ n *
      ∏ m ∈ Icc (k + 1) l.length, aT m ^ nAt xs m := by
    have e : R = (modLast (· - n) (xs.take k) ++ [(t, n)]) ++ xs.drop k := by
      rw [hR]; unfold release; simp
    rw [e, AP_append, AP_append_single, toks_modLast, toks_take, prod_Icc_eq_range]
    congr 1
    rw [List.length_drop, hll]
    apply Finset.prod_congr rfl
    intro j hj
    simp only [mem_range] at hj
    rw [nAt_drop]
    congr 1
    have e1 : toks (modLast (· - n) (xs.take k) ++ [(t, n)]) = l.take k ++ [t] := by
      rw [toks_append, toks_modLast, toks_take]; rfl
    rw [e1, toks_drop, ← hl]
    simp only [haT]
    apply alpha_perm P h2
    · apply List.Nodup.sublist _ hLnd
      rw [List.append_assoc, List.singleton_append]
      exact (List.Sublist.refl _).append ((List.take_sublist _ _).cons_cons t)
    · rw [show l.take (k + j + 1) = l.take k ++ (l.drop k).take (j + 1) by
        rw [show k + j + 1 = k + (j + 1) by omega]; exact List.take_add]
      rw [List.append_assoc, List.append_assoc]
      exact List.Perm.append_left _ (List.perm_append_comm)
  have hAx : AP P xs = AP P (xs.take k) * ∏ m ∈ Icc (k + 1) l.length, a m ^ nAt xs m := by
    conv_lhs => rw [← List.take_append_drop k xs]
    rw [AP_append, prod_Icc_eq_range, List.length_drop, hll]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    rw [nAt_drop, toks_take, toks_drop, ← hl]
    simp only [ha, pre, ← hl]
    rw [show l.take (k + j + 1) = l.take k ++ (l.drop k).take (j + 1) by
        rw [show k + j + 1 = k + (j + 1) by omega]; exact List.take_add]
  -- positivity facts
  have hKT : ∀ m, 0 < kfun P (l.take m ++ [t]) := by
    intro m
    apply hk
    · rw [List.nodup_append]
      refine ⟨hlnd.sublist (List.take_sublist _ _), List.nodup_singleton t, ?_⟩
      intro u hu v hv huv
      simp only [List.mem_singleton] at hv
      subst hv; subst huv
      exact ht (List.mem_of_mem_take hu)
    · simp
  have hK : ∀ m, 1 ≤ m → m ≤ l.length → 0 < kfun P (l.take m) := by
    intro m hm1 hm2
    apply hk
    · exact hlnd.sublist (List.take_sublist _ _)
    · apply List.ne_nil_of_length_pos; rw [List.length_take]; omega
  have hUle : ∀ m, lamU P (l.take m).toFinset ≤ lamU P (insert t (l.take m).toFinset) :=
    fun m => lamU_mono P hS (Finset.subset_insert _ _)
  have hU0 : ∀ m, 0 ≤ lamU P (l.take m).toFinset := fun m => lamU_nonneg P hS _
  have haT' : ∀ m, aT m = lamU P (insert t (l.take m).toFinset) / kfun P (l.take m ++ [t]) := by
    intro m; simp only [haT, alpha, toFinset_append_single]
  have ha' : ∀ m, a m = lamU P (l.take m).toFinset / kfun P (l.take m) := by
    intro m; simp only [ha, alpha]
  have hbeta : ∀ m, 1 ≤ m → beta P xs m t =
      lamU P (l.take m).toFinset / lamU P (insert t (l.take m).toFinset) := by
    intro m hm; simp only [beta, pre, ← hl, if_neg (by omega : m ≠ 0)]
  -- the position-`k` relation
  have hH : beta P xs k t ^ n * AP P (modLast (· - n) (xs.take k)) * aT k ^ n =
      AP P (xs.take k) * (kfun P (l.take k) / kfun P (l.take k ++ [t])) ^ n := by
    cases k with
    | zero =>
      have : n = 0 := by simp [nAt] at hn; omega
      subst this; simp; rfl
    | succ k' =>
      have hk' : k' < xs.length := by omega
      rw [take_succ_split xs k' hk', modLast_append_single, AP_append_single, AP_append_single]
      rw [nAt_succ xs k' hk'] at hn
      have et : toks (xs.take k') ++ [xs[k'].1] = l.take (k' + 1) := by
        rw [toks_take, pre, ← hl, ← List.take_append_getElem (by rw [hll]; exact hk')]
        simp [hl, toks]
      rw [et]
      change _ * (_ * a (k' + 1) ^ _) * _ = _ * a (k' + 1) ^ _ * _
      rw [hbeta _ (by omega), haT', ha']
      have hKp := hK (k' + 1) (by omega) (by omega)
      have hKTp := hKT (k' + 1)
      set U := lamU P (l.take (k' + 1)).toFinset
      set UT := lamU P (insert t (l.take (k' + 1)).toFinset)
      set K := kfun P (l.take (k' + 1))
      set KT := kfun P (l.take (k' + 1) ++ [t])
      have hkr := key_ratio U UT K KT (hU0 _) (hUle _)
      have hsplit : (U / K) ^ xs[k'].2 = (U / K) ^ (xs[k'].2 - n) * (U / K) ^ n := by
        rw [← pow_add]; congr 1; omega
      rw [hsplit]
      have : (U / UT) ^ n * (UT / KT) ^ n = (U / K) ^ n * (K / KT) ^ n := by
        rw [← mul_pow, ← mul_pow, hkr]; congr 1; field_simp
      linear_combination (AP P (List.take k' xs) * (U / K) ^ (xs[k'].2 - n)) * this
  -- the product relation over positions `k+1,…,i`
  have hQ : (∏ m ∈ Icc (k + 1) l.length, beta P xs m t ^ nAt xs m) *
      (∏ m ∈ Icc (k + 1) l.length, aT m ^ nAt xs m) =
      (∏ m ∈ Icc (k + 1) l.length, kfun P (l.take m ++ [t]) / kfun P (l.take m)) *
      (∏ m ∈ Icc (k + 1) l.length, a m ^ nAt xs m) *
      ∏ m ∈ Icc (k + 1) l.length,
        (kfun P (l.take m) / kfun P (l.take m ++ [t])) ^ (nAt xs m + 1) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro m hm
    simp only [Finset.mem_Icc] at hm
    rw [hbeta m (by omega), haT', ha']
    have hKp := hK m (by omega) hm.2
    have hKTp := hKT m
    set U := lamU P (l.take m).toFinset
    set UT := lamU P (insert t (l.take m).toFinset)
    set K := kfun P (l.take m)
    set KT := kfun P (l.take m ++ [t])
    set e := nAt xs m
    have hkr := key_ratio U UT K KT (hU0 _) (hUle _)
    have h3 : (U / K) ^ e * (K / KT) ^ e = (U / KT) ^ e := by
      rw [← mul_pow]; congr 1; field_simp
    have h4 : KT / K * (K / KT) = 1 := by field_simp
    calc (U / UT) ^ e * (UT / KT) ^ e = (U / KT) ^ e := by rw [← mul_pow, hkr]
      _ = (U / K) ^ e * (K / KT) ^ e * (KT / K * (K / KT)) := by rw [h3, h4, mul_one]
      _ = KT / K * (U / K) ^ e * (K / KT) ^ (e + 1) := by ring
  -- assemble
  rw [hmu, weightL_AP, weightL_AP P xs, hpl, hpk, hAR, hAx, hphi, prodEta_succ]
  unfold rfac
  rw [← hll]
  change P.eta (phi xs + 1) * (kfun P (l.take k ++ [t]) - kfun P (l.take k)) * _ * _ = _
  set Qb := ∏ m ∈ Icc (k + 1) l.length, beta P xs m t ^ nAt xs m
  set Q2 := ∏ m ∈ Icc (k + 1) l.length, aT m ^ nAt xs m
  set Q1 := ∏ m ∈ Icc (k + 1) l.length, kfun P (l.take m ++ [t]) / kfun P (l.take m)
  set Q3 := ∏ m ∈ Icc (k + 1) l.length, a m ^ nAt xs m
  set Q4 := ∏ m ∈ Icc (k + 1) l.length,
        (kfun P (l.take m) / kfun P (l.take m ++ [t])) ^ (nAt xs m + 1)
  have hQ1 : 0 < Q1 := by
    apply Finset.prod_pos
    intro m hm
    simp only [Finset.mem_Icc] at hm
    exact div_pos (hKT m) (hK m (by omega) hm.2)
  have hPi : 0 < piK P l := piK_pos P hk l hlnd
  have he : 0 < P.eta (phi xs + 1) := hS.2.2.2.2.2.2 _ (by omega)
  have hKTk := hKT k
  set E := ∏ j ∈ Icc 1 (phi xs), (P.eta j)⁻¹
  set HR := AP P (modLast (· - n) (xs.take k))
  set Hx := AP P (xs.take k)
  set Kk := kfun P (l.take k)
  set KTk := kfun P (l.take k ++ [t])
  set bk := beta P xs k t
  set Λ := piLam P l
  set lt := lamTok P l.toFinset t
  set η := P.eta (phi xs + 1)
  exact final_alg13 η KTk Kk bk Qb Λ lt HR (aT k) Q2 E Q1 (piK P l) Hx Q3 Q4 n he.ne' hKTk.ne'
    hQ1.ne' hPi.ne' hH hQ

end TQLib

theorem solution {C T : Type} [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T]
    (P : Params C T) (hS : P.Standing) (h1 : Condition1 P) (h2 : Condition2 P) (hk : KPos P)
    (x : State T) (t : T) (ht : t ∉ toks x.1) :
    lamTok P (toks x.1).toFinset t * weightL P x.1 =
      ∑ k ∈ range (x.1.length + 1), ∑ n ∈ range (nAt x.1 k + 1),
        muTok P (release x.1 k n t) k * rfac P x.1 k n t * weightL P (release x.1 k n t) := by
  obtain ⟨xs, hxs⟩ := x
  simp only at ht ⊢
  have hterm : ∀ k ∈ range (xs.length + 1), ∀ n ∈ range (nAt xs k + 1),
      muTok P (release xs k n t) k * rfac P xs k n t * weightL P (release xs k n t) =
      lamTok P (toks xs).toFinset t * weightL P xs *
        ((kfun P ((toks xs).take k ++ [t]) - kfun P ((toks xs).take k)) /
            kfun P ((toks xs).take k ++ [t]) *
          (∏ j ∈ Icc (k + 1) (toks xs).length,
            (kfun P ((toks xs).take j) / kfun P ((toks xs).take j ++ [t])) ^ (nAt xs j + 1)) *
          (kfun P ((toks xs).take k) / kfun P ((toks xs).take k ++ [t])) ^ n) := by
    intro k hk' n hn
    simp only [mem_range] at hk' hn
    exact eq13_term P hS h1 h2 hk xs hxs t ht k (by omega) n (by omega)
  rw [Finset.sum_congr rfl (fun k hk' => Finset.sum_congr rfl (hterm k hk'))]
  simp_rw [← Finset.mul_sum]
  have htl : (t :: toks xs).Nodup := List.nodup_cons.mpr ⟨ht, hxs⟩
  have h29 := TokenQueue.ProductForm.eq_29 P hk (toks xs) t htl (nAt xs) (nAt_zero xs)
  rw [← toks_length xs, h29, mul_one]
