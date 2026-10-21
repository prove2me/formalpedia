-- Prove2me | solution 1 for TokenQueue.ProductForm.eq_8_9
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T09:23:10.772496+00:00
-- url     : https://prove2.me/submissions/1c6c12f7-463b-44dc-9ab8-be42bd6d3df6

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


theorem concat_cases' (l : List (T × ℕ)) :
    l = [] ∨ ∃ L t n, l = L ++ [(t, n)] := by
  rcases List.eq_nil_or_concat l with h | ⟨L, ⟨t, n⟩, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨L, t, n, by simpa using h⟩

theorem map_fst_modLast (f : ℕ → ℕ) (l : List (T × ℕ)) :
    (modLast f l).map Prod.fst = l.map Prod.fst := toks_modLast f l

theorem toks_single (t : T) (n : ℕ) : toks [(t, n)] = [t] := rfl

theorem pos_k_rel (P : Params C T) (hS : P.Standing) (hk : KPos P) (xs : List (T × ℕ))
    (hxs : (toks xs).Nodup) (t : T) (k : ℕ) (hkl : k ≤ xs.length)
    (hkT : ((toks xs).take k ++ [t]).Nodup) (n : ℕ) (hn : n ≤ nAt xs k) :
    beta P xs k t ^ n * AP P (modLast (· - n) (xs.take k)) * alpha P ((toks xs).take k ++ [t]) ^ n
      = AP P (xs.take k) *
        (kfun P ((toks xs).take k) / kfun P ((toks xs).take k ++ [t])) ^ n := by
  cases k with
  | zero =>
    have : n = 0 := by simp [nAt] at hn; omega
    subst this; simp; rfl
  | succ k' =>
    have hk' : k' < xs.length := by omega
    rw [take_succ_split xs k' hk', modLast_append_single, AP_append_single, AP_append_single]
    rw [nAt_succ xs k' hk'] at hn
    have et : toks (xs.take k') ++ [xs[k'].1] = (toks xs).take (k' + 1) := by
      rw [toks_take, pre, ← List.take_append_getElem (by rw [toks_length]; exact hk')]
      simp [toks]
    rw [et]
    have hb : beta P xs (k' + 1) t = lamU P ((toks xs).take (k' + 1)).toFinset /
        lamU P (insert t ((toks xs).take (k' + 1)).toFinset) := by
      simp only [beta, pre, if_neg (Nat.succ_ne_zero k')]
    rw [hb]
    have hKp : 0 < kfun P ((toks xs).take (k' + 1)) := by
      apply hk
      · exact hxs.sublist (List.take_sublist _ _)
      · apply List.ne_nil_of_length_pos; rw [List.length_take, toks_length]; omega
    have hKTp : 0 < kfun P ((toks xs).take (k' + 1) ++ [t]) := by
      apply hk _ hkT; simp
    unfold alpha
    rw [toFinset_append_single]
    set U := lamU P ((toks xs).take (k' + 1)).toFinset
    set UT := lamU P (insert t ((toks xs).take (k' + 1)).toFinset)
    set K := kfun P ((toks xs).take (k' + 1))
    set KT := kfun P ((toks xs).take (k' + 1) ++ [t])
    have hkr := key_ratio U UT K KT (lamU_nonneg P hS _) (lamU_mono P hS (Finset.subset_insert _ _))
    have hsplit : (U / K) ^ xs[k'].2 = (U / K) ^ (xs[k'].2 - n) * (U / K) ^ n := by
      rw [← pow_add]; congr 1; omega
    rw [hsplit]
    have : (U / UT) ^ n * (UT / KT) ^ n = (U / K) ^ n * (K / KT) ^ n := by
      rw [← mul_pow, ← mul_pow, hkr]; congr 1; field_simp
    linear_combination (AP P (List.take k' xs) * (U / K) ^ (xs[k'].2 - n)) * this

theorem prod_rel (P : Params C T) (hS : P.Standing) (xs : List (T × ℕ)) (t : T) (I : Finset ℕ)
    (hI : ∀ m ∈ I, 1 ≤ m ∧ 0 < kfun P ((toks xs).take m) ∧ 0 < kfun P ((toks xs).take m ++ [t])) :
    (∏ m ∈ I, beta P xs m t ^ nAt xs m) *
      (∏ m ∈ I, alpha P ((toks xs).take m ++ [t]) ^ nAt xs m) =
      (∏ m ∈ I, kfun P ((toks xs).take m ++ [t]) / kfun P ((toks xs).take m)) *
      (∏ m ∈ I, alpha P ((toks xs).take m) ^ nAt xs m) *
      ∏ m ∈ I, (kfun P ((toks xs).take m) / kfun P ((toks xs).take m ++ [t])) ^ (nAt xs m + 1) := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro m hm
  obtain ⟨hm1, hKp, hKTp⟩ := hI m hm
  have hb : beta P xs m t = lamU P ((toks xs).take m).toFinset /
      lamU P (insert t ((toks xs).take m).toFinset) := by
    simp only [beta, pre, if_neg (by omega : m ≠ 0)]
  rw [hb]
  unfold alpha
  rw [toFinset_append_single]
  set U := lamU P ((toks xs).take m).toFinset
  set UT := lamU P (insert t ((toks xs).take m).toFinset)
  set K := kfun P ((toks xs).take m)
  set KT := kfun P ((toks xs).take m ++ [t])
  set e := nAt xs m
  have hkr := key_ratio U UT K KT (lamU_nonneg P hS _) (lamU_mono P hS (Finset.subset_insert _ _))
  have h3 : (U / K) ^ e * (K / KT) ^ e = (U / KT) ^ e := by
    rw [← mul_pow]; congr 1; field_simp
  have h4 : KT / K * (K / KT) = 1 := by field_simp
  calc (U / UT) ^ e * (UT / KT) ^ e = (U / KT) ^ e := by rw [← mul_pow, hkr]
    _ = (U / K) ^ e * (K / KT) ^ e * (KT / K * (K / KT)) := by rw [h3, h4, mul_one]
    _ = KT / K * (U / K) ^ e * (K / KT) ^ (e + 1) := by ring

theorem final_alg14 (η KJk Kk bk Qb bj Λ PiS HS aJk Q2 aj1 Zp E Pi Hx Q3 Q4 Q1 Kj1 dU : ℝ)
    (n nJ : ℕ) (hη : η ≠ 0) (hKJ : KJk ≠ 0) (hQ1 : Q1 ≠ 0) (hPi : Pi ≠ 0) (hKj1 : Kj1 ≠ 0)
    (hPiS : PiS * Kj1 = Pi * KJk * Q1)
    (hH : bk ^ n * HS * aJk ^ n = Hx * (Kk / KJk) ^ n) (hQ : Qb * Q2 = Q1 * Q3 * Q4)
    (hlast : (1 - bj) * aj1 = dU / Kj1) :
    η * (KJk - Kk) * (bk ^ n * Qb * (1 - bj)) *
        (Λ / PiS * (HS * aJk ^ n * Q2 * aj1 ^ (1 + nJ) * Zp) * (E * η⁻¹)) =
      Λ / Pi * (Hx * Q3 * aj1 ^ nJ * Zp) * E * dU * ((KJk - Kk) / KJk * Q4 * (Kk / KJk) ^ n) := by
  have hPiS' : PiS = Pi * KJk * Q1 / Kj1 := by rw [← hPiS]; field_simp
  have e : η * (KJk - Kk) * (bk ^ n * Qb * (1 - bj)) *
      (Λ / PiS * (HS * aJk ^ n * Q2 * aj1 ^ (1 + nJ) * Zp) * (E * η⁻¹)) =
      (KJk - Kk) * Λ * E / PiS * (bk ^ n * HS * aJk ^ n) * (Qb * Q2) * ((1 - bj) * aj1) *
        aj1 ^ nJ * Zp * (η * η⁻¹) := by
    rw [pow_add, pow_one]; ring
  rw [e, hH, hQ, hlast, mul_inv_cancel₀ hη, hPiS']
  have hu := inv_mul_cancel₀ hQ1
  have hv := mul_inv_cancel₀ hKj1
  simp only [div_eq_mul_inv, mul_inv, inv_inv]
  linear_combination
    (Λ * Pi⁻¹ * Hx * Q3 * aj1 ^ nJ * Zp * E * dU * (KJk - Kk) * KJk⁻¹ * Q4 * (Kk * KJk⁻¹) ^ n *
      (Kj1 * Kj1⁻¹)) * hu +
    (Λ * Pi⁻¹ * Hx * Q3 * aj1 ^ nJ * Zp * E * dU * (KJk - Kk) * KJk⁻¹ * Q4 * (Kk * KJk⁻¹) ^ n) * hv





theorem list_sum_filter_map {α : Type} (L : List α) (p : α → Bool) (g : α → ℝ) :
    ((L.filter p).map g).sum = (L.map (fun a => if p a then g a else 0)).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.filter_cons]
    split_ifs with h <;> simp [h, ih]

theorem sum_finRange_filter_lt (n j : ℕ) (g : ℕ → ℝ) :
    (((List.finRange n).filter (fun l : Fin n => decide (j < l.val))).map (fun l => g l.val)).sum
      = ∑ l ∈ Ico (j + 1) n, g l := by
  rw [list_sum_filter_map]
  have : ((List.finRange n).map
      (fun a : Fin n => if decide (j < a.val) = true then g a.val else 0)).sum =
      ∑ a : Fin n, if j < a.val then g a.val else 0 := by
    rw [Fin.sum_univ_def]; simp
  rw [this, Fin.sum_univ_eq_sum_range (fun a => if j < a then g a else 0) n,
    ← Finset.sum_filter]
  congr 1
  ext l; simp; omega

theorem geom_part (r b : ℝ) (c : ℕ) :
    ((List.range c).map fun m => r * (b ^ m * (1 - b))).sum = r * (1 - b ^ c) := by
  rw [← List.sum_toFinset _ (List.nodup_range), List.toFinset_range]
  rw [← Finset.mul_sum, ← Finset.sum_mul, geom_sum_mul_neg]

theorem sum_map_flatMap {α β : Type} (L : List α) (f : α → List β) (g : β → ℝ) :
    ((L.flatMap f).map g).sum = (L.map (fun a => ((f a).map g).sum)).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [List.flatMap_cons, ih]

theorem dep_sum_generic {α : Type} (n : ℕ) (j : Fin n) (r : ℝ) (b : ℕ → ℝ) (cnt : ℕ → ℕ)
    (tA : ℕ → α) (tB : Fin n → ℕ → α) (tC : α) :
    ((((List.range (cnt j.val)).map (fun m => (tA m, r * (b j.val ^ m * (1 - b j.val))))) ++
      (((List.finRange n).filter (fun l => decide (j < l))).flatMap fun l =>
        (List.range (cnt l.val)).map fun m =>
          (tB l m, r * ((∏ l' ∈ Ico j.val l.val, b l' ^ cnt l') * b l.val ^ m * (1 - b l.val)))) ++
      [(tC, r * ∏ l' ∈ Ico j.val n, b l' ^ cnt l')]).map Prod.snd).sum = r := by
  set surv : ℕ → ℝ := fun l => ∏ l' ∈ Ico j.val l, b l' ^ cnt l' with hsurv
  rw [List.map_append, List.map_append, List.sum_append, List.sum_append, sum_map_flatMap]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, List.map_map]
  have hA : ((List.range (cnt j.val)).map
      (Prod.snd ∘ fun m => (tA m, r * (b j.val ^ m * (1 - b j.val))))).sum =
      r * (1 - b j.val ^ cnt j.val) := by
    rw [← geom_part]; rfl
  have hB : ∀ l : Fin n, ((List.range (cnt l.val)).map
      (Prod.snd ∘ fun m => (tB l m, r * ((∏ l' ∈ Ico j.val l.val, b l' ^ cnt l') * b l.val ^ m *
        (1 - b l.val))))).sum = r * surv l.val * (1 - b l.val ^ cnt l.val) := by
    intro l
    have e : (Prod.snd ∘ fun m => (tB l m, r * ((∏ l' ∈ Ico j.val l.val, b l' ^ cnt l') *
        b l.val ^ m * (1 - b l.val)))) =
        fun m => (r * surv l.val) * (b l.val ^ m * (1 - b l.val)) := by
      funext m; simp only [Function.comp, hsurv]; ring
    rw [e, geom_part]
  simp only [hB]
  have hfilt : (List.filter (fun l => decide (j < l)) (List.finRange n)) =
      (List.filter (fun l : Fin n => decide (j.val < l.val)) (List.finRange n)) := by
    congr 1
  rw [hfilt, sum_finRange_filter_lt n j.val (fun l => r * surv l * (1 - b l ^ cnt l)), hA]
  have hstep : ∀ l, j.val ≤ l → surv (l + 1) = surv l * b l ^ cnt l := by
    intro l hl
    simp only [hsurv]
    rw [Finset.prod_Ico_succ_top hl]
  have htel : ∑ l ∈ Ico (j.val + 1) n, r * surv l * (1 - b l ^ cnt l) =
      r * (surv (j.val + 1) - surv n) := by
    have e : ∀ l ∈ Ico (j.val + 1) n, r * surv l * (1 - b l ^ cnt l) =
        r * surv l - r * surv (l + 1) := by
      intro l hl
      simp only [Finset.mem_Ico] at hl
      rw [hstep l (by omega)]; ring
    rw [Finset.sum_congr rfl e, Finset.sum_Ico_eq_sum_range]
    have := Finset.sum_range_sub' (fun i => r * surv (j.val + 1 + i)) (n - (j.val + 1))
    rw [show j.val + 1 + (n - (j.val + 1)) = n by omega, add_zero] at this
    rw [mul_sub, ← this]
    rfl
  rw [htel]
  have h0 : surv j.val = 1 := by simp [hsurv]
  have h1 : surv (j.val + 1) = b j.val ^ cnt j.val := by
    rw [hstep j.val le_rfl, h0, one_mul]
  rw [h1]
  change r * (1 - b j.val ^ cnt j.val) + r * (b j.val ^ cnt j.val - surv n) + r * surv n = r
  ring

theorem departures_sum (P : Params C T) (y : List (T × ℕ)) (j : Fin y.length) :
    ((departures P y j).map Prod.snd).sum = muTok P y j.val := by
  unfold departures
  dsimp only
  exact dep_sum_generic y.length j (muTok P y j.val)
    (fun l => lamU P (((toks y).take (l + 1)).toFinset.erase (y.get j).1) /
      lamU P ((toks y).take (l + 1)).toFinset)
    (fun l => (y.map Prod.snd).getD l 0) _ _ _







theorem hasSum_rate_list (L : List (List (T × ℕ) × ℝ)) (hL : ∀ e ∈ L, (e.1.map Prod.fst).Nodup) :
    HasSum (fun x : State T => ((L.filter (fun e => e.1 = x.1)).map Prod.snd).sum)
      (L.map Prod.snd).sum := by
  induction L with
  | nil => simpa using hasSum_zero
  | cons e L ih =>
    have he := hL e (List.mem_cons_self ..)
    have ih' := ih (fun e' h => hL e' (List.mem_cons_of_mem _ h))
    have h1 : HasSum (fun x : State T => if x = ⟨e.1, he⟩ then e.2 else 0) e.2 :=
      hasSum_ite_eq _ _
    have := h1.add ih'
    convert this using 1
    · funext x
      rw [List.filter_cons]
      by_cases hx : e.1 = x.1
      · have h2 : x = ⟨e.1, he⟩ := Subtype.ext hx.symm
        rw [if_pos (by simpa using hx), List.map_cons, List.sum_cons, if_pos h2]
      · have h2 : x ≠ ⟨e.1, he⟩ := fun h => hx (by rw [h])
        rw [if_neg (by simpa using hx), if_neg h2, zero_add]
    · simp







theorem split_at {α : Type} (y : List α) (i : ℕ) (hi : i < y.length) :
    y = y.take i ++ y[i] :: y.drop (i + 1) := by
  rw [List.getElem_cons_drop, List.take_append_drop]

theorem departures_nodup (P : Params C T) (y : List (T × ℕ)) (hy : (y.map Prod.fst).Nodup)
    (j : Fin y.length) : ∀ e ∈ departures P y j, (e.1.map Prod.fst).Nodup := by
  intro e he
  have hj := j.2
  unfold departures at he
  simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap, List.mem_filter,
    List.mem_finRange, true_and, List.mem_singleton, decide_eq_true_eq] at he
  set F := y.map Prod.fst with hF
  have hFl : F.length = y.length := by simp [hF]
  have hFj : F[j.val]'(by omega) = (y.get j).1 := by simp [hF]
  have hsplit := split_at F j.val (by omega)
  rw [hFj] at hsplit
  rcases he with (⟨m, hm, rfl⟩ | ⟨l, hl, m, hm, rfl⟩) | rfl
  · -- reclaimed in its own portion: same tokens
    have : (modLast (· + m) (y.take j.val) ++ ((y.get j).1, (y.map Prod.snd).getD j.val 0 - m - 1) ::
        y.drop (j.val + 1)).map Prod.fst = F := by
      simp only [List.map_append, map_fst_modLast, List.map_cons, List.map_take, List.map_drop, ← hF]
      exact hsplit.symm
    rw [this]; exact hy
  · -- reclaimed by a later portion: a permutation of the tokens
    have hlj : j.val < l.val := hl
    have hl2 := l.2
    have hFl' : F[l.val]'(by omega) = (y.get l).1 := by simp [hF]
    have e1 : F.drop (j.val + 1) = (F.take l.val).drop (j.val + 1) ++ (y.get l).1 :: F.drop (l.val + 1) := by
      rw [← hFl', List.getElem_cons_drop]
      conv_lhs => rw [← List.take_append_drop l.val F]
      rw [List.drop_append_of_le_length (by simp; omega)]
    apply (List.Perm.nodup_iff _).mpr hy
    simp only [List.map_append, map_fst_modLast, List.map_take, List.map_drop, List.map_cons, ← hF]
    conv_rhs => rw [hsplit, e1]
    rw [List.append_assoc]
    apply List.Perm.append_left
    have := List.perm_middle (a := (y.get j).1) (l₁ := (F.take l.val).drop (j.val + 1) ++ [(y.get l).1])
      (l₂ := F.drop (l.val + 1))
    simpa using this
  · -- released: a sublist of the tokens
    apply List.Nodup.sublist _ hy
    simp only [List.map_append, map_fst_modLast, List.map_take, List.map_drop, ← hF]
    conv_rhs => rw [hsplit]
    exact (List.Sublist.refl _).append ((List.Sublist.refl _).cons _)

theorem transitions_nodup (P : Params C T) (y : State T) :
    ∀ e ∈ transitions P y.1, (e.1.map Prod.fst).Nodup := by
  intro e he
  unfold transitions at he
  simp only [List.mem_append, List.mem_map, List.mem_flatMap, List.mem_finRange, true_and] at he
  rcases he with (h | ⟨t, ht, rfl⟩) | ⟨j, hj⟩
  · split_ifs at h with hy
    · simp at h
    · simp only [List.mem_singleton] at h
      subst h
      simp only [map_fst_modLast]
      exact y.2
  · simp only [Finset.mem_toList, Finset.mem_sdiff, Finset.mem_univ, true_and,
      List.mem_toFinset] at ht
    simp only [List.map_append, List.map_cons, List.map_nil]
    rw [List.nodup_append]
    refine ⟨y.2, List.nodup_singleton _, ?_⟩
    intro a ha b hb hab
    simp only [List.mem_singleton] at hb
    subst hb; subst hab
    exact ht ha
  · exact departures_nodup P y.1 y.2 j e hj


end TQLib

open TQLib TokenQueue.ProductForm Finset

namespace TQLib

variable {C T : Type} [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T]

/-- `F` is a finite linear combination of point evaluations. -/
def IsFC (F : (List (T × ℕ) → ℝ) → ℝ) : Prop :=
  ∃ L : List (List (T × ℕ) × ℝ), ∀ f, F f = (L.map (fun p => p.2 * f p.1)).sum

theorem isFC_zero : IsFC (T := T) (fun _ => 0) := ⟨[], fun f => by simp⟩

theorem isFC_eval (c : ℝ) (s : List (T × ℕ)) : IsFC (fun f => c * f s) :=
  ⟨[(s, c)], fun f => by simp⟩

theorem isFC_add {F G : (List (T × ℕ) → ℝ) → ℝ} (hF : IsFC F) (hG : IsFC G) :
    IsFC (fun f => F f + G f) := by
  obtain ⟨L, hL⟩ := hF
  obtain ⟨L', hL'⟩ := hG
  exact ⟨L ++ L', fun f => by show F f + G f = _; rw [hL, hL', List.map_append, List.sum_append]⟩

theorem isFC_sum {ι : Type} [DecidableEq ι] (S : Finset ι) (F : ι → (List (T × ℕ) → ℝ) → ℝ)
    (h : ∀ i ∈ S, IsFC (F i)) : IsFC (fun f => ∑ i ∈ S, F i f) := by
  induction S using Finset.induction_on with
  | empty => simpa using isFC_zero
  | insert a S ha ih =>
    have h1 := h a (Finset.mem_insert_self _ _)
    have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have := isFC_add h1 h2
    simpa [Finset.sum_insert ha] using this

def delta (y : List (T × ℕ)) : List (T × ℕ) → ℝ := fun s => if s = y then 1 else 0

theorem hasSum_list_delta (L : List (List (T × ℕ) × ℝ)) (π : State T → ℝ) :
    HasSum (fun y : State T => π y * (L.map (fun p => p.2 * delta y.1 p.1)).sum)
      (L.map (fun p => p.2 * piExt π p.1)).sum := by
  induction L with
  | nil => simpa using hasSum_zero
  | cons p L ih =>
    simp only [List.map_cons, List.sum_cons, mul_add]
    apply HasSum.add _ ih
    by_cases hp : (p.1.map Prod.fst).Nodup
    · have h1 : HasSum (fun y : State T => if y = ⟨p.1, hp⟩ then p.2 * π ⟨p.1, hp⟩ else 0)
          (p.2 * π ⟨p.1, hp⟩) := hasSum_ite_eq _ _
      have hpe : piExt π p.1 = π ⟨p.1, hp⟩ := by simp [piExt, hp]
      rw [hpe]
      convert h1 using 1
      funext y
      by_cases hy : y = ⟨p.1, hp⟩
      · subst hy; simp [delta]; ring
      · have : p.1 ≠ y.1 := fun h => hy (Subtype.ext h.symm)
        simp [delta, this, hy]
    · have hpe : piExt π p.1 = 0 := by simp [piExt, hp]
      rw [hpe, mul_zero]
      convert hasSum_zero using 1
      funext y
      have : p.1 ≠ y.1 := fun h => hp (h ▸ y.2)
      simp [delta, this]

theorem hasSum_FC {F : (List (T × ℕ) → ℝ) → ℝ} (hF : IsFC F) (π : State T → ℝ) :
    HasSum (fun y : State T => π y * F (delta y.1)) (F (piExt π)) := by
  obtain ⟨L, hL⟩ := hF
  simp only [hL]
  exact hasSum_list_delta L π

theorem balanceRHS_FC (P : Params C T) (x : List (T × ℕ)) : IsFC (fun f => balanceRHS P f x) := by
  unfold balanceRHS
  simp only
  apply isFC_add
  apply isFC_add
  · cases h : x.getLast? with
    | none => simpa using isFC_zero
    | some p =>
      obtain ⟨Ti, ni⟩ := p
      simp only
      split_ifs
      · exact isFC_eval _ _
      · exact isFC_eval _ _
  · apply isFC_sum; intro t _
    apply isFC_sum; intro k _
    apply isFC_sum; intro n _
    exact isFC_eval _ _
  · apply isFC_sum; intro j _
    apply isFC_sum; intro k _
    apply isFC_sum; intro n _
    exact isFC_eval _ _

end TQLib

namespace TQLib

variable {C T : Type} [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T]

def cntD (y : List (T × ℕ)) (l : ℕ) : ℕ := (y.map Prod.snd).getD l 0

noncomputable def bD (P : Params C T) (y : List (T × ℕ)) (Tj : T) (l : ℕ) : ℝ :=
  lamU P (((toks y).take (l + 1)).toFinset.erase Tj) / lamU P ((toks y).take (l + 1)).toFinset

noncomputable def survD (P : Params C T) (y : List (T × ℕ)) (Tj : T) (jn l : ℕ) : ℝ :=
  ∏ l' ∈ Ico jn l, bD P y Tj l' ^ cntD y l'

def tOwn (y : List (T × ℕ)) (jn : ℕ) (Tj : T) (m : ℕ) : List (T × ℕ) :=
  modLast (· + m) (y.take jn) ++ (Tj, cntD y jn - m - 1) :: y.drop (jn + 1)

def tLater (y : List (T × ℕ)) (jn : ℕ) (Tj : T) (l : Fin y.length) (m : ℕ) : List (T × ℕ) :=
  modLast (· + cntD y jn) (y.take jn) ++ (y.take l.val).drop (jn + 1) ++
    ((y.get l).1, m) :: (Tj, cntD y l.val - m - 1) :: y.drop (l.val + 1)

def tRel (y : List (T × ℕ)) (jn : ℕ) : List (T × ℕ) :=
  modLast (· + cntD y jn) (y.take jn) ++ y.drop (jn + 1)

theorem departures_eq (P : Params C T) (y : List (T × ℕ)) (j : Fin y.length) :
    departures P y j =
      ((List.range (cntD y j.val)).map fun m =>
        (tOwn y j.val (y.get j).1 m,
          muTok P y j.val * (bD P y (y.get j).1 j.val ^ m * (1 - bD P y (y.get j).1 j.val)))) ++
      (((List.finRange y.length).filter (fun l => j < l)).flatMap fun l =>
        (List.range (cntD y l.val)).map fun m =>
          (tLater y j.val (y.get j).1 l m,
            muTok P y j.val * (survD P y (y.get j).1 j.val l.val * bD P y (y.get j).1 l.val ^ m *
              (1 - bD P y (y.get j).1 l.val)))) ++
      [(tRel y j.val, muTok P y j.val * survD P y (y.get j).1 j.val y.length)] := by
  rfl

end TQLib

namespace TQLib

variable {C T : Type} [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T]

def gx (x : List (T × ℕ)) (e : List (T × ℕ) × ℝ) : ℝ := if e.1 = x then e.2 else 0

theorem arrA (P : Params C T) (y : List (T × ℕ)) (x : List (T × ℕ)) :
    (((if y = [] then [] else [(modLast (· + 1) y, lamU P (toks y).toFinset)]) ++
      ((univ \ (toks y).toFinset).toList.map fun t =>
        (y ++ [(t, 0)], lamTok P (toks y).toFinset t))).map (gx x)).sum =
      (if y ≠ [] ∧ modLast (· + 1) y = x then lamU P (toks y).toFinset else 0) +
      ∑ t ∈ univ \ (toks y).toFinset, (if y ++ [(t, 0)] = x then lamTok P (toks y).toFinset t else 0) := by
  rw [List.map_append, List.sum_append, List.map_map]
  congr 1
  · split_ifs with h1 h2 h2 <;> simp_all [gx]
  · rw [← Finset.sum_map_toList]
    congr 1

theorem arr_nil (P : Params C T) (y : List (T × ℕ)) :
    (if y ≠ [] ∧ modLast (· + 1) y = ([] : List (T × ℕ)) then lamU P (toks y).toFinset else 0) +
      ∑ t ∈ univ \ (toks y).toFinset,
        (if y ++ [(t, 0)] = ([] : List (T × ℕ)) then lamTok P (toks y).toFinset t else 0) = 0 := by
  rw [if_neg, Finset.sum_eq_zero]
  · simp
  · intro t _; simp
  · rintro ⟨h1, h2⟩
    have := congrArg List.length h2
    rw [length_modLast] at this
    exact h1 (List.eq_nil_of_length_eq_zero this)

theorem arr_concat (P : Params C T) (y : List (T × ℕ)) (X : List (T × ℕ)) (t0 : T) (n0 : ℕ)
    (hx : ((X ++ [(t0, n0)]).map Prod.fst).Nodup) :
    (if y ≠ [] ∧ modLast (· + 1) y = X ++ [(t0, n0)] then lamU P (toks y).toFinset else 0) +
      ∑ t ∈ univ \ (toks y).toFinset,
        (if y ++ [(t, 0)] = X ++ [(t0, n0)] then lamTok P (toks y).toFinset t else 0) =
      if 0 < n0 then lamU P (toks (X ++ [(t0, n0)])).toFinset * delta y (X ++ [(t0, n0 - 1)])
      else lamTok P (toks X).toFinset t0 * delta y X := by
  rcases Nat.eq_zero_or_pos n0 with hn | hn
  · subst hn
    rw [if_neg (lt_irrefl 0), if_neg]
    · rw [zero_add]
      by_cases hy : y = X
      · subst hy
        rw [Finset.sum_eq_single t0]
        · simp [delta]
        · intro t _ ht
          rw [if_neg]
          intro h
          have := List.append_inj' h rfl
          simp at this
          exact ht this
        · intro h0
          rw [if_neg]
          intro h
          apply h0
          simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, List.mem_toFinset]
          rw [List.map_append, List.nodup_append] at hx
          intro hmem
          exact hx.2.2 t0 hmem t0 (by simp) rfl
      · rw [Finset.sum_eq_zero]
        · have hy' : X ≠ y := fun h => hy h.symm
          simp [delta, hy']
        · intro t _
          rw [if_neg]
          intro h
          exact hy (List.append_inj' h rfl).1
    · rintro ⟨h1, h2⟩
      rcases concat_cases' y with h | ⟨Y, s, c, rfl⟩
      · exact h1 h
      · rw [modLast_append_single] at h2
        have := (List.append_inj' h2 rfl).2
        simp at this
  · rw [if_pos hn]
    rw [Finset.sum_eq_zero]
    · rw [add_zero]
      by_cases hy : y = X ++ [(t0, n0 - 1)]
      · subst hy
        rw [if_pos]
        · simp [delta]
          congr 2
          simp [toks]
        · refine ⟨by simp, ?_⟩
          rw [modLast_append_single]
          congr 3; omega
      · rw [if_neg]
        · have hy' : X ++ [(t0, n0 - 1)] ≠ y := fun h => hy h.symm
          simp [delta, hy']
        · rintro ⟨h1, h2⟩
          apply hy
          rcases concat_cases' y with h | ⟨Y, s, c, rfl⟩
          · exact absurd h h1
          · rw [modLast_append_single] at h2
            obtain ⟨hY, hp⟩ := List.append_inj' h2 rfl
            simp at hp
            obtain ⟨rfl, hc⟩ := hp
            subst hY
            congr 3; omega
    · intro t _
      rw [if_neg]
      intro h
      have := (List.append_inj' h rfl).2
      simp at this
      omega

end TQLib

namespace TQLib

variable {C T : Type} [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T]

theorem release_length (x : List (T × ℕ)) (k n : ℕ) (t : T) (hk : k ≤ x.length) :
    (release x k n t).length = x.length + 1 := by
  simp [release, length_modLast]; omega

theorem release_getElem (x : List (T × ℕ)) (k n : ℕ) (t : T) (hk : k ≤ x.length) :
    (release x k n t)[k]'(by rw [release_length x k n t hk]; omega) = (t, n) := by
  simp only [release]
  rw [List.getElem_append_right (by simp [length_modLast])]
  simp only [length_modLast, List.length_take, show min k x.length = k by omega, Nat.sub_self,
    List.getElem_cons_zero]

theorem modLast_take_cancel (x : List (T × ℕ)) (k n : ℕ) (hk : k ≤ x.length) (hn : n ≤ nAt x k) :
    modLast (· + n) (modLast (· - n) (x.take k)) = x.take k := by
  cases k with
  | zero => rfl
  | succ k =>
    rw [nAt_succ x k (by omega)] at hn
    rw [take_succ_split x k (by omega), modLast_append_single, modLast_append_single]
    congr 3; omega

theorem tRel_release (x : List (T × ℕ)) (k n : ℕ) (t : T) (hk : k ≤ x.length) (hn : n ≤ nAt x k) :
    tRel (release x k n t) k = x := by
  have hlen : (modLast (· - n) (x.take k)).length = k := by
    rw [length_modLast]; simp; omega
  have hc : cntD (release x k n t) k = n := by
    unfold cntD
    rw [List.getD_eq_getElem?_getD, List.getElem?_map]
    rw [List.getElem?_eq_getElem (by rw [release_length x k n t hk]; omega), release_getElem x k n t hk]
    rfl
  unfold tRel
  rw [hc]
  simp only [release]
  rw [List.take_append_of_le_length (by rw [hlen]), List.take_of_length_le (by rw [hlen]),
    List.drop_append, List.drop_eq_nil_of_le (by rw [hlen]; omega), List.nil_append, hlen,
    show k + 1 - k = 1 by omega, List.drop_one, List.tail_cons, modLast_take_cancel x k n hk hn,
    List.take_append_drop]

theorem cntD_eq (y : List (T × ℕ)) (j : ℕ) (hj : j < y.length) : cntD y j = y[j].2 := by
  unfold cntD
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]
  rfl

theorem tRel_inv (y x : List (T × ℕ)) (j : ℕ) (hj : j < y.length) (h : tRel y j = x) :
    (j = 0 ∧ 0 < y[j].2) ∨ (release x j y[j].2 y[j].1 = y ∧ y[j].2 ≤ nAt x j) := by
  have hsplit := split_at y j hj
  unfold tRel at h
  rw [cntD_eq y j hj] at h
  cases j with
  | zero =>
    rcases Nat.eq_zero_or_pos y[0].2 with h0 | h0
    · right
      refine ⟨?_, by rw [h0]; simp [nAt]⟩
      subst h
      simp only [release, List.take_zero, modLast_nil, List.nil_append, List.drop_zero]
      rw [h0]
      conv_rhs => rw [hsplit]
      simp only [List.take_zero, List.nil_append, zero_add]
      congr 1
      exact Prod.ext rfl h0.symm
    · left; exact ⟨rfl, h0⟩
  | succ k =>
    right
    have hk : k < y.length := by omega
    rw [take_succ_split y k hk, modLast_append_single] at h
    have hxl : x.length = y.length - 1 := by
      rw [← h]; simp; omega
    have hxt : x.take (k + 1) = y.take k ++ [(y[k].1, y[k].2 + y[k + 1].2)] := by
      rw [← h, List.take_append_of_le_length (by simp; omega), List.take_of_length_le (by simp)]
    have hxd : x.drop (k + 1) = y.drop (k + 1 + 1) := by
      rw [← h, List.drop_append_of_le_length (by simp; omega), List.drop_eq_nil_of_le (by simp),
        List.nil_append]
    have hnat : nAt x (k + 1) = y[k].2 + y[k + 1].2 := by
      rw [nAt_succ x k (by omega)]
      have : x[k]'(by omega) = (x.take (k + 1))[k]'(by simp; omega) := by simp
      rw [this]
      simp only [hxt]
      simp
    refine ⟨?_, by rw [hnat]; omega⟩
    simp only [release]
    rw [hxt, hxd, modLast_append_single, show y[k].2 + y[k + 1].2 - y[k + 1].2 = y[k].2 by omega]
    conv_rhs => rw [hsplit, take_succ_split y k hk]

theorem lamU_empty (P : Params C T) (hS : P.Standing) : lamU P ∅ = 0 := by
  unfold lamU
  apply Finset.sum_eq_zero
  intro c hc
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.subset_empty] at hc
  exact absurd hc (hS.2.1 c).ne_empty

theorem toks_release (x : List (T × ℕ)) (k n : ℕ) (t : T) :
    toks (release x k n t) = (toks x).take k ++ t :: (toks x).drop k := by
  unfold release
  rw [toks_append, toks_modLast, toks_take]
  simp [toks, pre, List.map_drop]

theorem bD_release (P : Params C T) (hS : P.Standing) (x : List (T × ℕ)) (k n : ℕ) (t : T)
    (ht : t ∉ toks x) (hk : k ≤ x.length) (l : ℕ) (hkl : k ≤ l) :
    bD P (release x k n t) t l = beta P x l t := by
  unfold bD
  rw [toks_release]
  have hkx : k ≤ (toks x).length := by rw [toks_length]; exact hk
  have e : ((toks x).take k ++ t :: (toks x).drop k).take (l + 1) =
      (toks x).take k ++ t :: ((toks x).drop k).take (l - k) := by
    rw [List.take_append, List.take_of_length_le (by simp; omega)]
    congr 1
    rw [List.length_take]
    rw [Nat.min_eq_left hkx, show l + 1 - k = (l - k) + 1 by omega, List.take_succ_cons]
  rw [e]
  have e2 : ((toks x).take k ++ t :: ((toks x).drop k).take (l - k)).toFinset =
      insert t ((toks x).take l).toFinset := by
    have : (toks x).take l = (toks x).take k ++ ((toks x).drop k).take (l - k) := by
      rw [← List.take_add]; congr 1; omega
    rw [this]
    ext a; simp
  rw [e2, Finset.erase_insert (by simp only [List.mem_toFinset]; exact fun h => ht (List.mem_of_mem_take h))]
  unfold beta
  split_ifs with h0
  · subst h0; simp [lamU_empty P hS]
  · rfl

theorem cntD_release_after (x : List (T × ℕ)) (k n : ℕ) (t : T) (hk : k ≤ x.length) (l : ℕ)
    (hkl : k < l) (hl : l ≤ x.length) : cntD (release x k n t) l = nAt x l := by
  have hlen : (modLast (· - n) (x.take k)).length = k := by
    rw [length_modLast]; simp; omega
  obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  unfold cntD nAt
  simp only [release, List.map_append, List.map_cons, List.getD_eq_getElem?_getD,
    Nat.add_sub_cancel, if_neg (Nat.succ_ne_zero l')]
  rw [List.getElem?_append_right (by simp [length_modLast]; omega)]
  simp only [List.length_map, hlen]
  rw [show l' + 1 - k = (l' - k) + 1 by omega, List.getElem?_cons_succ,
    List.getElem?_map, List.getElem?_drop, List.getElem?_map]
  congr 3; omega

theorem cntD_release_at (x : List (T × ℕ)) (k n : ℕ) (t : T) (hk : k ≤ x.length) :
    cntD (release x k n t) k = n := by
  rw [cntD_eq _ _ (by rw [release_length x k n t hk]; omega), release_getElem x k n t hk]

theorem survD_release (P : Params C T) (hS : P.Standing) (x : List (T × ℕ)) (k n : ℕ) (t : T)
    (ht : t ∉ toks x) (hk : k ≤ x.length) :
    survD P (release x k n t) t k (release x k n t).length = rfac P x k n t := by
  unfold survD rfac
  rw [release_length x k n t hk, Finset.prod_eq_prod_Ico_succ_bot (by omega),
    bD_release P hS x k n t ht hk k le_rfl, cntD_release_at x k n t hk,
    ← Finset.Ico_add_one_right_eq_Icc]
  congr 1
  apply Finset.prod_congr rfl
  intro l hl
  simp only [Finset.mem_Ico] at hl
  rw [bD_release P hS x k n t ht hk l (by omega), cntD_release_after x k n t hk l (by omega) (by omega)]

theorem survD_zero (P : Params C T) (hS : P.Standing) (y : List (T × ℕ)) (hy0 : 0 < y.length)
    (hc : 0 < y[0].2) : survD P y y[0].1 0 y.length = 0 := by
  unfold survD
  apply Finset.prod_eq_zero (i := 0) (by simp; omega)
  have hb : bD P y y[0].1 0 = 0 := by
    unfold bD
    have : ((toks y).take (0 + 1)).toFinset.erase y[0].1 = ∅ := by
      obtain ⟨p, q, rfl⟩ : ∃ p q, y = p :: q := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos hy0)
      simp [toks]
    rw [this, lamU_empty P hS, zero_div]
  rw [hb, cntD_eq y 0 hy0]
  exact zero_pow (by omega)

theorem tRel_length (y : List (T × ℕ)) (j : ℕ) (hj : j < y.length) :
    (tRel y j).length = y.length - 1 := by
  simp [tRel, length_modLast]; omega

theorem release_eq_imp (x y : List (T × ℕ)) (k n : ℕ) (t : T) (hk : k ≤ x.length)
    (h : release x k n t = y) (hky : k < y.length) : t = y[k].1 ∧ n = y[k].2 := by
  have := release_getElem x k n t hk
  subst h
  rw [this]; exact ⟨rfl, rfl⟩

theorem release_nodup_imp (x : List (T × ℕ)) (k n : ℕ) (t : T)
    (h : (toks (release x k n t)).Nodup) : t ∉ toks x := by
  rw [toks_release] at h
  have hp := List.perm_middle (a := t) (l₁ := (toks x).take k) (l₂ := (toks x).drop k)
  rw [List.take_append_drop] at hp
  have := hp.nodup_iff.mp h
  exact (List.nodup_cons.mp this).1

theorem rel_term (P : Params C T) (hS : P.Standing) (x y : List (T × ℕ)) (hy : (toks y).Nodup)
    (hl : y.length = x.length + 1) (j : ℕ) (hj : j < y.length) :
    gx x (tRel y j, muTok P y j * survD P y y[j].1 j y.length) =
      ∑ t ∈ univ \ (toks x).toFinset, ∑ n ∈ range (nAt x j + 1),
        muTok P (release x j n t) j * rfac P x j n t * delta y (release x j n t) := by
  have hjx : j ≤ x.length := by omega
  obtain ⟨Ts, cs, hTc⟩ : ∃ Ts cs, y[j] = (Ts, cs) := ⟨_, _, rfl⟩
  have hT : y[j].1 = Ts := by rw [hTc]
  have hc : y[j].2 = cs := by rw [hTc]
  rw [hT]
  have hF : ∀ t ∈ univ \ (toks x).toFinset, ∑ n ∈ range (nAt x j + 1),
      muTok P (release x j n t) j * rfac P x j n t * delta y (release x j n t) =
      if t = Ts then (if cs ∈ range (nAt x j + 1) then
        muTok P (release x j cs Ts) j * rfac P x j cs Ts *
          delta y (release x j cs Ts) else 0) else 0 := by
    intro t _
    split_ifs with htT hcr
    · subst htT
      rw [Finset.sum_eq_single_of_mem cs hcr]
      intro n _ hn
      have : release x j n t ≠ y := fun h => hn ((release_eq_imp x y _ _ _ hjx h hj).2.trans hc)
      simp [delta, this]
    · subst htT
      apply Finset.sum_eq_zero
      intro n hn
      have : release x j n t ≠ y := by
        intro h
        have := (release_eq_imp x y _ _ _ hjx h hj).2.trans hc
        subst this; exact hcr hn
      simp [delta, this]
    · apply Finset.sum_eq_zero
      intro n _
      have : release x j n t ≠ y := fun h => htT ((release_eq_imp x y _ _ _ hjx h hj).1.trans hT)
      simp [delta, this]
  rw [Finset.sum_congr rfl hF, Finset.sum_ite_eq']
  unfold gx
  simp only
  by_cases hrel : tRel y j = x
  · rw [if_pos hrel]
    rcases tRel_inv y x j hj hrel with ⟨h0, hc0⟩ | ⟨hR, hcle⟩
    · subst h0
      have : survD P y Ts 0 y.length = 0 := by
        rw [← hT]; exact survD_zero P hS y hj hc0
      rw [this, mul_zero]
      rw [hc] at hc0
      split_ifs with h1 h2
      · simp only [Finset.mem_range] at h2
        simp [nAt] at h2; omega
      · rfl
      · rfl
    · rw [hT, hc] at hR
      rw [hc] at hcle
      have hTnot : Ts ∉ toks x := release_nodup_imp x j cs Ts (by rw [hR]; exact hy)
      rw [if_pos (by simp [hTnot]), if_pos (by simp; omega)]
      have key := survD_release P hS x j cs Ts hTnot hjx
      rw [hR] at key
      have hd : delta y (release x j cs Ts) = 1 := by simp [delta, hR]
      rw [hd, key, hR, mul_one]
  · rw [if_neg hrel]
    split_ifs with h1 h2
    · have : release x j cs Ts ≠ y := by
        intro hR
        apply hrel
        have := tRel_release x j cs Ts hjx (by simp only [Finset.mem_range] at h2; omega)
        rw [hR] at this
        exact this
      simp [delta, this]
    · rfl
    · rfl

theorem rel_match (P : Params C T) (hS : P.Standing) (x y : List (T × ℕ)) (hy : (toks y).Nodup) :
    ∑ j : Fin y.length, gx x (tRel y j.val, muTok P y j.val * survD P y (y.get j).1 j.val y.length) =
      ∑ t ∈ univ \ (toks x).toFinset, ∑ k ∈ range (x.length + 1), ∑ n ∈ range (nAt x k + 1),
        muTok P (release x k n t) k * rfac P x k n t * delta y (release x k n t) := by
  by_cases hl : y.length = x.length + 1
  · have hconv : ∀ G : ℕ → ℝ, ∑ k ∈ range (x.length + 1), G k = ∑ j : Fin y.length, G j.val := by
      intro G; rw [← hl]; exact (Fin.sum_univ_eq_sum_range G _).symm
    rw [Finset.sum_comm, hconv]
    apply Finset.sum_congr rfl
    intro j _
    exact rel_term P hS x y hy hl j.val j.2
  · rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
    · intro t _
      apply Finset.sum_eq_zero
      intro k hk
      apply Finset.sum_eq_zero
      intro n _
      simp only [Finset.mem_range] at hk
      have : release x k n t ≠ y := by
        intro h
        apply hl
        rw [← h, release_length x k n t (by omega)]
      simp [delta, this]
    · intro j _
      unfold gx
      rw [if_neg]
      intro h
      simp only at h
      apply hl
      have h3 := tRel_length y j.val j.2
      rw [h] at h3
      have hj2 := j.2
      omega

end TQLib

namespace TQLib

variable {C T : Type} [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T]

theorem list_range_sum (n : ℕ) (f : ℕ → ℝ) :
    ((List.range n).map f).sum = ∑ m ∈ range n, f m := by
  rw [← List.sum_toFinset _ (List.nodup_range), List.toFinset_range]

theorem shift_own_eq (x : List (T × ℕ)) (j n : ℕ) (Tj : T) :
    shift x (j + 1) j n Tj = modLast (· - n) (x.take j) ++ (Tj, n + 1 + nAt x (j + 1)) :: x.drop (j + 1) := by
  unfold shift; rw [if_neg (lt_irrefl _)]

theorem modLast_sub_add (Y : List (T × ℕ)) (m : ℕ) : modLast (· - m) (modLast (· + m) Y) = Y := by
  rcases concat_cases' Y with rfl | ⟨Y', s, d, rfl⟩
  · rfl
  · rw [modLast_append_single, modLast_append_single]; congr 3; omega

/-- `bD` only depends on the token list and the departing token. -/
theorem bD_eq_beta (P : Params C T) (hS : P.Standing) (y x : List (T × ℕ)) (Tj : T) (l : ℕ)
    (hpre : ((toks y).take (l + 1)).toFinset = insert Tj ((toks x).take l).toFinset)
    (hT : Tj ∉ (toks x).take l) : bD P y Tj l = beta P x l Tj := by
  unfold bD beta
  rw [hpre, Finset.erase_insert (by simpa using hT)]
  split_ifs with h0
  · subst h0; simp [lamU_empty P hS]
  · rfl

theorem tOwn_shift (x : List (T × ℕ)) (j n : ℕ) (hj : j < x.length) (hn : n ≤ nAt x j) :
    tOwn (shift x (j + 1) j n x[j].1) j x[j].1 n = x := by
  rw [shift_own_eq]
  have hlen : (modLast (· - n) (x.take j)).length = j := by rw [length_modLast]; simp; omega
  unfold tOwn
  have hc : cntD (modLast (· - n) (x.take j) ++ (x[j].1, n + 1 + nAt x (j + 1)) :: x.drop (j + 1)) j =
      n + 1 + nAt x (j + 1) := by
    rw [cntD_eq _ _ (by simp [hlen])]
    rw [List.getElem_append_right (by rw [hlen])]
    simp [hlen]
  rw [hc, List.take_append_of_le_length (by rw [hlen]), List.take_of_length_le (by rw [hlen]),
    List.drop_append, List.drop_eq_nil_of_le (by rw [hlen]; omega), List.nil_append, hlen,
    show j + 1 - j = 1 by omega, List.drop_one, List.tail_cons, modLast_take_cancel x j n hj.le hn,
    show n + 1 + nAt x (j + 1) - n - 1 = nAt x (j + 1) by omega, nAt_succ x j hj]
  exact (split_at x j hj).symm

theorem nAt_of_take (x : List (T × ℕ)) (j : ℕ) (hj : j ≤ x.length) :
    nAt x j = nAt (x.take j) j := by
  cases j with
  | zero => simp [nAt]
  | succ k =>
    rw [nAt_succ x k (by omega), nAt_succ _ k (by simp; omega)]
    simp

theorem tOwn_inv (y x : List (T × ℕ)) (j m : ℕ) (hj : j < y.length) (hm : m < cntD y j)
    (h : tOwn y j y[j].1 m = x) (h0 : j = 0 → m = 0) :
    ∃ hjx : j < x.length, x[j].1 = y[j].1 ∧ shift x (j + 1) j m x[j].1 = y ∧ m ≤ nAt x j := by
  rw [cntD_eq y j hj] at hm
  unfold tOwn at h
  rw [cntD_eq y j hj] at h
  have hlen : (modLast (· + m) (y.take j)).length = j := by rw [length_modLast]; simp; omega
  have hxl : x.length = y.length := by rw [← h]; simp [hlen]; omega
  have hjx : j < x.length := by omega
  have hxj : x[j] = (y[j].1, y[j].2 - m - 1) := by
    simp only [← h]
    rw [List.getElem_append_right (by rw [hlen])]
    simp [hlen]
  have hxt : x.take j = modLast (· + m) (y.take j) := by
    rw [← h, List.take_append_of_le_length (by rw [hlen]), List.take_of_length_le (by rw [hlen])]
  have hxd : x.drop (j + 1) = y.drop (j + 1) := by
    rw [← h, List.drop_append, List.drop_eq_nil_of_le (by rw [hlen]; omega), List.nil_append, hlen,
      show j + 1 - j = 1 by omega, List.drop_one, List.tail_cons]
  have hnx : nAt x (j + 1) = y[j].2 - m - 1 := by rw [nAt_succ x j hjx, hxj]
  refine ⟨hjx, by rw [hxj], ?_, ?_⟩
  · rw [shift_own_eq, hxt, hxd, hnx, modLast_sub_add, hxj,
      show m + 1 + (y[j].2 - m - 1) = y[j].2 by omega]
    exact (split_at y j hj).symm
  · cases j with
    | zero => rw [h0 rfl]; exact Nat.zero_le _
    | succ k =>
      rw [nAt_of_take x (k + 1) hjx.le, hxt, take_succ_split y k (by omega), modLast_append_single,
        nAt_succ _ k (by simp; omega)]
      simp

theorem bD_zero (P : Params C T) (hS : P.Standing) (y : List (T × ℕ)) (hy0 : 0 < y.length) :
    bD P y y[0].1 0 = 0 := by
  unfold bD
  have : ((toks y).take (0 + 1)).toFinset.erase y[0].1 = ∅ := by
    obtain ⟨p, q, rfl⟩ : ∃ p q, y = p :: q := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos hy0)
    simp [toks]
  rw [this, lamU_empty P hS, zero_div]

theorem toks_tOwn (y : List (T × ℕ)) (j m : ℕ) (hj : j < y.length) :
    toks (tOwn y j y[j].1 m) = toks y := by
  unfold tOwn
  rw [toks_append, toks_modLast]
  conv_rhs => rw [split_at y j hj, toks_append]
  rfl

theorem bD_own (P : Params C T) (hS : P.Standing) (x y : List (T × ℕ)) (hx : (toks x).Nodup)
    (j : ℕ) (hjx : j < x.length) (y' : T) (hty : toks y = toks x) (hT : y' = x[j].1) :
    bD P y y' j = beta P x j y' := by
  subst hT
  apply bD_eq_beta P hS
  · rw [hty, ← List.take_append_getElem (by rw [toks_length]; exact hjx), toFinset_append_single]
    simp [toks]
  · intro hmem
    have hnd : ((toks x).take j ++ [x[j].1]).Nodup := by
      have : (toks x).take j ++ [x[j].1] = (toks x).take (j + 1) := by
        rw [← List.take_append_getElem (by rw [toks_length]; exact hjx)]; simp [toks]
      rw [this]; exact hx.sublist (List.take_sublist _ _)
    rw [List.nodup_append] at hnd
    exact hnd.2.2 _ hmem _ (List.mem_singleton_self _) rfl

theorem own_match (P : Params C T) (hS : P.Standing) (x y : List (T × ℕ)) (hx : (toks x).Nodup)
    (hl : y.length = x.length) (j : ℕ) (hj : j < y.length) :
    ∑ m ∈ range (cntD y j), gx x (tOwn y j y[j].1 m,
        muTok P y j * (bD P y y[j].1 j ^ m * (1 - bD P y y[j].1 j))) =
      ∑ n ∈ range (nAt x j + 1),
        muTok P (shift x (j + 1) j n (x[j]'(by omega)).1) j *
          sfac P x (j + 1) j n (x[j]'(by omega)).1 *
          delta y (shift x (j + 1) j n (x[j]'(by omega)).1) := by
  have hjx : j < x.length := by omega
  have hsf : ∀ n, sfac P x (j + 1) j n x[j].1 = beta P x j x[j].1 ^ n * (1 - beta P x j x[j].1) := by
    intro n
    unfold sfac
    rw [Nat.add_sub_cancel, Finset.Icc_eq_empty (by omega), Finset.prod_empty, mul_one]
  -- facts for nonzero left-hand terms
  have hLnz : ∀ m, m ∈ range (cntD y j) → gx x (tOwn y j y[j].1 m,
      muTok P y j * (bD P y y[j].1 j ^ m * (1 - bD P y y[j].1 j))) ≠ 0 →
      tOwn y j y[j].1 m = x ∧ (j = 0 → m = 0) := by
    intro m hm hne
    unfold gx at hne
    simp only at hne
    by_cases h : tOwn y j y[j].1 m = x
    swap
    · simp [h] at hne
    rw [if_pos h] at hne
    refine ⟨h, fun h0 => ?_⟩
    subst h0
    by_contra hm0
    apply hne
    rw [bD_zero P hS y hj, zero_pow hm0]; ring
  apply Finset.sum_bij_ne_zero (fun m _ _ => m)
  · intro m hm hne
    obtain ⟨h1, h2⟩ := hLnz m hm hne
    obtain ⟨_, _, _, hle⟩ := tOwn_inv y x j m hj (by simpa using hm) h1 h2
    simp; omega
  · intro _ _ _ _ _ _ h; exact h
  · intro n hn hne
    simp only [Finset.mem_range] at hn
    have hS' : shift x (j + 1) j n x[j].1 = y := by
      by_contra hc
      apply hne; simp [delta, hc]
    have hc : cntD y j = n + 1 + nAt x (j + 1) := by
      rw [← hS', shift_own_eq]
      have hlen : (modLast (· - n) (x.take j)).length = j := by rw [length_modLast]; simp; omega
      rw [cntD_eq _ _ (by simp [hlen])]
      rw [List.getElem_append_right (by rw [hlen])]
      simp [hlen]
    have hTy : y[j].1 = x[j].1 := by
      have : y[j] = (shift x (j + 1) j n x[j].1)[j]'(by rw [hS']; exact hj) := by simp only [hS']
      rw [this]
      simp only [shift_own_eq]
      rw [List.getElem_append_right (by simp [length_modLast])]
      simp only [length_modLast, List.length_take, Nat.min_eq_left hjx.le, Nat.sub_self,
        List.getElem_cons_zero]
    refine ⟨n, Finset.mem_range.mpr (by rw [hc]; omega), ?_, rfl⟩
    have hto : tOwn y j y[j].1 n = x := by
      have := tOwn_shift x j n hjx (by omega)
      rw [hS'] at this
      rw [hTy]; exact this
    unfold gx
    simp only [if_pos hto]
    intro hz
    apply hne
    rw [bD_own P hS x y hx j hjx _ (by rw [← toks_tOwn y j n hj, hto]) hTy, hTy] at hz
    rw [hS', hsf]
    simp only [delta, if_true, mul_one]
    linear_combination hz
  · intro m hm hne
    obtain ⟨h1, h2⟩ := hLnz m hm hne
    obtain ⟨_, hT, hS', _⟩ := tOwn_inv y x j m hj (by simpa using hm) h1 h2
    unfold gx
    simp only [if_pos h1]
    have hTy : y[j].1 = x[j].1 := hT.symm
    rw [hS', hsf, bD_own P hS x y hx j hjx _ (by rw [← toks_tOwn y j m hj, h1]) hTy, hTy]
    simp [delta]

/-- Generic shape `A ++ p :: D ++ q :: R`. -/
theorem shape1_take (A D R : List (T × ℕ)) (p q : T × ℕ) :
    (A ++ p :: D ++ q :: R).take A.length = A := by
  rw [List.append_assoc, List.take_left]

theorem shape1_get_p (A D R : List (T × ℕ)) (p q : T × ℕ) :
    (A ++ p :: D ++ q :: R)[A.length]'(by simp) = p := by
  simp [List.getElem_append_right]

theorem shape1_mid (A D R : List (T × ℕ)) (p q : T × ℕ) :
    ((A ++ p :: D ++ q :: R).take (A.length + 1 + D.length)).drop (A.length + 1) = D := by
  have e : A ++ p :: D ++ q :: R = (A ++ [p] ++ D) ++ q :: R := by simp
  rw [e, List.take_left' (by simp; omega), List.drop_left' (by simp)]

theorem shape1_get_q (A D R : List (T × ℕ)) (p q : T × ℕ) :
    (A ++ p :: D ++ q :: R)[A.length + 1 + D.length]'(by simp; omega) = q := by
  have e : A ++ p :: D ++ q :: R = (A ++ [p] ++ D) ++ q :: R := by simp
  simp only [e]
  rw [List.getElem_append_right (by simp; omega)]
  simp only [List.length_append, List.length_singleton, show A.length + 1 + D.length -
    (A.length + 1 + D.length) = 0 by omega, List.getElem_cons_zero]

theorem shape1_drop (A D R : List (T × ℕ)) (p q : T × ℕ) :
    (A ++ p :: D ++ q :: R).drop (A.length + 1 + D.length + 1) = R := by
  have e : A ++ p :: D ++ q :: R = (A ++ [p] ++ D ++ [q]) ++ R := by simp
  rw [e, List.drop_left' (by simp; omega)]

theorem shape1_length (A D R : List (T × ℕ)) (p q : T × ℕ) :
    (A ++ p :: D ++ q :: R).length = A.length + 1 + D.length + 1 + R.length := by
  simp; omega

theorem cntD_of_getElem (L : List (T × ℕ)) (i : ℕ) (hi : i < L.length) (p : T × ℕ)
    (h : L[i] = p) : cntD L i = p.2 := by
  rw [cntD_eq L i hi, h]

theorem shape1_cnt_p (A D R : List (T × ℕ)) (p q : T × ℕ) :
    cntD (A ++ p :: D ++ q :: R) A.length = p.2 :=
  cntD_of_getElem _ _ _ _ (shape1_get_p A D R p q)

theorem shape1_cnt_q (A D R : List (T × ℕ)) (p q : T × ℕ) :
    cntD (A ++ p :: D ++ q :: R) (A.length + 1 + D.length) = q.2 :=
  cntD_of_getElem _ _ _ _ (shape1_get_q A D R p q)

def tLaterN (y : List (T × ℕ)) (jn : ℕ) (Tj : T) (ln : ℕ) (Tl : T) (m : ℕ) : List (T × ℕ) :=
  modLast (· + cntD y jn) (y.take jn) ++ (y.take ln).drop (jn + 1) ++
    (Tl, m) :: (Tj, cntD y ln - m - 1) :: y.drop (ln + 1)

theorem tLater_eq (y : List (T × ℕ)) (jn : ℕ) (Tj : T) (l : Fin y.length) (m : ℕ) :
    tLater y jn Tj l m = tLaterN y jn Tj l.val (y.get l).1 m := rfl

theorem take_drop_split (x : List (T × ℕ)) (j l : ℕ) (hjl : j < l) (hl : l ≤ x.length) :
    (x.take l).drop j = (x.take (l - 1)).drop j ++ [x[l - 1]] := by
  rw [show x.take l = x.take (l - 1) ++ [x[l - 1]] by
    rw [List.take_append_getElem (by omega)]; congr 1; omega]
  rw [List.drop_append_of_le_length (by simp; omega)]

theorem shift_later_shape (x : List (T × ℕ)) (j l n : ℕ) (Tj : T) (hjl : j < l)
    (hl : l < x.length) :
    shift x (l + 1) j n Tj = modLast (· - n) (x.take j) ++ (Tj, n) ::
      (x.take (l - 1)).drop j ++ (x[l - 1].1, x[l - 1].2 + (1 + nAt x (l + 1))) :: x.drop (l + 1) := by
  unfold shift
  rw [if_pos (by omega), Nat.add_sub_cancel, take_drop_split x j l hjl hl.le,
    modLast_append_single]
  simp

theorem tLater_shift (x : List (T × ℕ)) (j l n : ℕ) (hjl : j < l) (hl : l < x.length)
    (hn : n ≤ nAt x j) :
    tLaterN (shift x (l + 1) j n x[l].1) j x[l].1 l x[l - 1].1 (nAt x l) = x := by
  rw [shift_later_shape x j l n x[l].1 hjl hl]
  set A := modLast (· - n) (x.take j) with hA
  set D := (x.take (l - 1)).drop j with hD
  have hAl : A.length = j := by rw [hA, length_modLast]; simp; omega
  have hDl : D.length = l - 1 - j := by rw [hD]; simp; omega
  have hjA : j = A.length := hAl.symm
  have hlD : l = A.length + 1 + D.length := by omega
  unfold tLaterN
  have e1 := shape1_take A D (x.drop (l + 1)) (x[l].1, n)
      (x[l - 1].1, x[l - 1].2 + (1 + nAt x (l + 1)))
  have e2 := shape1_cnt_p A D (x.drop (l + 1)) (x[l].1, n)
      (x[l - 1].1, x[l - 1].2 + (1 + nAt x (l + 1)))
  have e3 := shape1_mid A D (x.drop (l + 1)) (x[l].1, n)
      (x[l - 1].1, x[l - 1].2 + (1 + nAt x (l + 1)))
  have e4 := shape1_cnt_q A D (x.drop (l + 1)) (x[l].1, n)
      (x[l - 1].1, x[l - 1].2 + (1 + nAt x (l + 1)))
  have e5 := shape1_drop A D (x.drop (l + 1)) (x[l].1, n)
      (x[l - 1].1, x[l - 1].2 + (1 + nAt x (l + 1)))
  rw [← hlD] at e3 e4 e5
  rw [← hjA] at e1 e2 e3
  rw [e1, e2, e3, e4, e5]
  simp only
  rw [hA, modLast_take_cancel x j n (by omega) hn]
  have hnl : nAt x l = x[l - 1].2 := by
    obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
    rw [nAt_succ x l' (by omega)]; rfl
  have hnl1 : nAt x (l + 1) = x[l].2 := nAt_succ x l hl
  rw [hnl, show x[l - 1].2 + (1 + nAt x (l + 1)) - x[l - 1].2 - 1 = x[l].2 by omega]
  -- reassemble `x`
  have h1 : x.take j ++ D = x.take (l - 1) := by
    rw [hD]
    conv_rhs => rw [← List.take_append_drop j (x.take (l - 1))]
    rw [List.take_take, Nat.min_eq_left (by omega)]
  calc x.take j ++ D ++ (x[l - 1].1, x[l - 1].2) :: (x[l].1, x[l].2) :: x.drop (l + 1)
      = (x.take (l - 1) ++ [x[l - 1]]) ++ x[l] :: x.drop (l + 1) := by
        rw [h1, List.append_assoc, List.singleton_append]
    _ = x := by
      have h2 : x.take (l - 1) ++ [x[l - 1]] = x.take l := by
        rw [List.take_append_getElem (by omega)]; congr 1; omega
      rw [h2]
      exact (split_at x l hl).symm

theorem split2 (y : List (T × ℕ)) (j l : ℕ) (hjl : j < l) (hl : l < y.length) :
    y = y.take j ++ y[j] :: (y.take l).drop (j + 1) ++ y[l] :: y.drop (l + 1) := by
  have h1 : y.take j ++ y[j] :: (y.take l).drop (j + 1) = y.take l := by
    calc y.take j ++ y[j] :: (y.take l).drop (j + 1)
        = (y.take j ++ [y[j]]) ++ (y.take l).drop (j + 1) := by
          rw [List.append_assoc, List.singleton_append]
      _ = y.take (j + 1) ++ (y.take l).drop (j + 1) := by rw [List.take_append_getElem (by omega)]
      _ = (y.take l).take (j + 1) ++ (y.take l).drop (j + 1) := by
        rw [List.take_take, Nat.min_eq_left (by omega)]
      _ = y.take l := List.take_append_drop _ _
  rw [h1]
  exact split_at y l hl

theorem shape2_get1 (A D R : List (T × ℕ)) (q1 q2 : T × ℕ) :
    ((A ++ D) ++ [q1, q2] ++ R)[A.length + D.length]? = some q1 := by
  rw [List.append_assoc, List.getElem?_append_right (by simp)]
  simp

theorem shape2_get2 (A D R : List (T × ℕ)) (q1 q2 : T × ℕ) :
    ((A ++ D) ++ [q1, q2] ++ R)[A.length + D.length + 1]? = some q2 := by
  rw [List.append_assoc, List.getElem?_append_right (by simp)]
  simp [show A.length + D.length + 1 - (A.length + D.length) = 1 by omega]

theorem getElem_of_getElem? {L : List (T × ℕ)} {i : ℕ} {q : T × ℕ} (hi : i < L.length)
    (h : L[i]? = some q) : L[i] = q := by
  rw [List.getElem?_eq_getElem hi] at h
  exact Option.some_inj.mp h

theorem tLater_inv (y x : List (T × ℕ)) (j l m : ℕ) (hjl : j < l) (hl : l < y.length)
    (hm : m < cntD y l) (h : tLaterN y j y[j].1 l y[l].1 m = x) (h0 : j = 0 → cntD y 0 = 0) :
    ∃ hlx : l < x.length, x[l].1 = y[j].1 ∧ shift x (l + 1) j (cntD y j) x[l].1 = y ∧
      cntD y j ≤ nAt x j ∧ m = nAt x l := by
  unfold tLaterN at h
  set c := cntD y j with hc
  set A' := modLast (· + c) (y.take j) with hA'
  set Dy := (y.take l).drop (j + 1) with hDy
  set R := y.drop (l + 1) with hR
  have hA'l : A'.length = j := by rw [hA', length_modLast]; simp; omega
  have hDl : Dy.length = l - j - 1 := by rw [hDy]; simp; omega
  have hxe : x = (A' ++ Dy) ++ [(y[l].1, m), (y[j].1, cntD y l - m - 1)] ++ R := by
    rw [← h]; simp
  have hxl : x.length = y.length := by rw [hxe]; simp [hA'l, hDl, hR]; omega
  have hlx : l < x.length := by omega
  have hjy : j < y.length := Nat.lt_trans hjl hl
  have hxl' : x[l] = ((y[j]'hjy).1, cntD y l - m - 1) := by
    apply getElem_of_getElem? hlx
    have key := shape2_get2 A' Dy R ((y[l]'hl).1, m) ((y[j]'hjy).1, cntD y l - m - 1)
    rw [show A'.length + Dy.length + 1 = l by omega] at key
    rw [hxe]; exact key
  have hxl1 : x[l - 1]'(by omega) = ((y[l]'hl).1, m) := by
    apply getElem_of_getElem? (by omega)
    have key := shape2_get1 A' Dy R ((y[l]'hl).1, m) ((y[j]'hjy).1, cntD y l - m - 1)
    rw [show A'.length + Dy.length = l - 1 by omega] at key
    rw [hxe]; exact key
  have hxt : x.take j = A' := by
    rw [hxe, List.append_assoc, List.append_assoc, List.take_left' hA'l]
  have hxtd : (x.take (l - 1)).drop j = Dy := by
    rw [hxe, List.append_assoc, List.take_left' (by simp [hA'l, hDl]; omega), List.drop_left' hA'l]
  have hxd : x.drop (l + 1) = R := by
    rw [hxe, List.drop_left' (by simp [hA'l, hDl]; omega)]
  have hnl : nAt x l = m := by
    obtain ⟨l', hl'⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
    have := hxl1
    simp only [hl', Nat.add_sub_cancel] at this
    rw [hl', nAt_succ x l' (by omega), this]
  have hnl1 : nAt x (l + 1) = cntD y l - m - 1 := by
    rw [nAt_succ x l hlx, hxl']
  refine ⟨hlx, by rw [hxl'], ?_, ?_, hnl.symm⟩
  · rw [shift_later_shape x j l c x[l].1 hjl hlx, hxt, hxtd, hxd, hxl1, hnl1, hxl', hA',
      modLast_sub_add]
    simp only
    rw [show m + (1 + (cntD y l - m - 1)) = cntD y l by omega]
    conv_rhs => rw [split2 y j l hjl hl]
    rw [hc, cntD_eq y j (by omega), cntD_eq y l hl]
  · cases j with
    | zero => rw [hc, h0 rfl]; exact Nat.zero_le _
    | succ k =>
      rw [nAt_of_take x (k + 1) (by omega), hxt, hA', take_succ_split y k (by omega),
        modLast_append_single, nAt_succ _ k (by simp; omega)]
      simp

theorem toks_shift_later (x : List (T × ℕ)) (j l n : ℕ) (Tj : T) (hjl : j < l)
    (hl : l < x.length) :
    toks (shift x (l + 1) j n Tj) =
      (toks x).take j ++ Tj :: ((toks x).take l).drop j ++ (toks x).drop (l + 1) := by
  unfold shift
  rw [if_pos (by omega), Nat.add_sub_cancel]
  simp only [toks_append, toks_modLast, toks_take, toks_drop, pre, List.cons_append,
    toks, List.map_cons, List.map_append, List.map_take, List.map_drop, map_fst_modLast]

theorem prefix_shift_later (x : List (T × ℕ)) (j l n : ℕ) (Tj : T) (hjl : j < l)
    (hl : l < x.length) (l' : ℕ) (hjl' : j ≤ l') (hl' : l' ≤ l) :
    ((toks (shift x (l + 1) j n Tj)).take (l' + 1)).toFinset = insert Tj ((toks x).take l').toFinset := by
  rw [toks_shift_later x j l n Tj hjl hl]
  have hlen : ((toks x).take j).length = j := by simp [toks_length]; omega
  have e : ((toks x).take j ++ Tj :: ((toks x).take l).drop j ++ (toks x).drop (l + 1)).take (l' + 1) =
      (toks x).take j ++ Tj :: (((toks x).take l).drop j).take (l' - j) := by
    rw [List.append_assoc, List.take_append, hlen, List.take_of_length_le (by omega),
      show l' + 1 - j = (l' - j) + 1 by omega, List.cons_append, List.take_succ_cons,
      List.take_append_of_le_length (by simp [toks_length]; omega)]
  rw [e]
  have e2 : (toks x).take l' = (toks x).take j ++ (((toks x).take l).drop j).take (l' - j) := by
    rw [List.drop_take, List.take_take, Nat.min_eq_left (by omega), ← List.take_add,
      show j + (l' - j) = l' by omega]
  rw [e2]
  ext a; simp

theorem notin_prefix (x : List (T × ℕ)) (hx : (toks x).Nodup) (l l' : ℕ) (hl : l < x.length)
    (hl' : l' ≤ l) : x[l].1 ∉ (toks x).take l' := by
  intro hmem
  have hmem' : x[l].1 ∈ (toks x).take l := List.take_subset_take_left _ hl' hmem
  have hnd : ((toks x).take l ++ [x[l].1]).Nodup := by
    have : (toks x).take l ++ [x[l].1] = (toks x).take (l + 1) := by
      rw [← List.take_append_getElem (by rw [toks_length]; exact hl)]; simp [toks]
    rw [this]; exact hx.sublist (List.take_sublist _ _)
  rw [List.nodup_append] at hnd
  exact hnd.2.2 _ hmem' _ (List.mem_singleton_self _) rfl

theorem bD_later (P : Params C T) (hS : P.Standing) (x : List (T × ℕ)) (hx : (toks x).Nodup)
    (j l n : ℕ) (hjl : j < l) (hl : l < x.length) (l' : ℕ) (hjl' : j ≤ l') (hl' : l' ≤ l) :
    bD P (shift x (l + 1) j n x[l].1) x[l].1 l' = beta P x l' x[l].1 :=
  bD_eq_beta P hS _ _ _ _ (prefix_shift_later x j l n _ hjl hl l' hjl' hl')
    (notin_prefix x hx l l' hl hl')

theorem cntD_shape_mid (A D R : List (T × ℕ)) (p q : T × ℕ) (r : ℕ) (hr : r < D.length) :
    cntD (A ++ p :: D ++ q :: R) (A.length + 1 + r) = cntD D r := by
  unfold cntD
  simp only [List.getD_eq_getElem?_getD, List.map_append, List.map_cons]
  rw [List.append_assoc, List.getElem?_append_right (by simp; omega)]
  simp only [List.length_map, show A.length + 1 + r - A.length = r + 1 by omega,
    List.cons_append, List.getElem?_cons_succ]
  rw [List.getElem?_append_left (by simpa using hr)]

theorem cntD_shift_mid (x : List (T × ℕ)) (j l n : ℕ) (Tj : T) (hjl : j < l) (hl : l < x.length)
    (l' : ℕ) (hjl' : j < l') (hl' : l' < l) :
    cntD (shift x (l + 1) j n Tj) l' = nAt x l' := by
  rw [shift_later_shape x j l n Tj hjl hl]
  have hAl : (modLast (· - n) (x.take j)).length = j := by rw [length_modLast]; simp; omega
  have := cntD_shape_mid (modLast (· - n) (x.take j)) ((x.take (l - 1)).drop j) (x.drop (l + 1))
    (Tj, n) (x[l - 1].1, x[l - 1].2 + (1 + nAt x (l + 1))) (l' - j - 1) (by simp; omega)
  rw [hAl, show j + 1 + (l' - j - 1) = l' by omega] at this
  rw [this]
  obtain ⟨l'', rfl⟩ : ∃ l'', l' = l'' + 1 := ⟨l' - 1, by omega⟩
  unfold cntD nAt
  simp only [List.getD_eq_getElem?_getD, if_neg (Nat.succ_ne_zero l''), Nat.add_sub_cancel,
    List.getElem?_map, List.getElem?_drop, List.getElem?_take]
  rw [if_pos (by omega)]
  congr 3; omega

theorem cntD_shift_j (x : List (T × ℕ)) (j l n : ℕ) (Tj : T) (hjl : j < l) (hl : l < x.length) :
    cntD (shift x (l + 1) j n Tj) j = n := by
  rw [shift_later_shape x j l n Tj hjl hl]
  have hAl : (modLast (· - n) (x.take j)).length = j := by rw [length_modLast]; simp; omega
  have := shape1_cnt_p (modLast (· - n) (x.take j)) ((x.take (l - 1)).drop j) (x.drop (l + 1))
    (Tj, n) (x[l - 1].1, x[l - 1].2 + (1 + nAt x (l + 1)))
  rw [hAl] at this
  exact this

theorem cntD_shift_l (x : List (T × ℕ)) (j l n : ℕ) (Tj : T) (hjl : j < l) (hl : l < x.length) :
    cntD (shift x (l + 1) j n Tj) l = nAt x l + (1 + nAt x (l + 1)) := by
  rw [shift_later_shape x j l n Tj hjl hl]
  have hAl : (modLast (· - n) (x.take j)).length = j := by rw [length_modLast]; simp; omega
  have hDl : ((x.take (l - 1)).drop j).length = l - 1 - j := by simp; omega
  have := shape1_cnt_q (modLast (· - n) (x.take j)) ((x.take (l - 1)).drop j) (x.drop (l + 1))
    (Tj, n) (x[l - 1].1, x[l - 1].2 + (1 + nAt x (l + 1)))
  rw [hAl, hDl, show j + 1 + (l - 1 - j) = l by omega] at this
  rw [this]
  obtain ⟨l'', rfl⟩ : ∃ l'', l = l'' + 1 := ⟨l - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [nAt_succ x l'' (by omega)]

theorem survD_shift_later (P : Params C T) (hS : P.Standing) (x : List (T × ℕ)) (hx : (toks x).Nodup)
    (j l n : ℕ) (hjl : j < l) (hl : l < x.length) :
    survD P (shift x (l + 1) j n x[l].1) x[l].1 j l =
      beta P x j x[l].1 ^ n * ∏ l' ∈ Ico (j + 1) l, beta P x l' x[l].1 ^ nAt x l' := by
  unfold survD
  rw [Finset.prod_eq_prod_Ico_succ_bot hjl, bD_later P hS x hx j l n hjl hl j le_rfl hjl.le,
    cntD_shift_j x j l n _ hjl hl]
  congr 1
  apply Finset.prod_congr rfl
  intro l' hl'
  simp only [Finset.mem_Ico] at hl'
  rw [bD_later P hS x hx j l n hjl hl l' (by omega) (by omega),
    cntD_shift_mid x j l n _ hjl hl l' (by omega) hl'.2]

theorem shape1_get?_p (A D R : List (T × ℕ)) (p q : T × ℕ) :
    (A ++ p :: D ++ q :: R)[A.length]? = some p := by
  rw [List.append_assoc, List.getElem?_append_right (by simp)]; simp

theorem shape1_get?_q (A D R : List (T × ℕ)) (p q : T × ℕ) :
    (A ++ p :: D ++ q :: R)[A.length + 1 + D.length]? = some q := by
  rw [List.append_assoc, List.getElem?_append_right (by omega)]
  simp only [show A.length + 1 + D.length - A.length = D.length + 1 by omega, List.cons_append,
    List.getElem?_cons_succ]
  rw [List.getElem?_append_right (by simp)]; simp

theorem shift_later_get_j (x : List (T × ℕ)) (j l n : ℕ) (Tj : T) (hjl : j < l) (hl : l < x.length) :
    (shift x (l + 1) j n Tj)[j]? = some (Tj, n) := by
  rw [shift_later_shape x j l n Tj hjl hl]
  have hAl : (modLast (· - n) (x.take j)).length = j := by rw [length_modLast]; simp; omega
  have := shape1_get?_p (modLast (· - n) (x.take j)) ((x.take (l - 1)).drop j) (x.drop (l + 1))
    (Tj, n) (x[l - 1].1, x[l - 1].2 + (1 + nAt x (l + 1)))
  rw [hAl] at this; exact this

theorem shift_later_get_l (x : List (T × ℕ)) (j l n : ℕ) (Tj : T) (hjl : j < l) (hl : l < x.length) :
    (shift x (l + 1) j n Tj)[l]? = some (x[l - 1].1, x[l - 1].2 + (1 + nAt x (l + 1))) := by
  rw [shift_later_shape x j l n Tj hjl hl]
  have hAl : (modLast (· - n) (x.take j)).length = j := by rw [length_modLast]; simp; omega
  have hDl : ((x.take (l - 1)).drop j).length = l - 1 - j := by simp; omega
  have := shape1_get?_q (modLast (· - n) (x.take j)) ((x.take (l - 1)).drop j) (x.drop (l + 1))
    (Tj, n) (x[l - 1].1, x[l - 1].2 + (1 + nAt x (l + 1)))
  rw [hAl, hDl, show j + 1 + (l - 1 - j) = l by omega] at this; exact this

theorem shift_later_length (x : List (T × ℕ)) (j l n : ℕ) (Tj : T) (hjl : j < l) (hl : l < x.length) :
    (shift x (l + 1) j n Tj).length = x.length := by
  rw [shift_later_shape x j l n Tj hjl hl]
  simp [length_modLast]; omega

theorem later_value (P : Params C T) (hS : P.Standing) (x : List (T × ℕ)) (hx : (toks x).Nodup)
    (j l n : ℕ) (hjl : j < l) (hl : l < x.length) (hn : n ≤ nAt x j) :
    gx x (tLaterN (shift x (l + 1) j n x[l].1) j x[l].1 l x[l - 1].1 (nAt x l),
      muTok P (shift x (l + 1) j n x[l].1) j *
        (survD P (shift x (l + 1) j n x[l].1) x[l].1 j l *
          bD P (shift x (l + 1) j n x[l].1) x[l].1 l ^ nAt x l *
          (1 - bD P (shift x (l + 1) j n x[l].1) x[l].1 l))) =
      muTok P (shift x (l + 1) j n x[l].1) j * sfac P x (l + 1) j n x[l].1 *
        delta (shift x (l + 1) j n x[l].1) (shift x (l + 1) j n x[l].1) := by
  unfold gx
  rw [if_pos (tLater_shift x j l n hjl hl hn), survD_shift_later P hS x hx j l n hjl hl,
    bD_later P hS x hx j l n hjl hl l hjl.le le_rfl]
  simp only [delta, if_true, mul_one]
  unfold sfac
  rw [Nat.add_sub_cancel, ← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_succ_top (by omega)]
  ring

theorem later_match (P : Params C T) (hS : P.Standing) (x y : List (T × ℕ)) (hx : (toks x).Nodup)
    (hlen : y.length = x.length) (j l : ℕ) (hjl : j < l) (hl : l < y.length) :
    ∑ m ∈ range (cntD y l), gx x (tLaterN y j (y[j]'(by omega)).1 l (y[l]'hl).1 m,
        muTok P y j * (survD P y (y[j]'(by omega)).1 j l * bD P y (y[j]'(by omega)).1 l ^ m *
          (1 - bD P y (y[j]'(by omega)).1 l))) =
      ∑ n ∈ range (nAt x j + 1),
        muTok P (shift x (l + 1) j n (x[l]'(by omega)).1) j *
          sfac P x (l + 1) j n (x[l]'(by omega)).1 *
          delta y (shift x (l + 1) j n (x[l]'(by omega)).1) := by
  have hlx : l < x.length := by omega
  have hjy : j < y.length := by omega
  -- nonzero left-hand terms come from genuine transitions
  have hLnz : ∀ m, m ∈ range (cntD y l) →
      gx x (tLaterN y j (y[j]'hjy).1 l (y[l]'hl).1 m,
        muTok P y j * (survD P y (y[j]'hjy).1 j l * bD P y (y[j]'hjy).1 l ^ m *
          (1 - bD P y (y[j]'hjy).1 l))) ≠ 0 →
      tLaterN y j (y[j]'hjy).1 l (y[l]'hl).1 m = x ∧ (j = 0 → cntD y 0 = 0) := by
    intro m hm hne
    unfold gx at hne
    simp only at hne
    by_cases h : tLaterN y j (y[j]'hjy).1 l (y[l]'hl).1 m = x
    swap
    · simp [h] at hne
    rw [if_pos h] at hne
    refine ⟨h, fun h0 => ?_⟩
    subst h0
    by_contra hc
    apply hne
    have : survD P y (y[0]'hjy).1 0 l = 0 := by
      unfold survD
      apply Finset.prod_eq_zero (i := 0) (by simp; omega)
      rw [bD_zero P hS y hjy]
      exact zero_pow hc
    rw [this]; ring
  apply Finset.sum_bij_ne_zero (fun m _ _ => cntD y j)
  · intro m hm hne
    obtain ⟨h1, h2⟩ := hLnz m hm hne
    obtain ⟨_, _, _, hle, _⟩ := tLater_inv y x j l m hjl hl (by simpa using hm) h1 h2
    simp; omega
  · intro m1 hm1 hne1 m2 hm2 hne2 _
    obtain ⟨a1, b1⟩ := hLnz m1 hm1 hne1
    obtain ⟨a2, b2⟩ := hLnz m2 hm2 hne2
    obtain ⟨_, _, _, _, e1⟩ := tLater_inv y x j l m1 hjl hl (by simpa using hm1) a1 b1
    obtain ⟨_, _, _, _, e2⟩ := tLater_inv y x j l m2 hjl hl (by simpa using hm2) a2 b2
    rw [e1, e2]
  · intro n hn hne
    simp only [Finset.mem_range] at hn
    have hSy : shift x (l + 1) j n (x[l]'hlx).1 = y := by
      by_contra hc
      apply hne; simp [delta, hc]
    have hc : cntD y j = n := by rw [← hSy]; exact cntD_shift_j x j l n _ hjl hlx
    have hyj : (y[j]'hjy).1 = (x[l]'hlx).1 := by
      have h1 := shift_later_get_j x j l n (x[l]'hlx).1 hjl hlx
      rw [hSy] at h1
      rw [getElem_of_getElem? hjy h1]
    have hyl : (y[l]'hl).1 = (x[l - 1]'(by omega)).1 := by
      have h1 := shift_later_get_l x j l n (x[l]'hlx).1 hjl hlx
      rw [hSy] at h1
      rw [getElem_of_getElem? hl h1]
    have hcl : cntD y l = nAt x l + (1 + nAt x (l + 1)) := by
      rw [← hSy]; exact cntD_shift_l x j l n _ hjl hlx
    refine ⟨nAt x l, by simp; omega, ?_, hc⟩
    have hv := later_value P hS x hx j l n hjl hlx (by omega)
    rw [hSy] at hv
    rw [hyj, hyl, hv]
    rw [hSy] at hne
    exact hne
  · intro m hm hne
    obtain ⟨h1, h2⟩ := hLnz m hm hne
    obtain ⟨_, hT, hSy, hle, hmx⟩ := tLater_inv y x j l m hjl hl (by simpa using hm) h1 h2
    have hyj : (y[j]'hjy).1 = (x[l]'hlx).1 := hT.symm
    have hyl : (y[l]'hl).1 = (x[l - 1]'(by omega)).1 := by
      have h3 := shift_later_get_l x j l (cntD y j) (x[l]'hlx).1 hjl hlx
      rw [hSy] at h3
      rw [getElem_of_getElem? hl h3]
    have hv := later_value P hS x hx j l (cntD y j) hjl hlx hle
    rw [hSy] at hv
    rw [hyj, hyl, hmx, hv, hSy]

theorem tOwn_length (y : List (T × ℕ)) (j : ℕ) (Tj : T) (m : ℕ) (hj : j < y.length) :
    (tOwn y j Tj m).length = y.length := by
  simp [tOwn, length_modLast]; omega

theorem tLaterN_length (y : List (T × ℕ)) (j l : ℕ) (Tj Tl : T) (m : ℕ) (hjl : j < l)
    (hl : l < y.length) : (tLaterN y j Tj l Tl m).length = y.length := by
  simp [tLaterN, length_modLast]; omega

theorem shift_length (x : List (T × ℕ)) (J k n : ℕ) (Tj : T) (hkJ : k ≤ J) (hJ : J < x.length) :
    (shift x (J + 1) k n Tj).length = x.length := by
  rcases lt_or_eq_of_le hkJ with h | h
  · exact shift_later_length x k J n Tj h hJ
  · subst h; rw [shift_own_eq]; simp [length_modLast]; omega

theorem sum_finRange_filter_lt' (n j : ℕ) (h : Fin n → ℝ) :
    (((List.finRange n).filter (fun l : Fin n => decide (j < l.val))).map h).sum =
      ∑ l ∈ Ico (j + 1) n, (if hl : l < n then h ⟨l, hl⟩ else 0) := by
  rw [list_sum_filter_map]
  have : ((List.finRange n).map
      (fun a : Fin n => if decide (j < a.val) = true then h a else 0)).sum =
      ∑ a : Fin n, if j < a.val then h a else 0 := by
    rw [Fin.sum_univ_def]; simp
  rw [this, Finset.sum_fin_eq_sum_range]
  rw [← Finset.sum_filter_add_sum_filter_not (range n) (fun l => j < l)]
  have h2 : ∑ x ∈ (range n).filter (fun l => ¬ j < l),
      (if hx : x < n then (if j < (⟨x, hx⟩ : Fin n).val then h ⟨x, hx⟩ else 0) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    simp only [Finset.mem_filter] at hx
    split_ifs <;> simp_all
  rw [h2, add_zero]
  have hset : (range n).filter (fun l => j < l) = Ico (j + 1) n := by
    ext l; simp; omega
  rw [hset]
  apply Finset.sum_congr rfl
  intro l hl
  simp only [Finset.mem_Ico] at hl
  rw [dif_pos (by omega), dif_pos (by omega), if_pos (by simp; omega)]

theorem sh_match (P : Params C T) (hS : P.Standing) (x y : List (T × ℕ)) (hx : (toks x).Nodup) :
    ∑ j : Fin y.length,
      (((((List.range (cntD y j.val)).map fun m =>
        (tOwn y j.val (y.get j).1 m,
          muTok P y j.val * (bD P y (y.get j).1 j.val ^ m * (1 - bD P y (y.get j).1 j.val))))).map
          (gx x)).sum +
      (((((List.finRange y.length).filter (fun l => j < l)).flatMap fun l =>
        (List.range (cntD y l.val)).map fun m =>
          (tLater y j.val (y.get j).1 l m,
            muTok P y j.val * (survD P y (y.get j).1 j.val l.val * bD P y (y.get j).1 l.val ^ m *
              (1 - bD P y (y.get j).1 l.val))))).map (gx x)).sum) =
    ∑ J : Fin x.length, ∑ k ∈ range (J.val + 1), ∑ n ∈ range (nAt x k + 1),
      muTok P (shift x (J.val + 1) k n (x.get J).1) k * sfac P x (J.val + 1) k n (x.get J).1 *
        delta y (shift x (J.val + 1) k n (x.get J).1) := by
  by_cases hlen : y.length = x.length
  · -- rewrite the right-hand side as a sum over `k` first
    set N := x.length with hN
    set H : ℕ → ℕ → ℝ := fun J k => if hJ : J < N then ∑ n ∈ range (nAt x k + 1),
      muTok P (shift x (J + 1) k n (x[J]'hJ).1) k * sfac P x (J + 1) k n (x[J]'hJ).1 *
        delta y (shift x (J + 1) k n (x[J]'hJ).1) else 0 with hH
    have hR : ∑ J : Fin x.length, ∑ k ∈ range (J.val + 1), ∑ n ∈ range (nAt x k + 1),
        muTok P (shift x (J.val + 1) k n (x.get J).1) k * sfac P x (J.val + 1) k n (x.get J).1 *
          delta y (shift x (J.val + 1) k n (x.get J).1) =
        ∑ k ∈ range N, (H k k + ∑ J ∈ Ico (k + 1) N, H J k) := by
      rw [Finset.sum_fin_eq_sum_range]
      have e1 : ∀ J ∈ range N, (if h : J < x.length then ∑ k ∈ range ((⟨J, h⟩ : Fin x.length).val + 1),
          ∑ n ∈ range (nAt x k + 1),
            muTok P (shift x ((⟨J, h⟩ : Fin x.length).val + 1) k n (x.get ⟨J, h⟩).1) k *
              sfac P x ((⟨J, h⟩ : Fin x.length).val + 1) k n (x.get ⟨J, h⟩).1 *
              delta y (shift x ((⟨J, h⟩ : Fin x.length).val + 1) k n (x.get ⟨J, h⟩).1) else 0) =
          ∑ k ∈ range (J + 1), H J k := by
        intro J hJ
        simp only [Finset.mem_range] at hJ
        rw [dif_pos hJ]
        apply Finset.sum_congr rfl
        intro k _
        simp only [hH, dif_pos hJ, List.get_eq_getElem]
      rw [Finset.sum_congr rfl e1]
      rw [Finset.sum_comm' (t' := range N) (s' := fun k => Ico k N)]
      · apply Finset.sum_congr rfl
        intro k hk
        simp only [Finset.mem_range] at hk
        rw [Finset.sum_eq_sum_Ico_succ_bot hk]
      · intro J k
        simp only [Finset.mem_range, Finset.mem_Ico]
        omega
    rw [hR, Finset.sum_fin_eq_sum_range, ← hlen]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_range] at hj
    rw [dif_pos hj]
    simp only [List.get_eq_getElem]
    congr 1
    · -- own part
      rw [List.map_map, list_range_sum]
      have := own_match P hS x y hx hlen j hj
      rw [show H j j = _ from dif_pos (by omega)]
      convert this using 2
      rfl
    · -- later part
      rw [sum_map_flatMap]
      have hf : (List.finRange y.length).filter (fun l => decide ((⟨j, hj⟩ : Fin y.length) < l)) =
          (List.finRange y.length).filter (fun l : Fin y.length => decide (j < l.val)) := by
        congr 1
      rw [hf, sum_finRange_filter_lt']
      apply Finset.sum_congr rfl
      intro l hl
      simp only [Finset.mem_Ico] at hl
      rw [dif_pos hl.2]
      simp only [hH, dif_pos (show l < N by omega)]
      rw [List.map_map, list_range_sum]
      have := later_match P hS x y hx hlen j l (by omega) hl.2
      convert this using 2
      rfl
  · rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
    · intro J _
      apply Finset.sum_eq_zero
      intro k hk
      apply Finset.sum_eq_zero
      intro n _
      simp only [Finset.mem_range] at hk
      have : shift x (J.val + 1) k n (x.get J).1 ≠ y := by
        intro h
        apply hlen
        rw [← h, shift_length x J.val k n _ (by omega) J.2]
      simp only [List.get_eq_getElem] at this
      simp [delta, this]
    · intro j _
      have hj := j.2
      have h1 : ((((List.range (cntD y j.val)).map fun m =>
          (tOwn y j.val (y.get j).1 m,
            muTok P y j.val * (bD P y (y.get j).1 j.val ^ m * (1 - bD P y (y.get j).1 j.val))))).map
            (gx x)).sum = 0 := by
        rw [List.map_map, list_range_sum]
        apply Finset.sum_eq_zero
        intro m _
        simp only [Function.comp, gx]
        rw [if_neg]
        intro h
        apply hlen
        rw [← h, tOwn_length y j.val _ m hj]
      have h2 : (((((List.finRange y.length).filter (fun l => j < l)).flatMap fun l =>
          (List.range (cntD y l.val)).map fun m =>
            (tLater y j.val (y.get j).1 l m,
              muTok P y j.val * (survD P y (y.get j).1 j.val l.val * bD P y (y.get j).1 l.val ^ m *
                (1 - bD P y (y.get j).1 l.val))))).map (gx x)).sum = 0 := by
        rw [sum_map_flatMap]
        apply List.sum_eq_zero
        intro v hv
        simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and,
          decide_eq_true_eq] at hv
        obtain ⟨l, hl, rfl⟩ := hv
        rw [List.map_map, list_range_sum]
        apply Finset.sum_eq_zero
        intro m _
        simp only [Function.comp, gx]
        rw [if_neg]
        intro h
        apply hlen
        rw [← h, tLater_eq, tLaterN_length y j.val l.val _ _ m hl l.2]
      rw [h1, h2, add_zero]

theorem rate_eq_delta (P : Params C T) (hS : P.Standing) (x y : State T) :
    rate P y x = balanceRHS P (delta y.1) x.1 := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy⟩ := y
  simp only
  unfold rate
  simp only
  rw [list_sum_filter_map]
  have hg : (fun a : List (T × ℕ) × ℝ => if decide (a.1 = x) = true then a.2 else 0) = gx x := by
    funext a; simp [gx]
  rw [hg]
  unfold transitions
  rw [List.map_append, List.sum_append, sum_map_flatMap]
  simp only [departures_eq, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]
  rw [← Fin.sum_univ_def]
  simp only [Finset.sum_add_distrib]
  unfold balanceRHS
  simp only
  have hRel := rel_match P hS x y hy
  have hSh := sh_match P hS x y hx
  have hA := arrA P y x
  rw [List.map_append, List.sum_append] at hA
  rw [hA, hRel]
  rw [Finset.sum_add_distrib] at hSh
  rw [hSh]
  -- arrival part
  rcases concat_cases' x with rfl | ⟨X, t0, n0, rfl⟩
  · simp only [List.getLast?_nil]
    rw [arr_nil P y]
    ring
  · rw [show (X ++ [(t0, n0)]).getLast? = some (t0, n0) by simp]
    simp only
    rw [arr_concat P y X t0 n0 hx, modLast_append_single, List.dropLast_concat]
    have hp : pre (X ++ [(t0, n0)]) ((X ++ [(t0, n0)]).length - 1) = toks X := by
      simp [pre, toks]
    rw [hp]
    ring

end TQLib

theorem solution {C T : Type} [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T]
    (P : Params C T) (hS : P.Standing) (π : State T → ℝ) (x : State T) :
    HasSum (fun y => π y * rate P y x) (balanceRHS P (piExt π) x.1) := by
  have h := hasSum_FC (balanceRHS_FC P x.1) π
  convert h using 1
  funext y
  rw [rate_eq_delta P hS x y]
