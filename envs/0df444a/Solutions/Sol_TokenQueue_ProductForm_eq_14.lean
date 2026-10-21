-- Prove2me | solution 1 for TokenQueue.ProductForm.eq_14
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T08:41:02.691853+00:00
-- url     : https://prove2.me/submissions/a70d843f-a16a-449f-8658-1238b6675ffc

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

end TQLib

open TQLib TokenQueue.ProductForm Finset

namespace TQLib

variable {C T : Type} [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T]

theorem nAt_append_left (Y Z : List (T × ℕ)) (r : ℕ) (hr : r < Y.length) :
    nAt (Y ++ Z) (r + 1) = nAt Y (r + 1) := by
  rw [nAt_succ _ r (by simp; omega), nAt_succ _ r hr, List.getElem_append_left hr]

theorem nAt_take (x : List (T × ℕ)) (j r : ℕ) (hr : r < j) :
    nAt (x.take j) (r + 1) = nAt x (r + 1) := by
  simp [nAt, List.getD_eq_getElem?_getD, List.map_take, List.getElem?_take, hr]

theorem prod_range_modLast (Mx : List (T × ℕ)) (hM : Mx ≠ []) (f : ℕ → ℝ) (c : ℕ) :
    ∏ r ∈ range Mx.length, f r ^ nAt (modLast (· + c) Mx) (r + 1) =
      (∏ r ∈ range Mx.length, f r ^ nAt Mx (r + 1)) * f (Mx.length - 1) ^ c := by
  rcases concat_cases' Mx with h | ⟨Y, a, b, rfl⟩
  · exact absurd h hM
  · rw [modLast_append_single]
    simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel]
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    have e : ∀ r ∈ range Y.length, f r ^ nAt (Y ++ [(a, b + c)]) (r + 1) =
        f r ^ nAt (Y ++ [(a, b)]) (r + 1) := by
      intro r hr
      simp only [mem_range] at hr
      rw [nAt_append_left _ _ r hr, nAt_append_left _ _ r hr]
    rw [Finset.prod_congr rfl e]
    have h1 : nAt (Y ++ [(a, b + c)]) (Y.length + 1) = b + c := by
      rw [nAt_succ _ _ (by simp)]; simp
    have h2 : nAt (Y ++ [(a, b)]) (Y.length + 1) = b := by
      rw [nAt_succ _ _ (by simp)]; simp
    rw [h1, h2, pow_add]; ring

end TQLib

namespace TQLib

variable {C T : Type} [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T]

theorem eq14_term (P : Params C T) (hS : P.Standing) (h1 : Condition1 P) (h2 : Condition2 P)
    (hk : KPos P) (xs : List (T × ℕ)) (hxs : (xs.map Prod.fst).Nodup) (j : ℕ)
    (hj : j < xs.length) (k : ℕ) (hkj : k ≤ j) (n : ℕ) (hn : n ≤ nAt xs k) :
    muTok P (shift xs (j + 1) k n xs[j].1) k * sfac P xs (j + 1) k n xs[j].1 *
        weightL P (shift xs (j + 1) k n xs[j].1) =
      weightL P xs *
        (lamU P ((toks xs).take (j + 1)).toFinset - lamU P ((toks xs).take j).toFinset) *
        ((kfun P ((toks xs).take k ++ [xs[j].1]) - kfun P ((toks xs).take k)) /
            kfun P ((toks xs).take k ++ [xs[j].1]) *
          (∏ m ∈ Icc (k + 1) j,
            (kfun P ((toks xs).take m) / kfun P ((toks xs).take m ++ [xs[j].1])) ^ (nAt xs m + 1)) *
          (kfun P ((toks xs).take k) / kfun P ((toks xs).take k ++ [xs[j].1])) ^ n) := by
  have e57 := (TokenQueue.ProductForm.eq_5_7 P ⟨xs, hxs⟩).2 ⟨j, hj⟩ k hkj n hn
  simp only [List.get_eq_getElem] at e57
  obtain ⟨hphi, hmu⟩ := e57
  set l := toks xs with hl
  set TJ := xs[j].1 with hTJ
  have hlnd : l.Nodup := hxs
  have hll : l.length = xs.length := toks_length xs
  have hjl : j < l.length := by omega
  have hlj : l[j] = TJ := by simp [hl, toks, hTJ]
  set l' := l.take j ++ l.drop (j + 1) with hl'
  have hl'len : l'.length = l.length - 1 := by simp [hl']; omega
  have hl'take : ∀ m ≤ j, l'.take m = l.take m := by
    intro m hm
    rw [hl', List.take_append_of_le_length (by simp; omega), List.take_take]
    congr 1; omega
  have hl'drop : ∀ m ≤ j, l'.drop m = (l.take j).drop m ++ l.drop (j + 1) := by
    intro m hm
    rw [hl', List.drop_append_of_le_length (by simp; omega)]
  have hlsplit : l = l'.take j ++ TJ :: l'.drop j := by
    rw [hl'take j le_rfl, hl'drop j le_rfl, List.drop_eq_nil_of_le (as := l.take j) (by simp),
      List.nil_append,
      ← hlj, List.getElem_cons_drop, List.take_append_drop]
  have htl' : (TJ :: l').Nodup := by
    have hp : l.Perm (TJ :: l') := by
      conv_lhs => rw [hlsplit]
      have := List.perm_middle (a := TJ) (l₁ := l'.take j) (l₂ := l'.drop j)
      rwa [List.take_append_drop] at this
    exact hp.nodup_iff.mp hlnd
  set S := shift xs (j + 1) k n TJ with hSdef
  have htS : toks S = l'.take k ++ TJ :: l'.drop k := by
    rw [hSdef]; unfold shift
    split_ifs with hc
    · simp only [Nat.add_sub_cancel]
      rw [hl'take k hkj, hl'drop k hkj]
      simp [toks, pre, hl, map_fst_modLast, List.map_drop, List.map_take]
    · have hk' : k = j := by omega
      subst hk'
      rw [hl'take k le_rfl, hl'drop k le_rfl,
        List.drop_eq_nil_of_le (as := l.take k) (by simp), List.nil_append]
      simp [toks, pre, hl, map_fst_modLast, List.map_drop, List.map_take]
  have hp : l.Perm (TJ :: l') := by
    conv_lhs => rw [hlsplit]
    have := List.perm_middle (a := TJ) (l₁ := l'.take j) (l₂ := l'.drop j)
    rwa [List.take_append_drop] at this
  have hSperm : (toks S).Perm l := by
    rw [htS]
    have := List.perm_middle (a := TJ) (l₁ := l'.take k) (l₂ := l'.drop k)
    rw [List.take_append_drop] at this
    exact this.trans hp.symm
  have hSnd : (toks S).Nodup := hSperm.nodup_iff.mpr hlnd
  have hpl : piLam P (toks S) = piLam P l := h1 _ _ hSnd hSperm
  have hjl' : j ≤ l'.length := by omega
  have hA := TokenQueue.ProductForm.pi_k_rearrangement P h2 hk l' TJ htl' k (by omega)
  have hB := TokenQueue.ProductForm.pi_k_rearrangement P h2 hk l' TJ htl' j hjl'
  rw [← hlsplit] at hB
  rw [← htS] at hA
  set g : ℕ → ℝ := fun m => kfun P (l'.take m ++ [TJ]) / kfun P (l'.take m) with hg
  have hsplitI : ∏ m ∈ Icc (k + 1) l'.length, g m =
      (∏ m ∈ Icc (k + 1) j, g m) * ∏ m ∈ Icc (j + 1) l'.length, g m := by
    rw [Finset.Icc_add_one_left_eq_Ioc, Finset.Icc_add_one_left_eq_Ioc,
      Finset.Icc_add_one_left_eq_Ioc, Finset.prod_Ioc_consecutive _ hkj hjl']
  have hgj : ∀ m ∈ Icc (k + 1) j, g m = kfun P (l.take m ++ [TJ]) / kfun P (l.take m) := by
    intro m hm
    simp only [Finset.mem_Icc] at hm
    simp only [hg, hl'take m hm.2]
  rw [hsplitI, Finset.prod_congr rfl hgj, hl'take k hkj] at hA
  rw [hl'take j le_rfl] at hB
  have hlj1 : l.take j ++ [TJ] = l.take (j + 1) := by
    rw [← hlj, List.take_append_getElem hjl]
  rw [hlj1] at hB
  -- `hA : piK (toks S) = KJ_k * piK l' * (Q1 * G)`, `hB : piK l = K_{j+1} * piK l' * G`
  -- alpha-products
  set aJ : ℕ → ℝ := fun m => alpha P (l.take m ++ [TJ]) with haJ
  set a : ℕ → ℝ := fun m => alpha P (l.take m) with ha
  set c := 1 + nAt xs (j + 1) with hc
  set Zp := ∏ r ∈ range (xs.length - (j + 1)),
    alpha P (l.take (j + 1) ++ (l.drop (j + 1)).take (r + 1)) ^ nAt xs (j + 1 + r + 1) with hZp
  have hZpart : ∀ W : List (T × ℕ), (toks W).Perm (l.take (j + 1)) → (toks W).Nodup →
      ∏ r ∈ range (xs.drop (j + 1)).length,
        alpha P (toks W ++ (toks (xs.drop (j + 1))).take (r + 1)) ^ nAt (xs.drop (j + 1)) (r + 1)
        = Zp := by
    intro W hW hWnd
    rw [List.length_drop, hZp]
    apply Finset.prod_congr rfl
    intro r hr
    simp only [mem_range] at hr
    rw [nAt_drop, toks_drop, ← hl]
    congr 1
    apply alpha_perm P h2
    · have e : l.take (j + 1) ++ (l.drop (j + 1)).take (r + 1) = l.take (j + 1 + (r + 1)) :=
        List.take_add.symm
      apply ((hW.append_right _).nodup_iff).mpr
      rw [e]; exact hlnd.sublist (List.take_sublist _ _)
    · exact hW.append_right _
  have hmid : ∀ r, r < j - k →
      l.take k ++ ((l.take j).drop k).take (r + 1) = l.take (k + r + 1) := by
    intro r hr
    rw [show l.take (k + r + 1) = (l.take j).take (k + (r + 1)) by
      rw [List.take_take]; congr 1; omega]
    have e1 : (l.take j).take (k + (r + 1)) =
        (l.take j).take k ++ ((l.take j).drop k).take (r + 1) := List.take_add
    rw [e1, List.take_take, Nat.min_eq_left hkj]
  have hAx : AP P xs = AP P (xs.take k) * (∏ m ∈ Icc (k + 1) j, a m ^ nAt xs m) *
      a (j + 1) ^ nAt xs (j + 1) * Zp := by
    conv_lhs => rw [← List.take_append_drop (j + 1) xs]
    rw [AP_append, hZpart (xs.take (j + 1)) (by rw [toks_take]; rfl)
      (by rw [toks_take]; exact hlnd.sublist (List.take_sublist _ _))]
    rw [AP_take_succ P xs j hj]
    congr 2
    conv_lhs => rw [← List.take_append_drop k (xs.take j)]
    rw [AP_append, List.take_take, show min k j = k by omega, prod_Icc_eq_range]
    congr 1
    rw [List.length_drop, List.length_take, show min j xs.length = j by omega]
    apply Finset.prod_congr rfl
    intro r hr
    simp only [mem_range] at hr
    rw [nAt_drop, nAt_take _ _ _ (by omega), toks_take, toks_drop, toks_take]
    simp only [ha, pre, ← hl]
    rw [hmid r hr]
  have hlj1' : l.take j ++ [TJ] = l.take (j + 1) := hlj1
  have hAS : AP P S = AP P (modLast (· - n) (xs.take k)) * aJ k ^ n *
      (∏ m ∈ Icc (k + 1) j, aJ m ^ nAt xs m) * a (j + 1) ^ c * Zp := by
    rcases lt_or_eq_of_le hkj with hlt | heq
    · have eS : S = ((modLast (· - n) (xs.take k) ++ [(TJ, n)]) ++
          modLast (· + c) ((xs.take j).drop k)) ++ xs.drop (j + 1) := by
        rw [hSdef]; unfold shift
        rw [if_pos (by omega)]
        simp only [Nat.add_sub_cancel, List.append_assoc, List.cons_append, List.singleton_append,
          List.nil_append, hc]
      have hMne : (xs.take j).drop k ≠ [] := by
        apply List.ne_nil_of_length_pos; simp; omega
      have hMlen : ((xs.take j).drop k).length = j - k := by simp; omega
      have e2 : l.take k ++ (l.take j).drop k = l.take j := by
        conv_rhs => rw [← List.take_append_drop k (l.take j)]
        rw [List.take_take, Nat.min_eq_left hkj]
      have hYperm : (l.take k ++ [TJ] ++ (l.take j).drop k).Perm (l.take (j + 1)) := by
        have h0 : (l.take k ++ [TJ] ++ (l.take j).drop k).Perm
            (l.take k ++ (l.take j).drop k ++ [TJ]) := by
          rw [List.append_assoc, List.append_assoc]
          exact List.Perm.append_left _ List.perm_append_comm
        refine h0.trans ?_
        rw [e2, hlj1']
      have hYnd : (l.take k ++ [TJ] ++ (l.take j).drop k).Nodup :=
        hYperm.nodup_iff.mpr (hlnd.sublist (List.take_sublist _ _))
      have htY : toks ((modLast (· - n) (xs.take k) ++ [(TJ, n)]) ++
          modLast (· + c) ((xs.take j).drop k)) = l.take k ++ [TJ] ++ (l.take j).drop k := by
        rw [toks_append, toks_append, toks_modLast, toks_modLast, toks_take, toks_drop, toks_take]
        rfl
      rw [eS, AP_append, hZpart _ (by rw [htY]; exact hYperm) (by rw [htY]; exact hYnd)]
      rw [AP_append, AP_append_single, length_modLast, prod_range_modLast _ hMne]
      simp only [toks_modLast, toks_take, toks_drop, toks_append, pre, ← hl, toks_single]
      have hQ2' : ∏ r ∈ range ((xs.take j).drop k).length,
          alpha P (l.take k ++ [TJ] ++ ((l.take j).drop k).take (r + 1)) ^
            nAt ((xs.take j).drop k) (r + 1) = ∏ m ∈ Icc (k + 1) j, aJ m ^ nAt xs m := by
        rw [prod_Icc_eq_range, hMlen]
        apply Finset.prod_congr rfl
        intro r hr
        simp only [mem_range] at hr
        rw [nAt_drop, nAt_take _ _ _ (by omega)]
        congr 1
        simp only [haJ]
        apply alpha_perm P h2
        · exact hYnd.sublist ((List.take_sublist _ _).append_left _)
        · rw [← hmid r hr, List.append_assoc, List.append_assoc]
          exact List.Perm.append_left _ List.perm_append_comm
      have hlast' : alpha P (l.take k ++ [TJ] ++ ((l.take j).drop k).take
          (((xs.take j).drop k).length - 1 + 1)) = a (j + 1) := by
        rw [hMlen, show j - k - 1 + 1 = j - k by omega,
          List.take_of_length_le (l := (l.take j).drop k) (by simp; omega)]
        exact alpha_perm P h2 hYnd hYperm
      rw [hQ2', hlast']
      ring
    · subst heq
      have eS : S = (modLast (· - n) (xs.take k) ++ [(TJ, n + c)]) ++ xs.drop (k + 1) := by
        rw [hSdef]; unfold shift
        rw [if_neg (lt_irrefl _)]
        simp only [List.append_assoc, List.singleton_append, hc]
        ring_nf
      have htY : toks (modLast (· - n) (xs.take k) ++ [(TJ, n + c)]) = l.take (k + 1) := by
        rw [toks_append, toks_modLast, toks_take, ← hlj1']; rfl
      rw [eS, AP_append, hZpart _ (by rw [htY]) (by rw [htY]; exact hlnd.sublist (List.take_sublist _ _))]
      rw [AP_append_single, toks_modLast, toks_take, Finset.Icc_eq_empty (by omega),
        Finset.prod_empty, mul_one, pow_add]
      have : alpha P (pre xs k ++ [TJ]) = a (k + 1) := by
        simp only [ha, pre, ← hl]; rw [← hlj1']
      have this2 : aJ k = a (k + 1) := by simp only [haJ, ha]; rw [← hlj1']
      rw [this, this2]
      ring
  -- positivity
  have hTJnot : ∀ m ≤ j, TJ ∉ l.take m := by
    intro m hm hmem
    have hnd2 : (l.take j ++ [TJ]).Nodup := by
      rw [hlj1']; exact hlnd.sublist (List.take_sublist _ _)
    rw [List.nodup_append] at hnd2
    have : TJ ∈ l.take j := by
      have := List.take_subset_take_left l (show m ≤ j from hm)
      exact this hmem
    exact hnd2.2.2 TJ this TJ (List.mem_singleton_self _) rfl
  have hKTnd : ∀ m ≤ j, (l.take m ++ [TJ]).Nodup := by
    intro m hm
    rw [List.nodup_append]
    refine ⟨hlnd.sublist (List.take_sublist _ _), List.nodup_singleton _, ?_⟩
    intro u hu v hv huv
    simp only [List.mem_singleton] at hv
    subst hv; subst huv
    exact hTJnot m hm hu
  have hKT : ∀ m ≤ j, 0 < kfun P (l.take m ++ [TJ]) := fun m hm => hk _ (hKTnd m hm) (by simp)
  have hK : ∀ m, 1 ≤ m → m ≤ l.length → 0 < kfun P (l.take m) := by
    intro m hm1 hm2
    apply hk
    · exact hlnd.sublist (List.take_sublist _ _)
    · apply List.ne_nil_of_length_pos; rw [List.length_take]; omega
  have hH := pos_k_rel P hS hk xs hxs TJ k (by omega) (hKTnd k hkj) n hn
  have hQ := prod_rel P hS xs TJ (Icc (k + 1) j) (by
    intro m hm
    simp only [Finset.mem_Icc] at hm
    exact ⟨by omega, hK m (by omega) (by omega), hKT m hm.2⟩)
  have hlast : (1 - beta P xs j TJ) * a (j + 1) =
      (lamU P (l.take (j + 1)).toFinset - lamU P (l.take j).toFinset) / kfun P (l.take (j + 1)) := by
    have hins : insert TJ (l.take j).toFinset = (l.take (j + 1)).toFinset := by
      rw [← hlj1', toFinset_append_single]
    simp only [ha, alpha]
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · subst hj0
      have hU0 : lamU P (l.take 0).toFinset = 0 := by
        simp only [List.take_zero, List.toFinset_nil]
        unfold lamU
        apply Finset.sum_eq_zero
        intro c hc
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.subset_empty] at hc
        exact absurd hc (hS.2.1 c).ne_empty
      rw [show beta P xs 0 TJ = 0 from by simp [beta], hU0]
      ring
    · simp only [beta, if_neg (by omega : j ≠ 0), pre, ← hl, hins]
      have hle := lamU_mono P hS (show (l.take j).toFinset ⊆ (l.take (j + 1)).toFinset by
        rw [← hins]; exact Finset.subset_insert _ _)
      have h0 := lamU_nonneg P hS (l.take j).toFinset
      rcases eq_or_lt_of_le (h0.trans hle) with h | h
      · rw [← h]
        have : lamU P (l.take j).toFinset = 0 := le_antisymm (h ▸ hle) h0
        rw [this]; simp
      · field_simp
  -- assemble
  rw [hmu, weightL_AP, weightL_AP P xs, hpl, hAS, hAx, hphi, prodEta_succ]
  unfold sfac
  simp only [Nat.add_sub_cancel]
  change P.eta (phi xs + 1) * (kfun P (l.take k ++ [TJ]) - kfun P (l.take k)) * _ * _ = _
  have hPiS : piK P (toks S) * kfun P (l.take (j + 1)) =
      piK P l * kfun P (l.take k ++ [TJ]) *
        ∏ m ∈ Icc (k + 1) j, kfun P (l.take m ++ [TJ]) / kfun P (l.take m) := by
    rw [hA, hB]; ring
  have hQ1 : 0 < ∏ m ∈ Icc (k + 1) j, kfun P (l.take m ++ [TJ]) / kfun P (l.take m) := by
    apply Finset.prod_pos
    intro m hm
    simp only [Finset.mem_Icc] at hm
    exact div_pos (hKT m hm.2) (hK m (by omega) (by omega))
  have hPi : 0 < piK P l := piK_pos P hk l hlnd
  have he : 0 < P.eta (phi xs + 1) := hS.2.2.2.2.2.2 _ (by omega)
  have hKj1 : 0 < kfun P (l.take (j + 1)) := hK (j + 1) (by omega) (by omega)
  exact final_alg14 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n (nAt xs (j + 1)) he.ne'
    (hKT k hkj).ne' hQ1.ne' hPi.ne' hKj1.ne' hPiS hH hQ hlast

end TQLib

theorem solution {C T : Type} [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T]
    (P : Params C T) (hS : P.Standing) (h1 : Condition1 P) (h2 : Condition2 P) (hk : KPos P)
    (x : State T) :
    lamU P (toks x.1).toFinset * weightL P x.1 =
      ∑ j : Fin x.1.length, ∑ k ∈ range (j.val + 1), ∑ n ∈ range (nAt x.1 k + 1),
        muTok P (shift x.1 (j.val + 1) k n (x.1.get j).1) k *
          sfac P x.1 (j.val + 1) k n (x.1.get j).1 *
          weightL P (shift x.1 (j.val + 1) k n (x.1.get j).1) := by
  obtain ⟨xs, hxs⟩ := x
  simp only [List.get_eq_getElem]
  set l := toks xs with hl
  have hlnd : l.Nodup := hxs
  have hinner : ∀ j : Fin xs.length,
      ∑ k ∈ range (j.val + 1), ∑ n ∈ range (nAt xs k + 1),
        muTok P (shift xs (j.val + 1) k n xs[j.val].1) k *
          sfac P xs (j.val + 1) k n xs[j.val].1 *
          weightL P (shift xs (j.val + 1) k n xs[j.val].1) =
      weightL P xs * (lamU P (l.take (j.val + 1)).toFinset - lamU P (l.take j.val).toFinset) := by
    intro j
    have hj := j.2
    set TJ := xs[j.val].1 with hTJ
    rw [Finset.sum_congr rfl (fun k hk' => Finset.sum_congr rfl (fun n hn =>
      eq14_term P hS h1 h2 hk xs hxs j.val hj k (by simp at hk'; omega) n
        (by simp at hn; omega)))]
    simp_rw [← Finset.mul_sum]
    set D := l.take j.val with hD
    have hDlen : D.length = j.val := by simp [hD, hl, toks_length]
    have hDt : ∀ m ≤ j.val, D.take m = l.take m := by
      intro m hm; rw [hD, List.take_take, Nat.min_eq_left hm]
    have hlj : l[j.val]'(by rw [hl, toks_length]; exact hj) = TJ := by simp [hl, toks, hTJ]
    have hDnd : (TJ :: D).Nodup := by
      have h' : (D ++ [TJ]).Nodup := by
        rw [hD, ← hlj, List.take_append_getElem]
        exact hlnd.sublist (List.take_sublist _ _)
      exact (List.perm_append_singleton TJ D).nodup_iff.mp h'
    have h29 := TokenQueue.ProductForm.eq_29 P hk D TJ hDnd (nAt xs) (nAt_zero xs)
    rw [hDlen] at h29
    have e : ∀ k ∈ range (j.val + 1),
        (kfun P (D.take k ++ [TJ]) - kfun P (D.take k)) / kfun P (D.take k ++ [TJ]) *
          (∏ m ∈ Icc (k + 1) j.val,
            (kfun P (D.take m) / kfun P (D.take m ++ [TJ])) ^ (nAt xs m + 1)) *
          ∑ m ∈ range (nAt xs k + 1), (kfun P (D.take k) / kfun P (D.take k ++ [TJ])) ^ m =
        (kfun P (l.take k ++ [TJ]) - kfun P (l.take k)) / kfun P (l.take k ++ [TJ]) *
          (∏ m ∈ Icc (k + 1) j.val,
            (kfun P (l.take m) / kfun P (l.take m ++ [TJ])) ^ (nAt xs m + 1)) *
          ∑ m ∈ range (nAt xs k + 1), (kfun P (l.take k) / kfun P (l.take k ++ [TJ])) ^ m := by
      intro k hk'
      simp only [mem_range] at hk'
      rw [hDt k (by omega)]
      congr 2
      apply Finset.prod_congr rfl
      intro m hm
      simp only [Finset.mem_Icc] at hm
      rw [hDt m hm.2]
    rw [Finset.sum_congr rfl e] at h29
    rw [h29, mul_one]
  rw [Finset.sum_congr rfl (fun j _ => hinner j), ← Finset.mul_sum, mul_comm]
  congr 1
  rw [Fin.sum_univ_eq_sum_range
    (fun j => lamU P (l.take (j + 1)).toFinset - lamU P (l.take j).toFinset) xs.length,
    Finset.sum_range_sub (fun j => lamU P (l.take j).toFinset)]
  have hU0 : lamU P (l.take 0).toFinset = 0 := by
    simp only [List.take_zero, List.toFinset_nil]
    unfold lamU
    apply Finset.sum_eq_zero
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.subset_empty] at hc
    exact absurd hc (hS.2.1 c).ne_empty
  rw [hU0, sub_zero, List.take_of_length_le (by rw [hl, toks_length])]
