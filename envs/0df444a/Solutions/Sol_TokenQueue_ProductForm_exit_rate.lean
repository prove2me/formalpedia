-- Prove2me | solution 1 for TokenQueue.ProductForm.exit_rate
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T08:40:10.639548+00:00
-- url     : https://prove2.me/submissions/0bb53096-bb8a-4f1a-8501-4ccec3a1112d

import Theorems.Thm_TokenQueue_ProductForm_eq_1
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

end TQLib

namespace TQLib

variable {C T : Type} [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T]

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

end TQLib

namespace TQLib

variable {C T : Type} [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T]

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

theorem transitions_sum (P : Params C T) (hS : P.Standing) (y : State T) :
    ((transitions P y.1).map Prod.snd).sum = lamTot P + mu P y.1 := by
  unfold transitions
  rw [List.map_append, List.map_append, List.sum_append, List.sum_append, sum_map_flatMap]
  have hdep : ((List.finRange y.1.length).map
      (fun j => ((departures P y.1 j).map Prod.snd).sum)).sum = mu P y.1 := by
    simp only [departures_sum]
    rw [← Fin.sum_univ_def, Fin.sum_univ_eq_sum_range (fun j => muTok P y.1 j) y.1.length]
    rfl
  rw [hdep]
  have harr : (((univ \ (toks y.1).toFinset).toList.map
      (fun t => (y.1 ++ [(t, 0)], lamTok P (toks y.1).toFinset t))).map Prod.snd).sum =
      ∑ t ∈ univ \ (toks y.1).toFinset, lamTok P (toks y.1).toFinset t := by
    rw [List.map_map]
    exact Finset.sum_map_toList _ _
  rw [harr]
  have e1 := TokenQueue.ProductForm.eq_1 P hS (toks y.1).toFinset
  rw [← e1]
  split_ifs with hy
  · rw [hy]
    have hU : lamU P (toks ([] : List (T × ℕ))).toFinset = 0 := by
      unfold lamU
      apply Finset.sum_eq_zero
      intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
      simp [toks] at hc
      exact absurd hc (hS.2.1 c).ne_empty
    simp only [hU]; simp
  · simp

end TQLib

theorem solution {C T : Type} [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T]
    (P : Params C T) (hS : P.Standing) (y : State T) :
    HasSum (fun x => rate P y x) (lamTot P + mu P y.1) := by
  rw [← transitions_sum P hS y]
  exact hasSum_rate_list _ (transitions_nodup P y)
