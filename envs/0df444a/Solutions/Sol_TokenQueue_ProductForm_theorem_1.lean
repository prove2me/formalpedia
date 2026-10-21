-- Prove2me | solution 1 for TokenQueue.ProductForm.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T07:54:03.637988+00:00
-- url     : https://prove2.me/submissions/61e507fe-c5d3-422c-b5aa-7ed0a0bd39ac

import Theorems.Thm_TokenQueue_ProductForm_eq_1
import Theorems.Thm_TokenQueue_ProductForm_exit_rate
import Theorems.Thm_TokenQueue_ProductForm_eq_8_9
import Theorems.Thm_TokenQueue_ProductForm_eq_12
import Theorems.Thm_TokenQueue_ProductForm_eq_13
import Theorems.Thm_TokenQueue_ProductForm_eq_14
import Definitions.Def_KellyStochasticNetworks_Balance
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

theorem mu_eq' (P : Params C T) (x : List (T × ℕ)) :
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

/-- A descriptor with a repeated token has weight zero: some factor `λ_{T_j}({T_1,…,T_{j-1}})`
of `Π_λ` vanishes because `T_j` is already unavailable. -/
theorem piLam_eq_zero_of_not_nodup (P : Params C T) (hS : P.Standing) (l : List T)
    (hl : ¬ l.Nodup) : piLam P l = 0 := by
  rw [List.nodup_iff_injective_get] at hl
  simp only [Function.Injective, not_forall] at hl
  obtain ⟨a, b, hab, hne⟩ := hl
  have key : ∀ a b : Fin l.length, a < b → l.get a = l.get b → piLam P l = 0 := by
    intro a b hlt heq
    unfold piLam
    apply Finset.prod_eq_zero (i := b) (Finset.mem_univ _)
    unfold lamTok
    apply Finset.sum_eq_zero
    intro c _
    rw [hS.2.2.2.1 c _ _, mul_zero]
    simp only [Finset.mem_sdiff, List.mem_toFinset, not_and, not_not]
    intro _
    rw [← heq]
    simp only [List.get_eq_getElem]
    exact List.mem_iff_getElem.mpr ⟨a.val, by simp; omega, by simp⟩
  rcases lt_or_gt_of_ne hne with h | h
  · exact key a b h hab
  · exact key b a h hab.symm

theorem weightL_eq_zero_of_not_nodup (P : Params C T) (hS : P.Standing) (x : List (T × ℕ))
    (hx : ¬ (x.map Prod.fst).Nodup) : weightL P x = 0 := by
  unfold weightL
  rw [show toks x = x.map Prod.fst from rfl, piLam_eq_zero_of_not_nodup P hS _ hx]
  simp

theorem piExt_weight (P : Params C T) (hS : P.Standing) (Z : ℝ) :
    piExt (fun y : State T => weight P y / Z) = fun l => weightL P l / Z := by
  funext l
  unfold piExt
  split_ifs with h
  · rfl
  · rw [weightL_eq_zero_of_not_nodup P hS l h, zero_div]

theorem balanceRHS_smul (P : Params C T) (f : List (T × ℕ) → ℝ) (Z : ℝ) (x : List (T × ℕ)) :
    balanceRHS P (fun l => f l / Z) x = balanceRHS P f x / Z := by
  unfold balanceRHS
  simp only
  rw [add_div, add_div]
  congr 1
  congr 1
  · split
    · simp
    · split_ifs <;> ring
  · rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro t _
    rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro k _
    rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro n _
    ring
  · rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro j _
    rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro k _
    rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro n _
    ring

end TQLib

namespace TQLib

variable {C T : Type} [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T]

theorem balance_weight (P : Params C T) (hS : P.Standing) (h1 : Condition1 P)
    (h2 : Condition2 P) (hk : KPos P) (x : State T) :
    balanceRHS P (weightL P) x.1 = (lamTot P + mu P x.1) * weightL P x.1 := by
  have hR : (∑ t ∈ univ \ (toks x.1).toFinset, ∑ k ∈ range (x.1.length + 1),
      ∑ n ∈ range (nAt x.1 k + 1),
        muTok P (release x.1 k n t) k * rfac P x.1 k n t * weightL P (release x.1 k n t)) =
      (lamTot P - lamU P (toks x.1).toFinset) * weightL P x.1 := by
    rw [TokenQueue.ProductForm.eq_1 P hS, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t ht
    have ht' : t ∉ toks x.1 := by simpa using ht
    rw [TokenQueue.ProductForm.eq_13 P hS h1 h2 hk x t ht']
  have hSh := TokenQueue.ProductForm.eq_14 P hS h1 h2 hk x
  unfold balanceRHS
  simp only
  rw [hR, ← hSh]
  rcases eq_or_ne x.1 [] with h | h
  · have e : x.1.getLast? = none := by simp [h]
    rw [e]
    have hm : mu P x.1 = 0 := by simp [mu, h]
    simp only [hm]
    ring
  · rw [List.getLast?_eq_getLast h]
    have e12 := TokenQueue.ProductForm.eq_12 P hS hk x h
    generalize x.1.getLast h = p at e12 ⊢
    obtain ⟨t, n⟩ := p
    simp only at e12 ⊢
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp only [lt_irrefl, if_false, if_true, zero_add] at e12 ⊢
      rw [← e12]; ring
    · rw [if_pos hn, if_neg (by omega), add_zero] at e12
      rw [if_pos hn, ← e12]; ring

end TQLib

namespace TQLib

variable {C T : Type} [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T]

/-- Last count of a descriptor (`0` for the empty one). -/
def lastCnt (l : List (T × ℕ)) : ℕ := (l.getLast?.map Prod.snd).getD 0

/-- The predecessor of a descriptor under the arrival transitions. -/
def predL (l : List (T × ℕ)) : List (T × ℕ) :=
  if 0 < lastCnt l then modLast (· - 1) l else l.dropLast

/-- The token of the last portion, when that portion is empty. -/
def predTag (l : List (T × ℕ)) : Option T :=
  if lastCnt l = 0 then l.getLast?.map Prod.fst else none

theorem predL_nodup (l : List (T × ℕ)) (hl : (l.map Prod.fst).Nodup) :
    ((predL l).map Prod.fst).Nodup := by
  unfold predL
  split_ifs
  · have := toks_modLast (fun n => n - 1) l
    simp only [toks] at this
    rw [this]; exact hl
  · exact hl.sublist ((List.dropLast_sublist l).map _)

def predS (x : State T) : State T := ⟨predL x.1, predL_nodup x.1 x.2⟩

theorem concat_cases (l : List (T × ℕ)) :
    l = [] ∨ ∃ L t n, l = L ++ [(t, n)] := by
  rcases List.eq_nil_or_concat l with h | ⟨L, ⟨t, n⟩, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨L, t, n, by simpa using h⟩

theorem lastCnt_concat (L : List (T × ℕ)) (t : T) (n : ℕ) : lastCnt (L ++ [(t, n)]) = n := by
  simp [lastCnt]

theorem pred_inj : Function.Injective (fun x : State T => (predS x, predTag x.1)) := by
  intro x y hxy
  simp only [Prod.mk.injEq, predS, Subtype.mk.injEq] at hxy
  obtain ⟨h1, h2⟩ := hxy
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy⟩ := y
  simp only at h1 h2
  apply Subtype.ext
  simp only
  rcases concat_cases x with rfl | ⟨L1, t1, n1, rfl⟩ <;>
    rcases concat_cases y with rfl | ⟨L2, t2, n2, rfl⟩
  · rfl
  · exfalso
    simp only [predL, predTag, lastCnt_concat] at h1 h2
    simp [lastCnt] at h1 h2
    rcases Nat.eq_zero_or_pos n2 with hn | hn
    · simp [hn] at h2
    · rw [if_pos hn, modLast_append_single] at h1; simp at h1
  · exfalso
    simp only [predL, predTag, lastCnt_concat] at h1 h2
    simp [lastCnt] at h1 h2
    rcases Nat.eq_zero_or_pos n1 with hn | hn
    · simp [hn] at h2
    · rw [if_pos hn, modLast_append_single] at h1; simp at h1
  · simp only [predL, predTag, lastCnt_concat] at h1 h2
    rcases Nat.eq_zero_or_pos n1 with hn1 | hn1 <;> rcases Nat.eq_zero_or_pos n2 with hn2 | hn2
    · subst hn1; subst hn2
      simp at h1 h2
      rw [h1, h2]
    · subst hn1; simp [hn2.ne'] at h2
    · subst hn2; simp [hn1.ne'] at h2
    · rw [if_pos hn1, if_pos hn2, modLast_append_single, modLast_append_single] at h1
      obtain ⟨hL, hp⟩ := List.append_inj' h1 rfl
      simp only [List.cons.injEq, Prod.mk.injEq, and_true] at hp
      obtain ⟨ht, hn⟩ := hp
      subst hL; subst ht
      have : n1 = n2 := by omega
      subst this; rfl

end TQLib

namespace TQLib

variable {C T : Type} [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T]

theorem lamTot_nonneg (P : Params C T) (hS : P.Standing) : 0 ≤ lamTot P := by
  unfold lamTot; exact Finset.sum_nonneg fun c _ => (hS.1 c).le

theorem muW_le (P : Params C T) (hS : P.Standing) (hk : KPos P) (x : State T) :
    mu P x.1 * weightL P x.1 ≤ lamTot P * weightL P (predL x.1) := by
  rcases eq_or_ne x.1 [] with h | h
  · rw [h]; simp only [mu, List.length_nil, Finset.range_zero, Finset.sum_empty, zero_mul]
    exact mul_nonneg (lamTot_nonneg P hS) (weightL_nonneg P hS _)
  · rw [TokenQueue.ProductForm.eq_12 P hS hk x h]
    have hd := List.dropLast_append_getLast h
    have hlc : lastCnt x.1 = (x.1.getLast h).2 := by
      simp [lastCnt, List.getLast?_eq_getLast h]
    unfold predL
    rw [hlc]
    rcases Nat.eq_zero_or_pos (x.1.getLast h).2 with hn | hn
    · rw [if_neg (by omega), if_pos hn, if_neg (by omega), zero_add]
      exact mul_le_mul_of_nonneg_right (lamTok_le P hS _ _) (weightL_nonneg P hS _)
    · rw [if_pos hn, if_pos hn, if_neg (by omega), add_zero]
      exact mul_le_mul_of_nonneg_right (lamU_le P hS _) (weightL_nonneg P hS _)

theorem mu_nonneg (P : Params C T) (hS : P.Standing) (x : List (T × ℕ)) : 0 ≤ mu P x := by
  unfold mu
  apply Finset.sum_nonneg
  intro j hj
  simp only [Finset.mem_range] at hj
  unfold muTok
  apply mul_nonneg
  · apply (hS.2.2.2.2.2.2 _ _).le
    unfold phi; omega
  · exact hS.2.2.2.2.2.1 _

theorem summable_muW (P : Params C T) (hS : P.Standing) (hk : KPos P)
    (hstab : Summable (weight P)) : Summable (fun x : State T => mu P x.1 * weightL P x.1) := by
  have hF : Summable (fun p : State T × Option T => lamTot P * weight P p.1) := by
    rw [summable_prod_of_nonneg]
    · constructor
      · intro x; exact Summable.of_finite
      · simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        exact (hstab.mul_left (lamTot P)).mul_left _
    · intro p; exact mul_nonneg (lamTot_nonneg P hS) (weightL_nonneg P hS _)
  have hc := hF.comp_injective (pred_inj (T := T))
  refine Summable.of_nonneg_of_le (fun x => ?_) (fun x => ?_) hc
  · exact mul_nonneg (mu_nonneg P hS x.1) (weightL_nonneg P hS _)
  · exact muW_le P hS hk x

end TQLib

theorem solution {C T : Type} [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T]
    (P : Params C T) (hS : P.Standing) (h1 : Condition1 P) (h2 : Condition2 P) (hk : KPos P)
    (hstab : Summable (weight P)) :
    let π : State T → ℝ := fun x => weight P x / ∑' y, weight P y
    π State.empty = (1 + ∑' x : {x : State T // x.1 ≠ []}, weight P x.1)⁻¹ ∧
    (∀ x, π x = π State.empty * weight P x) ∧
    (∀ x, 0 ≤ π x) ∧ HasSum π 1 ∧
    (∀ x, HasSum (fun y => rate P x y) (lamTot P + mu P x.1)) ∧
    (∀ x, Summable (fun y => π y * rate P y x)) ∧
    Summable (fun x => π x * (lamTot P + mu P x.1)) ∧
    KellyStochasticNetworks.FullBalance π (rate P) := by
  intro π
  set Z := ∑' y, weight P y with hZ
  have hw0 : weight P State.empty = 1 := weightL_nil P
  have hwnn : ∀ x, 0 ≤ weight P x := fun x => weightL_nonneg P hS x.1
  -- split off the empty state
  have hsplit : Z = 1 + ∑' x : {x : State T // x.1 ≠ []}, weight P x.1 := by
    rw [hZ, hstab.tsum_eq_add_tsum_ite State.empty, hw0]
    congr 1
    rw [show (∑' x : {x : State T // x.1 ≠ []}, weight P x.1) =
      ∑' x : ({x : State T | x.1 ≠ []} : Set (State T)), weight P x from rfl, _root_.tsum_subtype]
    congr 1
    funext x
    simp only [Set.indicator, Set.mem_setOf_eq]
    by_cases h : x = State.empty
    · subst h; simp [State.empty]
    · rw [if_neg h, if_pos]
      intro h'
      apply h
      exact Subtype.ext h'
  have hZpos : 0 < Z := by
    rw [hsplit]
    have : 0 ≤ ∑' x : {x : State T // x.1 ≠ []}, weight P x.1 :=
      tsum_nonneg (fun x => hwnn x.1)
    linarith
  have hπ0 : π State.empty = Z⁻¹ := by
    show weight P State.empty / Z = Z⁻¹
    rw [hw0, one_div]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hπ0, hsplit]
  · intro x
    rw [hπ0]
    show weight P x / Z = Z⁻¹ * weight P x
    rw [div_eq_inv_mul]
  · intro x
    exact div_nonneg (hwnn x) hZpos.le
  · have := hstab.hasSum.div_const Z
    rwa [← hZ, div_self hZpos.ne'] at this
  · exact fun x => TokenQueue.ProductForm.exit_rate P hS x
  · exact fun x => (TokenQueue.ProductForm.eq_8_9 P hS π x).summable
  · have hmu := summable_muW P hS hk hstab
    have hl := hstab.mul_left (lamTot P)
    have := (hl.add hmu).div_const Z
    refine this.congr (fun x => ?_)
    show (lamTot P * weight P x + mu P x.1 * weightL P x.1) / Z = weight P x / Z * _
    unfold weight
    ring
  · intro x
    rw [(TokenQueue.ProductForm.exit_rate P hS x).tsum_eq,
      (TokenQueue.ProductForm.eq_8_9 P hS π x).tsum_eq]
    have hpi : piExt π = fun l => weightL P l / Z := piExt_weight P hS Z
    rw [hpi, balanceRHS_smul, balance_weight P hS h1 h2 hk x]
    show weight P x / Z * _ = _
    unfold weight
    ring
