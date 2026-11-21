-- Prove2me | solution 1 for StreamSubmod.concavity
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T02:50:51.0751+00:00
-- url     : https://prove2.me/submissions/67866cbe-943d-4da2-b3a7-f3ef991ca9bd

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_F

namespace Aux_StreamSubmod_concavity

open NonmonotoneSubmod.Shared

variable {E : Type} [DecidableEq E]

noncomputable def P (U : Finset E) (h : Finset E → ℝ) (t : ℝ) : ℝ :=
  ∑ T ∈ U.powerset, h T * t ^ T.card * (1 - t) ^ (U.card - T.card)

def dd (u : E) (h : Finset E → ℝ) : Finset E → ℝ := fun T => h (insert u T) - h T

lemma P_empty (h : Finset E → ℝ) (t : ℝ) : P ∅ h t = h ∅ := by
  simp [P]

lemma P_insert (a : E) (U : Finset E) (ha : a ∉ U) (h : Finset E → ℝ) (t : ℝ) :
    P (insert a U) h t = t * P U (fun T => h (insert a T)) t + (1 - t) * P U h t := by
  unfold P
  rw [Finset.sum_powerset_insert ha, Finset.card_insert_of_notMem ha]
  have h1 : ∑ T ∈ U.powerset, h T * t ^ T.card * (1 - t) ^ (U.card + 1 - T.card)
      = (1 - t) * ∑ T ∈ U.powerset, h T * t ^ T.card * (1 - t) ^ (U.card - T.card) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T hT
    have hc : T.card ≤ U.card := Finset.card_le_card (Finset.mem_powerset.mp hT)
    have : U.card + 1 - T.card = (U.card - T.card) + 1 := by omega
    rw [this, pow_succ]
    ring
  have h2 : ∑ T ∈ U.powerset, h (insert a T) * t ^ (insert a T).card
        * (1 - t) ^ (U.card + 1 - (insert a T).card)
      = t * ∑ T ∈ U.powerset, h (insert a T) * t ^ T.card * (1 - t) ^ (U.card - T.card) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T hT
    have hTU : T ⊆ U := Finset.mem_powerset.mp hT
    have haT : a ∉ T := fun h' => ha (hTU h')
    rw [Finset.card_insert_of_notMem haT]
    have : U.card + 1 - (T.card + 1) = U.card - T.card := by omega
    rw [this, pow_succ]
    ring
  rw [h1, h2]
  ring

lemma P_sub (U : Finset E) (h1 h2 : Finset E → ℝ) (t : ℝ) :
    P U (fun T => h1 T - h2 T) t = P U h1 t - P U h2 t := by
  unfold P
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro T _
  ring

lemma P_dd (U : Finset E) (a : E) (h : Finset E → ℝ) (t : ℝ) :
    P U (dd a h) t = P U (fun T => h (insert a T)) t - P U h t :=
  P_sub U (fun T => h (insert a T)) h t

lemma P_hasDeriv (U : Finset E) : ∀ (h : Finset E → ℝ) (t : ℝ),
    HasDerivAt (fun s => P U h s) (∑ u ∈ U, P (U.erase u) (dd u h) t) t := by
  refine Finset.induction_on U ?_ ?_
  · intro h t
    rw [Finset.sum_empty]
    have : (fun s => P (∅ : Finset E) h s) = fun _ => h ∅ := funext (fun s => P_empty h s)
    rw [this]
    exact hasDerivAt_const t (h ∅)
  · intro a U ha ih h t
    have e1 : (fun s => P (insert a U) h s)
        = fun s => s * P U (fun T => h (insert a T)) s + (1 - s) * P U h s :=
      funext (P_insert a U ha h)
    rw [e1]
    have d1 := ((hasDerivAt_id' t).mul (ih (fun T => h (insert a T)) t)).add
      (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id' t)).mul (ih h t))
    refine d1.congr_deriv ?_
    have hs : ∑ u ∈ U, P ((insert a U).erase u) (dd u h) t
        = t * ∑ u ∈ U, P (U.erase u) (dd u (fun T => h (insert a T))) t
          + (1 - t) * ∑ u ∈ U, P (U.erase u) (dd u h) t := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro u hu
      have hau : a ≠ u := fun e => ha (e ▸ hu)
      have hne : a ∉ U.erase u := fun h' => ha (Finset.mem_of_mem_erase h')
      rw [Finset.erase_insert_of_ne hau, P_insert a _ hne]
      have hfun : (fun T => dd u h (insert a T)) = dd u (fun T => h (insert a T)) := by
        funext T
        simp only [dd]
        rw [Finset.insert_comm]
      rw [hfun]
    rw [Finset.sum_insert ha, Finset.erase_insert ha, P_dd, hs]
    simp only [Pi.sub_apply]
    ring

lemma dd_dd_nonpos (h : Finset E → ℝ) (hsub : ∀ X Y : Finset E, h (X ∪ Y) + h (X ∩ Y) ≤ h X + h Y)
    (u v : E) (huv : u ≠ v) (T : Finset E) : dd v (dd u h) T ≤ 0 := by
  simp only [dd]
  have := hsub (insert u T) (insert v T)
  have e1 : insert u T ∪ insert v T = insert u (insert v T) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_insert]
    tauto
  have e2 : insert u T ∩ insert v T = T := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_insert]
    constructor
    · rintro ⟨h1 | h1, h2 | h2⟩
      · exact absurd (h1.symm.trans h2) huv
      · exact h2
      · exact h1
      · exact h1
    · intro hx
      exact ⟨Or.inr hx, Or.inr hx⟩
  rw [e1, e2] at this
  linarith

lemma P_nonpos (U : Finset E) (h : Finset E → ℝ) (t : ℝ) (hh : ∀ T, h T ≤ 0) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : P U h t ≤ 0 := by
  unfold P
  apply Finset.sum_nonpos
  intro T _
  rw [mul_assoc]
  exact mul_nonpos_of_nonpos_of_nonneg (hh T)
    (mul_nonneg (pow_nonneg ht0 _) (pow_nonneg (sub_nonneg.mpr ht1) _))

lemma P_concave (U : Finset E) (h : Finset E → ℝ)
    (hsub : ∀ X Y : Finset E, h (X ∪ Y) + h (X ∩ Y) ≤ h X + h Y) :
    ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (fun t => P U h t) := by
  have hd := P_hasDeriv U
  have hderiv : deriv (fun s => P U h s) = fun t => ∑ u ∈ U, P (U.erase u) (dd u h) t :=
    funext fun t => (hd h t).deriv
  have hd2 : ∀ t, HasDerivAt (fun t => ∑ u ∈ U, P (U.erase u) (dd u h) t)
      (∑ u ∈ U, ∑ v ∈ U.erase u, P ((U.erase u).erase v) (dd v (dd u h)) t) t :=
    fun t => HasDerivAt.fun_sum (fun u _ => P_hasDeriv (U.erase u) (dd u h) t)
  apply AntitoneOn.concaveOn_of_deriv (convex_Icc 0 1)
  · exact fun t _ => (hd h t).continuousAt.continuousWithinAt
  · exact fun t _ => (hd h t).differentiableAt.differentiableWithinAt
  · rw [hderiv]
    refine AntitoneOn.mono ?_ interior_subset
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · exact fun t _ => (hd2 t).continuousAt.continuousWithinAt
    · exact fun t _ => (hd2 t).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hd2 x).deriv]
      apply Finset.sum_nonpos
      intro u _
      apply Finset.sum_nonpos
      intro v hv
      exact P_nonpos _ _ _
        (fun T => dd_dd_nonpos h hsub u v (Finset.ne_of_mem_erase hv).symm T) hx.1.le hx.2.le

variable [Fintype E]

lemma F_rec (f : Finset E → ℝ) (x : E → ℝ) (a : E) :
    F f x = x a * F f (Function.update x a 1) + (1 - x a) * F f (Function.update x a 0) := by
  unfold F
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro T _
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a)]
  have h1 : ∏ i ∈ Finset.univ.erase a,
      (if i ∈ T then Function.update x a 1 i else 1 - Function.update x a 1 i)
      = ∏ i ∈ Finset.univ.erase a, (if i ∈ T then x i else 1 - x i) :=
    Finset.prod_congr rfl (fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)])
  have h0 : ∏ i ∈ Finset.univ.erase a,
      (if i ∈ T then Function.update x a 0 i else 1 - Function.update x a 0 i)
      = ∏ i ∈ Finset.univ.erase a, (if i ∈ T then x i else 1 - x i) :=
    Finset.prod_congr rfl (fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)])
  rw [h1, h0]
  by_cases ha : a ∈ T <;> simp only [ha, ↓reduceIte, Function.update_self] <;> ring

lemma F_indicator (f : Finset E → ℝ) (B : Finset E) :
    F f (fun e => if e ∈ B then 1 else 0) = f B := by
  unfold F
  rw [Finset.sum_eq_single B]
  · rw [Finset.prod_eq_one, mul_one]
    intro i _
    by_cases hi : i ∈ B <;> simp [hi]
  · intro T _ hTB
    have : ∃ i, ¬ (i ∈ T ↔ i ∈ B) := by
      by_contra hcon
      push_neg at hcon
      exact hTB (Finset.ext hcon)
    obtain ⟨i, hi⟩ := this
    rw [Finset.prod_eq_zero (Finset.mem_univ i), mul_zero]
    by_cases h1 : i ∈ T <;> by_cases h2 : i ∈ B <;> simp_all
  · intro h
    exact absurd (Finset.mem_univ B) h

lemma F_line (f : Finset E → ℝ) (U : Finset E) : ∀ B : Finset E, Disjoint B U → ∀ t : ℝ,
    F f (fun e => if e ∈ B then 1 else if e ∈ U then t else 0) = P U (fun T => f (B ∪ T)) t := by
  refine Finset.induction_on U ?_ ?_
  · intro B _ t
    have : (fun e => if e ∈ B then (1 : ℝ) else if e ∈ (∅ : Finset E) then t else 0)
        = fun e => if e ∈ B then 1 else 0 := by
      funext e
      simp
    rw [this, F_indicator, P_empty, Finset.union_empty]
  · intro a U ha ih B hB t
    have haB : a ∉ B := fun h => Finset.disjoint_left.mp hB h (Finset.mem_insert_self a U)
    have h0 : Disjoint B U := hB.mono_right (Finset.subset_insert a U)
    have h1 : Disjoint (insert a B) U := Finset.disjoint_insert_left.mpr ⟨ha, h0⟩
    set x : E → ℝ := fun e => if e ∈ B then 1 else if e ∈ insert a U then t else 0 with hx
    have hxa : x a = t := by simp [hx, haB]
    have hu1 : Function.update x a 1 = fun e => if e ∈ insert a B then 1 else if e ∈ U then t else 0 := by
      funext e
      by_cases he : e = a
      · rw [he, Function.update_self]
        simp
      · rw [Function.update_of_ne he]
        simp [hx, he]
    have hu0 : Function.update x a 0 = fun e => if e ∈ B then 1 else if e ∈ U then t else 0 := by
      funext e
      by_cases he : e = a
      · rw [he, Function.update_self]
        simp [haB, ha]
      · rw [Function.update_of_ne he]
        simp [hx, he]
    have key := F_rec f x a
    rw [hxa, hu1, hu0, ih (insert a B) h1 t, ih B h0 t] at key
    rw [key, P_insert a U ha]
    simp only [Finset.union_insert, Finset.insert_union]

end Aux_StreamSubmod_concavity

open NonmonotoneSubmod.Shared in
theorem solution {E : Type} [Fintype E] [DecidableEq E] (f : Finset E → ℝ) (hf : Submodular f)
    (S B : Finset E) :
    ConcaveOn ℝ (Set.Icc (0 : ℝ) 1)
      (fun t : ℝ => F f (fun e => max (t * (if e ∈ S then 1 else 0)) (if e ∈ B then 1 else 0))) := by
  have hsub : ∀ X Y : Finset E, (fun T => f (B ∪ T)) (X ∪ Y) + (fun T => f (B ∪ T)) (X ∩ Y)
      ≤ (fun T => f (B ∪ T)) X + (fun T => f (B ∪ T)) Y := by
    intro X Y
    show f (B ∪ (X ∪ Y)) + f (B ∪ (X ∩ Y)) ≤ f (B ∪ X) + f (B ∪ Y)
    have := hf (B ∪ X) (B ∪ Y)
    have e1 : B ∪ X ∪ (B ∪ Y) = B ∪ (X ∪ Y) := by
      ext x
      simp only [Finset.mem_union]
      tauto
    have e2 : (B ∪ X) ∩ (B ∪ Y) = B ∪ (X ∩ Y) := by
      ext x
      simp only [Finset.mem_union, Finset.mem_inter]
      tauto
    rw [e1, e2] at this
    exact this
  have hc := Aux_StreamSubmod_concavity.P_concave (S \ B) (fun T => f (B ∪ T)) hsub
  refine hc.congr ?_
  intro t ht
  dsimp only
  rw [← Aux_StreamSubmod_concavity.F_line f (S \ B) B Finset.disjoint_sdiff t]
  congr 1
  funext e
  by_cases hB : e ∈ B <;> by_cases hS : e ∈ S
  · simp only [hB, hS, ↓reduceIte, mul_one]
    exact (max_eq_right ht.2).symm
  · simp only [hB, hS, ↓reduceIte, mul_zero]
    exact (max_eq_right zero_le_one).symm
  · have h1 : e ∈ S \ B := Finset.mem_sdiff.mpr ⟨hS, hB⟩
    simp only [hB, hS, h1, ↓reduceIte, mul_one]
    exact (max_eq_left ht.1).symm
  · have h1 : e ∉ S \ B := fun h => hS (Finset.mem_sdiff.mp h).1
    simp only [hB, hS, h1, ↓reduceIte, mul_zero, max_self]
