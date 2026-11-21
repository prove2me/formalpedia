-- Prove2me | solution 1 for StreamSubmod.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T03:25:20.330381+00:00
-- url     : https://prove2.me/submissions/17b08634-6715-4386-90dd-56602c58398a

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_StreamSubmod_optVal
import Definitions.Def_StreamSubmod_IsStream
import Definitions.Def_StreamSubmod_IsApproxOffline
import Definitions.Def_StreamSubmod_Algorithm1
import Definitions.Def_NonmonotoneSubmod_Shared_F

namespace Aux_StreamSubmod_lemma_6

open StreamSubmod NonmonotoneSubmod.Shared

section A

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


lemma scan_none {p : ℕ} (f : Finset E → ℝ) (k : ℕ) (θ : ℝ) (e : E) (S : Fin p → Finset E) :
    ∀ l : List (Fin p), (scan f k θ e S l).1 = none →
      ∀ i ∈ l, (S i).card < k → marginal f e (S i) < θ := by
  intro l
  induction l with
  | nil => intro _ i hi; simp at hi
  | cons j l ih =>
    intro h i hi hc
    simp only [scan] at h
    by_cases h1 : (S j).card < k
    · rw [if_pos h1] at h
      by_cases h2 : θ ≤ marginal f e (S j)
      · rw [if_pos h2] at h
        simp at h
      · rw [if_neg h2] at h
        rcases List.mem_cons.mp hi with rfl | hi
        · exact not_le.mp h2
        · exact ih h i hi hc
    · rw [if_neg h1] at h
      rcases List.mem_cons.mp hi with rfl | hi
      · exact absurd hc h1
      · exact ih h i hi hc

lemma thresh_cases {p : ℕ} (f : Finset E → ℝ) (k : ℕ) (θ : ℝ) (e : E) (S : Fin p → Finset E) :
    (threshStep f k θ e S).1 = S ∨
      ∃ j, (threshStep f k θ e S).1 = Function.update S j (insert e (S j)) := by
  unfold threshStep
  rcases hs : scan f k θ e S (List.finRange p) with ⟨o, n⟩
  cases o with
  | none => left; rfl
  | some j => right; exact ⟨j, rfl⟩

lemma thresh_rej {p : ℕ} (f : Finset E → ℝ) (k : ℕ) (θ : ℝ) (e : E) (S : Fin p → Finset E)
    (h : ∀ i, e ∉ (threshStep f k θ e S).1 i) :
    ∀ i, (S i).card < k → marginal f e (S i) < θ := by
  unfold threshStep at h
  rcases hs : scan f k θ e S (List.finRange p) with ⟨o, n⟩
  rw [hs] at h
  cases o with
  | none =>
    intro i hc
    exact scan_none f k θ e S _ (by rw [hs]) i (List.mem_finRange i) hc
  | some j =>
    have := h j
    simp at this

lemma thresh_mono {p : ℕ} (f : Finset E → ℝ) (k : ℕ) (θ : ℝ) (e : E) (S : Fin p → Finset E)
    (i : Fin p) : S i ⊆ (threshStep f k θ e S).1 i := by
  rcases thresh_cases f k θ e S with h | ⟨j, h⟩
  · intro x hx
    rw [h]
    exact hx
  · rw [h]
    intro x hx
    by_cases hi : i = j
    · rw [hi, Function.update_self]
      rw [hi] at hx
      exact Finset.mem_insert_of_mem hx
    · rw [Function.update_of_ne hi]
      exact hx

lemma run_mono {p : ℕ} (f : Finset E → ℝ) (k : ℕ) (θ : ℝ) (L : List E) :
    ∀ S : Fin p → Finset E, ∀ i,
      S i ⊆ (L.foldl (fun S e => (threshStep f k θ e S).1) S) i := by
  induction L with
  | nil => intro S i; exact Finset.Subset.refl _
  | cons a L ih =>
    intro S i
    simp only [List.foldl_cons]
    exact (thresh_mono f k θ a S i).trans (ih _ i)

lemma run_disj {p : ℕ} (f : Finset E → ℝ) (k : ℕ) (θ : ℝ) (L : List E) (hnd : L.Nodup) :
    ∀ S : Fin p → Finset E, (∀ i j, i ≠ j → Disjoint (S i) (S j)) → (∀ i, ∀ e ∈ L, e ∉ S i) →
      ∀ i j, i ≠ j → Disjoint ((L.foldl (fun S e => (threshStep f k θ e S).1) S) i)
        ((L.foldl (fun S e => (threshStep f k θ e S).1) S) j) := by
  induction L with
  | nil => intro S hS _; exact hS
  | cons a L ih =>
    intro S hS hL
    rw [List.nodup_cons] at hnd
    simp only [List.foldl_cons]
    have haS : ∀ i, a ∉ S i := fun i => hL i a (List.mem_cons.mpr (Or.inl rfl))
    apply ih hnd.2
    · rcases thresh_cases f k θ a S with h | ⟨j, h⟩
      · rw [h]
        exact hS
      · rw [h]
        intro i i' hii'
        by_cases hi : i = j
        · rw [hi] at hii' ⊢
          rw [Function.update_self, Function.update_of_ne (Ne.symm hii')]
          exact Finset.disjoint_insert_left.mpr ⟨haS i', hS j i' hii'⟩
        · by_cases hi' : i' = j
          · rw [hi'] at hii' ⊢
            rw [Function.update_self, Function.update_of_ne hi]
            exact Finset.disjoint_insert_right.mpr ⟨haS i, hS i j hii'⟩
          · rw [Function.update_of_ne hi, Function.update_of_ne hi']
            exact hS i i' hii'
    · intro i e he hm
      have hea : e ≠ a := fun h' => hnd.1 (h' ▸ he)
      have heS : e ∉ S i := hL i e (List.mem_cons_of_mem a he)
      rcases thresh_cases f k θ a S with h | ⟨j, h⟩
      · rw [h] at hm
        exact heS hm
      · rw [h] at hm
        by_cases hi : i = j
        · rw [hi, Function.update_self] at hm
          rw [hi] at heS
          rcases Finset.mem_insert.mp hm with h1 | h1
          · exact hea h1
          · exact heS h1
        · rw [Function.update_of_ne hi] at hm
          exact heS hm

lemma rejected {p : ℕ} (f : Finset E → ℝ) (k : ℕ) (θ : ℝ) (σ : List E) (o : E) (ho : o ∈ σ)
    (hnot : ∀ i : Fin p,
      o ∉ (σ.foldl (fun S e => (threshStep f k θ e S).1) (fun _ : Fin p => (∅ : Finset E))) i) :
    ∀ i : Fin p, ∃ Y : Finset E,
      Y ⊆ (σ.foldl (fun S e => (threshStep f k θ e S).1) (fun _ : Fin p => (∅ : Finset E))) i ∧
      (Y.card < k → marginal f o Y < θ) := by
  obtain ⟨L1, L2, hL⟩ := List.append_of_mem ho
  rw [hL, List.foldl_append, List.foldl_cons] at hnot ⊢
  obtain ⟨St, hSt⟩ : ∃ St : Fin p → Finset E,
      St = L1.foldl (fun S e => (threshStep f k θ e S).1) (fun _ : Fin p => (∅ : Finset E)) :=
    ⟨_, rfl⟩
  rw [← hSt] at hnot ⊢
  intro i
  have hrej := thresh_rej f k θ o St (fun j hj => hnot j (run_mono f k θ L2 _ j hj))
  exact ⟨St i, (thresh_mono f k θ o St i).trans (run_mono f k θ L2 _ i), hrej i⟩


end A

section B

variable {E : Type} [Fintype E] [DecidableEq E]

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


lemma add_rej (f : Finset E → ℝ) (hf : Submodular f) (θ : ℝ) (hθ : 0 ≤ θ) (Z : Finset E) :
    ∀ Q : Finset E, (∀ q ∈ Q, ∃ Y ⊆ Z, marginal f q Y < θ) →
      f (Z ∪ Q) ≤ f Z + (Q.card : ℝ) * θ := by
  intro Q
  refine Finset.induction_on Q ?_ ?_
  · intro _
    simp
  · intro q Q hq ih hQ
    have ih' := ih (fun q' hq' => hQ q' (Finset.mem_insert_of_mem hq'))
    rw [Finset.union_insert, Finset.card_insert_of_notMem hq]
    push_cast
    by_cases hm : q ∈ Z ∪ Q
    · rw [Finset.insert_eq_of_mem hm]
      linarith
    · obtain ⟨Y, hYZ, hY⟩ := hQ q (Finset.mem_insert_self q Q)
      have hsub := hf (insert q Y) (Z ∪ Q)
      have hYZQ : Y ⊆ Z ∪ Q := hYZ.trans Finset.subset_union_left
      have e1 : insert q Y ∪ (Z ∪ Q) = insert q (Z ∪ Q) := by
        rw [Finset.insert_union, Finset.union_eq_right.mpr hYZQ]
      have e2 : insert q Y ∩ (Z ∪ Q) = Y := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_insert]
        constructor
        · rintro ⟨h1 | h1, h2⟩
          · rw [h1] at h2
            exact absurd h2 hm
          · exact h1
        · intro h
          exact ⟨Or.inr h, hYZQ h⟩
      rw [e1, e2] at hsub
      unfold marginal at hY
      linarith

lemma disj_union (f : Finset E → ℝ) (hf : Submodular f) (X : Finset E) {p : ℕ}
    (S : Fin p → Finset E) (hd : ∀ i j, i ≠ j → Disjoint (S i) (S j)) :
    ∀ I : Finset (Fin p), f (X ∪ I.biUnion S) + ((I.card : ℝ) - 1) * f X ≤
      ∑ i ∈ I, f (X ∪ S i) := by
  intro I
  refine Finset.induction_on I ?_ ?_
  · simp only [Finset.biUnion_empty, Finset.union_empty, Finset.card_empty, Finset.sum_empty,
      Nat.cast_zero]
    linarith
  · intro j I hj ih
    rw [Finset.sum_insert hj, Finset.card_insert_of_notMem hj, Finset.biUnion_insert]
    push_cast
    have hsub := hf (X ∪ S j) (X ∪ I.biUnion S)
    have e1 : X ∪ S j ∪ (X ∪ I.biUnion S) = X ∪ (S j ∪ I.biUnion S) := by
      ext x
      simp only [Finset.mem_union]
      tauto
    have e2 : (X ∪ S j) ∩ (X ∪ I.biUnion S) = X := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_biUnion]
      constructor
      · rintro ⟨h1 | h1, h2 | ⟨i, hi, h2⟩⟩
        · exact h1
        · exact h1
        · exact h2
        · exfalso
          have hij : j ≠ i := fun h => hj (by rw [h]; exact hi)
          exact Finset.disjoint_left.mp (hd j i hij) h1 h2
      · intro h
        exact ⟨Or.inl h, Or.inl h⟩
    rw [e1, e2] at hsub
    linarith


noncomputable def u (x : E → ℝ) (i j : E) (b d : ℝ) : E → ℝ := Function.update (Function.update x i b) j d

lemma u_i (x : E → ℝ) (i j : E) (hij : i ≠ j) (b d : ℝ) : u x i j b d i = b := by
  unfold u
  rw [Function.update_of_ne hij, Function.update_self]

lemma u_j (x : E → ℝ) (i j : E) (b d : ℝ) : u x i j b d j = d := by
  unfold u
  rw [Function.update_self]

lemma u_other (x : E → ℝ) (i j : E) (b d : ℝ) (c : E) (hci : c ≠ i) (hcj : c ≠ j) :
    u x i j b d c = x c := by
  unfold u
  rw [Function.update_of_ne hcj, Function.update_of_ne hci]

lemma u_u (x : E → ℝ) (i j : E) (a c b d : ℝ) : u (u x i j a c) i j b d = u x i j b d := by
  funext l
  simp only [u, Function.update_apply]
  by_cases h1 : l = j <;> by_cases h2 : l = i <;> simp [h1, h2]

lemma u_upd_ij (x : E → ℝ) (a : E) (e : ℝ) (i j : E) (b d : ℝ) (hai : a = i ∨ a = j) :
    u (Function.update x a e) i j b d = u x i j b d := by
  funext l
  simp only [u, Function.update_apply]
  rcases hai with h | h <;> by_cases h1 : l = j <;> by_cases h2 : l = i <;> simp [h, h1, h2]

lemma u_upd_comm (x : E → ℝ) (a : E) (e : ℝ) (i j : E) (b d : ℝ) (hai : a ≠ i) (haj : a ≠ j) :
    Function.update (u x i j b d) a e = u (Function.update x a e) i j b d := by
  funext l
  simp only [u, Function.update_apply]
  by_cases h0 : l = a
  · simp [h0, hai, haj]
  · by_cases h1 : l = j <;> by_cases h2 : l = i <;> simp [h0, h1, h2, Ne.symm hai, Ne.symm haj]

lemma sum_update (x : E → ℝ) (i : E) (v : ℝ) :
    ∑ c, Function.update x i v c = ∑ c, x c + (v - x i) := by
  have h : ∀ c, Function.update x i v c = x c + (if c = i then v - x i else 0) := by
    intro c
    by_cases hc : c = i
    · rw [hc, Function.update_self, if_pos rfl]
      ring
    · rw [Function.update_of_ne hc, if_neg hc]
      ring
  rw [Finset.sum_congr rfl (fun c _ => h c), Finset.sum_add_distrib]
  simp

lemma sum_u (x : E → ℝ) (i j : E) (hij : i ≠ j) (b d : ℝ) :
    ∑ c, u x i j b d c = ∑ c, x c + (b - x i) + (d - x j) := by
  unfold u
  rw [sum_update, sum_update, Function.update_of_ne hij.symm]

lemma F_two (f : Finset E → ℝ) (x : E → ℝ) (i j : E) (hij : i ≠ j) :
    F f x = x i * (x j * F f (u x i j 1 1) + (1 - x j) * F f (u x i j 1 0))
      + (1 - x i) * (x j * F f (u x i j 0 1) + (1 - x j) * F f (u x i j 0 0)) := by
  simp only [u]
  rw [F_rec f x i, F_rec f (Function.update x i 1) j, F_rec f (Function.update x i 0) j,
    Function.update_of_ne hij.symm, Function.update_of_ne hij.symm]

lemma F_u_rec (f : Finset E → ℝ) (x : E → ℝ) (i j a : E) (b d : ℝ) (hai : a ≠ i) (haj : a ≠ j) :
    F f (u x i j b d) = x a * F f (u (Function.update x a 1) i j b d)
      + (1 - x a) * F f (u (Function.update x a 0) i j b d) := by
  rw [F_rec f (u x i j b d) a, u_upd_comm x a 1 i j b d hai haj, u_upd_comm x a 0 i j b d hai haj,
    u_other x i j b d a hai haj]

noncomputable def D (f : Finset E → ℝ) (x : E → ℝ) (i j : E) : ℝ :=
  F f (u x i j 1 1) + F f (u x i j 0 0) - F f (u x i j 1 0) - F f (u x i j 0 1)

lemma u_ind (x : E → ℝ) (i j : E) (hij : i ≠ j) (h01 : ∀ c, x c = 0 ∨ x c = 1) (R : Finset E)
    (hR : ∀ c, c ≠ i → c ≠ j → (c ∈ R ↔ x c = 1)) (b d : ℝ) (T : Finset E)
    (hb : b = 0 ∨ b = 1) (hbT : b = 1 ↔ i ∈ T) (hd : d = 0 ∨ d = 1) (hdT : d = 1 ↔ j ∈ T)
    (hT : ∀ c, c ≠ i → c ≠ j → (c ∈ T ↔ c ∈ R)) :
    u x i j b d = fun c => if c ∈ T then 1 else 0 := by
  funext c
  show u x i j b d c = if c ∈ T then 1 else 0
  by_cases hci : c = i
  · rw [hci, u_i x i j hij]
    rcases hb with h | h
    · have : i ∉ T := fun hm => by
        have := hbT.mpr hm
        rw [h] at this
        norm_num at this
      rw [if_neg this, h]
    · rw [if_pos (hbT.mp h), h]
  · by_cases hcj : c = j
    · rw [hcj, u_j]
      rcases hd with h | h
      · have : j ∉ T := fun hm => by
          have := hdT.mpr hm
          rw [h] at this
          norm_num at this
        rw [if_neg this, h]
      · rw [if_pos (hdT.mp h), h]
    · rw [u_other x i j b d c hci hcj]
      rcases h01 c with h | h
      · have : c ∉ T := fun hm => by
          have := (hR c hci hcj).mp ((hT c hci hcj).mp hm)
          rw [h] at this
          norm_num at this
        rw [if_neg this, h]
      · rw [if_pos ((hT c hci hcj).mpr ((hR c hci hcj).mpr h)), h]

lemma cross_le (f : Finset E → ℝ) (hf : Submodular f) (i j : E) (hij : i ≠ j) (W : Finset E) :
    ∀ x : E → ℝ, (∀ c, 0 ≤ x c ∧ x c ≤ 1) → (∀ c, c ∉ W → x c = 0 ∨ x c = 1) →
      D f x i j ≤ 0 := by
  refine Finset.induction_on W ?_ ?_
  · intro x _ h01
    have h01' : ∀ c, x c = 0 ∨ x c = 1 := fun c => h01 c (Finset.notMem_empty c)
    obtain ⟨R, hRdef⟩ : ∃ R : Finset E,
        R = Finset.univ.filter (fun c => x c = 1 ∧ c ≠ i ∧ c ≠ j) := ⟨_, rfl⟩
    have hiR : i ∉ R := by
      rw [hRdef]
      simp
    have hjR : j ∉ R := by
      rw [hRdef]
      simp
    have hR : ∀ c, c ≠ i → c ≠ j → (c ∈ R ↔ x c = 1) := by
      intro c hci hcj
      rw [hRdef]
      simp [hci, hcj]
    have e11 : u x i j 1 1 = fun c => if c ∈ insert i (insert j R) then 1 else 0 :=
      u_ind x i j hij h01' R hR 1 1 _ (Or.inr rfl) (by simp) (Or.inr rfl) (by simp)
        (fun c hci hcj => by simp [hci, hcj])
    have e00 : u x i j 0 0 = fun c => if c ∈ R then 1 else 0 :=
      u_ind x i j hij h01' R hR 0 0 _ (Or.inl rfl) (by simp [hiR]) (Or.inl rfl) (by simp [hjR])
        (fun c _ _ => Iff.rfl)
    have e10 : u x i j 1 0 = fun c => if c ∈ insert i R then 1 else 0 :=
      u_ind x i j hij h01' R hR 1 0 _ (Or.inr rfl) (by simp) (Or.inl rfl)
        (by simp [hjR, hij.symm]) (fun c hci _ => by simp [hci])
    have e01 : u x i j 0 1 = fun c => if c ∈ insert j R then 1 else 0 :=
      u_ind x i j hij h01' R hR 0 1 _ (Or.inl rfl) (by simp [hiR, hij]) (Or.inr rfl)
        (by simp) (fun c _ hcj => by simp [hcj])
    unfold D
    rw [e11, e00, e10, e01, F_indicator, F_indicator, F_indicator, F_indicator]
    have := hf (insert i R) (insert j R)
    have hU : insert i R ∪ insert j R = insert i (insert j R) := by
      ext c
      simp only [Finset.mem_union, Finset.mem_insert]
      tauto
    have hI : insert i R ∩ insert j R = R := by
      ext c
      simp only [Finset.mem_inter, Finset.mem_insert]
      constructor
      · rintro ⟨h1 | h1, h2 | h2⟩
        · exact absurd (h1.symm.trans h2) hij
        · exact h2
        · exact h1
        · exact h1
      · intro hc
        exact ⟨Or.inr hc, Or.inr hc⟩
    rw [hU, hI] at this
    linarith
  · intro a W ha ih x hx h01
    have hcube : ∀ v : ℝ, 0 ≤ v → v ≤ 1 → ∀ c, 0 ≤ Function.update x a v c ∧
        Function.update x a v c ≤ 1 := by
      intro v hv0 hv1 c
      by_cases hc : c = a
      · rw [hc, Function.update_self]
        exact ⟨hv0, hv1⟩
      · rw [Function.update_of_ne hc]
        exact hx c
    have hW : ∀ v : ℝ, (v = 0 ∨ v = 1) → ∀ c, c ∉ W →
        Function.update x a v c = 0 ∨ Function.update x a v c = 1 := by
      intro v hv c hc
      by_cases hca : c = a
      · rw [hca, Function.update_self]
        exact hv
      · rw [Function.update_of_ne hca]
        exact h01 c (fun h => (Finset.mem_insert.mp h).elim hca hc)
    by_cases hai : a = i ∨ a = j
    · have hD : D f (Function.update x a 0) i j = D f x i j := by
        unfold D
        rw [u_upd_ij x a 0 i j 1 1 hai, u_upd_ij x a 0 i j 0 0 hai, u_upd_ij x a 0 i j 1 0 hai,
          u_upd_ij x a 0 i j 0 1 hai]
      rw [← hD]
      exact ih _ (hcube 0 le_rfl zero_le_one) (hW 0 (Or.inl rfl))
    · push_neg at hai
      have hrecD : D f x i j = x a * D f (Function.update x a 1) i j
          + (1 - x a) * D f (Function.update x a 0) i j := by
        unfold D
        rw [F_u_rec f x i j a 1 1 hai.1 hai.2, F_u_rec f x i j a 0 0 hai.1 hai.2,
          F_u_rec f x i j a 1 0 hai.1 hai.2, F_u_rec f x i j a 0 1 hai.1 hai.2]
        ring
      have h1 := ih _ (hcube 1 zero_le_one le_rfl) (hW 1 (Or.inr rfl))
      have h0 := ih _ (hcube 0 le_rfl zero_le_one) (hW 0 (Or.inl rfl))
      rw [hrecD]
      have m1 := mul_le_mul_of_nonneg_left h1 (hx a).1
      have m0 := mul_le_mul_of_nonneg_left h0 (by linarith [(hx a).2] : (0 : ℝ) ≤ 1 - x a)
      linarith

noncomputable def G (a11 a10 a01 a00 xi xj s : ℝ) : ℝ :=
  (xi + s) * ((xj - s) * a11 + (1 - (xj - s)) * a10)
    + (1 - (xi + s)) * ((xj - s) * a01 + (1 - (xj - s)) * a00)

lemma G_quad (a11 a10 a01 a00 xi xj s : ℝ) :
    G a11 a10 a01 a00 xi xj s = G a11 a10 a01 a00 xi xj 0
      + s * ((xj - xi) * a11 + (xi + 1 - xj) * a10 - (1 - xi + xj) * a01 + (xj - xi) * a00)
      + s ^ 2 * (a10 + a01 - a11 - a00) := by
  unfold G
  ring

lemma quad_aux (g0 g1 g2 s1 s2 B C : ℝ) (hC : 0 ≤ C) (hs1 : s1 < 0) (hs2 : 0 < s2)
    (h1 : g1 = g0 + s1 * B + s1 ^ 2 * C) (h2 : g2 = g0 + s2 * B + s2 ^ 2 * C) :
    g0 ≤ g1 ∨ g0 ≤ g2 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨k1, k2⟩ := hcon
  have p1 : s2 * (s1 * B + s1 ^ 2 * C) < 0 := mul_neg_of_pos_of_neg hs2 (by linarith)
  have p2 : (-s1) * (s2 * B + s2 ^ 2 * C) < 0 := mul_neg_of_pos_of_neg (by linarith) (by linarith)
  have p3 : 0 ≤ s1 * s2 * (s1 - s2) * C :=
    mul_nonneg (le_of_lt (mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos hs1 hs2) (by linarith))) hC
  have e : s2 * (s1 * B + s1 ^ 2 * C) + (-s1) * (s2 * B + s2 ^ 2 * C)
      = s1 * s2 * (s1 - s2) * C := by ring
  linarith

lemma G_max (a11 a10 a01 a00 xi xj s1 s2 : ℝ) (hC : a11 + a00 ≤ a10 + a01) (hs1 : s1 < 0)
    (hs2 : 0 < s2) :
    G a11 a10 a01 a00 xi xj 0 ≤ G a11 a10 a01 a00 xi xj s1 ∨
      G a11 a10 a01 a00 xi xj 0 ≤ G a11 a10 a01 a00 xi xj s2 :=
  quad_aux _ _ _ s1 s2 _ _ (by linarith) hs1 hs2 (G_quad a11 a10 a01 a00 xi xj s1)
    (G_quad a11 a10 a01 a00 xi xj s2)

lemma F_move (f : Finset E → ℝ) (x : E → ℝ) (i j : E) (hij : i ≠ j) (s : ℝ) :
    F f (u x i j (x i + s) (x j - s)) = G (F f (u x i j 1 1)) (F f (u x i j 1 0))
      (F f (u x i j 0 1)) (F f (u x i j 0 0)) (x i) (x j) s := by
  unfold G
  rw [F_two f _ i j hij, u_i x i j hij, u_j, u_u, u_u, u_u, u_u]

noncomputable def Fr (x : E → ℝ) : Finset E := Finset.univ.filter (fun c => 0 < x c ∧ x c < 1)

lemma mem_Fr (x : E → ℝ) (c : E) : c ∈ Fr x ↔ 0 < x c ∧ x c < 1 := by
  simp [Fr]

lemma integral_case (f : Finset E → ℝ) (k : ℕ) (x : E → ℝ) (h01 : ∀ c, x c = 0 ∨ x c = 1)
    (hsum : ∑ c, x c < (k : ℝ) + 1) :
    ∃ A : Finset E, (∀ e ∈ A, x e = 1) ∧ A.card ≤ k ∧ F f x = f A := by
  obtain ⟨A, hA⟩ : ∃ A : Finset E, A = Finset.univ.filter (fun c => x c = 1) := ⟨_, rfl⟩
  have hx : x = fun c => if c ∈ A then 1 else 0 := by
    funext c
    rcases h01 c with h | h <;> simp [hA, h]
  refine ⟨A, ?_, ?_, ?_⟩
  · intro e he
    rw [hA] at he
    exact (Finset.mem_filter.mp he).2
  · have hs : ∑ c, x c = (A.card : ℝ) := by
      rw [hx]
      simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hs] at hsum
    have : A.card < k + 1 := by exact_mod_cast hsum
    omega
  · rw [hx]
    exact F_indicator f A

lemma move_ok (x : E → ℝ) (hx : ∀ c, 0 ≤ x c ∧ x c ≤ 1) (i j : E) (hij : i ≠ j)
    (hi : 0 < x i ∧ x i < 1) (hj : 0 < x j ∧ x j < 1) (s : ℝ)
    (hs1 : -min (x i) (1 - x j) ≤ s) (hs2 : s ≤ min (1 - x i) (x j)) :
    (∀ c, 0 ≤ u x i j (x i + s) (x j - s) c ∧ u x i j (x i + s) (x j - s) c ≤ 1) ∧
    ∑ c, u x i j (x i + s) (x j - s) c = ∑ c, x c ∧
    (∀ e, 0 < u x i j (x i + s) (x j - s) e → 0 < x e) ∧
    Fr (u x i j (x i + s) (x j - s)) ⊆ Fr x := by
  have m1 := min_le_left (x i) (1 - x j)
  have m2 := min_le_right (x i) (1 - x j)
  have m3 := min_le_left (1 - x i) (x j)
  have m4 := min_le_right (1 - x i) (x j)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c
    by_cases hci : c = i
    · rw [hci, u_i x i j hij]
      constructor <;> linarith
    · by_cases hcj : c = j
      · rw [hcj, u_j]
        constructor <;> linarith
      · rw [u_other x i j _ _ c hci hcj]
        exact hx c
  · rw [sum_u x i j hij]
    ring
  · intro e he
    by_cases hei : e = i
    · rw [hei]
      exact hi.1
    · by_cases hej : e = j
      · rw [hej]
        exact hj.1
      · rw [u_other x i j _ _ e hei hej] at he
        exact he
  · intro c hc
    rw [mem_Fr] at hc ⊢
    by_cases hci : c = i
    · rw [hci]
      exact hi
    · by_cases hcj : c = j
      · rw [hcj]
        exact hj
      · rw [u_other x i j _ _ c hci hcj] at hc
        exact hc

lemma round_main (f : Finset E → ℝ) (hf : Submodular f) (k : ℕ) (n : ℕ) :
    ∀ x : E → ℝ, (Fr x).card = n → (∀ c, 0 ≤ x c ∧ x c ≤ 1) → ∑ c, x c ≤ (k : ℝ) →
      ∃ A : Finset E, (∀ e ∈ A, 0 < x e) ∧ A.card ≤ k ∧ F f x ≤ f A := by
  refine Nat.strong_induction_on n ?_
  intro n ih x hn hx hsum
  by_cases h2 : ∃ i j, i ≠ j ∧ i ∈ Fr x ∧ j ∈ Fr x
  · obtain ⟨i, j, hij, hi, hj⟩ := h2
    have hiF := hi
    have hjF := hj
    rw [mem_Fr] at hi hj
    obtain ⟨s1, hs1d⟩ : ∃ s1 : ℝ, s1 = -min (x i) (1 - x j) := ⟨_, rfl⟩
    obtain ⟨s2, hs2d⟩ : ∃ s2 : ℝ, s2 = min (1 - x i) (x j) := ⟨_, rfl⟩
    have hs1 : s1 < 0 := by
      rw [hs1d]
      exact neg_neg_of_pos (lt_min hi.1 (by linarith [hj.2]))
    have hs2 : 0 < s2 := by
      rw [hs2d]
      exact lt_min (by linarith [hi.2]) hj.1
    have hle : s1 ≤ s2 := by linarith
    have hcross : F f (u x i j 1 1) + F f (u x i j 0 0) ≤ F f (u x i j 1 0) + F f (u x i j 0 1) := by
      have := cross_le f hf i j hij Finset.univ x hx (fun c hc => absurd (Finset.mem_univ c) hc)
      unfold D at this
      linarith
    have hF0 : F f x = G (F f (u x i j 1 1)) (F f (u x i j 1 0))
        (F f (u x i j 0 1)) (F f (u x i j 0 0)) (x i) (x j) 0 := by
      rw [F_two f x i j hij]
      unfold G
      ring
    have hm1 : i ∉ Fr (u x i j (x i + s1) (x j - s1)) ∨ j ∉ Fr (u x i j (x i + s1) (x j - s1)) := by
      rcases le_total (x i) (1 - x j) with h | h
      · left
        rw [mem_Fr, u_i x i j hij, hs1d, min_eq_left h]
        intro hc
        linarith [hc.1]
      · right
        rw [mem_Fr, u_j, hs1d, min_eq_right h]
        intro hc
        linarith [hc.2]
    have hm2 : i ∉ Fr (u x i j (x i + s2) (x j - s2)) ∨ j ∉ Fr (u x i j (x i + s2) (x j - s2)) := by
      rcases le_total (1 - x i) (x j) with h | h
      · left
        rw [mem_Fr, u_i x i j hij, hs2d, min_eq_left h]
        intro hc
        linarith [hc.2]
      · right
        rw [mem_Fr, u_j, hs2d, min_eq_right h]
        intro hc
        linarith [hc.1]
    have finish : ∀ s : ℝ, s1 ≤ s → s ≤ s2 →
        (i ∉ Fr (u x i j (x i + s) (x j - s)) ∨ j ∉ Fr (u x i j (x i + s) (x j - s))) →
        F f x ≤ F f (u x i j (x i + s) (x j - s)) →
        ∃ A : Finset E, (∀ e ∈ A, 0 < x e) ∧ A.card ≤ k ∧ F f x ≤ f A := by
      intro s hsa hsb hm hFle
      obtain ⟨c1, c2, c3, c4⟩ := move_ok x hx i j hij hi hj s (by rw [← hs1d]; exact hsa)
        (by rw [← hs2d]; exact hsb)
      have hlt : (Fr (u x i j (x i + s) (x j - s))).card < n := by
        rw [← hn]
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset c4]
        rcases hm with h | h
        · exact ⟨i, hiF, h⟩
        · exact ⟨j, hjF, h⟩
      obtain ⟨A, hA1, hA2, hA3⟩ := ih _ hlt _ rfl c1 (by rw [c2]; exact hsum)
      exact ⟨A, fun e he => c3 e (hA1 e he), hA2, le_trans hFle hA3⟩
    rcases G_max _ _ _ _ (x i) (x j) s1 s2 hcross hs1 hs2 with h | h
    · exact finish s1 le_rfl hle hm1 (by rw [hF0, F_move f x i j hij s1]; exact h)
    · exact finish s2 hle le_rfl hm2 (by rw [hF0, F_move f x i j hij s2]; exact h)
  · push_neg at h2
    by_cases h1 : ∃ i, i ∈ Fr x
    · obtain ⟨i, hi⟩ := h1
      have hother : ∀ c, c ≠ i → x c = 0 ∨ x c = 1 := by
        intro c hc
        have hcn : c ∉ Fr x := h2 i c (Ne.symm hc) hi
        rw [mem_Fr] at hcn
        rcases (hx c).1.lt_or_eq with h | h
        · right
          by_contra hne
          exact hcn ⟨h, lt_of_le_of_ne (hx c).2 hne⟩
        · left
          exact h.symm
      rw [mem_Fr] at hi
      have h01 : ∀ v : ℝ, (v = 0 ∨ v = 1) → ∀ c,
          Function.update x i v c = 0 ∨ Function.update x i v c = 1 := by
        intro v hv c
        by_cases hc : c = i
        · rw [hc, Function.update_self]
          exact hv
        · rw [Function.update_of_ne hc]
          exact hother c hc
      have hsum1 : ∑ c, Function.update x i 1 c < (k : ℝ) + 1 := by
        rw [sum_update]
        linarith [hi.1]
      have hsum0 : ∑ c, Function.update x i 0 c < (k : ℝ) + 1 := by
        rw [sum_update]
        linarith [hi.1]
      obtain ⟨A1, hA1, hc1, hF1⟩ := integral_case f k _ (h01 1 (Or.inr rfl)) hsum1
      obtain ⟨A0, hA0, hc0, hF0⟩ := integral_case f k _ (h01 0 (Or.inl rfl)) hsum0
      have hrec := F_rec f x i
      by_cases hcmp : F f (Function.update x i 0) ≤ F f (Function.update x i 1)
      · refine ⟨A1, ?_, hc1, ?_⟩
        · intro e he
          have he1 := hA1 e he
          by_cases hei : e = i
          · rw [hei]
            exact hi.1
          · rw [Function.update_of_ne hei] at he1
            rw [he1]
            norm_num
        · have m := mul_le_mul_of_nonneg_left hcmp (by linarith [hi.2] : (0 : ℝ) ≤ 1 - x i)
          rw [← hF1]
          linarith
      · push_neg at hcmp
        refine ⟨A0, ?_, hc0, ?_⟩
        · intro e he
          have he0 := hA0 e he
          by_cases hei : e = i
          · rw [hei, Function.update_self] at he0
            norm_num at he0
          · rw [Function.update_of_ne hei] at he0
            rw [he0]
            norm_num
        · have m := mul_le_mul_of_nonneg_left hcmp.le hi.1.le
          rw [← hF0]
          linarith
    · push_neg at h1
      have h01 : ∀ c, x c = 0 ∨ x c = 1 := by
        intro c
        have hcn := h1 c
        rw [mem_Fr] at hcn
        rcases (hx c).1.lt_or_eq with h | h
        · right
          by_contra hne
          exact hcn ⟨h, lt_of_le_of_ne (hx c).2 hne⟩
        · left
          exact h.symm
      obtain ⟨A, hA, hc, hF⟩ := integral_case f k x h01 (by linarith)
      refine ⟨A, ?_, hc, le_of_eq hF⟩
      intro e he
      rw [hA e he]
      norm_num


end B

lemma concave_main {E : Type} [Fintype E] [DecidableEq E] (f : Finset E → ℝ) (hf : Submodular f)
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
  have hc := P_concave (S \ B) (fun T => f (B ∪ T)) hsub
  refine hc.congr ?_
  intro t ht
  dsimp only
  rw [← F_line f (S \ B) B Finset.disjoint_sdiff t]
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


lemma lemma5_main {E : Type} [Fintype E] [DecidableEq E] (f : Finset E → ℝ) (hf0 : ∀ S, 0 ≤ f S)
    (hf : Submodular f) (k : ℕ) (hk : 1 ≤ k) (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (p : ℕ)
    (hp : 1 ≤ p) (τ : ℝ) (hτ : 0 ≤ τ) (σ : List E) (hσ : IsStream σ) (OPT : Finset E)
    (hlt : ∀ i, (alg1Sets p f k α τ σ i).card < k) (A : Finset E) :
    let S := alg1Sets p f k α τ σ
    let O := OPT \ Finset.univ.biUnion S
    let b : ℝ := (O.card : ℝ) / (k : ℝ)
    (1 - (p : ℝ)⁻¹) * f (O ∪ A) - α * b * τ / (1 + α) ≤ (p : ℝ)⁻¹ * ∑ i, f (S i ∪ A) := by
  intro S O b
  have hb : b = (O.card : ℝ) / (k : ℝ) := rfl
  have hO : O = OPT \ Finset.univ.biUnion S := rfl
  have hSdef : S = σ.foldl (fun S e => (threshStep f k (threshold α k τ) e S).1)
      (fun _ => (∅ : Finset E)) := rfl
  have hθ0 : 0 ≤ threshold α k τ := by
    unfold threshold
    have : (0 : ℝ) ≤ α / (1 + α) := div_nonneg hα0.le (by linarith)
    exact div_nonneg (mul_nonneg this hτ) (Nat.cast_nonneg k)
  have hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j) := by
    rw [hSdef]
    exact run_disj f k _ σ hσ.1 _ (fun _ _ _ => by simp) (fun _ _ _ => by simp)
  have hrej : ∀ q ∈ O, ∀ i, ∃ Y ⊆ S i, marginal f q Y < threshold α k τ := by
    intro q hq i
    have hq' : ∀ j, q ∉ S j := by
      intro j hj
      rw [hO] at hq
      exact (Finset.mem_sdiff.mp hq).2 (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hj⟩)
    rw [hSdef] at hq' ⊢
    obtain ⟨Y, hY1, hY2⟩ := rejected f k (threshold α k τ) σ q (hσ.2 q) hq' i
    exact ⟨Y, hY1, hY2 (lt_of_le_of_lt (Finset.card_le_card hY1) (hlt i))⟩
  have hclaim1 : ∀ i, f ((O ∪ A) ∪ S i) ≤ f (S i ∪ A) + (O.card : ℝ) * threshold α k τ := by
    intro i
    have := add_rej f hf (threshold α k τ) hθ0 (S i ∪ A) O
      (fun q hq => by
        obtain ⟨Y, hY1, hY2⟩ := hrej q hq i
        exact ⟨Y, hY1.trans Finset.subset_union_left, hY2⟩)
    have e : (O ∪ A) ∪ S i = (S i ∪ A) ∪ O := by
      ext x
      simp only [Finset.mem_union]
      tauto
    rw [e]
    exact this
  have hclaim2 := disj_union f hf (O ∪ A) S hdisj Finset.univ
  rw [Finset.card_univ, Fintype.card_fin] at hclaim2
  have hnn : 0 ≤ f ((O ∪ A) ∪ Finset.univ.biUnion S) := hf0 _
  have hsum : ∑ i, f ((O ∪ A) ∪ S i) ≤ ∑ i, (f (S i ∪ A) + (O.card : ℝ) * threshold α k τ) :=
    Finset.sum_le_sum (fun i _ => hclaim1 i)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hsum
  have key : ((p : ℝ) - 1) * f (O ∪ A) - (p : ℝ) * ((O.card : ℝ) * threshold α k τ) ≤
      ∑ i, f (S i ∪ A) := by linarith
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have m := mul_le_mul_of_nonneg_left key (inv_nonneg.mpr hp0.le)
  have hP : (p : ℝ)⁻¹ * p = 1 := inv_mul_cancel₀ hp0.ne'
  have e : (p : ℝ)⁻¹ * (((p : ℝ) - 1) * f (O ∪ A) - (p : ℝ) * ((O.card : ℝ) * threshold α k τ))
      = (1 - (p : ℝ)⁻¹) * f (O ∪ A) - (O.card : ℝ) * threshold α k τ := by
    linear_combination (f (O ∪ A) - (O.card : ℝ) * threshold α k τ) * hP
  have hθb : (O.card : ℝ) * threshold α k τ = α * b * τ / (1 + α) := by
    rw [hb]
    unfold threshold
    ring
  rw [← hθb]
  linarith


lemma lemma6_main {E Ω : Type} [Fintype E] [DecidableEq E] [Fintype Ω] (f : Finset E → ℝ)
    (hf0 : ∀ S, 0 ≤ f S) (hf : Submodular f) (k : ℕ) (hk : 1 ≤ k) (α : ℝ) (hα0 : 0 < α)
    (hα1 : α ≤ 1) (μ : Ω → ℝ) (Off : Ω → Finset E → Finset E)
    (hOff : IsApproxOffline f k α μ Off) (p : ℕ) (hp : 1 ≤ p) (τ : ℝ) (hτ0 : 0 ≤ τ) (σ : List E)
    (hσ : IsStream σ) (OPT : Finset E) (hOPT : OPT.card ≤ k) (hτ : τ ≤ f OPT)
    (hlt : ∀ i, (alg1Sets p f k α τ σ i).card < k) :
    let S := alg1Sets p f k α τ σ
    let O := OPT \ Finset.univ.biUnion S
    let b : ℝ := (O.card : ℝ) / (k : ℝ)
    α * b * τ * (1 - (p : ℝ)⁻¹ - α * b / (1 + α)) + α * (1 - b) * f (OPT \ O) ≤
      ∑ ω, μ ω * f (Off ω (Finset.univ.biUnion S)) := by
  intro S O b
  have hb : b = (O.card : ℝ) / (k : ℝ) := rfl
  have hO : O = OPT \ Finset.univ.biUnion S := rfl
  obtain ⟨B, hB⟩ : ∃ B : Finset E, B = OPT \ O := ⟨_, rfl⟩
  rw [← hB]
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hOsub : O ⊆ OPT := by
    rw [hO]
    exact Finset.sdiff_subset
  have hcardO : O.card + B.card = OPT.card := by
    rw [hB, add_comm]
    exact Finset.card_sdiff_add_card_eq_card hOsub
  have hb0 : 0 ≤ b := by
    rw [hb]
    positivity
  have hbk : b * k = O.card := by
    rw [hb, div_mul_cancel₀ _ hk0.ne']
  have hb1 : b ≤ 1 := by
    rw [hb, div_le_one hk0]
    exact_mod_cast (Finset.card_le_card hOsub).trans hOPT
  have hOB : O ∪ B = OPT := by
    rw [hB]
    exact Finset.union_sdiff_of_subset hOsub
  have hBU : ∀ e ∈ B, e ∈ Finset.univ.biUnion S := by
    intro e he
    rw [hB, Finset.mem_sdiff, hO, Finset.mem_sdiff] at he
    by_contra h
    exact he.2 ⟨he.1, h⟩
  set R := ∑ ω, μ ω * f (Off ω (Finset.univ.biUnion S)) with hR
  have hi : ∀ i, α * ((1 - b) * f B + b * f (S i ∪ B)) ≤ R := by
    intro i
    obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, g = fun t : ℝ =>
        F f (fun e => max (t * (if e ∈ S i then 1 else 0)) (if e ∈ B then 1 else 0)) := ⟨_, rfl⟩
    have hc : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) g := by
      rw [hg]
      exact concave_main f hf (S i) B
    have hcc := hc.2 (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one)
      (by linarith : (0 : ℝ) ≤ 1 - b) hb0 (by ring : 1 - b + b = 1)
    simp only [smul_eq_mul, mul_zero, mul_one, zero_add] at hcc
    have hpt0 : ∀ e, max ((0 : ℝ) * (if e ∈ S i then 1 else 0)) (if e ∈ B then 1 else 0)
        = if e ∈ B then 1 else 0 := by
      intro e
      by_cases h : e ∈ B
      · rw [if_pos h, zero_mul]
        exact max_eq_right zero_le_one
      · rw [if_neg h, zero_mul, max_self]
    have hg0 : g 0 = f B := by
      rw [hg]
      show F f (fun e => max ((0 : ℝ) * (if e ∈ S i then 1 else 0)) (if e ∈ B then 1 else 0)) = f B
      have hfun : (fun e => max ((0 : ℝ) * (if e ∈ S i then 1 else 0)) (if e ∈ B then 1 else 0))
          = fun e => if e ∈ B then 1 else 0 := funext hpt0
      rw [hfun]
      exact F_indicator f B
    have hpt1 : ∀ e, max ((1 : ℝ) * (if e ∈ S i then 1 else 0)) (if e ∈ B then 1 else 0)
        = if e ∈ S i ∪ B then 1 else 0 := by
      intro e
      rw [one_mul]
      by_cases hS : e ∈ S i <;> by_cases hB' : e ∈ B
      · rw [if_pos hS, if_pos hB', if_pos (Finset.mem_union.mpr (Or.inl hS)), max_self]
      · rw [if_pos hS, if_neg hB', if_pos (Finset.mem_union.mpr (Or.inl hS))]
        exact max_eq_left zero_le_one
      · rw [if_neg hS, if_pos hB', if_pos (Finset.mem_union.mpr (Or.inr hB'))]
        exact max_eq_right zero_le_one
      · rw [if_neg hS, if_neg hB', if_neg (fun h => (Finset.mem_union.mp h).elim hS hB'), max_self]
    have hg1 : g 1 = f (S i ∪ B) := by
      rw [hg]
      show F f (fun e => max ((1 : ℝ) * (if e ∈ S i then 1 else 0)) (if e ∈ B then 1 else 0))
        = f (S i ∪ B)
      have hfun : (fun e => max ((1 : ℝ) * (if e ∈ S i then 1 else 0)) (if e ∈ B then 1 else 0))
          = fun e => if e ∈ S i ∪ B then 1 else 0 := funext hpt1
      rw [hfun]
      exact F_indicator f (S i ∪ B)
    have hgb : g b = F f (fun e => max (b * (if e ∈ S i then 1 else 0)) (if e ∈ B then 1 else 0)) := by
      rw [hg]
    rw [hg0, hg1, hgb] at hcc
    have hind0 : ∀ e, (0 : ℝ) ≤ (if e ∈ B then 1 else 0) := fun e => by
      split_ifs <;> norm_num
    have hindS0 : ∀ e, (0 : ℝ) ≤ b * (if e ∈ S i then 1 else 0) := fun e =>
      mul_nonneg hb0 (by split_ifs <;> norm_num)
    have hx0 : ∀ e, 0 ≤ max (b * (if e ∈ S i then (1 : ℝ) else 0)) (if e ∈ B then 1 else 0) :=
      fun e => le_max_of_le_right (hind0 e)
    have hx1 : ∀ e, max (b * (if e ∈ S i then (1 : ℝ) else 0)) (if e ∈ B then 1 else 0) ≤ 1 :=
      fun e => max_le (by split_ifs <;> linarith) (by split_ifs <;> norm_num)
    have hxk : ∑ e, max (b * (if e ∈ S i then (1 : ℝ) else 0)) (if e ∈ B then 1 else 0) ≤ (k : ℝ) := by
      have h1 : ∀ e, max (b * (if e ∈ S i then (1 : ℝ) else 0)) (if e ∈ B then 1 else 0) ≤
          b * (if e ∈ S i then 1 else 0) + (if e ∈ B then 1 else 0) := fun e =>
        max_le (le_add_of_nonneg_right (hind0 e)) (le_add_of_nonneg_left (hindS0 e))
      have h2 : ∑ e, (b * (if e ∈ S i then (1 : ℝ) else 0) + (if e ∈ B then 1 else 0))
          = b * (S i).card + B.card := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
      have hSi : ((S i).card : ℝ) ≤ k := by exact_mod_cast (hlt i).le
      have m := mul_le_mul_of_nonneg_left hSi hb0
      have hc' : O.card + B.card ≤ k := by
        rw [hcardO]
        exact hOPT
      have hc'' : (O.card : ℝ) + B.card ≤ k := by exact_mod_cast hc'
      have hs := Finset.sum_le_sum (fun e (_ : e ∈ Finset.univ) => h1 e)
      rw [h2] at hs
      linarith
    obtain ⟨A, hA1, hA2, hA3⟩ := round_main f hf k _
      (fun e => max (b * (if e ∈ S i then (1 : ℝ) else 0)) (if e ∈ B then 1 else 0)) rfl
      (fun c => ⟨hx0 c, hx1 c⟩) hxk
    have hAU : A ⊆ Finset.univ.biUnion S := by
      intro e he
      have hpos : 0 < max (b * (if e ∈ S i then (1 : ℝ) else 0)) (if e ∈ B then 1 else 0) :=
        hA1 e he
      by_cases heS : e ∈ S i
      · exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, heS⟩
      · by_cases heB : e ∈ B
        · exact hBU e heB
        · exfalso
          rw [if_neg heS, if_neg heB, mul_zero, max_self] at hpos
          exact lt_irrefl 0 hpos
    have happ := hOff.approx _ A hAU hA2
    calc α * ((1 - b) * f B + b * f (S i ∪ B)) ≤ α * f A :=
          mul_le_mul_of_nonneg_left (hcc.trans hA3) hα0.le
      _ ≤ R := happ
  have h5 : (1 - (p : ℝ)⁻¹) * f (O ∪ B) - α * b * τ / (1 + α) ≤
      (p : ℝ)⁻¹ * ∑ i, f (S i ∪ B) :=
    lemma5_main f hf0 hf k hk α hα0 hα1 p hp τ hτ0 σ hσ OPT hlt B
  rw [hOB] at h5
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  have hsplit : ∑ i, α * ((1 - b) * f B + b * f (S i ∪ B))
      = ∑ i, (α * (1 - b) * f B + α * b * f (S i ∪ B)) :=
    Finset.sum_congr rfl (fun i _ => by ring)
  rw [hsplit, Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  rw [← Finset.mul_sum] at hsum
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hP : (p : ℝ)⁻¹ * p = 1 := inv_mul_cancel₀ hp0.ne'
  have m := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hp0.le)
  have e1 : (p : ℝ)⁻¹ * ((p : ℝ) * (α * (1 - b) * f B) + α * b * ∑ i, f (S i ∪ B))
      = α * (1 - b) * f B + α * b * ((p : ℝ)⁻¹ * ∑ i, f (S i ∪ B)) := by
    linear_combination (α * (1 - b) * f B) * hP
  have e2 : (p : ℝ)⁻¹ * ((p : ℝ) * R) = R := by
    linear_combination R * hP
  have hp1 : (0 : ℝ) ≤ 1 - (p : ℝ)⁻¹ := by
    have : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hp)
    linarith
  have hab : 0 ≤ α * b := mul_nonneg hα0.le hb0
  have m1 := mul_le_mul_of_nonneg_left h5 hab
  have m2 : α * b * ((1 - (p : ℝ)⁻¹) * τ) ≤ α * b * ((1 - (p : ℝ)⁻¹) * f OPT) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hτ hp1) hab
  have eq1 : α * b * τ * (1 - (p : ℝ)⁻¹ - α * b / (1 + α))
      = α * b * ((1 - (p : ℝ)⁻¹) * τ) - α * b * (α * b * τ / (1 + α)) := by ring
  have eq2 : α * b * ((1 - (p : ℝ)⁻¹) * f OPT - α * b * τ / (1 + α))
      = α * b * ((1 - (p : ℝ)⁻¹) * f OPT) - α * b * (α * b * τ / (1 + α)) := by ring
  rw [eq1]
  rw [eq2] at m1
  linarith

end Aux_StreamSubmod_lemma_6

open Aux_StreamSubmod_lemma_6 in
open NonmonotoneSubmod.Shared in
open StreamSubmod in
theorem solution {E Ω : Type} [Fintype E] [DecidableEq E] [Fintype Ω] (f : Finset E → ℝ)
    (hf0 : ∀ S, 0 ≤ f S) (hf : Submodular f) (k : ℕ) (hk : 1 ≤ k) (α : ℝ) (hα0 : 0 < α)
    (hα1 : α ≤ 1) (μ : Ω → ℝ) (Off : Ω → Finset E → Finset E)
    (hOff : IsApproxOffline f k α μ Off) (p : ℕ) (hp : 1 ≤ p) (τ : ℝ) (hτ0 : 0 ≤ τ) (σ : List E)
    (hσ : IsStream σ) (OPT : Finset E) (hOPT : OPT.card ≤ k) (hτ : τ ≤ f OPT)
    (hlt : ∀ i, (alg1Sets p f k α τ σ i).card < k) :
    let S := alg1Sets p f k α τ σ
    let O := OPT \ Finset.univ.biUnion S
    let b : ℝ := (O.card : ℝ) / (k : ℝ)
    α * b * τ * (1 - (p : ℝ)⁻¹ - α * b / (1 + α)) + α * (1 - b) * f (OPT \ O) ≤
      ∑ ω, μ ω * f (Off ω (Finset.univ.biUnion S)) :=
  lemma6_main f hf0 hf k hk α hα0 hα1 μ Off hOff p hp τ hτ0 σ hσ OPT hOPT hτ hlt
