-- Prove2me | solution 1 for TradingNetFlow.ChainStable.lemma_5_5
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-11T06:23:57.207742+00:00
-- url     : https://prove2.me/submissions/8ec3c10c-7e2d-40d6-85c9-a8602b646b13

import Mathlib
import Definitions.Def_TradingNetFlow_ChainStable_Model
import Theorems.Thm_TradingNetFlow_ChainStable_theorem_4_1

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace P8e319fe0
open Finset TradingNetFlow.ChainStable DiscreteConvex.EconomicEquilibrium
  DiscreteConvex.MConvexFunctions

variable {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E] [DecidableEq E]

/-- The signed vector of a trade set at agent `i`. -/
def vec (G : Economy N E) (i : N) (S : Finset E) : {e // e ∈ G.delta i} → ℤ :=
  fun e => if e.1 ∈ S then G.sign i e.1 else 0

theorem sign_ne_zero (G : Economy N E) (i : N) (e : E) : G.sign i e ≠ 0 := by
  unfold Economy.sign; split_ifs <;> norm_num

theorem sign_eq_one {G : Economy N E} {i : N} {e : E} (h : G.seller e = i) :
    G.sign i e = 1 := by
  simp [Economy.sign, h]

theorem sign_eq_neg_one {G : Economy N E} {i : N} {e : E} (h : ¬ G.seller e = i) :
    G.sign i e = -1 := by
  simp [Economy.sign, h]

theorem vec_wSigned (G : Economy N E) (i : N) (S : Finset E) (hS : S ⊆ G.delta i) :
    G.wSigned i (vec G i S) = ((G.w i S : ℝ) : WithBot ℝ) := by
  unfold Economy.wSigned
  rw [if_pos]
  · congr 2
    ext e
    simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype, vec]
    constructor
    · rintro ⟨a, ha, rfl⟩
      by_contra h
      exact (Finset.mem_filter.mp ha).2 (if_neg h)
    · intro he
      exact ⟨⟨e, hS he⟩, by simp [he, sign_ne_zero], rfl⟩
  · intro e
    unfold vec
    split_ifs <;> simp

theorem vec_mem_dom (G : Economy N E) (i : N) (S : Finset E) (hS : S ⊆ G.delta i) :
    vec G i S ∈ UDom (G.wSigned i) := by
  simp [UDom, vec_wSigned G i S hS]

/-- Per-agent exchange against the empty set, for a sold trade `e`. -/
theorem exc_sold (G : Economy N E) (hG : G.Standing) (i : N) (S : Finset E)
    (hS : S ⊆ G.delta i) (e : E) (he : e ∈ S) (hsell : G.seller e = i) :
    G.w i S + G.w i ∅ ≤ G.w i (S.erase e) + G.w i {e} ∨
      ∃ f ∈ S, ¬ G.seller f = i ∧
        G.w i S + G.w i ∅ ≤ G.w i (S \ {e, f}) + G.w i {e, f} := by
  have hed : e ∈ G.delta i := hS he
  obtain ⟨-, hexc⟩ := hG.2 i
  have hpos : (⟨e, hed⟩ : {e // e ∈ G.delta i}) ∈ SuppPos (vec G i S) (vec G i ∅) := by
    simp [SuppPos, vec, he, sign_eq_one hsell]
  have h := hexc _ (vec_mem_dom G i S hS) _ (vec_mem_dom G i ∅ (empty_subset _)) _ hpos
  have e1 : (fun w => vec G i S w - CharVec ⟨e, hed⟩ w) = vec G i (S.erase e) := by
    funext ⟨v, hv⟩
    simp only [vec, CharVec, Subtype.mk.injEq, mem_erase]
    by_cases hve : v = e
    · subst hve; simp [he, sign_eq_one hsell]
    · simp [hve]
  have e2 : (fun w => vec G i ∅ w + CharVec ⟨e, hed⟩ w) = vec G i {e} := by
    funext ⟨v, hv⟩
    simp only [vec, CharVec, Subtype.mk.injEq, mem_singleton, notMem_empty]
    by_cases hve : v = e
    · subst hve; simp [sign_eq_one hsell]
    · simp [hve]
  rw [e1, e2, vec_wSigned G i S hS, vec_wSigned G i ∅ (empty_subset _),
    vec_wSigned G i _ ((erase_subset _ _).trans hS),
    vec_wSigned G i {e} (singleton_subset_iff.mpr hed), ← WithBot.coe_add,
    ← WithBot.coe_add] at h
  rcases le_max_iff.mp h with h1 | h2
  · left; exact_mod_cast h1
  · right
    obtain ⟨⟨f, hf⟩, hj, hle⟩ := (Finset.le_sup_iff (WithBot.bot_lt_coe _)).mp h2
    have hfS : f ∈ S := by
      by_contra hfS
      simp [SuppNeg, vec, hfS] at hj
    have hfsell : ¬ G.seller f = i := by
      intro h'
      simp [SuppNeg, vec, hfS, sign_eq_one h'] at hj
    have hef : e ≠ f := by rintro rfl; exact hfsell hsell
    have hfe : f ≠ e := fun h => hef h.symm
    have e3 : (fun w => vec G i S w - CharVec ⟨e, hed⟩ w + CharVec ⟨f, hf⟩ w)
        = vec G i (S \ {e, f}) := by
      funext ⟨v, hv⟩
      simp only [vec, CharVec, Subtype.mk.injEq, mem_sdiff, mem_insert, mem_singleton]
      by_cases hve : v = e
      · subst hve; simp [he, hef, sign_eq_one hsell]
      · by_cases hvf : v = f
        · subst hvf; simp [hfS, hve, sign_eq_neg_one hfsell]
        · simp [hve, hvf]
    have e4 : (fun w => vec G i ∅ w + CharVec ⟨e, hed⟩ w - CharVec ⟨f, hf⟩ w)
        = vec G i {e, f} := by
      funext ⟨v, hv⟩
      simp only [vec, CharVec, Subtype.mk.injEq, mem_insert, mem_singleton, notMem_empty]
      by_cases hve : v = e
      · subst hve; simp [hef, sign_eq_one hsell]
      · by_cases hvf : v = f
        · subst hvf; simp [hve, sign_eq_neg_one hfsell]
        · simp [hve, hvf]
    have hsub : ({e, f} : Finset E) ⊆ G.delta i := by
      intro v hv
      simp only [mem_insert, mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact hed
      · exact hf
    rw [e3, e4, vec_wSigned G i _ (sdiff_subset.trans hS), vec_wSigned G i _ hsub,
      ← WithBot.coe_add] at hle
    exact ⟨f, hfS, hfsell, by exact_mod_cast hle⟩

/-- Per-agent exchange against the empty set, for a bought trade `e`. -/
theorem exc_bought (G : Economy N E) (hG : G.Standing) (i : N) (S : Finset E)
    (hS : S ⊆ G.delta i) (e : E) (he : e ∈ S) (hsell : ¬ G.seller e = i) :
    G.w i S + G.w i ∅ ≤ G.w i (S.erase e) + G.w i {e} ∨
      ∃ f ∈ S, G.seller f = i ∧
        G.w i S + G.w i ∅ ≤ G.w i (S \ {e, f}) + G.w i {e, f} := by
  have hed : e ∈ G.delta i := hS he
  obtain ⟨-, hexc⟩ := hG.2 i
  have hpos : (⟨e, hed⟩ : {e // e ∈ G.delta i}) ∈ SuppPos (vec G i ∅) (vec G i S) := by
    simp [SuppPos, vec, he, sign_eq_neg_one hsell]
  have h := hexc _ (vec_mem_dom G i ∅ (empty_subset _)) _ (vec_mem_dom G i S hS) _ hpos
  have e1 : (fun w => vec G i ∅ w - CharVec ⟨e, hed⟩ w) = vec G i {e} := by
    funext ⟨v, hv⟩
    simp only [vec, CharVec, Subtype.mk.injEq, mem_singleton, notMem_empty]
    by_cases hve : v = e
    · subst hve; simp [sign_eq_neg_one hsell]
    · simp [hve]
  have e2 : (fun w => vec G i S w + CharVec ⟨e, hed⟩ w) = vec G i (S.erase e) := by
    funext ⟨v, hv⟩
    simp only [vec, CharVec, Subtype.mk.injEq, mem_erase]
    by_cases hve : v = e
    · subst hve; simp [he, sign_eq_neg_one hsell]
    · simp [hve]
  rw [e1, e2, vec_wSigned G i S hS, vec_wSigned G i ∅ (empty_subset _),
    vec_wSigned G i _ ((erase_subset _ _).trans hS),
    vec_wSigned G i {e} (singleton_subset_iff.mpr hed), ← WithBot.coe_add,
    ← WithBot.coe_add] at h
  rcases le_max_iff.mp h with h1 | h2
  · left
    have h1' : G.w i ∅ + G.w i S ≤ G.w i {e} + G.w i (S.erase e) := by exact_mod_cast h1
    linarith
  · right
    obtain ⟨⟨f, hf⟩, hj, hle⟩ := (Finset.le_sup_iff (WithBot.bot_lt_coe _)).mp h2
    have hfS : f ∈ S := by
      by_contra hfS
      simp [SuppNeg, vec, hfS] at hj
    have hfsell : G.seller f = i := by
      by_contra h'
      simp [SuppNeg, vec, hfS, sign_eq_neg_one h'] at hj
    have hef : e ≠ f := by rintro rfl; exact hsell hfsell
    have hfe : f ≠ e := fun h => hef h.symm
    have e3 : (fun w => vec G i ∅ w - CharVec ⟨e, hed⟩ w + CharVec ⟨f, hf⟩ w)
        = vec G i {e, f} := by
      funext ⟨v, hv⟩
      simp only [vec, CharVec, Subtype.mk.injEq, mem_insert, mem_singleton, notMem_empty]
      by_cases hve : v = e
      · subst hve; simp [hef, sign_eq_neg_one hsell]
      · by_cases hvf : v = f
        · subst hvf; simp [hve, sign_eq_one hfsell]
        · simp [hve, hvf]
    have e4 : (fun w => vec G i S w + CharVec ⟨e, hed⟩ w - CharVec ⟨f, hf⟩ w)
        = vec G i (S \ {e, f}) := by
      funext ⟨v, hv⟩
      simp only [vec, CharVec, Subtype.mk.injEq, mem_sdiff, mem_insert, mem_singleton]
      by_cases hve : v = e
      · subst hve; simp [he, hef, sign_eq_neg_one hsell]
      · by_cases hvf : v = f
        · subst hvf; simp [hfS, hve, sign_eq_one hfsell]
        · simp [hve, hvf]
    have hsub : ({e, f} : Finset E) ⊆ G.delta i := by
      intro v hv
      simp only [mem_insert, mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact hed
      · exact hf
    rw [e3, e4, vec_wSigned G i _ hsub, vec_wSigned G i _ (sdiff_subset.trans hS),
      ← WithBot.coe_add] at hle
    have hle' : G.w i ∅ + G.w i S ≤ G.w i {e, f} + G.w i (S \ {e, f}) := by
      exact_mod_cast hle
    exact ⟨f, hfS, hfsell, by linarith⟩

/-! ## Part A: the penalised economy is still Standing. -/

/-- Penalise every trade outside `T` by `M` at each of its two ends. -/
def pen (G : Economy N E) (T : Finset E) (M : ℝ) : Economy N E where
  seller := G.seller
  buyer := G.buyer
  w i A := G.w i A - M * ((A \ T).card : ℝ)

/-- A linear functional on signed vectors. -/
def linf {K : Type*} [Fintype K] (a : K → ℝ) (z : K → ℤ) : ℝ := ∑ k, a k * (z k : ℝ)

theorem sup_add_const {K : Type*} (s : Finset K) (f : K → WithBot ℝ) (c : ℝ) :
    s.sup (fun j => f j + (c : WithBot ℝ)) = s.sup f + (c : WithBot ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sup_insert, Finset.sup_insert, ih]
    exact max_add_add_right _ _ _

theorem mnat_add_linear {K : Type*} [Fintype K] [DecidableEq K] (U : (K → ℤ) → WithBot ℝ)
    (a : K → ℝ) (hU : MNaturalConcave U) :
    MNaturalConcave (fun x => U x + (linf a x : WithBot ℝ)) := by
  obtain ⟨⟨x0, hx0⟩, hexc⟩ := hU
  have hdom : ∀ x, U x + (linf a x : WithBot ℝ) ≠ ⊥ ↔ U x ≠ ⊥ := by
    intro x
    simp [WithBot.add_eq_bot]
  refine ⟨⟨x0, (hdom x0).2 hx0⟩, ?_⟩
  intro x hx y hy i hi
  have hx' : x ∈ UDom U := (hdom x).1 hx
  have hy' : y ∈ UDom U := (hdom y).1 hy
  have h := hexc x hx' y hy' i hi
  have key : ∀ u v : K → ℤ, (∀ k, u k + v k = x k + y k) →
      (U u + (linf a u : WithBot ℝ)) + (U v + (linf a v : WithBot ℝ)) =
        (U u + U v) + ((linf a x + linf a y : ℝ) : WithBot ℝ) := by
    intro u v huv
    have hl : linf a u + linf a v = linf a x + linf a y := by
      simp only [linf, ← Finset.sum_add_distrib, ← mul_add]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      have := huv k
      congr 1
      exact_mod_cast this
    rw [← hl, WithBot.coe_add]
    abel
  have e2 : (SuppNeg x y).sup (fun j =>
      (U (fun w => x w - CharVec i w + CharVec j w) +
          (linf a (fun w => x w - CharVec i w + CharVec j w) : WithBot ℝ)) +
        (U (fun w => y w + CharVec i w - CharVec j w) +
          (linf a (fun w => y w + CharVec i w - CharVec j w) : WithBot ℝ))) =
      (SuppNeg x y).sup (fun j => U (fun w => x w - CharVec i w + CharVec j w) +
          U (fun w => y w + CharVec i w - CharVec j w)) +
        ((linf a x + linf a y : ℝ) : WithBot ℝ) := by
    rw [← sup_add_const]
    exact Finset.sup_congr rfl (fun j _ => key _ _ (fun k => by ring))
  beta_reduce
  rw [key x y (fun k => rfl), key (fun w => x w - CharVec i w) (fun w => y w + CharVec i w)
    (fun k => by ring), e2, max_add_add_right]
  gcongr

/-- Coefficients of the penalty as a linear functional at agent `i`. -/
def penc (G : Economy N E) (i : N) (T : Finset E) (M : ℝ) : {e // e ∈ G.delta i} → ℝ :=
  fun e => if e.1 ∈ T then 0 else -M * (G.sign i e.1 : ℝ)

theorem wSigned_pen_apply (G : Economy N E) (T : Finset E) (M : ℝ) (i : N)
    (x : {e // e ∈ G.delta i} → ℤ) :
    (pen G T M).wSigned i x = G.wSigned i x + (linf (penc G i T M) x : WithBot ℝ) := by
  show (if ∀ e : {e // e ∈ G.delta i}, x e = 0 ∨ x e = G.sign i e.1 then
      ((G.w i ((univ.filter (fun e => x e ≠ 0)).map (Function.Embedding.subtype _)) -
        M * ((((univ.filter (fun e => x e ≠ 0)).map (Function.Embedding.subtype _)) \ T).card : ℝ)
          : ℝ) : WithBot ℝ) else ⊥) = G.wSigned i x + (linf (penc G i T M) x : WithBot ℝ)
  unfold Economy.wSigned
  split_ifs with h
  · rw [← WithBot.coe_add]
    congr 1
    have hset : ((univ.filter (fun e => x e ≠ 0)).map (Function.Embedding.subtype _)) \ T =
        (univ.filter (fun e => x e ≠ 0 ∧ e.1 ∉ T)).map
          (Function.Embedding.subtype _) := by
      ext y
      simp only [mem_sdiff, mem_map, mem_filter, mem_univ, true_and,
        Function.Embedding.coe_subtype]
      constructor
      · rintro ⟨⟨a, ha, rfl⟩, hT⟩
        exact ⟨a, ⟨ha, hT⟩, rfl⟩
      · rintro ⟨a, ⟨ha, hT⟩, rfl⟩
        exact ⟨⟨a, ha, rfl⟩, hT⟩
    rw [hset, card_map, card_filter]
    push_cast
    rw [sub_eq_add_neg, neg_mul_eq_neg_mul, Finset.mul_sum]
    congr 1
    unfold linf penc
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rcases h e with h0 | hs
    · simp [h0]
    · have hne : x e ≠ 0 := by
        rw [hs]
        unfold Economy.sign
        split_ifs <;> norm_num
      by_cases hT : e.1 ∈ T
      · simp [hT]
      · simp only [hT, not_false_eq_true, and_true, hne, if_true, if_false, ne_eq]
        rw [hs]
        unfold Economy.sign
        split_ifs <;> push_cast <;> ring
  · simp

theorem wSigned_pen (G : Economy N E) (T : Finset E) (M : ℝ) (i : N) :
    (pen G T M).wSigned i = fun x => G.wSigned i x + (linf (penc G i T M) x : WithBot ℝ) := by
  funext x
  exact wSigned_pen_apply G T M i x

theorem Standing_pen (G : Economy N E) (hG : G.Standing) (T : Finset E) (M : ℝ) :
    (pen G T M).Standing := by
  refine ⟨hG.1, fun i => ?_⟩
  rw [wSigned_pen]
  exact mnat_add_linear _ _ (hG.2 i)

/-! ## Part B: prices supporting the empty outcome on a non-improving trade set. -/

/-- Net price received by agent `i` on trade `e`. -/
def cc (G : Economy N E) (i : N) (q : E → ℝ) (e : E) : ℝ :=
  (if G.seller e = i then q e else 0) - (if G.buyer e = i then q e else 0)

theorem utility_eq (G : Economy N E) (i : N) (Y : Finset E) (q : E → ℝ) :
    G.utility i Y q = G.w i Y + ∑ e ∈ Y, cc G i q e := by
  unfold Economy.utility cc
  have h1 : Y ∩ G.deltaOut i = Y.filter (fun e => G.seller e = i) := by
    ext e; simp [Economy.deltaOut]
  have h2 : Y ∩ G.deltaIn i = Y.filter (fun e => G.buyer e = i) := by
    ext e; simp [Economy.deltaIn]
  rw [h1, h2, Finset.sum_filter, Finset.sum_filter, Finset.sum_sub_distrib]
  ring

theorem cc_sum (G : Economy N E) (q : E → ℝ) (e : E) : ∑ i, cc G i q e = 0 := by
  simp [cc, Finset.sum_sub_distrib]

theorem cc_off (G : Economy N E) (i : N) (q : E → ℝ) (e : E) (he : e ∉ G.delta i) :
    cc G i q e = 0 := by
  unfold cc
  have h1 : ¬ G.seller e = i := fun h => he (by simp [Economy.delta, Economy.deltaOut, h])
  have h2 : ¬ G.buyer e = i := fun h => he (by simp [Economy.delta, Economy.deltaIn, h])
  simp [h1, h2]

theorem price_cancel (G : Economy N E) (q : E → ℝ) (A : Finset E) :
    ∑ i, ∑ e ∈ A ∩ G.delta i, cc G i q e = 0 := by
  have : ∀ i, ∑ e ∈ A ∩ G.delta i, cc G i q e = ∑ e ∈ A, cc G i q e := by
    intro i
    refine Finset.sum_subset Finset.inter_subset_left (fun e _ he => ?_)
    refine cc_off G i q e (fun hd => he ?_)
    simp_all
  simp only [this]
  rw [Finset.sum_comm]
  simp [cc_sum]

theorem welfare_util (G : Economy N E) (q : E → ℝ) (A : Finset E) :
    ∑ i, G.utility i (A ∩ G.delta i) q = G.welfare A := by
  simp only [utility_eq, Finset.sum_add_distrib, price_cancel, add_zero]
  rfl

theorem prices_of_nonimproving (G : Economy N E) (hG : G.Standing) (T : Finset E)
    (hT : ∀ A ⊆ T, G.welfare A ≤ G.welfare ∅)
    (h41 : ∀ G' : Economy N E, G'.Standing →
      ∃ (X : Finset E) (p : E → ℝ), G'.IsCompetitiveEquilibrium X p) :
    ∃ q : E → ℝ, ∀ i, ∀ Y ⊆ T ∩ G.delta i, G.utility i Y q ≤ G.w i ∅ := by
  set M : ℝ := ∑ A : Finset E, (|G.welfare A| + |G.welfare ∅|) with hM
  have hMA : ∀ A, G.welfare A - G.welfare ∅ ≤ M := fun A => by
    have h1 := Finset.single_le_sum (f := fun A : Finset E => |G.welfare A| + |G.welfare ∅|)
      (fun B _ => by positivity) (Finset.mem_univ A)
    have := le_abs_self (G.welfare A)
    have := neg_abs_le (G.welfare ∅)
    linarith
  have hM0 : 0 ≤ M := Finset.sum_nonneg (fun A _ => by positivity)
  obtain ⟨X, p, hX⟩ := h41 (pen G T M) (Standing_pen G hG T M)
  have hpw : ∀ i A, (pen G T M).w i A = G.w i A - M * ((A \ T).card : ℝ) := fun _ _ => rfl
  have hpd : ∀ i, (pen G T M).delta i = G.delta i := fun _ => rfl
  have hW : ∀ A, (pen G T M).welfare A ≤ G.welfare ∅ := by
    intro A
    have hexp : (pen G T M).welfare A =
        G.welfare A - M * ∑ i, (((A ∩ G.delta i) \ T).card : ℝ) := by
      unfold Economy.welfare
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      rfl
    rw [hexp]
    by_cases hA : A ⊆ T
    · have h0 : ∀ i, (((A ∩ G.delta i) \ T).card : ℝ) = 0 := by
        intro i
        have : (A ∩ G.delta i) \ T = ∅ :=
          Finset.sdiff_eq_empty_iff_subset.mpr (Finset.inter_subset_left.trans hA)
        simp [this]
      simp only [h0, Finset.sum_const_zero, mul_zero, sub_zero]
      exact hT A hA
    · obtain ⟨e, heA, heT⟩ := Finset.not_subset.mp hA
      have hmem : e ∈ (A ∩ G.delta (G.seller e)) \ T := by
        simp [Economy.delta, Economy.deltaOut, heA, heT]
      have h1 : (1:ℝ) ≤ (((A ∩ G.delta (G.seller e)) \ T).card : ℝ) := by
        exact_mod_cast Finset.card_pos.mpr ⟨e, hmem⟩
      have hge : (1:ℝ) ≤ ∑ i, (((A ∩ G.delta i) \ T).card : ℝ) :=
        h1.trans (Finset.single_le_sum (f := fun i => (((A ∩ G.delta i) \ T).card : ℝ))
          (fun _ _ => by positivity) (Finset.mem_univ _))
      have := hMA A
      nlinarith
  have hu0 : ∀ i, (pen G T M).utility i ∅ p = G.w i ∅ := by
    intro i
    simp [Economy.utility, hpw]
  have hle : ∀ i ∈ (univ : Finset N),
      (pen G T M).utility i ∅ p ≤ (pen G T M).utility i (X ∩ (pen G T M).delta i) p :=
    fun i _ => (hX i).2 ∅ (Finset.empty_subset _)
  have hsum : ∑ i, (pen G T M).utility i (X ∩ (pen G T M).delta i) p ≤
      ∑ i, (pen G T M).utility i ∅ p := by
    rw [welfare_util, Finset.sum_congr rfl (fun i _ => hu0 i)]
    exact hW X
  have heq := (Finset.sum_eq_sum_iff_of_le hle).mp (le_antisymm (Finset.sum_le_sum hle) hsum)
  refine ⟨p, fun i Y hY => ?_⟩
  have hYT : Y ⊆ T := hY.trans Finset.inter_subset_left
  have hYu : Y ⊆ univ ∩ (pen G T M).delta i := by
    intro e he
    simp only [mem_inter, mem_univ, true_and, hpd]
    exact (mem_inter.mp (hY he)).2
  have h1 := (hX i).2 Y hYu
  have h2 : (pen G T M).utility i Y p = G.utility i Y p := by
    simp [Economy.utility, hpw, Finset.sdiff_eq_empty_iff_subset.mpr hYT]
    rfl
  rw [← h2, ← hu0 i, heq i (Finset.mem_univ i)]
  exact h1


/-! ## Part C: per-agent decomposition of `S ∩ δ i` into parts. -/

/-- A part at agent `i`: a single trade, or a pair (bought `a`, sold `b`). -/
def PartShape (G : Economy N E) (i : N) (P : Finset E) : Prop :=
  (∃ e, P = {e}) ∨ (∃ a b, P = {a, b} ∧ G.buyer a = i ∧ G.seller b = i)

theorem PartShape.nonempty {G : Economy N E} {i : N} {P : Finset E} (h : PartShape G i P) :
    P.Nonempty := by
  rcases h with ⟨e, rfl⟩ | ⟨a, b, rfl, -, -⟩
  · exact singleton_nonempty e
  · exact insert_nonempty a {b}

/-- `F` is a partition of `A` into parts whose gains dominate the gain of `A`. -/
def Good (G : Economy N E) (i : N) (A : Finset E) (F : Finset (Finset E)) : Prop :=
  (∀ P ∈ F, P ⊆ A ∧ PartShape G i P) ∧ (∀ P ∈ F, ∀ Q ∈ F, ∀ e ∈ P, e ∈ Q → P = Q) ∧
    (∀ e ∈ A, ∃ P ∈ F, e ∈ P) ∧ G.w i A - G.w i ∅ ≤ ∑ P ∈ F, (G.w i P - G.w i ∅)

theorem good_glue (G : Economy N E) (i : N) (A P : Finset E) (F : Finset (Finset E))
    (hPA : P ⊆ A) (hsh : PartShape G i P)
    (hw : G.w i A + G.w i ∅ ≤ G.w i (A \ P) + G.w i P) (hF : Good G i (A \ P) F) :
    Good G i A (insert P F) := by
  unfold Good at hF ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hF
  obtain ⟨x, hx⟩ := hsh.nonempty
  have hPF : P ∉ F := by
    intro hP
    have := (h1 P hP).1 hx
    simp [hx] at this
  have hdisj : ∀ Q ∈ F, ∀ e ∈ P, e ∉ Q := by
    intro Q hQ e he heQ
    have := (h1 Q hQ).1 heQ
    simp [he] at this
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Q hQ
    rcases mem_insert.mp hQ with hQ | hQ
    · rw [hQ]; exact ⟨hPA, hsh⟩
    · exact ⟨(h1 Q hQ).1.trans sdiff_subset, (h1 Q hQ).2⟩
  · intro Q hQ R hR e heQ heR
    rcases mem_insert.mp hQ with hQ' | hQ' <;> rcases mem_insert.mp hR with hR' | hR'
    · rw [hQ', hR']
    · rw [hQ'] at heQ; exact absurd heR (hdisj R hR' e heQ)
    · rw [hR'] at heR; exact absurd heQ (hdisj Q hQ' e heR)
    · exact h2 Q hQ' R hR' e heQ heR
  · intro e he
    by_cases heP : e ∈ P
    · exact ⟨P, mem_insert_self _ _, heP⟩
    · obtain ⟨Q, hQ, heQ⟩ := h3 e (mem_sdiff.mpr ⟨he, heP⟩)
      exact ⟨Q, mem_insert_of_mem hQ, heQ⟩
  · rw [sum_insert hPF]
    linarith

theorem decomp (G : Economy N E) (hG : G.Standing) (i : N) :
    ∀ (n : ℕ) (A : Finset E), A.card = n → A ⊆ G.delta i → ∃ F, Good G i A F := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A hAn hA
  rcases A.eq_empty_or_nonempty with rfl | ⟨e, he⟩
  · exact ⟨∅, by unfold Good; simp⟩
  have hed : e ∈ G.delta i := hA he
  have hrec : ∀ P ⊆ A, PartShape G i P → G.w i A + G.w i ∅ ≤ G.w i (A \ P) + G.w i P →
      ∃ F, Good G i A F := by
    intro P hPA hsh hw
    obtain ⟨x, hx⟩ := hsh.nonempty
    have hlt : (A \ P).card < n := by
      rw [← hAn]
      exact card_lt_card (sdiff_ssubset hPA ⟨x, hx⟩)
    obtain ⟨F, hF⟩ := ih _ hlt (A \ P) rfl (sdiff_subset.trans hA)
    exact ⟨insert P F, good_glue G i A P F hPA hsh hw hF⟩
  have hsing : G.w i A + G.w i ∅ ≤ G.w i (A.erase e) + G.w i {e} → ∃ F, Good G i A F := by
    intro hw
    refine hrec {e} (singleton_subset_iff.mpr he) (Or.inl ⟨e, rfl⟩) ?_
    rwa [← erase_eq]
  by_cases hs : G.seller e = i
  · rcases exc_sold G hG i A hA e he hs with hw | ⟨f, hf, hfs, hw⟩
    · exact hsing hw
    · have hfb : G.buyer f = i := by
        have := hA hf
        simpa [Economy.delta, Economy.deltaOut, Economy.deltaIn, hfs] using this
      refine hrec {e, f} ?_ (Or.inr ⟨f, e, pair_comm e f, hfb, hs⟩) hw
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
  · rcases exc_bought G hG i A hA e he hs with hw | ⟨f, hf, hfs, hw⟩
    · exact hsing hw
    · have heb : G.buyer e = i := by
        simpa [Economy.delta, Economy.deltaOut, Economy.deltaIn, hs] using hed
      refine hrec {e, f} ?_ (Or.inr ⟨e, f, rfl, heb, hfs⟩) hw
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption

/-! ## Part D: on a closed non-improving region the part gains sum to at most zero. -/

theorem region (G : Economy N E) (F : N → Finset (Finset E)) (S T : Finset E) (q : E → ℝ)
    (hpart : ∀ i, ∀ P ∈ F i, P ⊆ S ∩ G.delta i)
    (hdisj : ∀ i, ∀ P ∈ F i, ∀ Q ∈ F i, ∀ e ∈ P, e ∈ Q → P = Q)
    (hcov : ∀ i, ∀ e ∈ S ∩ G.delta i, ∃ P ∈ F i, e ∈ P) (hTS : T ⊆ S)
    (hcl : ∀ i, ∀ P ∈ F i, P ⊆ T ∨ Disjoint P T)
    (hq : ∀ i, ∀ Y ⊆ T ∩ G.delta i, G.utility i Y q ≤ G.w i ∅) :
    ∑ i, ∑ P ∈ (F i).filter (· ⊆ T), (G.w i P - G.w i ∅) ≤ 0 := by
  have hi : ∀ i, ∑ P ∈ (F i).filter (· ⊆ T), (G.w i P - G.w i ∅) ≤
      -∑ e ∈ T ∩ G.delta i, cc G i q e := by
    intro i
    have hbu : ((F i).filter (· ⊆ T)).biUnion id = T ∩ G.delta i := by
      ext e
      simp only [mem_biUnion, mem_filter, id, mem_inter]
      constructor
      · rintro ⟨P, ⟨hP, hPT⟩, heP⟩
        exact ⟨hPT heP, (mem_inter.mp (hpart i P hP heP)).2⟩
      · rintro ⟨heT, hed⟩
        obtain ⟨P, hP, heP⟩ := hcov i e (mem_inter.mpr ⟨hTS heT, hed⟩)
        refine ⟨P, ⟨hP, ?_⟩, heP⟩
        rcases hcl i P hP with h | h
        · exact h
        · exact absurd heT (disjoint_left.mp h heP)
    have hpd : (((F i).filter (· ⊆ T) : Finset (Finset E)) : Set (Finset E)).PairwiseDisjoint
        id := by
      intro P hP Q hQ hne
      have hP' := mem_filter.mp (mem_coe.mp hP)
      have hQ' := mem_filter.mp (mem_coe.mp hQ)
      exact disjoint_left.mpr (fun e heP heQ => hne (hdisj i P hP'.1 Q hQ'.1 e heP heQ))
    rw [← hbu, sum_biUnion hpd, ← sum_neg_distrib]
    refine sum_le_sum (fun P hP => ?_)
    obtain ⟨hPF, hPT⟩ := mem_filter.mp hP
    have hsub : P ⊆ T ∩ G.delta i := fun e he =>
      mem_inter.mpr ⟨hPT he, (mem_inter.mp (hpart i P hPF he)).2⟩
    have := hq i P hsub
    rw [utility_eq] at this
    simp only [id]
    linarith
  calc _ ≤ ∑ i, -∑ e ∈ T ∩ G.delta i, cc G i q e := sum_le_sum (fun i _ => hi i)
    _ = 0 := by rw [sum_neg_distrib, price_cancel, neg_zero]

/-! ## Part E: a minimal improving set is a chain. -/

theorem chain_succ {α : Type*} {R : α → α → Prop} :
    ∀ (l : List α), l.IsChain R → ∀ x ∈ l, (∀ y ∈ l, ¬ R x y) → l.getLast? = some x
  | [], _, x, hx, _ => by simp at hx
  | [a], _, x, hx, _ => by simp at hx; simp [hx]
  | a :: b :: t, hc, x, hx, hn => by
    have hab : R a b := (List.isChain_cons.mp hc).1 b (by simp)
    have hc2 : (b :: t).IsChain R := (List.isChain_cons.mp hc).2
    rcases List.mem_cons.mp hx with rfl | hx
    · exact absurd hab (hn b (by simp))
    · have := chain_succ (b :: t) hc2 x hx (fun y hy => hn y (List.mem_cons_of_mem _ hy))
      rw [List.getLast?_cons_cons]
      exact this

theorem chain_pred {α : Type*} {R : α → α → Prop} :
    ∀ (l : List α), l.IsChain R → ∀ x ∈ l, (∀ y ∈ l, ¬ R y x) → l.head? = some x
  | [], _, x, hx, _ => by simp at hx
  | [a], _, x, hx, _ => by simp at hx; simp [hx]
  | a :: b :: t, hc, x, hx, hn => by
    have hab : R a b := (List.isChain_cons.mp hc).1 b (by simp)
    have hc2 : (b :: t).IsChain R := (List.isChain_cons.mp hc).2
    rcases List.mem_cons.mp hx with rfl | hx
    · rfl
    · have := chain_pred (b :: t) hc2 x hx (fun y hy => hn y (List.mem_cons_of_mem _ hy))
      simp only [List.head?_cons, Option.some.injEq] at this
      subst this
      exact absurd hab (hn a (by simp))

/-- `b` follows `a`: the agent buying `a` sells `b`, and `{a, b}` is one of its parts. -/
def Lk (G : Economy N E) (F : N → Finset (Finset E)) (a b : E) : Prop :=
  G.buyer a = G.seller b ∧ ({a, b} : Finset E) ∈ F (G.buyer a)

/-- A linked list of distinct trades inside `S`. -/
def Vl (G : Economy N E) (F : N → Finset (Finset E)) (S : Finset E) (l : List E) : Prop :=
  l ≠ [] ∧ l.Nodup ∧ (∀ x ∈ l, x ∈ S) ∧ l.IsChain (Lk G F)

theorem main (G : Economy N E) (hG : G.Standing) (h : ¬ G.IsEfficient ∅)
    (h41 : ∀ G' : Economy N E, G'.Standing →
      ∃ (X : Finset E) (p : E → ℝ), G'.IsCompetitiveEquilibrium X p) :
    ∃ Z : Finset E, G.IsChain Z ∧ G.welfare ∅ < G.welfare Z := by
  classical
  have hex : ∃ n, ∃ A : Finset E, A.card = n ∧ G.welfare ∅ < G.welfare A := by
    unfold Economy.IsEfficient at h
    push Not at h
    obtain ⟨A, hA⟩ := h
    exact ⟨_, A, rfl, hA⟩
  obtain ⟨S, hScard, hSimp⟩ := Nat.find_spec hex
  have hmin : ∀ A : Finset E, A.card < S.card → G.welfare A ≤ G.welfare ∅ := by
    intro A hA
    by_contra hc
    push Not at hc
    exact Nat.find_min hex (hScard ▸ hA) ⟨A, rfl, hc⟩
  have hF : ∀ i, ∃ F, Good G i (S ∩ G.delta i) F :=
    fun i => decomp G hG i _ _ rfl inter_subset_right
  choose F hFg using hF
  have hpart : ∀ i, ∀ P ∈ F i, P ⊆ S ∩ G.delta i := fun i P hP => by
    obtain ⟨h1, -⟩ := hFg i; exact (h1 P hP).1
  have hshape : ∀ i, ∀ P ∈ F i, PartShape G i P := fun i P hP => by
    obtain ⟨h1, -⟩ := hFg i; exact (h1 P hP).2
  have hdisj : ∀ i, ∀ P ∈ F i, ∀ Q ∈ F i, ∀ e ∈ P, e ∈ Q → P = Q := fun i => by
    obtain ⟨-, h2, -⟩ := hFg i; exact h2
  have hcov : ∀ i, ∀ e ∈ S ∩ G.delta i, ∃ P ∈ F i, e ∈ P := fun i => by
    obtain ⟨-, -, h3, -⟩ := hFg i; exact h3
  have hbd : ∀ i, G.w i (S ∩ G.delta i) - G.w i ∅ ≤ ∑ P ∈ F i, (G.w i P - G.w i ∅) :=
    fun i => by obtain ⟨-, -, -, h4⟩ := hFg i; exact h4
  have hprice : ∀ T, T ⊆ S → T ≠ S →
      ∃ q : E → ℝ, ∀ i, ∀ Y ⊆ T ∩ G.delta i, G.utility i Y q ≤ G.w i ∅ := by
    intro T hTS hne
    refine prices_of_nonimproving G hG T (fun A hA => hmin A ?_) h41
    exact lt_of_le_of_lt (card_le_card hA) (card_lt_card (ssubset_of_subset_of_ne hTS hne))
  have hW : ∀ Z ⊆ S, Z ≠ S → Z.Nonempty → (∀ i, ∀ P ∈ F i, P ⊆ Z ∨ Disjoint P Z) →
      False := by
    intro Z hZS hne hZn hcl
    obtain ⟨z, hz⟩ := hZn
    have hne2 : S \ Z ≠ S := by
      intro heq
      have h1 : z ∈ S \ Z := by rw [heq]; exact hZS hz
      exact (mem_sdiff.mp h1).2 hz
    have hcl2 : ∀ i, ∀ P ∈ F i, P ⊆ S \ Z ∨ Disjoint P (S \ Z) := by
      intro i P hP
      rcases hcl i P hP with h1 | h1
      · exact Or.inr (disjoint_of_subset_left h1 disjoint_sdiff)
      · left
        intro e he
        exact mem_sdiff.mpr ⟨(mem_inter.mp (hpart i P hP he)).1, disjoint_left.mp h1 he⟩
    obtain ⟨q1, hq1⟩ := hprice Z hZS hne
    obtain ⟨q2, hq2⟩ := hprice (S \ Z) sdiff_subset hne2
    have r1 := region G F S Z q1 hpart hdisj hcov hZS hcl hq1
    have r2 := region G F S (S \ Z) q2 hpart hdisj hcov sdiff_subset hcl2 hq2
    have hsplit : ∀ i, ∑ P ∈ F i, (G.w i P - G.w i ∅) =
        ∑ P ∈ (F i).filter (· ⊆ Z), (G.w i P - G.w i ∅) +
          ∑ P ∈ (F i).filter (· ⊆ S \ Z), (G.w i P - G.w i ∅) := by
      intro i
      rw [← sum_filter_add_sum_filter_not (F i) (fun P => P ⊆ Z)]
      congr 1
      refine sum_congr (filter_congr (fun P hP => ?_)) (fun _ _ => rfl)
      obtain ⟨x, hx⟩ := (hshape i P hP).nonempty
      constructor
      · intro hPZ
        rcases hcl i P hP with h2 | h2
        · exact absurd h2 hPZ
        · intro e he
          exact mem_sdiff.mpr ⟨(mem_inter.mp (hpart i P hP he)).1, disjoint_left.mp h2 he⟩
      · intro h1 h2
        exact (mem_sdiff.mp (h1 hx)).2 (h2 hx)
    have e0 : G.welfare ∅ = ∑ i, G.w i ∅ := by simp [Economy.welfare]
    have hs := sum_le_sum (fun i (_ : i ∈ (univ : Finset N)) => hbd i)
    rw [sum_congr rfl (fun i _ => hsplit i), sum_add_distrib, sum_sub_distrib] at hs
    have hS : G.welfare S = ∑ i, G.w i (S ∩ G.delta i) := rfl
    linarith
  -- a longest linked list
  have hSne : S.Nonempty := by
    rcases S.eq_empty_or_nonempty with h0 | h0
    · rw [h0] at hSimp; exact absurd hSimp (lt_irrefl _)
    · exact h0
  obtain ⟨e0, he0⟩ := hSne
  have hneq : ∀ a, G.seller a ≠ G.buyer a := hG.1
  have hVlen : ∀ l, Vl G F S l → l.length ≤ S.card := by
    intro l hl
    obtain ⟨-, hn, hS', -⟩ := hl
    rw [← List.toFinset_card_of_nodup hn]
    exact card_le_card (fun x hx => hS' x (List.mem_toFinset.mp hx))
  have hQ1 : ∃ l, Vl G F S l ∧ l.length = 1 :=
    ⟨[e0], by unfold Vl; exact ⟨by simp, List.nodup_singleton _, by simpa using he0,
      List.isChain_singleton _⟩, rfl⟩
  have h1S : 1 ≤ S.card := card_pos.mpr ⟨e0, he0⟩
  obtain ⟨l, hl, hlen⟩ :=
    Nat.findGreatest_spec (P := fun n => ∃ l, Vl G F S l ∧ l.length = n) h1S hQ1
  have hmax : ∀ l', Vl G F S l' → l'.length ≤ l.length := by
    intro l' hl'
    rw [hlen]
    exact Nat.le_findGreatest (hVlen l' hl') ⟨l', hl', rfl⟩
  obtain ⟨hl0, hl1, hl2, hl3⟩ := hl
  have hZS : l.toFinset ⊆ S := fun x hx => hl2 x (List.mem_toFinset.mp hx)
  have hcl : ∀ i, ∀ P ∈ F i, P ⊆ l.toFinset ∨ Disjoint P l.toFinset := by
    intro i P hP
    rcases hshape i P hP with ⟨e, rfl⟩ | ⟨a, b, rfl, ha, hb⟩
    · by_cases he : e ∈ l.toFinset
      · exact Or.inl (singleton_subset_iff.mpr he)
      · exact Or.inr (disjoint_singleton_left.mpr he)
    · have haS : a ∈ S := (mem_inter.mp (hpart i _ hP (by simp))).1
      have hbS : b ∈ S := (mem_inter.mp (hpart i _ hP (by simp))).1
      have hLab : Lk G F a b := by
        refine ⟨ha.trans hb.symm, ?_⟩
        rw [ha]; exact hP
      by_cases haZ : a ∈ l.toFinset <;> by_cases hbZ : b ∈ l.toFinset
      · left
        intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      · exfalso
        by_cases hs : ∃ y ∈ l, Lk G F a y
        · obtain ⟨y, hy, hy1, hy2⟩ := hs
          rw [ha] at hy2
          have heq := hdisj i _ hy2 _ hP a (by simp) (by simp)
          have hyab : y ∈ ({a, b} : Finset E) := by rw [← heq]; simp
          simp only [mem_insert, mem_singleton] at hyab
          rcases hyab with rfl | rfl
          · exact hneq _ hy1.symm
          · exact hbZ (List.mem_toFinset.mpr hy)
        · push Not at hs
          have hlast := chain_succ l hl3 a (List.mem_toFinset.mp haZ) hs
          have hV : Vl G F S (l ++ [b]) := by
            refine ⟨by simp, ?_, ?_, ?_⟩
            · rw [List.nodup_append_comm]
              exact List.nodup_cons.mpr ⟨fun h => hbZ (List.mem_toFinset.mpr h), hl1⟩
            · intro x hx
              rcases List.mem_append.mp hx with hx | hx
              · exact hl2 x hx
              · rw [List.mem_singleton.mp hx]; exact hbS
            · rw [List.isChain_append]
              refine ⟨hl3, List.isChain_singleton _, ?_⟩
              intro x hx y hy
              rw [hlast] at hx
              simp only [Option.mem_def, Option.some.injEq, List.head?_cons] at hx hy
              subst hx; subst hy
              exact hLab
          have := hmax _ hV
          simp at this
      · exfalso
        by_cases hs : ∃ y ∈ l, Lk G F y b
        · obtain ⟨y, hy, hy1, hy2⟩ := hs
          have hyi : G.buyer y = i := hy1.trans hb
          rw [hyi] at hy2
          have heq := hdisj i _ hy2 _ hP b (by simp) (by simp)
          have hyab : y ∈ ({a, b} : Finset E) := by rw [← heq]; simp
          simp only [mem_insert, mem_singleton] at hyab
          rcases hyab with rfl | rfl
          · exact haZ (List.mem_toFinset.mpr hy)
          · exact hneq _ hy1.symm
        · push Not at hs
          have hhead := chain_pred l hl3 b (List.mem_toFinset.mp hbZ) hs
          have hV : Vl G F S (a :: l) := by
            refine ⟨by simp, List.nodup_cons.mpr ⟨fun h => haZ (List.mem_toFinset.mpr h), hl1⟩,
              ?_, ?_⟩
            · intro x hx
              rcases List.mem_cons.mp hx with hx | hx
              · rw [hx]; exact haS
              · exact hl2 x hx
            · rw [List.isChain_cons]
              refine ⟨?_, hl3⟩
              intro y hy
              rw [hhead] at hy
              simp only [Option.mem_def, Option.some.injEq] at hy
              subst hy
              exact hLab
          have := hmax _ hV
          simp at this
      · right
        rw [disjoint_left]
        intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
  have hZeq : l.toFinset = S := by
    by_contra hne
    exact hW _ hZS hne ((List.toFinset_nonempty_iff l).mpr hl0) hcl
  exact ⟨S, ⟨l, hl0, hl1, hZeq, hl3.imp (fun a b h => h.1)⟩, hSimp⟩

end P8e319fe0

open TradingNetFlow.ChainStable Finset in
theorem solution {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E] [DecidableEq E]
    (G : Economy N E) (hG : G.Standing) (h : ¬ G.IsEfficient ∅) :
    ∃ Z : Finset E, G.IsChain Z ∧ G.welfare ∅ < G.welfare Z := by
  exact P8e319fe0.main G hG h (fun G' hG' => theorem_4_1 G' hG')
