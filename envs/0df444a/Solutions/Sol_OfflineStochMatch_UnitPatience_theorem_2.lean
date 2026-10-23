-- Prove2me | solution 1 for OfflineStochMatch.UnitPatience.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T19:09:04.07385+00:00
-- url     : https://prove2.me/submissions/1fbe504f-e5fc-452c-964b-35f2458ee2e4

import Mathlib
import Definitions.Def_OfflineStochMatch_UnitPatience_Setting

set_option autoImplicit false

namespace OSM41

open Finset OfflineStochMatch.UnitPatience OfflineStochMatch.InfinitePatience

/-- Value of the first hit edge of a list (0 if none). -/
def Fv {E : Type} (w : E → ℝ) (h : E → Bool) (L : List E) : ℝ :=
  match L.find? h with
  | some e => w e
  | none => 0

lemma find_filter {E : Type} (L : List E) (p q : E → Bool) :
    (L.filter p).find? q = L.find? (fun a => p a && q a) := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    by_cases hp : p a = true <;> by_cases hq : q a = true <;>
      simp [List.filter_cons, List.find?_cons, hp, hq, ih]

lemma Fv_append_single {E : Type} (w : E → ℝ) (h : E → Bool) (L : List E) (a : E)
    (hw : ∀ x ∈ L, w a ≤ w x) :
    Fv w h (L ++ [a]) = w a * (if ∃ x ∈ L ++ [a], h x = true then 1 else 0)
      + Fv (fun x => w x - w a) h L := by
  unfold Fv
  rw [List.find?_append]
  cases hL : L.find? h with
  | some x =>
    have hx : x ∈ L := List.mem_of_find?_eq_some hL
    have hhx : h x = true := List.find?_some hL
    have : ∃ y ∈ L ++ [a], h y = true := ⟨x, List.mem_append_left _ hx, hhx⟩
    rw [if_pos this]
    simp only [Option.some_or]
    ring
  | none =>
    have hno : ∀ y ∈ L, ¬ h y = true := by
      intro y hy; simpa using List.find?_eq_none.1 hL y hy
    by_cases ha : h a = true
    · have : ∃ y ∈ L ++ [a], h y = true := ⟨a, by simp, ha⟩
      rw [if_pos this]
      simp [ha]
    · have : ¬ ∃ y ∈ L ++ [a], h y = true := by
        rintro ⟨y, hy, hhy⟩
        rcases List.mem_append.1 hy with hy | hy
        · exact hno y hy hhy
        · simp at hy; subst hy; exact ha hhy
      rw [if_neg this]
      simp [ha]

lemma sum_map_shift {E : Type} (w z : E → ℝ) (k : ℝ) (L : List E) :
    (L.map (fun e => (w e - k) * z e)).sum
      = (L.map (fun e => w e * z e)).sum - k * (L.map z).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, ih]; ring

lemma abstract_bound {E ι : Type} [Fintype ι] (π : ι → ℝ)
    (hit : ι → E → Bool) (z : E → ℝ) (c : ℝ) (L : List E) :
    ∀ (w : E → ℝ), L.Nodup → (∀ x ∈ L, 0 ≤ w x) → L.Pairwise (fun e f => w f ≤ w e) →
    (∀ S : List E, S.Nodup → (∀ x ∈ S, x ∈ L) →
      c * (S.map z).sum ≤ ∑ i, π i * (if ∃ x ∈ S, hit i x = true then 1 else 0)) →
    c * (L.map (fun e => w e * z e)).sum ≤ ∑ i, π i * Fv w (hit i) L := by
  induction L using List.reverseRecOn with
  | nil => intro w _ _ _ _; simp [Fv]
  | append_singleton L a ih =>
    intro w hnd hw hpw hq
    obtain ⟨hpL, -, hpLa⟩ := List.pairwise_append.1 hpw
    have hwa : ∀ x ∈ L, w a ≤ w x := fun x hx => hpLa x hx a (by simp)
    have hndL : L.Nodup := hnd.sublist (List.sublist_append_left L [a])
    have h1 := ih (fun x => w x - w a) hndL (fun x hx => sub_nonneg.2 (hwa x hx))
      (hpL.imp (fun h => sub_le_sub_right h _))
      (fun S hS hSL => hq S hS (fun x hx => List.mem_append_left _ (hSL x hx)))
    beta_reduce at h1
    have h2 := hq (L ++ [a]) hnd (fun x hx => hx)
    have hsum : ∑ i, π i * Fv w (hit i) (L ++ [a]) =
        w a * ∑ i, π i * (if ∃ x ∈ L ++ [a], hit i x = true then 1 else 0)
          + ∑ i, π i * Fv (fun x => w x - w a) (hit i) L := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Fv_append_single w (hit i) L a hwa]; ring
    rw [hsum]
    have hwa0 : 0 ≤ w a := hw a (by simp)
    have key : c * ((L ++ [a]).map (fun e => w e * z e)).sum
        = w a * (c * ((L ++ [a]).map z).sum)
          + c * (L.map (fun e => (w e - w a) * z e)).sum := by
      rw [sum_map_shift]
      simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil]
      ring
    rw [key]
    have := mul_le_mul_of_nonneg_left h2 hwa0
    linarith

variable {V₁ V₂ E : Type} [Fintype E] [DecidableEq V₁] [DecidableEq V₂] [DecidableEq E]

lemma bern_nonneg (q : ℝ) (hq : 0 ≤ q ∧ q ≤ 1) (b : Bool) : 0 ≤ bern q b := by
  cases b <;> simp [bern] <;> linarith [hq.1, hq.2]

lemma coin_nonneg (p : E → ℝ) (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1) (P : E → Bool) :
    0 ≤ coinWeight p P :=
  Finset.prod_nonneg (fun e _ => bern_nonneg _ (hp e) _)

lemma coin_prod (p : E → ℝ) (g : E → Bool → ℝ) :
    ∑ P : E → Bool, coinWeight p P * ∏ e, g e (P e)
      = ∏ e, (p e * g e true + (1 - p e) * g e false) := by
  have h : ∀ P : E → Bool, coinWeight p P * ∏ e, g e (P e)
      = ∏ e, (bern (p e) (P e) * g e (P e)) := by
    intro P; rw [coinWeight, ← Finset.prod_mul_distrib]
  simp_rw [h]
  rw [← Fintype.prod_sum (fun e b => bern (p e) b * g e b)]
  refine Finset.prod_congr rfl (fun e _ => ?_)
  simp [Fintype.sum_bool, bern]

lemma prod_univ_ite (S : Finset E) (f : E → ℝ) :
    ∏ e, (if e ∈ S then f e else 1) = ∏ e ∈ S, f e := by
  rw [← Finset.prod_filter]; congr 1; ext x; simp

lemma one_sub_prod_ge (S : Finset E) (z : E → ℝ) (hz : ∀ x ∈ S, 0 ≤ z x ∧ z x ≤ 1)
    (hs : ∑ x ∈ S, z x ≤ 1) :
    (1 - Real.exp (-1)) * ∑ x ∈ S, z x ≤ 1 - ∏ x ∈ S, (1 - z x) := by
  set s := ∑ x ∈ S, z x with hsdef
  have hs0 : 0 ≤ s := Finset.sum_nonneg (fun x hx => (hz x hx).1)
  have h1 : ∏ x ∈ S, (1 - z x) ≤ Real.exp (-s) := by
    calc ∏ x ∈ S, (1 - z x) ≤ ∏ x ∈ S, Real.exp (- z x) :=
          Finset.prod_le_prod (fun x hx => by linarith [(hz x hx).2])
            (fun x _ => by linarith [Real.add_one_le_exp (-z x)])
      _ = Real.exp (-s) := by rw [← Real.exp_sum, Finset.sum_neg_distrib]
  have h2 : Real.exp (-s) ≤ (1 - s) + s * Real.exp (-1) := by
    have := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (-1:ℝ))
      (by linarith : (0:ℝ) ≤ 1 - s) hs0 (by ring)
    simp only [smul_eq_mul, mul_zero, zero_add, mul_neg, mul_one, Real.exp_zero] at this
    linarith
  nlinarith [h1, h2]

lemma W_eq (w : E → ℝ) (ord : V₂ → List E) (v : V₂) (Y : Finset E) (P : E → Bool) :
    W w ord v Y P = Fv w (fun e => decide (e ∈ Y) && P e) (ord v) := by
  unfold W Fv probeList
  simp only [find_filter]
  split <;> split <;> simp_all

set_option maxHeartbeats 1000000 in
lemma prob_bound (G : BipGraph V₁ V₂ E) (p y : E → ℝ) (t : V₂ → ℕ∞)
    (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1) (hy : LPFeasible G p y t)
    (μ : Finset E → ℝ) (hμ : IsRounding G y t μ) (v : V₂) (S : Finset E)
    (hS : S ⊆ deltaR G v) :
    (1 - Real.exp (-1)) * ∑ x ∈ S, p x * y x ≤
      ∑ Y, ∑ P : E → Bool,
        μ Y * coinWeight p P * (if ∃ x ∈ S, x ∈ Y ∧ P x = true then 1 else 0) := by
  have hcw1 : ∑ P : E → Bool, coinWeight p P = 1 := by
    have := coin_prod p (fun _ _ => (1:ℝ)); simpa using this
  have hR : ∑ Y, ∑ P : E → Bool,
        μ Y * coinWeight p P * (if ∃ x ∈ S, x ∈ Y ∧ P x = true then 1 else 0)
      = 1 - ∑ P : E → Bool, coinWeight p P * PrAll μ (S.filter (fun x => P x = true)) false := by
    have e1 : ∀ Y (P : E → Bool),
        μ Y * coinWeight p P * (if ∃ x ∈ S, x ∈ Y ∧ P x = true then 1 else 0)
        = μ Y * coinWeight p P - coinWeight p P *
          (if ∀ x ∈ S.filter (fun x => P x = true), decide (x ∈ Y) = false then μ Y else 0) := by
      intro Y P
      by_cases h : ∃ x ∈ S, x ∈ Y ∧ P x = true
      · have h' : ¬ ∀ x ∈ S.filter (fun x => P x = true), decide (x ∈ Y) = false := by
          obtain ⟨x, hx, hxY, hPx⟩ := h
          intro hall
          have := hall x (by simp [hx, hPx])
          simp [hxY] at this
        rw [if_pos h, if_neg h']; ring
      · have h' : ∀ x ∈ S.filter (fun x => P x = true), decide (x ∈ Y) = false := by
          intro x hx
          simp only [Finset.mem_filter] at hx
          simp only [decide_eq_false_iff_not]
          intro hxY; exact h ⟨x, hx.1, hxY, hx.2⟩
        rw [if_neg h, if_pos h']; ring
    simp_rw [e1, Finset.sum_sub_distrib]
    have A : ∑ Y, ∑ P : E → Bool, μ Y * coinWeight p P = 1 := by
      simp_rw [← Finset.mul_sum, hcw1, mul_one]; exact hμ.sum_one
    have B : ∑ Y, ∑ P : E → Bool, coinWeight p P *
          (if ∀ x ∈ S.filter (fun x => P x = true), decide (x ∈ Y) = false then μ Y else 0)
        = ∑ P : E → Bool, coinWeight p P * PrAll μ (S.filter (fun x => P x = true)) false := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun P _ => ?_)
      rw [← Finset.mul_sum, PrAll, Finset.sum_filter]
    rw [A, B]
  rw [hR]
  have hPr1 : ∀ e, PrAll μ {e} false = 1 - y e := by
    intro e
    have h := Finset.sum_filter_add_sum_filter_not univ (fun Y : Finset E => e ∈ Y) μ
    rw [hμ.sum_one, hμ.marginal e] at h
    unfold PrAll
    have : (univ.filter (fun Y : Finset E => ∀ x ∈ ({e} : Finset E), decide (x ∈ Y) = false))
        = univ.filter (fun Y => ¬ e ∈ Y) := by
      ext Y; simp
    rw [this]; linarith
  have hneg : ∀ P : E → Bool, PrAll μ (S.filter (fun x => P x = true)) false
      ≤ ∏ x ∈ S, (if P x = true then 1 - y x else 1) := by
    intro P
    have h := hμ.neg_corr v (S.filter (fun x => P x = true))
      ((Finset.filter_subset _ _).trans hS) false
    rw [Finset.prod_filter] at h
    refine h.trans (le_of_eq ?_)
    refine Finset.prod_congr rfl (fun x _ => ?_)
    rw [hPr1]
  have hprod : ∑ P : E → Bool, coinWeight p P * ∏ x ∈ S, (if P x = true then 1 - y x else 1)
      = ∏ x ∈ S, (1 - p x * y x) := by
    have hc := coin_prod p (fun e b => if e ∈ S then (if b = true then 1 - y e else 1) else (1:ℝ))
    beta_reduce at hc
    simp only [prod_univ_ite] at hc
    rw [hc, ← prod_univ_ite S (fun x => 1 - p x * y x)]
    refine Finset.prod_congr rfl (fun e _ => ?_)
    by_cases he : e ∈ S
    · simp only [he, if_true, Bool.false_eq_true, if_false]; ring
    · simp only [he, if_false]; ring
  have hle : ∑ P : E → Bool, coinWeight p P * PrAll μ (S.filter (fun x => P x = true)) false
      ≤ ∏ x ∈ S, (1 - p x * y x) := by
    rw [← hprod]
    exact Finset.sum_le_sum (fun P _ => mul_le_mul_of_nonneg_left (hneg P) (coin_nonneg p hp P))
  have hz : ∀ x ∈ S, 0 ≤ p x * y x ∧ p x * y x ≤ 1 := by
    intro x _
    have h1 := hp x; have h2 := hy.y_mem x
    exact ⟨mul_nonneg h1.1 h2.1, by nlinarith [h1.1, h1.2, h2.1, h2.2]⟩
  have hs : ∑ x ∈ S, p x * y x ≤ 1 := by
    calc ∑ x ∈ S, p x * y x ≤ ∑ x ∈ deltaR G v, p x * y x :=
          Finset.sum_le_sum_of_subset_of_nonneg hS (fun x _ _ => mul_nonneg (hp x).1 (hy.y_mem x).1)
      _ = ∑ x ∈ deltaR G v, y x * p x := by
          refine Finset.sum_congr rfl (fun x _ => ?_); ring
      _ ≤ 1 := hy.match_right v
  have := one_sub_prod_ge S (fun x => p x * y x) hz hs
  linarith

end OSM41

open Finset OfflineStochMatch.UnitPatience OfflineStochMatch.InfinitePatience in
theorem solution {V₁ V₂ E : Type} [Fintype V₂] [Fintype E] [DecidableEq V₁] [DecidableEq V₂]
    [DecidableEq E] (G : BipGraph V₁ V₂ E) (w p y : E → ℝ) (t : V₂ → ℕ∞)
    (hw : ∀ e, 0 ≤ w e) (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1) (hy : LPFeasible G p y t)
    (μ : Finset E → ℝ) (hμ : IsRounding G y t μ)
    (ord : V₂ → List E) (hord : IsWeightOrder G w ord) :
    (1 - Real.exp (-1)) * ∑ v, ∑ e ∈ deltaR G v, w e * p e * y e ≤ EALG w p ord μ := by
  have hv : ∀ v, (1 - Real.exp (-1)) * ∑ e ∈ deltaR G v, w e * p e * y e ≤
      ∑ Y, ∑ P : E → Bool, μ Y * (coinWeight p P * W w ord v Y P) := by
    intro v
    obtain ⟨hnd, hmem, hpw⟩ := hord v
    have hdel : deltaR G v = (ord v).toFinset := by
      ext e; simp [deltaR, hmem e]
    have hL : ∑ e ∈ deltaR G v, w e * p e * y e
        = ((ord v).map (fun e => w e * (p e * y e))).sum := by
      rw [hdel, List.sum_toFinset _ hnd]
      congr 1
      apply List.map_congr_left
      intro e _; ring
    rw [hL]
    have hq : ∀ S : List E, S.Nodup → (∀ x ∈ S, x ∈ ord v) →
        (1 - Real.exp (-1)) * (S.map (fun e => p e * y e)).sum ≤
          ∑ i : Finset E × (E → Bool), μ i.1 * coinWeight p i.2 *
            (if ∃ x ∈ S, (decide (x ∈ i.1) && i.2 x) = true then 1 else 0) := by
      intro S hSnd hSL
      have hsub : S.toFinset ⊆ deltaR G v := by
        intro x hx; rw [hdel]; simp only [List.mem_toFinset] at hx ⊢; exact hSL x hx
      have h := OSM41.prob_bound G p y t hp hy μ hμ v S.toFinset hsub
      rw [List.sum_toFinset _ hSnd] at h
      refine h.trans (le_of_eq ?_)
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun Y _ => Finset.sum_congr rfl (fun P _ => ?_))
      congr 1
      simp [List.mem_toFinset]
    have hab := OSM41.abstract_bound (fun i : Finset E × (E → Bool) => μ i.1 * coinWeight p i.2)
      (fun i e => decide (e ∈ i.1) && i.2 e) (fun e => p e * y e) (1 - Real.exp (-1)) (ord v)
      w hnd (fun x _ => hw x) hpw hq
    refine hab.trans (le_of_eq ?_)
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun Y _ => Finset.sum_congr rfl (fun P _ => ?_))
    rw [OSM41.W_eq]
    dsimp only
    ring
  have hE : EALG w p ord μ = ∑ v, ∑ Y, ∑ P : E → Bool, μ Y * (coinWeight p P * W w ord v Y P) := by
    calc EALG w p ord μ = ∑ Y, ∑ P : E → Bool, ∑ v, μ Y * (coinWeight p P * W w ord v Y P) := by
          unfold EALG; simp_rw [Finset.mul_sum]
      _ = ∑ Y, ∑ v, ∑ P : E → Bool, μ Y * (coinWeight p P * W w ord v Y P) :=
          Finset.sum_congr rfl (fun Y _ => Finset.sum_comm)
      _ = ∑ v, ∑ Y, ∑ P : E → Bool, μ Y * (coinWeight p P * W w ord v Y P) := Finset.sum_comm
  rw [hE, Finset.mul_sum]
  exact Finset.sum_le_sum (fun v _ => hv v)
