-- Prove2me | solution 1 for OfflineStochMatching.UnitPatience.theorem_2_unit_patience_approximation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-05T13:16:35.227201+00:00
-- url     : https://prove2.me/submissions/8690ce17-5eb1-4474-bf4c-23eef868fa59

import Mathlib
import Definitions.Def_OfflineStochMatching_UnitPatience_IsLPOptimal
import Definitions.Def_OfflineStochMatching_UnitPatience_IsDependentRounding
import Definitions.Def_OfflineStochMatching_UnitPatience_IsWeightOrder
import Definitions.Def_OfflineStochMatching_UnitPatience_algMatch
import Definitions.Def_OfflineStochMatching_UnitPatience_algProbes
import Definitions.Def_OfflineStochMatching_UnitPatience_algValue
import Definitions.Def_OfflineStochMatching_UnitPatience_IsValidPolicy
import Definitions.Def_OfflineStochMatching_UnitPatience_policyValue

set_option autoImplicit false
set_option linter.all false
set_option linter.unusedSectionVars false

namespace OSM17

open Finset OfflineStochMatching.UnitPatience

/-! ### Part B: the per-star layer-cake bound (adapted from our accepted 41da26f9). -/

/-- Value of the first hit edge of a list (0 if none). -/
def Fv {E : Type*} (w : E → ℝ) (h : E → Bool) (L : List E) : ℝ :=
  match L.find? h with
  | some e => w e
  | none => 0

lemma Fv_append_single {E : Type*} (w : E → ℝ) (h : E → Bool) (L : List E) (a : E)
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

lemma sum_map_shift {E : Type*} (w z : E → ℝ) (k : ℝ) (L : List E) :
    (L.map (fun e => (w e - k) * z e)).sum
      = (L.map (fun e => w e * z e)).sum - k * (L.map z).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, ih]; ring

lemma abstract_bound {E ι : Type*} [Fintype ι] (π : ι → ℝ)
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

lemma one_sub_prod_ge {E : Type*} (S : Finset E) (z : E → ℝ) (hz : ∀ x ∈ S, 0 ≤ z x ∧ z x ≤ 1)
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

section main

variable {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]

lemma ap_nonneg (G : StochGraph V E) (P : E → Bool) : 0 ≤ activeProb G P := by
  unfold activeProb
  refine Finset.prod_nonneg (fun e _ => ?_)
  split_ifs
  · exact G.p_nonneg e
  · linarith [G.p_le_one e]

lemma coin_prod (G : StochGraph V E) (g : E → Bool → ℝ) :
    ∑ P : E → Bool, activeProb G P * ∏ e, g e (P e)
      = ∏ e, (G.p e * g e true + (1 - G.p e) * g e false) := by
  have h : ∀ P : E → Bool, activeProb G P * ∏ e, g e (P e)
      = ∏ e, ((if P e = true then G.p e else 1 - G.p e) * g e (P e)) := by
    intro P; rw [activeProb, ← Finset.prod_mul_distrib]
  simp_rw [h]
  rw [← Fintype.prod_sum (fun e b => (if b = true then G.p e else 1 - G.p e) * g e b)]
  refine Finset.prod_congr rfl (fun e _ => ?_)
  simp [Fintype.sum_bool]

lemma ap_sum (G : StochGraph V E) : ∑ P : E → Bool, activeProb G P = 1 := by
  have := coin_prod G (fun _ _ => (1:ℝ)); simpa using this

lemma prod_univ_ite (S : Finset E) (f : E → ℝ) :
    ∏ e, (if e ∈ S then f e else 1) = ∏ e ∈ S, f e := by
  rw [← Finset.prod_filter]; congr 1; ext x; simp

set_option maxHeartbeats 1000000 in
lemma prob_bound (G : StochGraph V E) (y : E → ℝ) (hy : IsLPFeasible G y) (V2 : Finset V)
    (μ : (E → Bool) → ℝ) (hμ : IsDependentRounding G V2 y μ) (v : V) (hv : v ∈ V2)
    (S : Finset E) (hS : S ⊆ incident G v) :
    (1 - Real.exp (-1)) * ∑ x ∈ S, G.p x * y x ≤
      ∑ Y : E → Bool, ∑ P : E → Bool,
        μ Y * activeProb G P * (if ∃ x ∈ S, Y x = true ∧ P x = true then 1 else 0) := by
  have hR : ∑ Y : E → Bool, ∑ P : E → Bool,
        μ Y * activeProb G P * (if ∃ x ∈ S, Y x = true ∧ P x = true then 1 else 0)
      = 1 - ∑ P : E → Bool, activeProb G P *
          ∑ Y ∈ Finset.univ.filter
            (fun Y : E → Bool => ∀ e ∈ S.filter (fun x => P x = true), Y e = false), μ Y := by
    have e1 : ∀ (Y P : E → Bool),
        μ Y * activeProb G P * (if ∃ x ∈ S, Y x = true ∧ P x = true then 1 else 0)
        = μ Y * activeProb G P - activeProb G P *
          (if ∀ e ∈ S.filter (fun x => P x = true), Y e = false then μ Y else 0) := by
      intro Y P
      by_cases h : ∃ x ∈ S, Y x = true ∧ P x = true
      · have h' : ¬ ∀ e ∈ S.filter (fun x => P x = true), Y e = false := by
          obtain ⟨x, hx, hxY, hPx⟩ := h
          intro hall
          have := hall x (by simp [hx, hPx])
          simp [hxY] at this
        rw [if_pos h, if_neg h']; ring
      · have h' : ∀ e ∈ S.filter (fun x => P x = true), Y e = false := by
          intro x hx
          simp only [Finset.mem_filter] at hx
          by_contra hY
          exact h ⟨x, hx.1, by simpa using hY, hx.2⟩
        rw [if_neg h, if_pos h']; ring
    simp_rw [e1, Finset.sum_sub_distrib]
    have A : ∑ Y : E → Bool, ∑ P : E → Bool, μ Y * activeProb G P = 1 := by
      simp_rw [← Finset.mul_sum, ap_sum, mul_one]; exact hμ.1.2
    have B : ∑ Y : E → Bool, ∑ P : E → Bool, activeProb G P *
          (if ∀ e ∈ S.filter (fun x => P x = true), Y e = false then μ Y else 0)
        = ∑ P : E → Bool, activeProb G P *
          ∑ Y ∈ Finset.univ.filter
            (fun Y : E → Bool => ∀ e ∈ S.filter (fun x => P x = true), Y e = false), μ Y := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun P _ => ?_)
      rw [← Finset.mul_sum, Finset.sum_filter]
    rw [A, B]
  rw [hR]
  have hPr1 : ∀ e, ∑ Y ∈ Finset.univ.filter (fun Y : E → Bool => Y e = false), μ Y = 1 - y e := by
    intro e
    have h := Finset.sum_filter_add_sum_filter_not Finset.univ (fun Y : E → Bool => Y e = true) μ
    rw [hμ.1.2, hμ.2.1 e] at h
    have : (Finset.univ.filter (fun Y : E → Bool => Y e = false))
        = Finset.univ.filter (fun Y : E → Bool => ¬ Y e = true) := by
      ext Y; simp
    rw [this]; linarith
  have hneg : ∀ P : E → Bool,
      ∑ Y ∈ Finset.univ.filter
          (fun Y : E → Bool => ∀ e ∈ S.filter (fun x => P x = true), Y e = false), μ Y
      ≤ ∏ x ∈ S, (if P x = true then 1 - y x else 1) := by
    intro P
    have h := hμ.2.2.2 v hv (S.filter (fun x => P x = true))
      ((Finset.filter_subset _ _).trans hS) false
    rw [Finset.prod_filter] at h
    refine h.trans (le_of_eq ?_)
    refine Finset.prod_congr rfl (fun x _ => ?_)
    rw [hPr1]
  have hprod : ∑ P : E → Bool, activeProb G P * ∏ x ∈ S, (if P x = true then 1 - y x else 1)
      = ∏ x ∈ S, (1 - G.p x * y x) := by
    have hc := coin_prod G
      (fun e b => if e ∈ S then (if b = true then 1 - y e else 1) else (1:ℝ))
    beta_reduce at hc
    simp only [prod_univ_ite] at hc
    rw [hc, ← prod_univ_ite S (fun x => 1 - G.p x * y x)]
    refine Finset.prod_congr rfl (fun e _ => ?_)
    by_cases he : e ∈ S
    · simp only [he, if_true, Bool.false_eq_true, if_false]; ring
    · simp only [he, if_false]; ring
  have hle : ∑ P : E → Bool, activeProb G P *
        ∑ Y ∈ Finset.univ.filter
          (fun Y : E → Bool => ∀ e ∈ S.filter (fun x => P x = true), Y e = false), μ Y
      ≤ ∏ x ∈ S, (1 - G.p x * y x) := by
    rw [← hprod]
    exact Finset.sum_le_sum (fun P _ => mul_le_mul_of_nonneg_left (hneg P) (ap_nonneg G P))
  have hz : ∀ x ∈ S, 0 ≤ G.p x * y x ∧ G.p x * y x ≤ 1 := by
    intro x _
    have h1 := G.p_nonneg x; have h1' := G.p_le_one x; have h2 := hy.1 x
    exact ⟨mul_nonneg h1 h2.1, by nlinarith [h2.1, h2.2]⟩
  have hs : ∑ x ∈ S, G.p x * y x ≤ 1 := by
    calc ∑ x ∈ S, G.p x * y x ≤ ∑ x ∈ incident G v, G.p x * y x :=
          Finset.sum_le_sum_of_subset_of_nonneg hS
            (fun x _ _ => mul_nonneg (G.p_nonneg x) (hy.1 x).1)
      _ = ∑ x ∈ incident G v, y x * G.p x := by
          refine Finset.sum_congr rfl (fun x _ => ?_); ring
      _ ≤ 1 := hy.2.1 v
  have := one_sub_prod_ge S (fun x => G.p x * y x) hz hs
  linarith

lemma neg_edge (G : StochGraph V E) (y : E → ℝ) (hy : IsLPOptimal G y) (e : E)
    (hw : G.w e < 0) : y e * G.p e = 0 := by
  set y' : E → ℝ := fun x => if x = e then 0 else y x with hy'
  have hle : ∀ x, y' x ≤ y x ∧ 0 ≤ y' x := by
    intro x
    by_cases hx : x = e
    · simp only [y', hx, if_true]; exact ⟨(hy.1.1 e).1, le_rfl⟩
    · simp only [y', hx, if_false]; exact ⟨le_rfl, (hy.1.1 x).1⟩
  have hf : IsLPFeasible G y' := by
    refine ⟨fun x => ⟨(hle x).2, (hle x).1.trans (hy.1.1 x).2⟩, fun x => ?_, fun x n h => ?_⟩
    · exact le_trans (Finset.sum_le_sum (fun e' _ =>
        mul_le_mul_of_nonneg_right (hle e').1 (G.p_nonneg e'))) (hy.1.2.1 x)
    · exact le_trans (Finset.sum_le_sum (fun e' _ => (hle e').1)) (hy.1.2.2 x n h)
  have hopt := hy.2 y' hf
  have hdiff : ∑ x, G.w x * (y x * G.p x) - ∑ x, G.w x * (y' x * G.p x)
      = G.w e * (y e * G.p e) := by
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single e]
    · simp [y']
    · intro b _ hb; simp [y', hb]
    · simp
  have h0 : 0 ≤ y e * G.p e := mul_nonneg (hy.1.1 e).1 (G.p_nonneg e)
  have : y e * G.p e ≤ 0 := by nlinarith
  linarith

lemma starWeight_eq (G : StochGraph V E) (σ : V → List E) (Y P : E → Bool) (v : V) :
    starWeight G σ Y P v = Fv G.w (fun e => Y e && P e) (σ v) := by
  unfold starWeight Fv algMatch
  split <;> split <;> simp_all

lemma Fv_pos (w : E → ℝ) (h : E → Bool) (L : List E) (c : ℝ)
    (hc : ∀ e, h e = true → w e < 0 → c = 0) :
    c * Fv (fun x => max (w x) 0) h L = c * Fv w h L := by
  unfold Fv
  cases hf : L.find? h with
  | none => simp
  | some e =>
    have he : h e = true := List.find?_some hf
    by_cases hw : w e < 0
    · rw [hc e he hw]; simp
    · simp [max_eq_left (not_lt.1 hw)]

set_option maxHeartbeats 1000000 in
lemma star_bound (G : StochGraph V E) (V2 : Finset V) (y : E → ℝ) (hy : IsLPOptimal G y)
    (μ : (E → Bool) → ℝ) (hμ : IsDependentRounding G V2 y μ) (σ : V → List E)
    (hσ : IsWeightOrder G V2 σ) (v : V) (hv : v ∈ V2) :
    (1 - Real.exp (-1)) * ∑ e ∈ incident G v, G.w e * G.p e * y e ≤
      ∑ Y : E → Bool, ∑ P : E → Bool, μ Y * activeProb G P * starWeight G σ Y P v := by
  obtain ⟨hnd, hmem, hpw⟩ := hσ v hv
  have hdel : incident G v = (σ v).toFinset := by
    ext e; simp [hmem e]
  have hL : ∑ e ∈ incident G v, G.w e * G.p e * y e
      = ((σ v).map (fun e => max (G.w e) 0 * (G.p e * y e))).sum := by
    rw [hdel, List.sum_toFinset _ hnd]
    congr 1
    apply List.map_congr_left
    intro e _
    by_cases hw : G.w e < 0
    · have := neg_edge G y hy e hw
      rw [max_eq_right hw.le, zero_mul]
      linear_combination G.w e * this
    · rw [max_eq_left (not_lt.1 hw)]; ring
  rw [hL]
  have hq : ∀ S : List E, S.Nodup → (∀ x ∈ S, x ∈ σ v) →
      (1 - Real.exp (-1)) * (S.map (fun e => G.p e * y e)).sum ≤
        ∑ i : (E → Bool) × (E → Bool), μ i.1 * activeProb G i.2 *
          (if ∃ x ∈ S, (i.1 x && i.2 x) = true then 1 else 0) := by
    intro S hSnd hSL
    have hsub : S.toFinset ⊆ incident G v := by
      intro x hx; rw [hdel]; simp only [List.mem_toFinset] at hx ⊢; exact hSL x hx
    have h := prob_bound G y hy.1 V2 μ hμ v hv S.toFinset hsub
    rw [List.sum_toFinset _ hSnd] at h
    refine h.trans (le_of_eq ?_)
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun Y _ => Finset.sum_congr rfl (fun P _ => ?_))
    congr 1
    simp [List.mem_toFinset]
  have hab := abstract_bound (fun i : (E → Bool) × (E → Bool) => μ i.1 * activeProb G i.2)
    (fun i e => i.1 e && i.2 e) (fun e => G.p e * y e) (1 - Real.exp (-1)) (σ v)
    (fun x => max (G.w x) 0) hnd (fun x _ => le_max_right _ _)
    (hpw.imp (fun h => max_le_max h (le_refl 0))) hq
  refine hab.trans (le_of_eq ?_)
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun Y _ => Finset.sum_congr rfl (fun P _ => ?_))
  rw [starWeight_eq]
  refine Fv_pos G.w (fun e => Y e && P e) (σ v) _ ?_
  intro e he hw
  have hYP : Y e = true ∧ P e = true := by simpa using he
  have h0 := neg_edge G y hy e hw
  rcases mul_eq_zero.1 h0 with h | h
  · have hz := hμ.2.1 e
    rw [h] at hz
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun Y' _ => hμ.1.1 Y')).1 hz Y (by simp [hYP.1])
    simp [this]
  · have : activeProb G P = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ e) (by simp [hYP.2, h])
    simp [this]

lemma part_b (G : StochGraph V E) (V2 : Finset V) (y : E → ℝ) (hy : IsLPOptimal G y)
    (μ : (E → Bool) → ℝ) (hμ : IsDependentRounding G V2 y μ) (σ : V → List E)
    (hσ : IsWeightOrder G V2 σ) :
    (1 - Real.exp (-1)) * ∑ v ∈ V2, ∑ e ∈ incident G v, G.w e * G.p e * y e ≤
      algValue G V2 σ μ := by
  have hE : algValue G V2 σ μ =
      ∑ v ∈ V2, ∑ Y : E → Bool, ∑ P : E → Bool, μ Y * activeProb G P * starWeight G σ Y P v := by
    unfold algValue
    simp_rw [Finset.mul_sum]
    calc ∑ Y : E → Bool, ∑ P : E → Bool, ∑ v ∈ V2, μ Y * activeProb G P * starWeight G σ Y P v
        = ∑ Y : E → Bool, ∑ v ∈ V2, ∑ P : E → Bool, μ Y * activeProb G P * starWeight G σ Y P v :=
          Finset.sum_congr rfl (fun Y _ => Finset.sum_comm)
      _ = _ := Finset.sum_comm
  rw [hE, Finset.mul_sum]
  exact Finset.sum_le_sum (fun v hv => star_bound G V2 y hy μ hμ σ hσ v hv)

/-! ### Part A: the algorithm is a probing algorithm. -/

lemma probes_sub (σ : V → List E) (Y P : E → Bool) (v : V) (e : E)
    (h : e ∈ algProbes σ Y P v) : e ∈ σ v ∧ Y e = true := by
  unfold algProbes at h
  have := List.mem_filter.1 (List.mem_of_mem_take h)
  exact this

lemma match_sub (σ : V → List E) (Y P : E → Bool) (v : V) (e : E)
    (h : e ∈ (algMatch σ Y P v).toFinset) : e ∈ σ v ∧ Y e = true ∧ P e = true := by
  rw [Option.mem_toFinset] at h
  unfold algMatch at h
  have h1 := List.mem_of_find?_eq_some h
  have h2 := List.find?_some h
  simp only [Bool.and_eq_true] at h2
  exact ⟨h1, h2⟩

lemma same_star (G : StochGraph V E) (V1 : Finset V)
    (hbip : ∀ e, (G.src e ∈ V1 ∧ G.dst e ∉ V1) ∨ (G.src e ∉ V1 ∧ G.dst e ∈ V1))
    {v x : V} {e : E} (hv : v ∉ V1) (hx : x ∉ V1)
    (he1 : e ∈ incident G v) (he2 : e ∈ incident G x) : v = x := by
  simp only [incident, Finset.mem_filter, Finset.mem_univ, true_and] at he1 he2
  rcases hbip e with ⟨h1, _⟩ | ⟨_, h1⟩
  · have hv' : G.dst e = v := by
      rcases he1 with h | h
      · exact absurd (h ▸ h1) hv
      · exact h
    have hx' : G.dst e = x := by
      rcases he2 with h | h
      · exact absurd (h ▸ h1) hx
      · exact h
    exact hv'.symm.trans hx'
  · have hv' : G.src e = v := by
      rcases he1 with h | h
      · exact h
      · exact absurd (h ▸ h1) hv
    have hx' : G.src e = x := by
      rcases he2 with h | h
      · exact h
      · exact absurd (h ▸ h1) hx
    exact hv'.symm.trans hx'

lemma deg_le (G : StochGraph V E) (V2 : Finset V) (y : E → ℝ) (hy : IsLPFeasible G y)
    (μ : (E → Bool) → ℝ) (hμ : IsDependentRounding G V2 y μ) (Y : E → Bool) (hY : μ Y ≠ 0)
    (x : V) (n : ℕ) (hn : G.t x = n) :
    ((incident G x).filter (fun e => Y e = true)).card ≤ n := by
  have h1 := hμ.2.2.1 Y hY x
  have h2 := hy.2.2 x n hn
  have h3 : ⌈∑ e ∈ incident G x, y e⌉ ≤ (n : ℤ) := Int.ceil_le.2 (by exact_mod_cast h2)
  exact_mod_cast h1.trans h3

lemma part_a [Fintype V] (G : StochGraph V E) (V1 : Finset V)
    (hbip : ∀ e, (G.src e ∈ V1 ∧ G.dst e ∉ V1) ∨ (G.src e ∉ V1 ∧ G.dst e ∈ V1))
    (hunit : ∀ u ∈ V1, G.t u = 1) (y : E → ℝ) (hy : IsLPOptimal G y)
    (μ : (E → Bool) → ℝ) (hμ : IsDependentRounding G V1ᶜ y μ)
    (σ : V → List E) (hσ : IsWeightOrder G V1ᶜ σ) :
    ∀ Y : E → Bool, μ Y ≠ 0 → ∀ (P : E → Bool) (x : V),
        ((((V1ᶜ.biUnion fun v => (algProbes σ Y P v).toFinset).filter
            (· ∈ incident G x)).card : ℕ) : ℕ∞) ≤ G.t x ∧
        ((V1ᶜ.biUnion fun v => (algMatch σ Y P v).toFinset).filter
            (· ∈ incident G x)).card ≤ 1 := by
  intro Y hY P x
  have hsubD : ((V1ᶜ.biUnion fun v => (algProbes σ Y P v).toFinset).filter
      (· ∈ incident G x)) ⊆ (incident G x).filter (fun e => Y e = true) := by
    intro e he
    simp only [Finset.mem_filter, Finset.mem_biUnion, List.mem_toFinset] at he ⊢
    obtain ⟨⟨v, _, hev⟩, hex⟩ := he
    exact ⟨hex, (probes_sub σ Y P v e hev).2⟩
  refine ⟨?_, ?_⟩
  · by_cases htop : G.t x = ⊤
    · rw [htop]; exact le_top
    · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 htop
      rw [← hn]
      exact_mod_cast (Finset.card_le_card hsubD).trans (deg_le G V1ᶜ y hy.1 μ hμ Y hY x n hn.symm)
  · by_cases hx : x ∈ V1
    · have hsub : ((V1ᶜ.biUnion fun v => (algMatch σ Y P v).toFinset).filter
          (· ∈ incident G x)) ⊆ (incident G x).filter (fun e => Y e = true) := by
        intro e he
        simp only [Finset.mem_filter, Finset.mem_biUnion] at he ⊢
        obtain ⟨⟨v, _, hev⟩, hex⟩ := he
        exact ⟨hex, (match_sub σ Y P v e hev).2.1⟩
      have h1 : G.t x = ((1 : ℕ) : ℕ∞) := by rw [hunit x hx]; rfl
      exact (Finset.card_le_card hsub).trans (deg_le G V1ᶜ y hy.1 μ hμ Y hY x 1 h1)
    · have hsub : ((V1ᶜ.biUnion fun v => (algMatch σ Y P v).toFinset).filter
          (· ∈ incident G x)) ⊆ (algMatch σ Y P x).toFinset := by
        intro e he
        simp only [Finset.mem_filter, Finset.mem_biUnion] at he
        obtain ⟨⟨v, hv, hev⟩, hex⟩ := he
        have hv' : v ∉ V1 := Finset.mem_compl.1 hv
        have hev' := match_sub σ Y P v e hev
        have hinc : e ∈ incident G v := ((hσ v hv).2.1 e).1 hev'.1
        have := same_star G V1 hbip hv' hx hinc hex
        subst this
        exact hev
      refine (Finset.card_le_card hsub).trans ?_
      cases algMatch σ Y P x <;> simp

/-! ### Part C: every valid policy is bounded by the LP. -/

lemma run_succ_none (π : Policy E) (P : E → Bool) (n : ℕ)
    (h : π (runPolicy π P n) = none) : runPolicy π P (n + 1) = runPolicy π P n := by
  simp only [runPolicy, h]

lemma run_succ_some (π : Policy E) (P : E → Bool) (n : ℕ) (e : E)
    (h : π (runPolicy π P n) = some e) :
    runPolicy π P (n + 1) = runPolicy π P n ++ [(e, P e)] := by
  simp only [runPolicy, h]

lemma run_sub (π : Policy E) (P : E → Bool) (n : ℕ) (eb : E × Bool)
    (h : eb ∈ runPolicy π P n) : eb ∈ runPolicy π P (n + 1) := by
  cases hc : π (runPolicy π P n) with
  | none => rw [run_succ_none π P n hc]; exact h
  | some e => rw [run_succ_some π P n e hc]; exact List.mem_append_left _ h

lemma run_indep (π : Policy E) (P P' : E → Bool) (e : E) (hPP : ∀ x, x ≠ e → P x = P' x) :
    ∀ n, e ∉ (runPolicy π P n).map Prod.fst → runPolicy π P n = runPolicy π P' n
  | 0 => fun _ => rfl
  | n + 1 => fun hn => by
    have hn' : e ∉ (runPolicy π P n).map Prod.fst := by
      intro h
      obtain ⟨eb, hm, hfe⟩ := List.mem_map.1 h
      exact hn (List.mem_map.2 ⟨eb, run_sub π P n eb hm, hfe⟩)
    have ih := run_indep π P P' e hPP n hn'
    cases hc : π (runPolicy π P n) with
    | none =>
      have hc' : π (runPolicy π P' n) = none := by rw [← ih]; exact hc
      rw [run_succ_none π P n hc, run_succ_none π P' n hc', ih]
    | some e'' =>
      have hc' : π (runPolicy π P' n) = some e'' := by rw [← ih]; exact hc
      have hne : e'' ≠ e := by
        rintro rfl
        apply hn
        rw [run_succ_some π P n _ hc]
        simp
      rw [run_succ_some π P n e'' hc, run_succ_some π P' n e'' hc', ih, hPP e'' hne]

lemma probed_iff (π : Policy E) (P P' : E → Bool) (e : E) (hPP : ∀ x, x ≠ e → P x = P' x)
    (n : ℕ) : e ∈ (runPolicy π P n).map Prod.fst ↔ e ∈ (runPolicy π P' n).map Prod.fst := by
  constructor
  · intro h
    by_contra h'
    have := run_indep π P' P e (fun x hx => (hPP x hx).symm) n h'
    rw [this] at h'
    exact h' h
  · intro h
    by_contra h'
    have := run_indep π P P' e hPP n h'
    rw [this] at h'
    exact h' h

lemma run_inv (G : StochGraph V E) (π : Policy E) (hπ : IsValidPolicy G π) (P : E → Bool) :
    ∀ n, ((runPolicy π P n).map Prod.fst).Nodup ∧ (∀ eb ∈ runPolicy π P n, eb.2 = P eb.1) ∧
      ∀ x, ((((runPolicy π P n).filter (fun eb => decide (eb.1 ∈ incident G x))).length : ℕ)
          : ℕ∞) ≤ G.t x ∧
        ((runPolicy π P n).filter (fun eb => decide (eb.1 ∈ incident G x) && eb.2)).length ≤ 1
  | 0 => by simp [runPolicy]
  | n + 1 => by
    obtain ⟨h1, h2, h3⟩ := run_inv G π hπ P n
    cases hc : π (runPolicy π P n) with
    | none => rw [run_succ_none π P n hc]; exact ⟨h1, h2, h3⟩
    | some e =>
      rw [run_succ_some π P n e hc]
      obtain ⟨hnot, hx⟩ := hπ P n e hc
      have hnm : e ∉ (runPolicy π P n).map Prod.fst := by
        intro hm
        obtain ⟨⟨a, b⟩, hab, hae⟩ := List.mem_map.1 hm
        simp only at hae
        subst hae
        exact hnot b hab
      refine ⟨?_, ?_, ?_⟩
      · have := List.Nodup.concat hnm h1
        simpa [List.concat_eq_append] using this
      · intro eb heb
        rcases List.mem_append.1 heb with h | h
        · exact h2 eb h
        · simp only [List.mem_singleton] at h; subst h; rfl
      · intro x
        by_cases he : e ∈ incident G x
        · have hxe : x = G.src e ∨ x = G.dst e := by
            simp only [incident, Finset.mem_filter, Finset.mem_univ, true_and] at he
            rcases he with h | h
            · exact Or.inl h.symm
            · exact Or.inr h.symm
          obtain ⟨hm, hlt⟩ := hx x hxe
          have hnil : (runPolicy π P n).filter
              (fun eb => decide (eb.1 ∈ incident G x) && eb.2) = [] := by
            rw [List.filter_eq_nil_iff]
            rintro ⟨e', b⟩ hmem
            cases b
            · simp
            · simp only [Bool.and_true, decide_eq_true_eq]
              exact hm e' hmem
          rw [List.filter_append, List.filter_append, hnil]
          refine ⟨?_, ?_⟩
          · simp only [List.filter_cons, List.filter_nil, he, decide_true, if_true,
              List.length_append, List.length_singleton]
            push_cast
            exact Order.add_one_le_of_lt hlt
          · exact (List.length_filter_le _ _).trans (by simp)
        · have hf1 : [(e, P e)].filter (fun eb => decide (eb.1 ∈ incident G x)) = [] := by
            simp [he]
          have hf2 : [(e, P e)].filter (fun eb => decide (eb.1 ∈ incident G x) && eb.2) = [] := by
            simp [he]
          rw [List.filter_append, List.filter_append, hf1, hf2, List.append_nil, List.append_nil]
          exact h3 x

lemma indep_sum (G : StochGraph V E) (e : E) (f : (E → Bool) → ℝ)
    (hf : ∀ P b, f (Function.update P e b) = f P) :
    ∑ P : E → Bool, activeProb G P * f P * (if P e = true then 1 else 0)
      = G.p e * ∑ P : E → Bool, activeProb G P * f P := by
  set R : (E → Bool) → ℝ := fun P =>
    ∏ x ∈ Finset.univ.erase e, (if P x = true then G.p x else 1 - G.p x) with hR
  have hfac : ∀ P, activeProb G P = (if P e = true then G.p e else 1 - G.p e) * R P := by
    intro P
    rw [activeProb, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ e)]
  set φ : (E → Bool) → (E → Bool) := fun P => Function.update P e (!P e) with hφ
  have hφe : ∀ P, φ P e = !P e := by intro P; simp [φ]
  have hinv : Function.Involutive φ := by
    intro P
    funext x
    by_cases hx : x = e
    · subst hx; simp [φ]
    · simp [φ, Function.update_of_ne hx]
  have hRφ : ∀ P, R (φ P) = R P := by
    intro P
    refine Finset.prod_congr rfl (fun x hx => ?_)
    have := Finset.ne_of_mem_erase hx
    simp [φ, Function.update_of_ne this]
  have hfφ : ∀ P, f (φ P) = f P := fun P => hf P _
  have hB : ∑ P : E → Bool, (if P e = true then 0 else R P * f P)
      = ∑ P : E → Bool, (if P e = true then R P * f P else 0) := by
    have := Equiv.sum_comp (Function.Involutive.toPerm φ hinv)
      (fun P : E → Bool => if P e = true then 0 else R P * f P)
    rw [← this]
    refine Finset.sum_congr rfl (fun P _ => ?_)
    simp only [Function.Involutive.coe_toPerm, hφe, hRφ, hfφ]
    cases P e <;> simp
  have hL : ∑ P : E → Bool, activeProb G P * f P * (if P e = true then 1 else 0)
      = G.p e * ∑ P : E → Bool, (if P e = true then R P * f P else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun P _ => ?_)
    rw [hfac]; split_ifs <;> ring
  have hT : ∑ P : E → Bool, activeProb G P * f P
      = G.p e * ∑ P : E → Bool, (if P e = true then R P * f P else 0)
        + (1 - G.p e) * ∑ P : E → Bool, (if P e = true then 0 else R P * f P) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun P _ => ?_)
    rw [hfac]; split_ifs <;> ring
  rw [hL, hT, hB]
  ring

lemma policy_le (G : StochGraph V E) (π : Policy E) (hπ : IsValidPolicy G π) (y : E → ℝ)
    (hy : IsLPOptimal G y) : policyValue G π ≤ ∑ e, G.w e * (y e * G.p e) := by
  set pr : (E → Bool) → E → ℝ :=
    fun P e => if e ∈ (runPolicy π P (Fintype.card E)).map Prod.fst then 1 else 0 with hpr
  set y' : E → ℝ := fun e => ∑ P : E → Bool, activeProb G P * pr P e with hy'
  have hpr01 : ∀ P e, 0 ≤ pr P e ∧ pr P e ≤ 1 := by
    intro P e; simp only [pr]; split_ifs <;> norm_num
  have hind : ∀ e, ∑ P : E → Bool, activeProb G P * pr P e * (if P e = true then 1 else 0)
      = y' e * G.p e := by
    intro e
    rw [indep_sum G e (fun P => pr P e), mul_comm]
    intro P b
    have := probed_iff π (Function.update P e b) P e
      (fun x hx => Function.update_of_ne hx b P) (Fintype.card E)
    simp only [pr, this]
  -- counting lemmas for a single realization
  have hcountM : ∀ P x, ∑ e ∈ incident G x, pr P e * (if P e = true then 1 else 0) ≤ 1 := by
    intro P x
    obtain ⟨_, h2, h3⟩ := run_inv G π hπ P (Fintype.card E)
    have hc : ∑ e ∈ incident G x, pr P e * (if P e = true then 1 else 0)
        = (((incident G x).filter
            (fun e => e ∈ (runPolicy π P (Fintype.card E)).map Prod.fst ∧ P e = true)).card : ℝ) := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl (fun e _ => ?_)
      simp only [pr]
      split_ifs <;> simp_all
    rw [hc]
    have hsub : (incident G x).filter
        (fun e => e ∈ (runPolicy π P (Fintype.card E)).map Prod.fst ∧ P e = true) ⊆
        (((runPolicy π P (Fintype.card E)).filter
          (fun eb => decide (eb.1 ∈ incident G x) && eb.2)).map Prod.fst).toFinset := by
      intro e he
      simp only [Finset.mem_filter] at he
      obtain ⟨hex, hm, hPe⟩ := he
      obtain ⟨eb, hebm, hfe⟩ := List.mem_map.1 hm
      rw [List.mem_toFinset]
      refine List.mem_map.2 ⟨eb, ?_, hfe⟩
      rw [List.mem_filter]
      refine ⟨hebm, ?_⟩
      have := h2 eb hebm
      subst hfe
      simp [hex, this, hPe]
    have := (Finset.card_le_card hsub).trans (List.toFinset_card_le _)
    rw [List.length_map] at this
    exact_mod_cast this.trans (h3 x).2
  have hcountT : ∀ P x (n : ℕ), G.t x = n → ∑ e ∈ incident G x, pr P e ≤ n := by
    intro P x n hn
    obtain ⟨_, _, h3⟩ := run_inv G π hπ P (Fintype.card E)
    have hc : ∑ e ∈ incident G x, pr P e
        = (((incident G x).filter
            (fun e => e ∈ (runPolicy π P (Fintype.card E)).map Prod.fst)).card : ℝ) := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl (fun e _ => ?_)
      simp only [pr]
      split_ifs <;> simp_all
    rw [hc]
    have hsub : (incident G x).filter (fun e => e ∈ (runPolicy π P (Fintype.card E)).map Prod.fst) ⊆
        (((runPolicy π P (Fintype.card E)).filter
          (fun eb => decide (eb.1 ∈ incident G x))).map Prod.fst).toFinset := by
      intro e he
      simp only [Finset.mem_filter] at he
      obtain ⟨hex, hm⟩ := he
      obtain ⟨eb, hebm, hfe⟩ := List.mem_map.1 hm
      rw [List.mem_toFinset]
      refine List.mem_map.2 ⟨eb, ?_, hfe⟩
      rw [List.mem_filter]
      subst hfe
      exact ⟨hebm, by simp [hex]⟩
    have hlen := (h3 x).1
    rw [hn] at hlen
    have hlen' : ((runPolicy π P (Fintype.card E)).filter
        (fun eb => decide (eb.1 ∈ incident G x))).length ≤ n := by exact_mod_cast hlen
    have := (Finset.card_le_card hsub).trans (List.toFinset_card_le _)
    rw [List.length_map] at this
    exact_mod_cast this.trans hlen'
  have hfeas : IsLPFeasible G y' := by
    refine ⟨fun e => ⟨?_, ?_⟩, fun x => ?_, fun x n hn => ?_⟩
    · exact Finset.sum_nonneg (fun P _ => mul_nonneg (ap_nonneg G P) (hpr01 P e).1)
    · calc y' e ≤ ∑ P : E → Bool, activeProb G P :=
            Finset.sum_le_sum (fun P _ => by
              have := hpr01 P e; have := ap_nonneg G P; nlinarith)
        _ = 1 := ap_sum G
    · calc ∑ e ∈ incident G x, y' e * G.p e
          = ∑ P : E → Bool, activeProb G P *
              ∑ e ∈ incident G x, pr P e * (if P e = true then 1 else 0) := by
            rw [Finset.sum_congr rfl (fun e _ => (hind e).symm), Finset.sum_comm]
            refine Finset.sum_congr rfl (fun P _ => ?_)
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun e _ => ?_)
            ring
        _ ≤ ∑ P : E → Bool, activeProb G P * 1 :=
            Finset.sum_le_sum (fun P _ => mul_le_mul_of_nonneg_left (hcountM P x) (ap_nonneg G P))
        _ = 1 := by simp [ap_sum]
    · calc ∑ e ∈ incident G x, y' e
          = ∑ P : E → Bool, activeProb G P * ∑ e ∈ incident G x, pr P e := by
            simp only [y']
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl (fun P _ => ?_)
            rw [Finset.mul_sum]
        _ ≤ ∑ P : E → Bool, activeProb G P * n :=
            Finset.sum_le_sum (fun P _ =>
              mul_le_mul_of_nonneg_left (hcountT P x n hn) (ap_nonneg G P))
        _ = n := by rw [← Finset.sum_mul, ap_sum, one_mul]
  have hval : policyValue G π = ∑ e, G.w e * (y' e * G.p e) := by
    unfold policyValue
    have hsum : ∀ P : E → Bool,
        ((runPolicy π P (Fintype.card E)).map (fun eb => if eb.2 then G.w eb.1 else 0)).sum
          = ∑ e, G.w e * (pr P e * (if P e = true then 1 else 0)) := by
      intro P
      obtain ⟨h1, h2, -⟩ := run_inv G π hπ P (Fintype.card E)
      have hm : (runPolicy π P (Fintype.card E)).map (fun eb => if eb.2 then G.w eb.1 else 0)
          = ((runPolicy π P (Fintype.card E)).map Prod.fst).map (fun e => if P e = true then G.w e else 0) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro eb heb
        show (if eb.2 = true then G.w eb.1 else 0) = (if P eb.1 = true then G.w eb.1 else 0)
        rw [h2 eb heb]
      rw [hm, ← List.sum_toFinset _ h1]
      calc ∑ e ∈ ((runPolicy π P (Fintype.card E)).map Prod.fst).toFinset, (if P e = true then G.w e else 0)
          = ∑ e ∈ Finset.univ.filter (fun e => e ∈ (runPolicy π P (Fintype.card E)).map Prod.fst),
              (if P e = true then G.w e else 0) := by
            congr 1; ext e; simp
        _ = ∑ e, if e ∈ (runPolicy π P (Fintype.card E)).map Prod.fst then
              (if P e = true then G.w e else 0) else 0 := Finset.sum_filter _ _
        _ = ∑ e, G.w e * (pr P e * (if P e = true then 1 else 0)) := by
            refine Finset.sum_congr rfl (fun e _ => ?_)
            simp only [pr]
            split_ifs <;> simp
    simp_rw [hsum, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [← hind e, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun P _ => ?_)
    ring
  rw [hval]
  exact hy.2 y' hfeas

lemma sum_bip [Fintype V] (G : StochGraph V E) (V1 : Finset V)
    (hbip : ∀ e, (G.src e ∈ V1 ∧ G.dst e ∉ V1) ∨ (G.src e ∉ V1 ∧ G.dst e ∈ V1)) (g : E → ℝ) :
    ∑ v ∈ V1ᶜ, ∑ e ∈ incident G v, g e = ∑ e, g e := by
  simp only [incident, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rcases hbip e with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [Finset.sum_eq_single (G.dst e)]
    · simp
    · intro b hb hne
      rw [if_neg]
      rintro (h | h)
      · exact (Finset.mem_compl.1 hb) (h ▸ h1)
      · exact hne h.symm
    · intro h; exact absurd (Finset.mem_compl.2 h2) h
  · rw [Finset.sum_eq_single (G.src e)]
    · simp
    · intro b hb hne
      rw [if_neg]
      rintro (h | h)
      · exact hne h.symm
      · exact (Finset.mem_compl.1 hb) (h ▸ h2)
    · intro h; exact absurd (Finset.mem_compl.2 h1) h

end main

end OSM17

open OfflineStochMatching.UnitPatience in
theorem solution {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : StochGraph V E) (V1 : Finset V)
    (hbip : ∀ e, (G.src e ∈ V1 ∧ G.dst e ∉ V1) ∨ (G.src e ∉ V1 ∧ G.dst e ∈ V1))
    (hunit : ∀ u ∈ V1, G.t u = 1) (y : E → ℝ) (hy : IsLPOptimal G y)
    (μ : (E → Bool) → ℝ) (hμ : IsDependentRounding G V1ᶜ y μ)
    (σ : V → List E) (hσ : IsWeightOrder G V1ᶜ σ) :
    (∀ Y : E → Bool, μ Y ≠ 0 → ∀ (P : E → Bool) (x : V),
        ((((V1ᶜ.biUnion fun v => (algProbes σ Y P v).toFinset).filter
            (· ∈ incident G x)).card : ℕ) : ℕ∞) ≤ G.t x ∧
        ((V1ᶜ.biUnion fun v => (algMatch σ Y P v).toFinset).filter
            (· ∈ incident G x)).card ≤ 1) ∧
    (1 - Real.exp (-1)) * ∑ v ∈ V1ᶜ, ∑ e ∈ incident G v, G.w e * G.p e * y e ≤
      algValue G V1ᶜ σ μ ∧
    ∀ π : Policy E, IsValidPolicy G π →
      (1 - Real.exp (-1)) * policyValue G π ≤ algValue G V1ᶜ σ μ := by
  have hB := OSM17.part_b G V1ᶜ y hy μ hμ σ hσ
  refine ⟨OSM17.part_a G V1 hbip hunit y hy μ hμ σ hσ, hB, fun π hπ => ?_⟩
  have h1 := OSM17.policy_le G π hπ y hy
  have h2 : ∑ e, G.w e * (y e * G.p e)
      = ∑ v ∈ V1ᶜ, ∑ e ∈ incident G v, G.w e * G.p e * y e := by
    rw [OSM17.sum_bip G V1 hbip (fun e => G.w e * G.p e * y e)]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    ring
  have hc : 0 ≤ 1 - Real.exp (-1) := by
    have := Real.exp_le_one_iff.2 (by norm_num : (-1:ℝ) ≤ 0)
    linarith
  calc (1 - Real.exp (-1)) * policyValue G π
      ≤ (1 - Real.exp (-1)) * ∑ v ∈ V1ᶜ, ∑ e ∈ incident G v, G.w e * G.p e * y e :=
        mul_le_mul_of_nonneg_left (h1.trans h2.le) hc
    _ ≤ algValue G V1ᶜ σ μ := hB
