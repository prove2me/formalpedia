-- Prove2me | solution 1 for PLIAG.lyapunov_recursion
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-24T21:00:08.935497+00:00
-- url     : https://prove2.me/submissions/1323fd8d-8f47-4570-a865-7537a35d5319

import Mathlib
import Definitions.Def_TensorAHPE_IsProperClosedConvex
import Definitions.Def_AubinLipschitz_effDom
import Definitions.Def_PLIAG_IsLegendre
import Definitions.Def_PLIAG_bregman
import Definitions.Def_PLIAG_optSet
import Definitions.Def_PLIAG_AssumptionB1
import Definitions.Def_PLIAG_AssumptionB2
import Definitions.Def_PLIAG_AssumptionB3
import Definitions.Def_PLIAG_AssumptionB4
import Definitions.Def_PLIAG_IsPLIAGSeq
import Definitions.Def_PLIAG_Lmax
import Definitions.Def_PLIAG_Delta
import Definitions.Def_PLIAG_alpha0
import Definitions.Def_PLIAG_Gamma
import Theorems.Thm_PLIAG_lemma_4_1
import Theorems.Thm_PLIAG_proposition_3_1
import Theorems.Thm_PLIAG_condition_4_4

namespace PLIAG_LR
open PLIAG

lemma sum_ne_bot {ι : Type*} (s : Finset ι) (g : ι → EReal) (hg : ∀ i, g i ≠ ⊥) :
    ∑ i ∈ s, g i ≠ ⊥ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact EReal.add_ne_bot_iff.2 ⟨hg a, ih⟩

lemma sum_ne_top {ι : Type*} (s : Finset ι) (g : ι → EReal) (hg : ∀ i, g i ≠ ⊥)
    (hg' : ∀ i ∈ s, g i ≠ ⊤) : ∑ i ∈ s, g i ≠ ⊤ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have h1 := ih (fun i hi => hg' i (Finset.mem_insert_of_mem hi))
    exact (EReal.add_ne_top_iff_ne_top₂ (hg a) (sum_ne_bot s g hg)).2
      ⟨hg' a (Finset.mem_insert_self a s), h1⟩

lemma geom_bound (a : ℝ) (n : ℕ) (ha0 : 0 < a) (ha1 : a < 1) :
    ((n : ℝ) + 1) * a ^ n * (1 - a) ≤ 1 - a ^ (n + 1) := by
  rw [← mul_neg_geom_sum]
  have hs : (Finset.range (n + 1)).card • a ^ n ≤ ∑ i ∈ Finset.range (n + 1), a ^ i :=
    Finset.card_nsmul_le_sum _ _ _ (fun i hi =>
      pow_le_pow_of_le_one ha0.le ha1.le (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)))
  rw [Finset.card_range, nsmul_eq_mul] at hs
  push_cast at hs
  have h1 : 0 ≤ 1 - a := by linarith
  nlinarith

lemma sum_le_Lmax {N : ℕ} (Lc : Fin N → ℝ) (J : ℕ → Finset (Fin N)) (hpos : ∀ n, 0 < Lc n)
    (k : ℕ) : ∑ j ∈ J k, Lc j ≤ Lmax Lc J := by
  apply le_ciSup (f := fun k => ∑ j ∈ J k, Lc j) _ k
  refine ⟨∑ j, Lc j, ?_⟩
  rintro _ ⟨m, rfl⟩
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun i _ _ => (hpos i).le)

lemma coe_sum {ι : Type*} (s : Finset ι) (g : ι → ℝ) :
    ((∑ i ∈ s, g i : ℝ) : EReal) = ∑ i ∈ s, (g i : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, EReal.coe_add, ih]

lemma xreal_shift (X : EReal) (s t : ℝ) : X + ((t - s : ℝ) : EReal) = X - (s : EReal) + (t : EReal) := by
  induction X with
  | bot => simp
  | top => rw [EReal.top_sub_coe, EReal.top_add_coe, EReal.top_add_coe]
  | coe r => norm_cast; ring

lemma bregman_top {d : ℕ} (w : EuclideanSpace ℝ (Fin d) → EReal) (y x : EuclideanSpace ℝ (Fin d))
    (hy : w y = ⊤) : bregman w y x = ⊤ := by
  unfold bregman; rw [hy]; exact EReal.top_sub_coe _

lemma bregman_real {d : ℕ} (w : EuclideanSpace ℝ (Fin d) → EReal) (y x : EuclideanSpace ℝ (Fin d))
    (hy : w y ≠ ⊤) (hy' : w y ≠ ⊥) : ∃ r : ℝ, bregman w y x = (r : EReal) := by
  unfold bregman
  refine ⟨(w y).toReal - ((w x).toReal + inner ℝ (gradient (fun z => (w z).toReal) x) (y - x)), ?_⟩
  conv_lhs => rw [← EReal.coe_toReal hy hy']
  rfl

end PLIAG_LR

open PLIAG in
theorem solution {d N : ℕ} (w : EuclideanSpace ℝ (Fin d) → EReal)
    (f : Fin N → EuclideanSpace ℝ (Fin d) → EReal) (h : EuclideanSpace ℝ (Fin d) → EReal)
    (Lc : Fin N → ℝ) (ℓ : ℕ → ℝ) (τ : ℕ) (J : ℕ → Finset (Fin N)) (τd : ℕ → Fin N → ℕ)
    (μ α : ℝ) (x : ℕ → EuclideanSpace ℝ (Fin d))
    (hw : IsLegendre w) (hh : TensorAHPE.IsProperClosedConvex h)
    (hXne : (optSet w f h).Nonempty) (hXc : IsCompact (optSet w f h))
    (hJ : ∀ k, (J k).Nonempty) (hA0 : ∀ k n, τd k n ≤ τ)
    (hB1 : AssumptionB1 w f Lc) (hB2 : AssumptionB2 w h) (hB3 : AssumptionB3 w f h μ)
    (hℓm : Monotone ℓ) (hℓ1 : ℓ 1 = 1) (hB4 : 0 < τ → AssumptionB4 w ℓ)
    (hα : 0 < α) (hαle : α ≤ alpha0 μ (Lmax Lc J) ℓ τ)
    (hx : IsPLIAGSeq w f h J τd α x) :
    ∀ k : ℕ, Gamma w f h α (x (k + 1)) ≤
      ((1 / (1 + α * μ) : ℝ) : EReal) * Gamma w f h α (x k)
        - ((1 / α : ℝ) : EReal) * bregman w (x (k + 1)) (x k)
        + Delta w Lc J ℓ τ x k := by
  have hμ : 0 < μ := hB3.1
  have hLc : ∀ n, 0 < Lc n := fun n => (hB1 n).2.2.2.1
  have hLpos : 0 < Lmax Lc J := lt_of_lt_of_le
    (Finset.sum_pos (fun i _ => hLc i) (hJ 0)) (PLIAG_LR.sum_le_Lmax Lc J hLc 0)
  have hℓτ : 1 ≤ ℓ (τ + 1) := hℓ1 ▸ hℓm (by omega)
  -- step size bound from (4.4)
  have hstep : α * (Lmax Lc J * ℓ (τ + 1) * ((τ : ℝ) + 1)) ≤ 1 := by
    have h44 := condition_4_4 μ (Lmax Lc J) ℓ τ α hμ hLpos hℓm hℓ1 hα hαle
    set a : ℝ := 1 / (1 + α * μ) with ha
    have hapos : 0 < a := by positivity
    have ha1 : a < 1 := by
      rw [ha, div_lt_one (by positivity)]; nlinarith
    have hgb := PLIAG_LR.geom_bound a τ hapos ha1
    have hpow : 0 < a ^ τ := pow_pos hapos τ
    have h1a : 0 < 1 - a := by linarith
    have hE : ((τ : ℝ) + 1) * (1 - a) ≤ (1 - a ^ (τ + 1)) / a ^ τ := by
      rw [le_div_iff₀ hpow]; nlinarith
    have hLl : 0 < Lmax Lc J * ℓ (τ + 1) := by nlinarith
    have hmain : Lmax Lc J * ℓ (τ + 1) * ((τ : ℝ) + 1) ≤
        Lmax Lc J * ℓ (τ + 1) / (1 - a) * ((1 - a ^ (τ + 1)) / a ^ τ) := by
      calc Lmax Lc J * ℓ (τ + 1) * ((τ : ℝ) + 1)
          = Lmax Lc J * ℓ (τ + 1) / (1 - a) * (((τ : ℝ) + 1) * (1 - a)) := by
            field_simp
        _ ≤ _ := by gcongr
    calc α * (Lmax Lc J * ℓ (τ + 1) * ((τ : ℝ) + 1)) ≤ α * (1 / α) := by
          gcongr; exact le_trans hmain h44
      _ = 1 := by field_simp
  -- all iterates are interior (Proposition 3.1)
  have hint : ∀ n, x n ∈ interior (AubinLipschitz.effDom w) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases n with _ | n
      · exact hx.1
      · have hS := PLIAG_LR.sum_le_Lmax Lc J hLc n
        have hSpos : 0 < ∑ j ∈ J n, Lc j := Finset.sum_pos (fun i _ => hLc i) (hJ n)
        have hτ1 : (1 : ℝ) ≤ (τ : ℝ) + 1 := by have : (0:ℝ) ≤ τ := Nat.cast_nonneg τ; linarith
        have h0 : τ = 0 → α ≤ 1 / ∑ j ∈ J n, Lc j := by
          intro hτ0
          rw [le_div_iff₀ hSpos]
          rw [hτ0] at hstep
          simp only [zero_add, hℓ1, Nat.cast_zero, mul_one] at hstep
          nlinarith
        have hp : 0 < τ → α ≤ 1 / (ℓ 2 * ∑ j ∈ J n, Lc j) := by
          intro hτp
          have hl2 : ℓ 2 ≤ ℓ (τ + 1) := hℓm (by omega)
          have hl2' : 1 ≤ ℓ 2 := hℓ1 ▸ hℓm (by omega)
          rw [le_div_iff₀ (by positivity)]
          calc α * (ℓ 2 * ∑ j ∈ J n, Lc j) ≤ α * (Lmax Lc J * ℓ (τ + 1) * 1) := by
                apply mul_le_mul_of_nonneg_left _ hα.le
                rw [mul_one, mul_comm (Lmax Lc J)]
                exact mul_le_mul hl2 hS hSpos.le (by linarith)
            _ ≤ α * (Lmax Lc J * ℓ (τ + 1) * ((τ : ℝ) + 1)) := by
                gcongr
            _ ≤ 1 := hstep
        exact (proposition_3_1 w f h Lc ℓ τ J τd α x n hw hh hXne hXc hJ hA0 hB1 hℓm hℓ1 hB4
          hB2.1 hα h0 hp (fun j hj => ih j (Nat.lt_succ_of_le hj))).2 (x (n + 1))
          (hx.2 n).1 (hx.2 n).2
  intro k
  set c : ℝ := 1 / α with hc
  have hcpos : 0 < c := by positivity
  set a : ℝ := 1 / (1 + α * μ) with ha
  have hapos : 0 < a := by positivity
  have hwbot : ∀ y, w y ≠ ⊥ := hw.1.1
  have hfbot : ∀ n y, f n y ≠ ⊥ := fun n => (hB1 n).1.1
  have hhbot : ∀ y, h y ≠ ⊥ := hh.1
  have hPhibot : ∀ y, Phi f h y ≠ ⊥ := fun y =>
    EReal.add_ne_bot_iff.2 ⟨PLIAG_LR.sum_ne_bot _ _ (fun n => hfbot n y), hhbot y⟩
  have hintdom : ∀ n, x n ∈ AubinLipschitz.effDom w := fun n => interior_subset (hint n)
  obtain ⟨z0, hz0⟩ := hXne
  obtain ⟨q, hqh, hqw⟩ := hB2.1
  have hPSbot : PhiStar w f h ≠ ⊥ := by rw [← hz0.2]; exact hPhibot z0
  have hPStop : PhiStar w f h ≠ ⊤ := by
    have hle : PhiStar w f h ≤ Phi f h q :=
      iInf₂_le (f := fun y (_ : y ∈ closure (AubinLipschitz.effDom w)) => Phi f h y) q
        (subset_closure (interior_subset hqw))
    have hq : Phi f h q ≠ ⊤ := by
      unfold Phi
      refine (EReal.add_ne_top_iff_ne_top₂ (PLIAG_LR.sum_ne_bot _ _ (fun n => hfbot n q))
        (hhbot q)).2 ⟨?_, hqh⟩
      exact PLIAG_LR.sum_ne_top _ _ (fun n => hfbot n q)
        (fun n _ => (hB1 n).2.1 (interior_subset hqw))
    exact ne_top_of_le_ne_top hq hle
  set p0 : ℝ := (PhiStar w f h).toReal
  have hp0 : PhiStar w f h = (p0 : EReal) := (EReal.coe_toReal hPStop hPSbot).symm
  obtain ⟨d10, hd10⟩ := PLIAG_LR.bregman_real w (x (k + 1)) (x k) (hintdom (k + 1)) (hwbot _)
  have hΔ : ∃ δ : ℝ, Delta w Lc J ℓ τ x k = (δ : EReal) := by
    have : ∀ j, ∃ r : ℝ, bregman w (x (j + 1)) (x j) = (r : EReal) := fun j =>
      PLIAG_LR.bregman_real w _ _ (hintdom _) (hwbot _)
    choose r hr using this
    refine ⟨Lmax Lc J * ℓ (τ + 1) * ∑ j ∈ Finset.Icc (k - τ) k, r j, ?_⟩
    unfold Delta
    simp only [hr]
    rw [EReal.coe_mul _ (∑ j ∈ Finset.Icc (k - τ) k, r j), PLIAG_LR.coe_sum]
  obtain ⟨δ, hδ⟩ := hΔ
  set R : ℝ := δ - c * d10 with hR
  have hL41 := lemma_4_1 w f h Lc ℓ τ J τd α x k hw hh ⟨z0, hz0⟩ hXc hJ hA0 hB1 hB2 hℓm hℓ1
    hB4 hα (fun j _ => hint j) (hx.2 k).1 (hx.2 k).2
  have hAB : ∀ z ∈ optSet w f h,
      Gamma w f h α (x (k + 1)) ≤ (c : EReal) * bregman w z (x k) + (R : EReal) := by
    intro z hz
    by_cases hwz : w z = ⊤
    · rw [PLIAG_LR.bregman_top w z (x k) hwz, EReal.coe_mul_top_of_pos hcpos, EReal.top_add_coe]
      exact le_top
    · obtain ⟨D0, hD0⟩ := PLIAG_LR.bregman_real w z (x k) hwz (hwbot z)
      obtain ⟨D1, hD1⟩ := PLIAG_LR.bregman_real w z (x (k + 1)) hwz (hwbot z)
      have h1 := hL41 z hwz
      rw [hz.2, hp0, hD0, hD1, hd10, hδ] at h1
      have hrhs : ((p0 : EReal) + (c : EReal) * D0 - (c : EReal) * D1 - (c : EReal) * d10 + δ)
          = ((p0 + c * D0 - c * D1 - c * d10 + δ : ℝ) : EReal) := by norm_cast
      rw [hrhs] at h1
      have hPtop : Phi f h (x (k + 1)) ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) h1
      set φ1 : ℝ := (Phi f h (x (k + 1))).toReal
      have hφ1 : Phi f h (x (k + 1)) = (φ1 : EReal) := (EReal.coe_toReal hPtop (hPhibot _)).symm
      rw [hφ1, EReal.coe_le_coe_iff] at h1
      rw [hD0]
      unfold Gamma
      rw [hφ1, hp0]
      calc (φ1 : EReal) - p0 + (c : EReal) * ⨅ z ∈ optSet w f h, bregman w z (x (k + 1))
          ≤ (φ1 : EReal) - p0 + (c : EReal) * D1 := by
            gcongr
            rw [← hD1]
            exact iInf₂_le (f := fun z (_ : z ∈ optSet w f h) => bregman w z (x (k + 1))) z hz
        _ ≤ (c : EReal) * D0 + R := by
            norm_cast
            rw [hR]; linarith
  have hC : Gamma w f h α (x (k + 1)) ≤
      (c : EReal) * (⨅ z ∈ optSet w f h, bregman w z (x k)) + (R : EReal) := by
    have key : ∀ t : EReal, Gamma w f h α (x (k + 1)) ≤ (c : EReal) * t + R ↔
        (Gamma w f h α (x (k + 1)) - R) / c ≤ t := by
      intro t
      rw [EReal.div_le_iff_le_mul (by exact_mod_cast hcpos) (EReal.coe_ne_top c),
        EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot R)) (Or.inl (EReal.coe_ne_top R))]
    rw [key]
    exact le_iInf₂ (fun z hz => (key _).1 (hAB z hz))
  have hD : (c : EReal) * (⨅ z ∈ optSet w f h, bregman w z (x k)) ≤
      (a : EReal) * Gamma w f h α (x k) := by
    have hB3k := hB3.2 (x k) (hint k)
    unfold Gamma
    rw [hp0] at hB3k ⊢
    generalize (⨅ z ∈ optSet w f h, bregman w z (x k)) = I at hB3k ⊢
    generalize Phi f h (x k) - (p0 : EReal) = A at hB3k ⊢
    induction I with
    | bot => rw [EReal.coe_mul_bot_of_pos hcpos]; exact bot_le
    | top =>
      rw [EReal.coe_mul_top_of_pos hμ, top_le_iff] at hB3k
      rw [hB3k, EReal.coe_mul_top_of_pos hcpos, EReal.top_add_top,
        EReal.coe_mul_top_of_pos hapos]
    | coe r =>
      induction A with
      | bot =>
        exfalso
        rw [le_bot_iff] at hB3k
        exact EReal.coe_ne_bot _ (by exact_mod_cast hB3k)
      | top =>
        rw [← EReal.coe_mul, EReal.top_add_coe, EReal.coe_mul_top_of_pos hapos]
        exact le_top
      | coe s =>
        norm_cast at hB3k ⊢
        have heq : a * (μ * r + c * r) = c * r := by
          rw [ha, hc]; field_simp; ring
        calc c * r = a * (μ * r + c * r) := heq.symm
          _ ≤ a * (s + c * r) := by gcongr
  calc Gamma w f h α (x (k + 1))
      ≤ (c : EReal) * (⨅ z ∈ optSet w f h, bregman w z (x k)) + (R : EReal) := hC
    _ ≤ (a : EReal) * Gamma w f h α (x k) + (R : EReal) := add_le_add hD le_rfl
    _ = _ := by
      rw [hd10, hδ, ← EReal.coe_mul, hR, PLIAG_LR.xreal_shift]
