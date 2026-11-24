-- Prove2me | solution 1 for PLIAG.theorem_4_2
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-24T21:09:26.477804+00:00
-- url     : https://prove2.me/submissions/f6dd59d0-ee1b-4392-b5f6-8ef15ff96d11

import Mathlib
import Definitions.Def_TensorAHPE_IsProperClosedConvex
import Definitions.Def_AubinLipschitz_effDom
import Definitions.Def_PLIAG_IsLegendre
import Definitions.Def_PLIAG_bregman
import Definitions.Def_PLIAG_Phi
import Definitions.Def_PLIAG_PhiStar
import Definitions.Def_PLIAG_optSet
import Definitions.Def_PLIAG_AssumptionB1
import Definitions.Def_PLIAG_AssumptionB2
import Definitions.Def_PLIAG_AssumptionB3
import Definitions.Def_PLIAG_AssumptionB4
import Definitions.Def_PLIAG_IsPLIAGSeq
import Definitions.Def_PLIAG_Lmax
import Definitions.Def_PLIAG_alpha0
import Definitions.Def_PLIAG_Gamma
import Definitions.Def_PLIAG_Delta
import Theorems.Thm_PLIAG_lyapunov_recursion
import Theorems.Thm_PLIAG_proposition_3_1
import Theorems.Thm_PLIAG_condition_4_4
import Theorems.Thm_PLIAG_lemma_4_2
import Theorems.Thm_PLIAG_eq_C_15

open Filter Topology

namespace PLIAG_T42
open PLIAG

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

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

lemma bregman_top {d : ℕ} (w : EuclideanSpace ℝ (Fin d) → EReal) (y x : EuclideanSpace ℝ (Fin d))
    (hy : w y = ⊤) : bregman w y x = ⊤ := by
  unfold bregman; rw [hy]; exact EReal.top_sub_coe _

lemma bregman_real {d : ℕ} (w : EuclideanSpace ℝ (Fin d) → EReal) (y x : EuclideanSpace ℝ (Fin d))
    (hy : w y ≠ ⊤) (hy' : w y ≠ ⊥) : ∃ r : ℝ, bregman w y x = (r : EReal) := by
  unfold bregman
  refine ⟨(w y).toReal - ((w x).toReal + inner ℝ (gradient (fun z => (w z).toReal) x) (y - x)), ?_⟩
  conv_lhs => rw [← EReal.coe_toReal hy hy']
  rfl

lemma slope_le {g : ℝ → ℝ} {c b : ℝ} (hg : HasDerivAt g c 0)
    (h : ∀ t ∈ Set.Ioo (0:ℝ) 1, g t - g 0 ≤ b * t) : c ≤ b := by
  have ht := hg.tendsto_slope_zero_right
  apply le_of_tendsto ht
  have : ∀ᶠ t in 𝓝[>] (0:ℝ), t ∈ Set.Ioo (0:ℝ) 1 := Ioo_mem_nhdsGT (by norm_num)
  filter_upwards [this] with t htt
  have := h t htt
  simp only [zero_add, smul_eq_mul]
  rw [inv_mul_le_iff₀ htt.1]; linarith

lemma line_deriv {φ : E → ℝ} {p : E} (hd : DifferentiableAt ℝ φ p) (v : E) :
    HasDerivAt (fun t : ℝ => φ (p + t • v)) (fderiv ℝ φ p v) 0 := by
  have hl : HasDerivAt (fun t : ℝ => p + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add p
  have h2 : HasFDerivAt φ (fderiv ℝ φ p) ((fun t : ℝ => p + t • v) 0) := by
    simpa using hd.hasFDerivAt
  exact h2.comp_hasDerivAt (0:ℝ) hl

lemma combo_eq (a b : E) (t : ℝ) : (1 - t) • a + t • b = a + t • (b - a) := by
  rw [smul_sub, sub_smul, one_smul]; abel

lemma grad_ineq {S : Set E} {φ : E → ℝ} (hφ : ConvexOn ℝ S φ) {p z : E} (hp : p ∈ S)
    (hz : z ∈ S) (hd : DifferentiableAt ℝ φ p) : φ p + fderiv ℝ φ p (z - p) ≤ φ z := by
  have := slope_le (b := φ z - φ p) (line_deriv hd (z - p)) (by
    intro t ht
    have h1 := hφ.2 hp hz (show (0:ℝ) ≤ 1 - t by linarith [ht.2]) ht.1.le
      (show 1 - t + t = 1 by ring)
    rw [combo_eq] at h1; simp only [smul_eq_mul] at h1
    simp only [zero_smul, add_zero]; nlinarith)
  linarith

lemma inner_grad [CompleteSpace E] (φ : E → ℝ) (p v : E) :
    inner ℝ (gradient φ p) v = fderiv ℝ φ p v := by
  simp [gradient, InnerProductSpace.toDual_symm_apply]

lemma ereal_convOn (F : E → EReal) (hbot : ∀ x, F x ≠ ⊥)
    (hc : Convex ℝ {p : E × ℝ | F p.1 ≤ (p.2 : EReal)}) :
    ConvexOn ℝ (AubinLipschitz.effDom F) (fun x => (F x).toReal) := by
  have key : ∀ a ∈ AubinLipschitz.effDom F, ∀ b ∈ AubinLipschitz.effDom F, ∀ θ η : ℝ,
      0 ≤ θ → 0 ≤ η → θ + η = 1 →
      F (θ • a + η • b) ≤ ((θ * (F a).toReal + η * (F b).toReal : ℝ) : EReal) := by
    intro a ha b hb θ η hθ hη hθη
    have h1 : (a, (F a).toReal) ∈ {p : E × ℝ | F p.1 ≤ (p.2 : EReal)} := by
      show F a ≤ ((F a).toReal : EReal); rw [EReal.coe_toReal ha (hbot a)]
    have h2 : (b, (F b).toReal) ∈ {p : E × ℝ | F p.1 ≤ (p.2 : EReal)} := by
      show F b ≤ ((F b).toReal : EReal); rw [EReal.coe_toReal hb (hbot b)]
    have := hc h1 h2 hθ hη hθη
    simpa using this
  refine ⟨?_, ?_⟩
  · intro a ha b hb θ η hθ hη hθη
    exact ne_top_of_le_ne_top (EReal.coe_ne_top _) (key a ha b hb θ η hθ hη hθη)
  · intro a ha b hb θ η hθ hη hθη
    have := EReal.toReal_le_toReal (key a ha b hb θ η hθ hη hθη) (hbot _) (EReal.coe_ne_top _)
    rw [EReal.toReal_coe] at this
    simpa using this

/-- Bregman distances to an interior point are nonnegative (gradient inequality). -/
lemma bregman_nonneg {d : ℕ} (w : EuclideanSpace ℝ (Fin d) → EReal) (hw : IsLegendre w)
    {y : EuclideanSpace ℝ (Fin d)} (hy : y ∈ interior (AubinLipschitz.effDom w))
    (z : EuclideanSpace ℝ (Fin d)) : 0 ≤ bregman w z y := by
  by_cases hz : w z = ⊤
  · rw [bregman_top w z y hz]; exact le_top
  · have hconv := ereal_convOn w hw.1.1 hw.1.2.2.2
    have hd : DifferentiableAt ℝ (fun x => (w x).toReal) y :=
      (hw.2.2.1 y hy).differentiableAt (isOpen_interior.mem_nhds hy)
    have hg := grad_ineq hconv (interior_subset hy) (show z ∈ AubinLipschitz.effDom w from hz) hd
    rw [← inner_grad] at hg
    unfold bregman
    rw [← EReal.coe_toReal hz (hw.1.1 z), ← EReal.coe_sub]
    exact_mod_cast (by linarith)

lemma coe_mul_mono (g : EReal) (hg : 0 ≤ g) (u v : ℝ) (hu : 0 < u) (huv : u ≤ v) :
    (u : EReal) * g ≤ (v : EReal) * g := by
  induction g with
  | bot => exact absurd hg (by simp)
  | top => rw [EReal.coe_mul_top_of_pos hu, EReal.coe_mul_top_of_pos (by linarith)]
  | coe r =>
    have : (0:ℝ) ≤ r := by exact_mod_cast hg
    norm_cast; nlinarith

end PLIAG_T42

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
    (∀ k : ℕ, Gamma w f h α (x k) ≤
        (((1 / (1 + α * μ)) ^ k : ℝ) : EReal) * Gamma w f h α (x 0)) ∧
    (∀ k : ℕ, Phi f h (x k) - PhiStar w f h ≤
        (((1 / (1 + α * μ)) ^ k : ℝ) : EReal) * Gamma w f h α (x 0)) ∧
    (∀ k : ℕ, (⨅ z ∈ optSet w f h, bregman w z (x k)) ≤
        (α : EReal) * Gamma w f h α (x 0) * (((1 / (1 + α * μ)) ^ (k + 1) : ℝ) : EReal)) ∧
    (α = alpha0 μ (Lmax Lc J) ℓ τ → ∀ k : ℕ, Gamma w f h α (x k) ≤
        (((1 - 1 / ((ℓ (τ + 1) * (Lmax Lc J / μ) + 1) * ((τ : ℝ) + 1))) ^ k : ℝ) : EReal) *
          Gamma w f h α (x 0)) := by
  have hμ : 0 < μ := hB3.1
  have hLc : ∀ n, 0 < Lc n := fun n => (hB1 n).2.2.2.1
  have hLpos : 0 < Lmax Lc J := lt_of_lt_of_le
    (Finset.sum_pos (fun i _ => hLc i) (hJ 0)) (PLIAG_T42.sum_le_Lmax Lc J hLc 0)
  have hℓτ : 1 ≤ ℓ (τ + 1) := hℓ1 ▸ hℓm (by omega)
  have h44 := condition_4_4 μ (Lmax Lc J) ℓ τ α hμ hLpos hℓm hℓ1 hα hαle
  set a : ℝ := 1 / (1 + α * μ) with ha
  have hapos : 0 < a := by positivity
  have ha1 : a < 1 := by
    rw [ha, div_lt_one (by positivity)]; nlinarith
  -- step size bound from (4.4)
  have hstep : α * (Lmax Lc J * ℓ (τ + 1) * ((τ : ℝ) + 1)) ≤ 1 := by
    have hgb := PLIAG_T42.geom_bound a τ hapos ha1
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
      · have hS := PLIAG_T42.sum_le_Lmax Lc J hLc n
        have hSpos : 0 < ∑ j ∈ J n, Lc j := Finset.sum_pos (fun i _ => hLc i) (hJ n)
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
                have : (0:ℝ) ≤ τ := Nat.cast_nonneg τ
                linarith
            _ ≤ 1 := hstep
        exact (proposition_3_1 w f h Lc ℓ τ J τd α x n hw hh hXne hXc hJ hA0 hB1 hℓm hℓ1 hB4
          hB2.1 hα h0 hp (fun j hj => ih j (Nat.lt_succ_of_le hj))).2 (x (n + 1))
          (hx.2 n).1 (hx.2 n).2
  have hwbot : ∀ y, w y ≠ ⊥ := hw.1.1
  have hfbot : ∀ n y, f n y ≠ ⊥ := fun n => (hB1 n).1.1
  have hhbot : ∀ y, h y ≠ ⊥ := hh.1
  have hPhibot : ∀ y, Phi f h y ≠ ⊥ := fun y =>
    EReal.add_ne_bot_iff.2 ⟨PLIAG_T42.sum_ne_bot _ _ (fun n => hfbot n y), hhbot y⟩
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
      refine (EReal.add_ne_top_iff_ne_top₂ (PLIAG_T42.sum_ne_bot _ _ (fun n => hfbot n q))
        (hhbot q)).2 ⟨?_, hqh⟩
      exact PLIAG_T42.sum_ne_top _ _ (fun n => hfbot n q)
        (fun n _ => (hB1 n).2.1 (interior_subset hqw))
    exact ne_top_of_le_ne_top hq hle
  set p0 : ℝ := (PhiStar w f h).toReal
  have hp0 : PhiStar w f h = (p0 : EReal) := (EReal.coe_toReal hPStop hPSbot).symm
  -- nonnegativity
  have hPhige : ∀ n, PhiStar w f h ≤ Phi f h (x n) := fun n =>
    iInf₂_le (f := fun y (_ : y ∈ closure (AubinLipschitz.effDom w)) => Phi f h y) (x n)
      (subset_closure (hintdom n))
  have hAnn : ∀ n, 0 ≤ Phi f h (x n) - PhiStar w f h := fun n =>
    (EReal.sub_nonneg (Or.inr hPStop) (Or.inr hPSbot)).2 (hPhige n)
  have hInn : ∀ n, 0 ≤ ⨅ z ∈ optSet w f h, bregman w z (x n) := fun n =>
    le_iInf₂ (fun z _ => PLIAG_T42.bregman_nonneg w hw (hint n) z)
  have hcInn : ∀ n, 0 ≤ ((1 / α : ℝ) : EReal) * ⨅ z ∈ optSet w f h, bregman w z (x n) :=
    fun n => EReal.mul_nonneg (by exact_mod_cast (by positivity : (0:ℝ) ≤ 1 / α)) (hInn n)
  have hΓnn : ∀ n, 0 ≤ Gamma w f h α (x n) := fun n => add_nonneg (hAnn n) (hcInn n)
  -- the increments
  have hDr : ∀ j, ∃ r : ℝ, bregman w (x (j + 1)) (x j) = (r : EReal) := fun j =>
    PLIAG_T42.bregman_real w _ _ (hintdom _) (hwbot _)
  choose D hD using hDr
  have hDnn : ∀ j, 0 ≤ D j := fun j => by
    have := PLIAG_T42.bregman_nonneg w hw (hint j) (x (j + 1))
    rw [hD j] at this; exact_mod_cast this
  have hΔ : ∀ k, Delta w Lc J ℓ τ x k =
      ((Lmax Lc J * ℓ (τ + 1) * ∑ j ∈ Finset.Icc (k - τ) k, D j : ℝ) : EReal) := by
    intro k
    unfold Delta
    simp only [hD]
    rw [EReal.coe_mul _ (∑ j ∈ Finset.Icc (k - τ) k, D j), PLIAG_T42.coe_sum]
  have hrec := lyapunov_recursion w f h Lc ℓ τ J τd μ α x hw hh ⟨z0, hz0⟩ hXc hJ hA0 hB1 hB2 hB3
    hℓm hℓ1 hB4 hα hαle hx
  -- (4.7)
  have h47 : ∀ k, Gamma w f h α (x k) ≤ ((a ^ k : ℝ) : EReal) * Gamma w f h α (x 0) := by
    by_cases hG0 : Gamma w f h α (x 0) = ⊤
    · intro k; rw [hG0, EReal.coe_mul_top_of_pos (pow_pos hapos k)]; exact le_top
    -- all Γ finite
    have hfin : ∀ n, Gamma w f h α (x n) ≠ ⊤ := by
      intro n
      induction n with
      | zero => exact hG0
      | succ n ih =>
        have hr := hrec n
        rw [← EReal.coe_toReal ih (ne_bot_of_le_ne_bot (by simp) (hΓnn n)), hD n, hΔ n] at hr
        refine ne_top_of_le_ne_top ?_ hr
        rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_sub, ← EReal.coe_add]
        exact EReal.coe_ne_top _
    set V : ℕ → ℝ := fun n => (Gamma w f h α (x n)).toReal with hVdef
    have hV : ∀ n, Gamma w f h α (x n) = (V n : EReal) := fun n =>
      (EReal.coe_toReal (hfin n) (ne_bot_of_le_ne_bot (by simp) (hΓnn n))).symm
    have hVnn : ∀ n, 0 ≤ V n := fun n => by
      have := hΓnn n; rw [hV n] at this; exact_mod_cast this
    have hrecR : ∀ k, V (k + 1) ≤ a * V k - (1 / α) * D k +
        Lmax Lc J * ℓ (τ + 1) * ∑ j ∈ Finset.Icc (k - τ) k, D j := by
      intro k
      have hr := hrec k
      rw [hV, hV, hD k, hΔ k] at hr
      exact_mod_cast hr
    have hL42 := lemma_4_2 V D a (1 / α) (Lmax Lc J * ℓ (τ + 1)) τ hVnn hDnn hapos ha1
      (by positivity) (by nlinarith) (fun k => by
        have := hrecR k; linarith) h44
    intro k
    rw [hV, hV]
    exact_mod_cast hL42 k
  refine ⟨h47, ?_, ?_, ?_⟩
  · -- (4.8)
    intro k
    calc Phi f h (x k) - PhiStar w f h ≤ Gamma w f h α (x k) :=
          le_add_of_nonneg_right (hcInn k)
      _ ≤ _ := h47 k
  · -- (4.9)
    intro k
    by_cases hG0 : Gamma w f h α (x 0) = ⊤
    · rw [hG0, EReal.coe_mul_top_of_pos hα, EReal.top_mul_coe_of_pos (pow_pos hapos _)]
      exact le_top
    set g0 : ℝ := (Gamma w f h α (x 0)).toReal
    have hg0 : Gamma w f h α (x 0) = (g0 : EReal) :=
      (EReal.coe_toReal hG0 (ne_bot_of_le_ne_bot (by simp) (hΓnn 0))).symm
    have hg0nn : 0 ≤ g0 := by have := hΓnn 0; rw [hg0] at this; exact_mod_cast this
    have hk := h47 k
    have hB3k := hB3.2 (x k) (hint k)
    have hIk := hInn k
    rw [hg0] at hk ⊢
    unfold Gamma at hk
    rw [← EReal.coe_mul, ← EReal.coe_mul] at *
    generalize (⨅ z ∈ optSet w f h, bregman w z (x k)) = I at hk hB3k hIk ⊢
    generalize Phi f h (x k) - PhiStar w f h = A at hk hB3k
    induction I with
    | bot => exact bot_le
    | top =>
      exfalso
      rw [EReal.coe_mul_top_of_pos hμ, top_le_iff] at hB3k
      rw [hB3k, EReal.coe_mul_top_of_pos (by positivity : (0:ℝ) < 1 / α), EReal.top_add_top] at hk
      exact EReal.coe_ne_top _ (top_le_iff.1 hk)
    | coe r =>
      induction A with
      | bot =>
        exfalso
        rw [le_bot_iff] at hB3k
        exact EReal.coe_ne_bot _ (by exact_mod_cast hB3k)
      | top =>
        exfalso
        rw [← EReal.coe_mul, EReal.top_add_coe] at hk
        exact EReal.coe_ne_top _ (top_le_iff.1 hk)
      | coe s =>
        norm_cast at hk hB3k hIk ⊢
        have hak : a ^ (k + 1) = a ^ k * a := pow_succ a k
        have hαa : α * a * (1 + α * μ) = α := by rw [ha]; field_simp
        have h1 : (1 + α * μ) * r ≤ α * (a ^ k * g0) := by
          have : 1 / α * r * α = r := by field_simp
          nlinarith
        have hpos : 0 < 1 + α * μ := by positivity
        rw [hak]
        have : r ≤ α * (a ^ k * g0) / (1 + α * μ) := by
          rw [le_div_iff₀ hpos]; linarith
        calc r ≤ α * (a ^ k * g0) / (1 + α * μ) := this
          _ = α * g0 * (a ^ k * a) := by rw [ha]; field_simp
  · -- (4.10)
    intro hα0 k
    have hC := (eq_C_15 μ (Lmax Lc J) ℓ τ hμ hLpos hℓm hℓ1).2.2.2 k
    rw [← hα0, ← ha, add_comm (1 : ℝ) (ℓ (τ + 1) * (Lmax Lc J / μ))] at hC
    exact (h47 k).trans
      (PLIAG_T42.coe_mul_mono _ (hΓnn 0) _ _ (pow_pos hapos k) hC)
