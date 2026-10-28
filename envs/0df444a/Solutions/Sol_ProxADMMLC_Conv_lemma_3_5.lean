-- Prove2me | solution 1 for ProxADMMLC.Conv.lemma_3_5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T22:59:19.45314+00:00
-- url     : https://prove2.me/submissions/91cc9c27-adf0-4963-86f9-92a74e58ad93

import Mathlib
import Definitions.Def_ProxADMMLC_Conv_Setting

namespace Aux_PALC35
open ProxADMMLC.Conv

lemma vi {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (φ : V → ℝ) (C : Set V)
    (hC : Convex ℝ C) (x0 x : V) (hx0 : x0 ∈ C) (hx : x ∈ C) (D : V →L[ℝ] ℝ)
    (hD : HasFDerivAt φ D x0) (hmin : ∀ w ∈ C, φ x0 ≤ φ w) : 0 ≤ D (x - x0) :=
  (isMinOn_iff.2 hmin).localize.hasFDerivWithinAt_nonneg hD.hasFDerivWithinAt
    (sub_mem_posTangentConeAt_of_segment_subset (hC.segment_subset hx0 hx))

lemma grad_apply {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (f : V → ℝ) (x h : V) : fderiv ℝ f x h = inner ℝ (gradient f x) h := by
  rw [gradient, InnerProductSpace.toDual_symm_apply]

lemma D1_eval {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (f : V → ℝ) (hfd : Differentiable ℝ f) (p : ℝ) (z x0 : V) :
    ∃ D : V →L[ℝ] ℝ, HasFDerivAt (fun x => f x + p / 2 * ‖x - z‖ ^ 2) D x0 ∧
      ∀ h, D h = inner ℝ (gradient f x0) h + p * inner ℝ (x0 - z) h := by
  refine ⟨_, (hfd x0).hasFDerivAt.add ((((hasFDerivAt_id x0).sub_const z).norm_sq).const_mul
    (p / 2)), ?_⟩
  intro h
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
    nsmul_eq_mul, Nat.cast_ofNat, grad_apply, id]
  ring

lemma DK_eval {n m : ℕ} (f : E n → ℝ) (hfd : Differentiable ℝ f) (A : E n →L[ℝ] E m) (b : E m)
    (Γ p : ℝ) (z : E n) (y : E m) (x0 : E n) :
    ∃ D : E n →L[ℝ] ℝ, HasFDerivAt (fun x => K f A b Γ p x z y) D x0 ∧
      ∀ h, D h = inner ℝ (gradient f x0) h + inner ℝ y (A h) + Γ * inner ℝ (A x0 - b) (A h) +
        p * inner ℝ (x0 - z) h := by
  have h1 := (hfd x0).hasFDerivAt
  have h2 : HasFDerivAt (fun x => inner ℝ y (A x - b)) ((innerSL ℝ y).comp A) x0 :=
    (innerSL ℝ y).hasFDerivAt.comp x0 (A.hasFDerivAt.sub_const b)
  have h3 := ((A.hasFDerivAt (x := x0)).sub_const b).norm_sq.const_mul (Γ / 2)
  have h4 := (((hasFDerivAt_id x0).sub_const z).norm_sq).const_mul (p / 2)
  refine ⟨_, ((h1.add h2).add h3).add h4, ?_⟩
  intro h
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
    nsmul_eq_mul, Nat.cast_ofNat, grad_apply, id]
  ring

lemma box_convex {n : ℕ} (ℓ u : Fin n → ℝ) : Convex ℝ (box ℓ u) := by
  intro x hx y hy a c ha hc hac i
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  obtain ⟨h1, h2⟩ := hx i
  obtain ⟨h3, h4⟩ := hy i
  have e : ℓ i = a * ℓ i + c * ℓ i := by rw [← add_mul, hac, one_mul]
  have e' : u i = a * u i + c * u i := by rw [← add_mul, hac, one_mul]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h3 hc]
  · nlinarith [mul_le_mul_of_nonneg_left h2 ha, mul_le_mul_of_nonneg_left h4 hc]

lemma feas_convex {n m : ℕ} (A : E n →L[ℝ] E m) (b : E m) (ℓ u : Fin n → ℝ) :
    Convex ℝ (feas A b ℓ u) := by
  apply (box_convex ℓ u).inter
  intro x hx y hy a c ha hc hac
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  rw [map_add, map_smul, map_smul, hx, hy, ← add_smul, hac, one_smul]

lemma core (nd C a q p γ : ℝ) (hnd : 0 ≤ nd) (hC : 0 ≤ C) (hpγ : 0 < p + γ)
    (hq : γ * nd ^ 2 ≤ a) (h : a + p * nd ^ 2 ≤ q) (hqb : q ≤ C * nd) : (p + γ) * nd ≤ C := by
  rcases eq_or_lt_of_le hnd with h0 | h0
  · rw [← h0, mul_zero]; exact hC
  · have : (p + γ) * nd * nd ≤ C * nd := by nlinarith
    exact le_of_mul_le_mul_right this h0

end Aux_PALC35

open ProxADMMLC.Conv Aux_PALC35 in
theorem solution {n m : ℕ} (f : E n → ℝ) (A : E n →L[ℝ] E m) (b : E m) (ℓ u : Fin n → ℝ)
    (hℓu : ∀ i, ℓ i < u i) (L : ℝ) (hf : Assump22c f ℓ u L) (γ : ℝ)
    (hγ : MonoConst f ℓ u γ) (Γ p : ℝ) (hΓ : 0 < Γ) (hp : 0 < p) (hpγ : -γ < p)
    (xs : E m → E n → E n) (hxs : IsXSel f A b ℓ u Γ p xs)
    (xst : E n → E n) (hxst : IsXStarSel f A b ℓ u p xst) :
    ∀ z ∈ box ℓ u, ∀ z' ∈ box ℓ u, ∀ y y' : E m,
      ‖xst z - xst z'‖ ≤ p / (p + γ) * ‖z - z'‖ ∧
      ‖xs y z - xs y z'‖ ≤ p / (p + γ) * ‖z - z'‖ ∧
      (p + γ) * ‖xs y z - xs y' z‖ ≤ ‖A‖ * ‖y - y'‖ := by
  intro z _ z' _ y y'
  have hpγ' : 0 < p + γ := by linarith
  have hfd := hf.1
  have conv : ∀ (x1 x2 : E n), (p + γ) * ‖x1 - x2‖ ≤ p * ‖z - z'‖ →
      ‖x1 - x2‖ ≤ p / (p + γ) * ‖z - z'‖ := by
    intro x1 x2 h
    rw [div_mul_eq_mul_div, le_div_iff₀ hpγ']
    linarith
  refine ⟨?_, ?_, ?_⟩
  · -- claim 1
    set x1 := xst z
    set x2 := xst z'
    obtain ⟨hx1, hmin1⟩ := hxst z
    obtain ⟨hx2, hmin2⟩ := hxst z'
    obtain ⟨D1, hD1, hD1e⟩ := D1_eval f hfd p z x1
    obtain ⟨D2, hD2, hD2e⟩ := D1_eval f hfd p z' x2
    have v1 := vi _ _ (feas_convex A b ℓ u) x1 x2 hx1 hx2 D1 hD1 hmin1
    have v2 := vi _ _ (feas_convex A b ℓ u) x2 x1 hx2 hx1 D2 hD2 hmin2
    rw [hD1e] at v1
    rw [hD2e] at v2
    rw [show x2 - x1 = -(x1 - x2) by abel, inner_neg_right, inner_neg_right] at v1
    have hmono := hγ x1 hx1.1 x2 hx2.1
    have e1 : inner ℝ (x1 - z) (x1 - x2) - inner ℝ (x2 - z') (x1 - x2) =
        ‖x1 - x2‖ ^ 2 - inner ℝ (z - z') (x1 - x2) := by
      rw [← inner_sub_left, show (x1 - z) - (x2 - z') = (x1 - x2) - (z - z') by abel,
        inner_sub_left, real_inner_self_eq_norm_sq]
    rw [inner_sub_left] at hmono
    have hb : p * inner ℝ (z - z') (x1 - x2) ≤ p * ‖z - z'‖ * ‖x1 - x2‖ := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (real_inner_le_norm _ _) hp.le
    apply conv
    exact core ‖x1 - x2‖ (p * ‖z - z'‖)
      (inner ℝ (gradient f x1) (x1 - x2) - inner ℝ (gradient f x2) (x1 - x2))
      (p * inner ℝ (z - z') (x1 - x2)) p γ (norm_nonneg _) (by positivity) hpγ' hmono
      (by nlinarith) hb
  · -- claim 2
    set x1 := xs y z
    set x2 := xs y z'
    obtain ⟨hx1, hmin1⟩ := hxs y z
    obtain ⟨hx2, hmin2⟩ := hxs y z'
    obtain ⟨D1, hD1, hD1e⟩ := DK_eval f hfd A b Γ p z y x1
    obtain ⟨D2, hD2, hD2e⟩ := DK_eval f hfd A b Γ p z' y x2
    have v1 := vi _ _ (box_convex ℓ u) x1 x2 hx1 hx2 D1 hD1 hmin1
    have v2 := vi _ _ (box_convex ℓ u) x2 x1 hx2 hx1 D2 hD2 hmin2
    rw [hD1e] at v1
    rw [hD2e] at v2
    rw [show x2 - x1 = -(x1 - x2) by abel, map_neg, inner_neg_right, inner_neg_right,
      inner_neg_right, inner_neg_right] at v1
    have hmono := hγ x1 hx1 x2 hx2
    have e1 : inner ℝ (x1 - z) (x1 - x2) - inner ℝ (x2 - z') (x1 - x2) =
        ‖x1 - x2‖ ^ 2 - inner ℝ (z - z') (x1 - x2) := by
      rw [← inner_sub_left, show (x1 - z) - (x2 - z') = (x1 - x2) - (z - z') by abel,
        inner_sub_left, real_inner_self_eq_norm_sq]
    have e2 : inner ℝ (A x1 - b) (A (x1 - x2)) - inner ℝ (A x2 - b) (A (x1 - x2)) =
        ‖A (x1 - x2)‖ ^ 2 := by
      rw [← inner_sub_left, show (A x1 - b) - (A x2 - b) = A (x1 - x2) by rw [map_sub]; abel,
        real_inner_self_eq_norm_sq]
    have hAd : 0 ≤ Γ * ‖A (x1 - x2)‖ ^ 2 := by positivity
    rw [inner_sub_left] at hmono
    have hb : p * inner ℝ (z - z') (x1 - x2) ≤ p * ‖z - z'‖ * ‖x1 - x2‖ := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (real_inner_le_norm _ _) hp.le
    apply conv
    exact core ‖x1 - x2‖ (p * ‖z - z'‖)
      (inner ℝ (gradient f x1) (x1 - x2) - inner ℝ (gradient f x2) (x1 - x2))
      (p * inner ℝ (z - z') (x1 - x2)) p γ (norm_nonneg _) (by positivity) hpγ' hmono
      (by nlinarith) hb
  · -- claim 3
    set x1 := xs y z
    set x2 := xs y' z
    obtain ⟨hx1, hmin1⟩ := hxs y z
    obtain ⟨hx2, hmin2⟩ := hxs y' z
    obtain ⟨D1, hD1, hD1e⟩ := DK_eval f hfd A b Γ p z y x1
    obtain ⟨D2, hD2, hD2e⟩ := DK_eval f hfd A b Γ p z y' x2
    have v1 := vi _ _ (box_convex ℓ u) x1 x2 hx1 hx2 D1 hD1 hmin1
    have v2 := vi _ _ (box_convex ℓ u) x2 x1 hx2 hx1 D2 hD2 hmin2
    rw [hD1e] at v1
    rw [hD2e] at v2
    rw [show x2 - x1 = -(x1 - x2) by abel, map_neg, inner_neg_right, inner_neg_right,
      inner_neg_right, inner_neg_right] at v1
    have hmono := hγ x1 hx1 x2 hx2
    have e1 : inner ℝ (x1 - z) (x1 - x2) - inner ℝ (x2 - z) (x1 - x2) = ‖x1 - x2‖ ^ 2 := by
      rw [← inner_sub_left, show (x1 - z) - (x2 - z) = x1 - x2 by abel,
        real_inner_self_eq_norm_sq]
    have e2 : inner ℝ (A x1 - b) (A (x1 - x2)) - inner ℝ (A x2 - b) (A (x1 - x2)) =
        ‖A (x1 - x2)‖ ^ 2 := by
      rw [← inner_sub_left, show (A x1 - b) - (A x2 - b) = A (x1 - x2) by rw [map_sub]; abel,
        real_inner_self_eq_norm_sq]
    have e3 : inner ℝ (y - y') (A (x1 - x2)) = inner ℝ y (A (x1 - x2)) - inner ℝ y' (A (x1 - x2)) :=
      inner_sub_left _ _ _
    have hAd : 0 ≤ Γ * ‖A (x1 - x2)‖ ^ 2 := by positivity
    rw [inner_sub_left] at hmono
    have hb : -inner ℝ (y - y') (A (x1 - x2)) ≤ ‖A‖ * ‖y - y'‖ * ‖x1 - x2‖ := by
      have h1 := neg_le_abs (inner ℝ (y - y') (A (x1 - x2)))
      have h2 := abs_real_inner_le_norm (y - y') (A (x1 - x2))
      have h3 := A.le_opNorm (x1 - x2)
      have h4 : ‖y - y'‖ * ‖A (x1 - x2)‖ ≤ ‖y - y'‖ * (‖A‖ * ‖x1 - x2‖) :=
        mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
      nlinarith
    exact core ‖x1 - x2‖ (‖A‖ * ‖y - y'‖)
      (inner ℝ (gradient f x1) (x1 - x2) - inner ℝ (gradient f x2) (x1 - x2))
      (-inner ℝ (y - y') (A (x1 - x2))) p γ (norm_nonneg _) (by positivity) hpγ' hmono
      (by nlinarith) hb
