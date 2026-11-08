-- Prove2me | solution 1 for RelSmoothFull.PrimalGrad.theorem_3_1_full
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-08T02:49:57.345272+00:00
-- url     : https://prove2.me/submissions/6a24c544-0d2c-421f-9e75-691b1c3c8614

import Mathlib
import Definitions.Def_RelSmoothFOM_PrimalGrad_Setting
import Definitions.Def_RelSmoothFull_PrimalGrad_completedRate

set_option autoImplicit false

namespace RSPGAux

open Filter Topology Set

section Helpers

/-- A one-sided slope bound at `0` bounds the derivative. -/
lemma deriv_le_of_slope {φ : ℝ → ℝ} {d c : ℝ} (hφ : HasDerivAt φ d 0)
    (h : ∀ t : ℝ, 0 < t → t < 1 → φ t - φ 0 ≤ t * c) : d ≤ c := by
  have hT := hφ.tendsto_slope_zero_right
  refine le_of_tendsto hT ?_
  filter_upwards [eventually_mem_nhdsWithin,
    nhdsWithin_le_nhds (eventually_lt_nhds one_pos)] with t ht0 ht1
  have ht0' : (0 : ℝ) < t := ht0
  rw [zero_add, smul_eq_mul, inv_mul_le_iff₀ ht0']
  exact h t ht0' ht1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma hasDerivAt_line {g : E → ℝ} {g' : E →L[ℝ] ℝ} {x v : E} (hd : HasFDerivAt g g' x) :
    HasDerivAt (fun t : ℝ => g (x + t • v)) (g' v) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hd' : HasFDerivAt g g' (x + (0 : ℝ) • v) := by simpa using hd
  have := HasFDerivAt.comp_hasDerivAt (x := (0 : ℝ)) hd' h1
  exact this

lemma grad_ineq {Q : Set E} {g : E → ℝ} (hg : ConvexOn ℝ Q g) {x y : E} (hx : x ∈ Q)
    (hy : y ∈ Q) {g' : E →L[ℝ] ℝ} (hd : HasFDerivAt g g' x) : g x + g' (y - x) ≤ g y := by
  have hK := deriv_le_of_slope (c := g y - g x) (hasDerivAt_line (v := y - x) hd)
    (fun t ht0 ht1 => by
      have hc := hg.2 hx hy (show (0 : ℝ) ≤ 1 - t by linarith) ht0.le
        (show (1 - t) + t = 1 by ring)
      have he : x + t • (y - x) = (1 - t) • x + t • y := by
        rw [smul_sub, sub_smul, one_smul]; abel
      simp only [zero_smul, add_zero, he, smul_eq_mul] at hc ⊢
      linarith)
  linarith

lemma opt_ineq {Q : Set E} (hQ : Convex ℝ Q) {ψ : E → ℝ} {ψ' : E →L[ℝ] ℝ} {p u : E}
    (hp : p ∈ Q) (hu : u ∈ Q) (hmin : ∀ w ∈ Q, ψ p ≤ ψ w) (hd : HasFDerivAt ψ ψ' p) :
    0 ≤ ψ' (u - p) := by
  have hK := deriv_le_of_slope (c := 0) (hasDerivAt_line (v := u - p) hd.neg)
    (fun t ht0 ht1 => by
      have he : p + t • (u - p) = (1 - t) • p + t • u := by
        rw [smul_sub, sub_smul, one_smul]; abel
      have hm := hmin _ (hQ hp hu (show (0 : ℝ) ≤ 1 - t by linarith) ht0.le
        (show (1 - t) + t = 1 by ring))
      simp only [zero_smul, add_zero, he, mul_zero, Pi.neg_apply]
      linarith)
  simp only [ContinuousLinearMap.coe_neg', Pi.neg_apply] at hK
  linarith

lemma convexOn_of_support {S : Set E} (hS : Convex ℝ S) (g : E → ℝ) (D : E → E →L[ℝ] ℝ)
    (h : ∀ z ∈ S, ∀ w ∈ S, g z + D z (w - z) ≤ g w) : ConvexOn ℝ S g := by
  refine ⟨hS, fun x hx y hy a b ha hb hab => ?_⟩
  have hz := hS hx hy ha hb hab
  have h1 := h _ hz x hx
  have h2 := h _ hz y hy
  obtain rfl : b = 1 - a := by linarith
  have hv : a • (x - (a • x + (1 - a) • y)) + (1 - a) • (y - (a • x + (1 - a) • y)) = 0 := by
    module
  have key := congrArg (D (a • x + (1 - a) • y)) hv
  simp only [map_add, map_smul, map_zero, smul_eq_mul] at key
  simp only [smul_eq_mul]
  nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

lemma ii_mono {A B : Set E} (hAB : A ⊆ B) (hs : affineSpan ℝ A = affineSpan ℝ B) :
    intrinsicInterior ℝ A ⊆ intrinsicInterior ℝ B := by
  have key : ∀ S : AffineSubspace ℝ E,
      ((↑) '' interior ((↑) ⁻¹' A : Set S) : Set E) ⊆ (↑) '' interior ((↑) ⁻¹' B : Set S) :=
    fun S => Set.image_mono (interior_mono (Set.preimage_mono hAB))
  have h1 : intrinsicInterior ℝ A =
      ((↑) '' interior ((↑) ⁻¹' A : Set (affineSpan ℝ A)) : Set E) := rfl
  have h2 : intrinsicInterior ℝ B =
      ((↑) '' interior ((↑) ⁻¹' B : Set (affineSpan ℝ B)) : Set E) := rfl
  rw [h1, h2, hs]
  exact key _

variable [FiniteDimensional ℝ E]

lemma relint_homothety {Q : Set E} (hQ : Convex ℝ Q) {x c : E} (hx : x ∈ Q)
    (hc : c ∈ intrinsicInterior ℝ Q) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    x + t • (c - x) ∈ intrinsicInterior ℝ Q := by
  set φ : E ≃ᵃ[ℝ] E := AffineEquiv.homothetyUnitsMulHom x (Units.mk0 t ht0.ne') with hφdef
  have hφ : ∀ z, φ z = x + t • (z - x) := by
    intro z
    rw [hφdef, AffineEquiv.coe_homothetyUnitsMulHom_apply, AffineMap.homothety_apply]
    simp only [Units.val_mk0, vsub_eq_sub, vadd_eq_add]
    abel
  have hconv : ∀ z ∈ Q, x + t • (z - x) ∈ Q := by
    intro z hz
    have he : x + t • (z - x) = (1 - t) • x + t • z := by
      rw [smul_sub, sub_smul, one_smul]; abel
    rw [he]; exact hQ hx hz (by linarith) ht0.le (by ring)
  have hsub : φ '' Q ⊆ Q := by
    rintro _ ⟨z, hz, rfl⟩; rw [hφ]; exact hconv z hz
  have hspan : affineSpan ℝ (φ '' Q) = affineSpan ℝ Q := by
    apply le_antisymm (affineSpan_mono ℝ hsub)
    rw [affineSpan_le]
    intro q hq
    have h0 : x ∈ affineSpan ℝ (φ '' Q) :=
      subset_affineSpan ℝ _ ⟨x, hx, by rw [hφ]; simp⟩
    have h1 : x + t • (q - x) ∈ affineSpan ℝ (φ '' Q) :=
      subset_affineSpan ℝ _ ⟨q, hq, hφ q⟩
    have hl := AffineMap.lineMap_mem (Q := affineSpan ℝ (φ '' Q)) t⁻¹ h0 h1
    rw [AffineMap.lineMap_apply] at hl
    have hq' : t⁻¹ • (x + t • (q - x) -ᵥ x) +ᵥ x = q := by
      simp only [vsub_eq_sub, vadd_eq_add, add_sub_cancel_left, smul_smul,
        inv_mul_cancel₀ ht0.ne', one_smul, sub_add_cancel]
    rw [hq'] at hl
    exact hl
  have hmem : φ c ∈ intrinsicInterior ℝ (φ '' Q) := by
    rw [AffineEquiv.intrinsicInterior_image]; exact ⟨c, hc, rfl⟩
  rw [← hφ]
  exact ii_mono hsub hspan hmem

lemma convex_relint {Q : Set E} (hQ : Convex ℝ Q) : Convex ℝ (intrinsicInterior ℝ Q) := by
  intro x hx y hy a b ha hb hab
  rcases ha.eq_or_lt with ha0 | ha0
  · subst ha0
    have hb1 : b = 1 := by linarith
    subst hb1
    simpa using hy
  · have hm := relint_homothety hQ (intrinsicInterior_subset hy) hx ha0 (by linarith)
    have he : y + a • (x - y) = a • x + b • y := by
      obtain rfl : b = 1 - a := by linarith
      rw [smul_sub, sub_smul, one_smul]; abel
    rwa [he] at hm

lemma convexOn_ext {Q : Set E} (hQ : Convex ℝ Q) (g : E → ℝ)
    (hg : ConvexOn ℝ (intrinsicInterior ℝ Q) g) (hcont : ∀ z ∈ Q, ContinuousAt g z) :
    ConvexOn ℝ Q g := by
  refine ⟨hQ, fun x hx y hy a b ha hb hab => ?_⟩
  obtain ⟨c, hc⟩ := Set.Nonempty.intrinsicInterior hQ ⟨x, hx⟩
  have hxy := hQ hx hy ha hb hab
  have tx : Tendsto (fun t : ℝ => x + t • (c - x)) (𝓝[>] 0) (𝓝 x) := by
    have hc' : Continuous (fun t : ℝ => x + t • (c - x)) := by fun_prop
    have := tendsto_nhdsWithin_of_tendsto_nhds (s := Set.Ioi (0:ℝ)) (hc'.tendsto 0)
    simpa using this
  have ty : Tendsto (fun t : ℝ => y + t • (c - y)) (𝓝[>] 0) (𝓝 y) := by
    have hc' : Continuous (fun t : ℝ => y + t • (c - y)) := by fun_prop
    have := tendsto_nhdsWithin_of_tendsto_nhds (s := Set.Ioi (0:ℝ)) (hc'.tendsto 0)
    simpa using this
  have tz : Tendsto (fun t : ℝ => a • (x + t • (c - x)) + b • (y + t • (c - y))) (𝓝[>] 0)
      (𝓝 (a • x + b • y)) := (tx.const_smul a).add (ty.const_smul b)
  have hL := (hcont _ hxy).tendsto.comp tz
  have hR := (((hcont x hx).tendsto.comp tx).const_mul a).add
    (((hcont y hy).tendsto.comp ty).const_mul b)
  simp only [smul_eq_mul]
  refine le_of_tendsto_of_tendsto hL hR ?_
  filter_upwards [eventually_mem_nhdsWithin,
    nhdsWithin_le_nhds (eventually_lt_nhds one_pos)] with t ht0 ht1
  have h1 := relint_homothety hQ hx hc ht0 ht1.le
  have h2 := relint_homothety hQ hy hc ht0 ht1.le
  have := hg.2 h1 h2 ha hb hab
  simpa [smul_eq_mul] using this

lemma support_ext {Q : Set E} (hQ : Convex ℝ Q) (g : E → ℝ) (D : E → E →L[ℝ] ℝ)
    (hD : ∀ z ∈ Q, HasFDerivAt g (D z) z)
    (hrel : ∀ z ∈ intrinsicInterior ℝ Q, ∀ w ∈ intrinsicInterior ℝ Q, g z + D z (w - z) ≤ g w) :
    ∀ z ∈ Q, ∀ w ∈ Q, g z + D z (w - z) ≤ g w := by
  have h1 := convexOn_of_support (convex_relint hQ) g D hrel
  have h2 := convexOn_ext hQ g h1 (fun z hz => (hD z hz).continuousAt)
  intro z hz w hw
  exact grad_ineq h2 hz hw (hD z hz)

end Helpers

open RelSmoothFOM.PrimalGrad RelSmoothFull.PrimalGrad in
theorem main_thm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (Q : Set E) (hQclosed : IsClosed Q) (hQ : Convex ℝ Q)
    (f h : E → ℝ)
    (hfd : ∀ x ∈ Q, DifferentiableAt ℝ f x) (hfc : ConvexOn ℝ Q f)
    (hhd : ∀ x ∈ Q, DifferentiableAt ℝ h x) (hhc : ConvexOn ℝ Q h)
    (L μ : ℝ) (hL : 0 < L) (hμ : 0 ≤ μ)
    (hsm : IsRelSmooth Q f h L) (hsc : IsRelStronglyConvex Q f h μ)
    (x : ℕ → E) (hrun : IsPrimalGradientRun Q f h L x) :
    (∀ i : ℕ, f (x (i + 1)) ≤ f (x i)) ∧
    (∀ k : ℕ, 1 ≤ k → ∀ u ∈ Q,
      f (x k) - f u ≤ completedRate L μ k (bregman h u (x 0)) ∧
      completedRate L μ k (bregman h u (x 0))
        ≤ (L - μ) / (k : ℝ) * bregman h u (x 0)) := by
  -- relative smoothness on all of `Q`
  have hS : ∀ z ∈ Q, ∀ w ∈ Q, f w ≤ f z + fderiv ℝ f z (w - z) + L * bregman h w z := by
    have hx := support_ext hQ (fun z => L * h z - f z)
      (fun z => L • fderiv ℝ h z - fderiv ℝ f z)
      (fun z hz => ((hhd z hz).hasFDerivAt.const_mul L).sub (hfd z hz).hasFDerivAt)
      (fun z hz w hw => by
        have := hsm z hz w hw
        simp only [bregman, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
          smul_eq_mul] at this ⊢
        linarith)
    intro z hz w hw
    have := hx z hz w hw
    simp only [bregman, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul] at this ⊢
    linarith
  -- relative strong convexity on all of `Q`
  have hC : ∀ z ∈ Q, ∀ w ∈ Q, f z + fderiv ℝ f z (w - z) + μ * bregman h w z ≤ f w := by
    have hx := support_ext hQ (fun z => f z - μ * h z)
      (fun z => fderiv ℝ f z - μ • fderiv ℝ h z)
      (fun z hz => (hfd z hz).hasFDerivAt.sub ((hhd z hz).hasFDerivAt.const_mul μ))
      (fun z hz w hw => by
        have := hsc z hz w hw
        simp only [bregman, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
          smul_eq_mul] at this ⊢
        linarith)
    intro z hz w hw
    have := hx z hz w hw
    simp only [bregman, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul] at this ⊢
    linarith
  have hB : ∀ z ∈ Q, ∀ w ∈ Q, 0 ≤ bregman h w z := by
    intro z hz w hw
    have := grad_ineq hhc hz hw (hhd z hz).hasFDerivAt
    simp only [bregman]; linarith
  have hxQ : ∀ i, x i ∈ Q := by
    intro i
    cases i with
    | zero => exact hrun.1
    | succ n => exact (hrun.2 n).1
  -- one-step inequality (three-point property)
  have hstar : ∀ i, ∀ u ∈ Q, f (x (i + 1)) - f u ≤
      (L - μ) * bregman h u (x i) - L * bregman h u (x (i + 1)) := by
    intro i u hu
    have hp : x (i + 1) ∈ Q := hxQ (i + 1)
    have hxi : x i ∈ Q := hxQ i
    have hopt := opt_ineq hQ
      (ψ := fun w => fderiv ℝ f (x i) w - fderiv ℝ f (x i) (x i) +
        L * (h w - h (x i) - (fderiv ℝ h (x i) w - fderiv ℝ h (x i) (x i))))
      (ψ' := fderiv ℝ f (x i) + L • (fderiv ℝ h (x (i + 1)) - fderiv ℝ h (x i))) hp hu
      (fun w hw => by
        have := (hrun.2 i).2 w hw
        simp only [bregman, map_sub] at this ⊢
        linarith)
      (((fderiv ℝ f (x i)).hasFDerivAt.sub_const _).add
        ((((hhd _ hp).hasFDerivAt.sub_const _).sub
          ((fderiv ℝ h (x i)).hasFDerivAt.sub_const _)).const_mul L))
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sub_apply, smul_eq_mul, map_sub] at hopt
    have h1 := hS (x i) hxi (x (i + 1)) hp
    have h2 := hC (x i) hxi u hu
    simp only [bregman, map_sub] at h1 h2 ⊢
    linarith
  have hmono : ∀ i, f (x (i + 1)) ≤ f (x i) := by
    intro i
    have h1 := hstar i (x i) (hxQ i)
    have hb := hB (x (i + 1)) (hxQ (i + 1)) (x i) (hxQ i)
    have h0 : bregman h (x i) (x i) = 0 := by simp [bregman]
    rw [h0] at h1
    nlinarith [mul_nonneg hL.le hb]
  have hanti : Antitone (fun i => f (x i)) := antitone_nat_of_succ_le hmono
  refine ⟨hmono, fun k hk u hu => ?_⟩
  have hd0 : ∀ i, 0 ≤ bregman h u (x i) := fun i => hB (x i) (hxQ i) u hu
  have hLμ : 0 ≤ (L - μ) * bregman h u (x 0) := by
    have h1 := hS (x 0) (hxQ 0) u hu
    have h2 := hC (x 0) (hxQ 0) u hu
    nlinarith
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hδk : ∀ i ≤ k, f (x k) ≤ f (x i) := fun i hi => (hanti hi : f (x k) ≤ f (x i))
  by_cases hμ0 : μ = 0
  · subst hμ0
    rw [completedRate, if_pos rfl]
    have hinv : ∀ n, n ≤ k → (n : ℝ) * (f (x k) - f u) + L * bregman h u (x n) ≤
        L * bregman h u (x 0) := by
      intro n
      induction n with
      | zero => intro _; simp
      | succ n ih =>
        intro hn
        have ih' := ih (by omega)
        have h1 := hstar n u hu
        have h2 := hδk (n + 1) hn
        push_cast
        linarith
    constructor
    · rw [le_div_iff₀ hkR]
      nlinarith [hinv k le_rfl, mul_nonneg hL.le (hd0 k)]
    · exact le_of_eq (by ring)
  · by_cases hlt : 0 < μ ∧ μ < L
    · rw [completedRate, if_neg hμ0, if_pos hlt]
      obtain ⟨hμpos, hμL⟩ := hlt
      set s := L - μ with hs
      have hspos : 0 < s := by linarith
      set r := μ / s with hr
      have hrpos : 0 < r := div_pos hμpos hspos
      have hμeq : μ = r * s := by rw [hr]; field_simp
      have hLeq : L = s * (1 + r) := by linarith
      have hinv : ∀ n, n ≤ k → ((1 + r) ^ n - 1) * (f (x k) - f u) +
          r * s * (1 + r) ^ n * bregman h u (x n) ≤ r * s * bregman h u (x 0) := by
        intro n
        induction n with
        | zero => intro _; simp
        | succ n ih =>
          intro hn
          have ih' := ih (by omega)
          have h1 := hstar n u hu
          have h2 := hδk (n + 1) hn
          have hbr : 0 ≤ r * (1 + r) ^ n :=
            mul_nonneg hrpos.le (pow_nonneg (by linarith) n)
          have key : r * (1 + r) ^ n * ((f (x k) - f u) + L * bregman h u (x (n + 1)) -
              s * bregman h u (x n)) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos hbr (by linarith)
          rw [hLeq] at key
          rw [pow_succ]
          linarith [key, ih']
      have hfin := hinv k le_rfl
      have hqk : 1 < (1 + r) ^ k := one_lt_pow₀ (by linarith) (by omega)
      have hpos : 0 < (1 + r) ^ k - 1 := by linarith
      have hnn : 0 ≤ r * s * (1 + r) ^ k * bregman h u (x k) :=
        mul_nonneg (mul_nonneg (mul_nonneg hrpos.le hspos.le) (pow_nonneg (by linarith) k))
          (hd0 k)
      constructor
      · rw [le_div_iff₀ hpos, hμeq]
        linarith
      · rw [div_le_iff₀ hpos]
        have hbern : 1 + (k : ℝ) * r ≤ (1 + r) ^ k := one_add_mul_le_pow (by linarith) k
        have hd00 := hd0 0
        have he : s / k * bregman h u (x 0) * ((k : ℝ) * r) = μ * bregman h u (x 0) := by
          rw [hμeq, show s / k * bregman h u (x 0) * ((k : ℝ) * r) =
            r * s * bregman h u (x 0) * ((k : ℝ) / k) by ring, div_self hkR.ne', mul_one]
        have h3 : s / k * bregman h u (x 0) * ((k : ℝ) * r) ≤
            s / k * bregman h u (x 0) * ((1 + r) ^ k - 1) :=
          mul_le_mul_of_nonneg_left (by linarith)
            (mul_nonneg (div_nonneg hspos.le hkR.le) hd00)
        linarith
    · rw [completedRate, if_neg hμ0, if_neg hlt]
      have hLμ' : L ≤ μ := by
        by_contra hc
        exact hlt ⟨lt_of_le_of_ne hμ (Ne.symm hμ0), not_le.mp hc⟩
      constructor
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        have h1 := hstar j u hu
        nlinarith [mul_nonneg (sub_nonneg.mpr hLμ') (hd0 j), mul_nonneg hL.le (hd0 (j + 1))]
      · rw [div_mul_eq_mul_div]
        exact div_nonneg hLμ hkR.le

end RSPGAux

open RelSmoothFOM.PrimalGrad RelSmoothFull.PrimalGrad in
theorem solution
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (Q : Set E) (hQclosed : IsClosed Q) (hQ : Convex ℝ Q)
    (f h : E → ℝ)
    (hfd : ∀ x ∈ Q, DifferentiableAt ℝ f x) (hfc : ConvexOn ℝ Q f)
    (hhd : ∀ x ∈ Q, DifferentiableAt ℝ h x) (hhc : ConvexOn ℝ Q h)
    (L μ : ℝ) (hL : 0 < L) (hμ : 0 ≤ μ)
    (hsm : IsRelSmooth Q f h L) (hsc : IsRelStronglyConvex Q f h μ)
    (x : ℕ → E) (hrun : IsPrimalGradientRun Q f h L x) :
    (∀ i : ℕ, f (x (i + 1)) ≤ f (x i)) ∧
    (∀ k : ℕ, 1 ≤ k → ∀ u ∈ Q,
      f (x k) - f u ≤ completedRate L μ k (bregman h u (x 0)) ∧
      completedRate L μ k (bregman h u (x 0))
        ≤ (L - μ) / (k : ℝ) * bregman h u (x 0)) := by
  exact RSPGAux.main_thm Q hQclosed hQ f h hfd hfc hhd hhc L μ hL hμ hsm hsc x hrun
