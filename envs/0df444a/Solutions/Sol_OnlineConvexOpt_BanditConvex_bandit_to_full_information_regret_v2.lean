-- Prove2me | solution 1 for OnlineConvexOpt.BanditConvex.bandit_to_full_information_regret_v2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T19:36:10.787238+00:00
-- url     : https://prove2.me/submissions/357e346f-e061-4d92-9bd5-357276144b25

import Mathlib
import Definitions.Def_OnlineConvexOpt_BanditConvex_FirstOrderAlgorithm
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol_v2

open MeasureTheory


namespace OnlineConvexOpt.BanditConvex

section aux
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma aux2_lin_grad (G z : E) : HasGradientAt (fun y => inner ℝ G y) G z := by
  rw [hasGradientAt_iff_isLittleO]
  refine (Asymptotics.isLittleO_zero _ _).congr_left (fun y => ?_)
  rw [inner_sub_right]; ring

lemma aux2_play (A : (ℕ → E → ℝ) → ℕ → E) (hA : IsFirstOrderOnlineAlgorithm A)
    (G : ℕ → E) (xs : ℕ → E)
    (hx0 : xs 0 = A (fun _ _ => (0 : ℝ)) 0)
    (hxs : ∀ t : ℕ, xs (t + 1) = A (fun τ y => if τ ≤ t then inner ℝ (G τ) y else 0) (t + 1)) :
    ∀ t, A (fun τ y => inner ℝ (G τ) y) t = xs t := by
  intro t
  cases t with
  | zero =>
    rw [hx0]; exact hA.1 _ _ 0 (fun s hs => absurd hs (Nat.not_lt_zero _))
  | succ n =>
    rw [hxs n]
    exact hA.1 _ _ (n + 1) (fun s hs => by
      have : s ≤ n := Nat.lt_succ_iff.mp hs
      funext y; simp [this])

lemma aux2_grad_ineq (K : Set E) (f : E → ℝ) (hfconv : ConvexOn ℝ K f) (gx x y : E)
    (hx : x ∈ K) (hy : y ∈ K)
    (hg : HasGradientAt f gx x) : f x + inner ℝ gx (y - x) ≤ f y := by
  set L : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x y with hL
  have e : ∀ s : ℝ, L s = x + s • (y - x) := by
    intro s; rw [hL, AffineMap.lineMap_apply_module']; abel
  have hc : ConvexOn ℝ (L ⁻¹' K) (fun s : ℝ => f (x + s • (y - x))) := by
    have h := hfconv.comp_affineMap L
    have heq : (f ∘ L) = fun s : ℝ => f (x + s • (y - x)) := by funext s; simp [e]
    rw [heq] at h; exact h
  have hd : HasDerivAt (fun s : ℝ => x + s • (y - x)) (y - x) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (y - x)).const_add x
  have hd2 : HasDerivAt (fun s : ℝ => f (x + s • (y - x))) (inner ℝ gx (y - x)) 0 := by
    have h1 := hg.hasFDerivAt
    have h1' : HasFDerivAt f ((InnerProductSpace.toDual ℝ E) gx) (x + (0:ℝ) • (y - x)) := by
      simpa using h1
    have := h1'.comp_hasDerivAt (0:ℝ) hd
    rw [InnerProductSpace.toDual_apply_apply] at this
    exact this
  have h0 : (0:ℝ) ∈ L ⁻¹' K := by simp [e, hx]
  have h1 : (1:ℝ) ∈ L ⁻¹' K := by simp [e, hy]
  have := hc.le_slope_of_hasDerivAt h0 h1 zero_lt_one hd2
  simp [slope] at this
  linarith

variable [MeasurableSpace E] [BorelSpace E]

lemma aux2_key {Ω : Type*} {m m0 : MeasurableSpace Ω} {Prob : Measure Ω}
    [IsProbabilityMeasure Prob] (hm : m ≤ m0)
    (V : Ω → E) (hV : Measurable[m] V) (C : ℝ) (hC : ∀ ω, ‖V ω‖ ≤ C)
    (g : Ω → E) (hg : Integrable g Prob) (Y : Ω → E)
    (hY : condExp m Prob g =ᵐ[Prob] Y) :
    Integrable (fun ω => inner ℝ (g ω) (V ω)) Prob ∧
    Integrable (fun ω => inner ℝ (Y ω) (V ω)) Prob ∧
    ∫ ω, inner ℝ (g ω) (V ω) ∂Prob = ∫ ω, inner ℝ (Y ω) (V ω) ∂Prob := by
  have hgae := hg.1
  set g' := hgae.mk g with hg'def
  have hg'sm : StronglyMeasurable g' := hgae.stronglyMeasurable_mk
  have hgg' : g =ᵐ[Prob] g' := hgae.ae_eq_mk
  set c := condExp m Prob g with hcdef
  have hc : StronglyMeasurable[m] c := stronglyMeasurable_condExp
  set S : Set E := Set.range g' ∪ Set.range c with hS
  have hSsep : TopologicalSpace.IsSeparable S :=
    hg'sm.isSeparable_range.union hc.isSeparable_range
  set W : Submodule ℝ E := (Submodule.span ℝ S).topologicalClosure with hW
  have : CompleteSpace W := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have hWsep : TopologicalSpace.IsSeparable (W : Set E) := by
    rw [hW, Submodule.topologicalClosure_coe]
    exact hSsep.span.closure
  have hSW : ∀ w ∈ S, w ∈ W := fun w hw =>
    Submodule.le_topologicalClosure _ (Submodule.subset_span hw)
  set P := W.starProjection with hP
  set Z : Ω → E := fun ω => P (V ω) with hZ
  have hPW : ∀ v, P v ∈ W := fun v => by
    rw [hP, Submodule.starProjection_apply]; exact Submodule.coe_mem _
  have hZsm : StronglyMeasurable[m] Z := by
    refine stronglyMeasurable_iff_measurable_separable.2 ⟨?_, ?_⟩
    · exact P.continuous.measurable.comp hV
    · refine hWsep.mono ?_
      rintro _ ⟨ω, rfl⟩; exact hPW _
  have hinW : ∀ v, ∀ w ∈ W, inner ℝ w v = inner ℝ w (P v) := by
    intro v w hw
    have := Submodule.starProjection_inner_eq_zero (K := W) v w hw
    rw [inner_sub_left] at this
    rw [hP]
    linarith [real_inner_comm v w, real_inner_comm (W.starProjection v) w]
  have hZbd : ∀ ω, ‖Z ω‖ ≤ C := fun ω =>
    (Submodule.norm_starProjection_apply_le (K := W) (V ω)).trans (hC ω)
  have hint : Integrable (fun ω => innerSL ℝ (Z ω) (g ω)) Prob := by
    refine Integrable.mono' (hg.norm.const_mul C) ?_ ?_
    · exact ((hZsm.mono hm).aestronglyMeasurable.inner hg.1)
    · filter_upwards with ω
      rw [innerSL_apply_apply, Real.norm_eq_abs]
      exact (abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right (hZbd ω) (norm_nonneg _))
  have hce := condExp_bilin_of_stronglyMeasurable_left (innerSL ℝ) hZsm hint hg
  have hint2 : Integrable (fun ω => innerSL ℝ (Z ω) (c ω)) Prob :=
    integrable_condExp.congr hce
  have e1 : (fun ω => inner ℝ (g ω) (V ω)) =ᵐ[Prob] fun ω => innerSL ℝ (Z ω) (g ω) := by
    filter_upwards [hgg'] with ω hω
    rw [innerSL_apply_apply, hω, hinW (V ω) (g' ω) (hSW _ (Or.inl ⟨ω, rfl⟩)), real_inner_comm]
  have e2 : (fun ω => inner ℝ (Y ω) (V ω)) =ᵐ[Prob] fun ω => innerSL ℝ (Z ω) (c ω) := by
    filter_upwards [hY] with ω hω
    rw [innerSL_apply_apply, ← hω, hinW (V ω) (c ω) (hSW _ (Or.inr ⟨ω, rfl⟩)), real_inner_comm]
  refine ⟨hint.congr e1.symm, hint2.congr e2.symm, ?_⟩
  rw [integral_congr_ae e1, integral_congr_ae e2, ← integral_condExp hm,
    integral_congr_ae hce]

end aux

theorem bfi_core {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
    {Ω : Type*} [m0 : MeasurableSpace Ω] {Prob : Measure Ω} [IsProbabilityMeasure Prob]
    (K : Set E) (hKbdd : Bornology.IsBounded K) (T : ℕ) (u : E) (hu : u ∈ K)
    (f : ℕ → E → ℝ) (hfconv : ∀ t, ConvexOn ℝ K (f t))
    (gradf : ℕ → E → E) (hf : ∀ t y, HasGradientAt (f t) (gradf t y) y)
    (A : (ℕ → E → ℝ) → ℕ → E) (hA : IsFirstOrderOnlineAlgorithm A)
    (hAK : ∀ (h : ℕ → E → ℝ) (t : ℕ), A h t ∈ K)
    (B : (ℕ → E) → ℝ)
    (hB : ∀ (h : ℕ → E → ℝ) (grad' : ℕ → E),
      (∀ t, ConvexOn ℝ K (h t)) →
      (∀ t, HasGradientAt (h t) (grad' t) (A h t)) →
      ∀ v ∈ K, (∑ t ∈ Finset.range T, (h t (A h t) - h t v)) ≤ B grad')
    (𝓕 : ℕ → MeasurableSpace Ω) (hFmono : Monotone 𝓕) (hFle : ∀ t, 𝓕 t ≤ m0)
    (x g : ℕ → Ω → E)
    (hx0 : x 0 = fun _ => A (fun _ _ => (0 : ℝ)) 0)
    (hxstep : ∀ t : ℕ, x (t + 1) =
      fun ω => A (fun τ y => if τ ≤ t then inner ℝ (g τ ω) y else 0) (t + 1))
    (hxmeas : ∀ t, Measurable[𝓕 t] (x t))
    (hgmeas : ∀ t, Measurable[𝓕 (t + 1)] (g t))
    (hgint : ∀ t, Integrable (g t) Prob)
    (hunbiased : ∀ t, condExp (𝓕 t) Prob (g t) =ᵐ[Prob] fun ω => gradf t (x t ω))
    (hfintegrable : ∀ t, Integrable (fun ω => f t (x t ω)) Prob)
    (hBintegrable : Integrable (fun ω => B (fun t => g t ω)) Prob) :
    (∫ ω, ∑ t ∈ Finset.range T, f t (x t ω) ∂Prob) - ∑ t ∈ Finset.range T, f t u ≤
      ∫ ω, B (fun t => g t ω) ∂Prob := by
  have hKconv : Convex ℝ K := (hfconv 0).1
  -- plays
  have hplay : ∀ ω t, A (fun τ y => inner ℝ (g τ ω) y) t = x t ω := fun ω =>
    aux2_play A hA (fun τ => g τ ω) (fun t => x t ω) (by rw [hx0]) (fun t => by rw [hxstep t])
  have hxK : ∀ t ω, x t ω ∈ K := fun t ω => by rw [← hplay ω t]; exact hAK _ _
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.1 hKbdd
  -- pathwise linear regret
  have path : ∀ ω, ∑ t ∈ Finset.range T, inner ℝ (g t ω) (x t ω - u) ≤ B (fun t => g t ω) := by
    intro ω
    have hconvℓ : ∀ t, ConvexOn ℝ K (fun y => inner ℝ (g t ω) y) := fun t =>
      ⟨hKconv, fun a _ b _ p q _ _ _ => le_of_eq (by
        simp only [inner_add_right, inner_smul_right, smul_eq_mul])⟩
    have := hB (fun τ y => inner ℝ (g τ ω) y) (fun t => g t ω) hconvℓ
      (fun t => aux2_lin_grad _ _) u hu
    refine le_trans (le_of_eq ?_) this
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [hplay ω t, inner_sub_right]
  -- convexity
  have conv : ∀ t ω, f t (x t ω) - f t u ≤ inner ℝ (gradf t (x t ω)) (x t ω - u) := by
    intro t ω
    have := aux2_grad_ineq K (f t) (hfconv t) (gradf t (x t ω)) (x t ω) u (hxK t ω) hu (hf t _)
    have e : inner ℝ (gradf t (x t ω)) (u - x t ω) = - inner ℝ (gradf t (x t ω)) (x t ω - u) := by
      rw [← inner_neg_right, neg_sub]
    linarith
  have key : ∀ t, Integrable (fun ω => inner ℝ (g t ω) (x t ω - u)) Prob ∧
      Integrable (fun ω => inner ℝ (gradf t (x t ω)) (x t ω - u)) Prob ∧
      ∫ ω, inner ℝ (g t ω) (x t ω - u) ∂Prob =
        ∫ ω, inner ℝ (gradf t (x t ω)) (x t ω - u) ∂Prob := by
    intro t
    exact aux2_key (hFle t) (fun ω => x t ω - u) ((hxmeas t).sub_const u) C
      (fun ω => by rw [← dist_eq_norm]; exact hC (hxK t ω) hu) (g t) (hgint t) _ (hunbiased t)
  have s1 : (∫ ω, ∑ t ∈ Finset.range T, f t (x t ω) ∂Prob) - ∑ t ∈ Finset.range T, f t u
      = ∑ t ∈ Finset.range T, ∫ ω, (f t (x t ω) - f t u) ∂Prob := by
    rw [integral_finset_sum _ (fun t _ => hfintegrable t), ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [integral_sub (hfintegrable t) (integrable_const _), integral_const]
    simp
  have s2 : ∑ t ∈ Finset.range T, ∫ ω, (f t (x t ω) - f t u) ∂Prob ≤
      ∑ t ∈ Finset.range T, ∫ ω, inner ℝ (g t ω) (x t ω - u) ∂Prob := by
    refine Finset.sum_le_sum (fun t _ => ?_)
    rw [(key t).2.2]
    exact integral_mono ((hfintegrable t).sub (integrable_const _)) (key t).2.1 (conv t)
  have s3 : ∑ t ∈ Finset.range T, ∫ ω, inner ℝ (g t ω) (x t ω - u) ∂Prob =
      ∫ ω, ∑ t ∈ Finset.range T, inner ℝ (g t ω) (x t ω - u) ∂Prob :=
    (integral_finset_sum _ (fun t _ => (key t).1)).symm
  have s4 : (∫ ω, ∑ t ∈ Finset.range T, inner ℝ (g t ω) (x t ω - u) ∂Prob) ≤
      ∫ ω, B (fun t => g t ω) ∂Prob :=
    integral_mono (integrable_finset_sum _ (fun t _ => (key t).1)) hBintegrable path
  linarith

end OnlineConvexOpt.BanditConvex

open OnlineConvexOpt.BanditConvex


theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
    {Ω : Type*} [m0 : MeasurableSpace Ω] {Prob : Measure Ω} [IsProbabilityMeasure Prob]
    (K : Set E) (hKbdd : Bornology.IsBounded K) (T : ℕ) (u : E) (hu : u ∈ K)
    (f : ℕ → E → ℝ) (hfconv : ∀ t, ConvexOn ℝ K (f t))
    (gradf : ℕ → E → E) (hf : ∀ t y, HasGradientAt (f t) (gradf t y) y)
    (A : (ℕ → E → ℝ) → ℕ → E) (hA : IsFirstOrderOnlineAlgorithm A)
    (hAK : ∀ (h : ℕ → E → ℝ) (t : ℕ), A h t ∈ K)
    (B : (ℕ → E) → ℝ)
    (hB : ∀ (h : ℕ → E → ℝ) (grad' : ℕ → E),
      (∀ t, ConvexOn ℝ K (h t)) →
      (∀ t, HasGradientAt (h t) (grad' t) (A h t)) →
      ∀ v ∈ K, (∑ t ∈ Finset.range T, (h t (A h t) - h t v)) ≤ B grad')
    (𝓕 : ℕ → MeasurableSpace Ω) (hFmono : Monotone 𝓕) (hFle : ∀ t, 𝓕 t ≤ m0)
    (x g : ℕ → Ω → E)
    (hx0 : x 0 = fun _ => A (fun _ _ => (0 : ℝ)) 0)
    (hxstep : ∀ t : ℕ, x (t + 1) =
      fun ω => A (fun τ y => if τ ≤ t then inner ℝ (g τ ω) y else 0) (t + 1))
    (hxmeas : ∀ t, Measurable[𝓕 t] (x t))
    (hgmeas : ∀ t, Measurable[𝓕 (t + 1)] (g t))
    (hgint : ∀ t, Integrable (g t) Prob)
    (hunbiased : ∀ t, condExp (𝓕 t) Prob (g t) =ᵐ[Prob] fun ω => gradf t (x t ω))
    (hfintegrable : ∀ t, Integrable (fun ω => f t (x t ω)) Prob)
    (hBintegrable : Integrable (fun ω => B (fun t => g t ω)) Prob) :
    (∫ ω, ∑ t ∈ Finset.range T, f t (x t ω) ∂Prob) - ∑ t ∈ Finset.range T, f t u ≤
      ∫ ω, B (fun t => g t ω) ∂Prob := by
  exact bfi_core K hKbdd T u hu f hfconv gradf hf A hA hAK B hB 𝓕 hFmono hFle x g hx0 hxstep hxmeas hgmeas hgint hunbiased hfintegrable hBintegrable
