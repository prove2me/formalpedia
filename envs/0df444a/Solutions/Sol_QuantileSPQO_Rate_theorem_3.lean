-- Prove2me | solution 1 for QuantileSPQO.Rate.theorem_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T20:13:02.778593+00:00
-- url     : https://prove2.me/submissions/bda0cbe8-ab10-46c8-b1e8-7e7fe04443d4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_QuantileSPQO_Rate_Setting
import Theorems.Thm_QuantileSPQO_Rate_lemma_3
import Theorems.Thm_QuantileSPQO_Rate_lemma_5

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal RealInnerProductSpace

namespace SPQOT3Aux
open QuantileSPQO.Rate

lemma proj_nonexp {d : ℕ} {Θ : Set (E d)} {Proj : E d → E d} (hc : Convex ℝ Θ)
    (hProj : SpectralProjGrad.Shared.IsProjOnto Θ Proj) {z : E d} (hz : z ∈ Θ) (x : E d) :
    ‖Proj x - z‖ ≤ ‖x - z‖ := by
  obtain ⟨hp, hmin⟩ := hProj x
  set p := Proj x
  have hvi : ⟪x - p, z - p⟫ ≤ 0 := by
    by_contra hpos
    push Not at hpos
    set δ := ⟪x - p, z - p⟫
    set t := min 1 (δ / (‖z - p‖ ^ 2 + 1))
    have ht0 : 0 < t := lt_min one_pos (by positivity)
    have ht1 : t ≤ 1 := min_le_left _ _
    have htδ : t ≤ δ / (‖z - p‖ ^ 2 + 1) := min_le_right _ _
    have hmem : p + t • (z - p) ∈ Θ := by
      have := hc hp hz (by linarith : (0:ℝ) ≤ 1 - t) ht0.le (by ring)
      convert this using 1
      simp only [smul_sub, sub_smul, one_smul]; abel
    have hle := hmin _ hmem
    have hsq : ‖x - p‖ ^ 2 ≤ ‖x - (p + t • (z - p))‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hle 2
    have e : x - (p + t • (z - p)) = (x - p) - t • (z - p) := by abel
    have e2 : ‖(x - p) - t • (z - p)‖ ^ 2 = ‖x - p‖ ^ 2 - 2 * t * δ + t ^ 2 * ‖z - p‖ ^ 2 := by
      rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      ring
    rw [e, e2] at hsq
    have h1 : t * ‖z - p‖ ^ 2 < δ := by
      have hpos' : (0:ℝ) < ‖z - p‖ ^ 2 + 1 := by positivity
      have := mul_le_mul_of_nonneg_right htδ (by positivity : (0:ℝ) ≤ ‖z - p‖ ^ 2 + 1)
      rw [div_mul_cancel₀ _ hpos'.ne'] at this
      nlinarith [sq_nonneg ‖z - p‖]
    nlinarith [mul_pos ht0 hpos]
  have h1 : ‖x - z‖ ^ 2 = ‖x - p‖ ^ 2 - 2 * ⟪x - p, z - p⟫ + ‖z - p‖ ^ 2 := by
    have : x - z = (x - p) - (z - p) := by abel
    rw [this, norm_sub_sq_real]
  have h2 : ‖p - z‖ = ‖z - p‖ := norm_sub_rev _ _
  have h3 : ‖p - z‖ ^ 2 ≤ ‖x - z‖ ^ 2 := by
    rw [h1, h2]; nlinarith [sq_nonneg ‖x - p‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h3

lemma grad_zero {d : ℕ} {Θ : Set (E d)} {q : E d → ℝ} {θs : E d} (hs : θs ∈ interior Θ)
    (hvi : ∀ θ' ∈ Θ, 0 ≤ ⟪gradient q θs, θ' - θs⟫) : gradient q θs = 0 := by
  set g := gradient q θs
  have hcont : Continuous (fun t : ℝ => θs - t • g) := by fun_prop
  have hev : ∀ᶠ t : ℝ in 𝓝 0, θs - t • g ∈ Θ := by
    have := hcont.tendsto 0
    simp only [zero_smul, sub_zero] at this
    exact this (mem_interior_iff_mem_nhds.1 hs)
  have hev2 : ∀ᶠ t : ℝ in 𝓝[>] 0, θs - t • g ∈ Θ ∧ t ∈ Set.Ioi 0 :=
    (Filter.Eventually.filter_mono nhdsWithin_le_nhds hev).and self_mem_nhdsWithin
  obtain ⟨t, ht, htpos⟩ := hev2.exists
  have := hvi _ ht
  have e : θs - t • g - θs = -(t • g) := by abel
  rw [e, inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq] at this
  have htp : (0:ℝ) < t := htpos
  have : ‖g‖ ^ 2 ≤ 0 := by nlinarith
  have : ‖g‖ = 0 := by nlinarith [norm_nonneg g]
  exact norm_eq_zero.1 this

lemma grad_lip {d : ℕ} {Θ : Set (E d)} {q : E d → ℝ} (hc : Convex ℝ Θ) (hK : IsCompact Θ)
    (hq2 : ∃ U : Set (E d), IsOpen U ∧ Θ ⊆ U ∧ ContDiffOn ℝ 2 q U) :
    ∃ L : ℝ, 0 < L ∧ ∀ x ∈ Θ, ∀ y ∈ Θ, ‖gradient q x - gradient q y‖ ≤ L * ‖x - y‖ := by
  obtain ⟨U, hU, hΘU, hq⟩ := hq2
  have h1 : ContDiffOn ℝ 1 (fun y => fderiv ℝ q y) U := hq.fderiv_of_isOpen hU (by norm_num)
  have hcont : ContinuousOn (fun x => fderiv ℝ (fun y => fderiv ℝ q y) x) U :=
    h1.continuousOn_fderiv_of_isOpen hU le_rfl
  have hdiff : ∀ x ∈ Θ, DifferentiableAt ℝ (fun y => fderiv ℝ q y) x := fun x hx =>
    (h1.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds (hΘU hx))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (f := fun x => fderiv ℝ (fun y => fderiv ℝ q y) x) (hcont.mono hΘU)
  refine ⟨max C 1, by positivity, fun x hx y hy => ?_⟩
  have hb : ∀ z ∈ Θ, ‖fderiv ℝ (fun y => fderiv ℝ q y) z‖ ≤ max C 1 :=
    fun z hz => (hC z hz).trans (le_max_left _ _)
  have key := hc.norm_image_sub_le_of_norm_fderiv_le hdiff hb hy hx
  have e : gradient q x - gradient q y =
      (InnerProductSpace.toDual ℝ (E d)).symm (fderiv ℝ q x - fderiv ℝ q y) := by
    simp only [gradient, map_sub]
  rw [e, LinearIsometryEquiv.norm_map]
  exact key

lemma strong_mono {d : ℕ} {q : E d → ℝ} {θ θs : E d} {ϱ : ℝ} (hϱ : 0 < ϱ)
    (hB : ∀ z ∈ segment ℝ θ θs, ∀ v : E d, ϱ * ‖v‖ ^ 2 ≤ ⟪hess q z v, v⟫) :
    ϱ * ‖θ - θs‖ ^ 2 ≤ ⟪gradient q θ - gradient q θs, θ - θs⟫ := by
  set ψ := θ - θs with hψ
  by_cases h0 : ψ = 0
  · rw [h0]; simp
  have hψpos : 0 < ‖ψ‖ := norm_pos_iff.2 h0
  set z : ℝ → E d := fun t => θs + t • ψ with hz
  have hzseg : ∀ t ∈ Set.Icc (0:ℝ) 1, z t ∈ segment ℝ θ θs := by
    intro t ht
    refine ⟨t, 1 - t, ht.1, by linarith [ht.2], by ring, ?_⟩
    simp only [hz, hψ, smul_sub, sub_smul, one_smul]; abel
  have hderiv : ∀ t ∈ Set.Icc (0:ℝ) 1,
      HasDerivAt (fun t => ⟪ψ, gradient q (z t)⟫) ⟪hess q (z t) ψ, ψ⟫ t := by
    intro t ht
    have hpos := hB (z t) (hzseg t ht) ψ
    have hne : hess q (z t) ≠ 0 := by
      intro h; rw [h] at hpos; simp at hpos; nlinarith [sq_pos_of_pos hψpos]
    have hd : DifferentiableAt ℝ (gradient q) (z t) := by
      by_contra hnd
      exact hne (fderiv_zero_of_not_differentiableAt hnd)
    have h1 : HasDerivAt z ψ t := by
      have := ((hasDerivAt_id t).smul_const ψ).const_add θs
      simpa [hz] using this
    have h2 : HasFDerivAt (gradient q) (hess q (z t)) (z t) := hd.hasFDerivAt
    have h3 := (innerSL ℝ ψ).hasFDerivAt.comp_hasDerivAt t (h2.comp_hasDerivAt t h1)
    have h4 := h3.congr_deriv (show _ = ⟪hess q (z t) ψ, ψ⟫ from by
      rw [innerSL_apply_apply]; exact real_inner_comm _ _)
    exact h4
  have hcont : ContinuousOn (fun t => ⟪ψ, gradient q (z t)⟫) (Set.Icc 0 1) :=
    fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
  have hdiffOn : DifferentiableOn ℝ (fun t => ⟪ψ, gradient q (z t)⟫) (interior (Set.Icc 0 1)) :=
    fun t ht => (hderiv t (interior_subset ht)).differentiableAt.differentiableWithinAt
  have hge : ∀ t ∈ interior (Set.Icc (0:ℝ) 1),
      ϱ * ‖ψ‖ ^ 2 ≤ deriv (fun t => ⟪ψ, gradient q (z t)⟫) t := by
    intro t ht
    rw [(hderiv t (interior_subset ht)).deriv]
    exact hB (z t) (hzseg t (interior_subset ht)) ψ
  have key := (convex_Icc (0:ℝ) 1).mul_sub_le_image_sub_of_le_deriv hcont hdiffOn hge
    0 (by simp) 1 (by simp) zero_le_one
  have e1 : z 1 = θ := by simp [hz, hψ]
  have e0 : z 0 = θs := by simp [hz]
  simp only [e1, e0, sub_zero, mul_one] at key
  rw [← inner_sub_right, real_inner_comm] at key
  exact key

lemma contraction {d : ℕ} (ψ g : E d) (α ϱ L : ℝ) (hα : 0 ≤ α)
    (hmono : ϱ * ‖ψ‖ ^ 2 ≤ ⟪g, ψ⟫) (hlip : ‖g‖ ≤ L * ‖ψ‖) (hαL : α * L ^ 2 ≤ ϱ)
    (hαϱ : α * ϱ ≤ 2) (hL : 0 ≤ L) :
    ‖ψ - α • g‖ ≤ (1 - α * ϱ / 2) * ‖ψ‖ := by
  have h1 : ‖ψ - α • g‖ ^ 2 = ‖ψ‖ ^ 2 - 2 * α * ⟪ψ, g⟫ + α ^ 2 * ‖g‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
      sq_abs]; ring
  have hg2 : ‖g‖ ^ 2 ≤ L ^ 2 * ‖ψ‖ ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hlip 2
  have hin : ⟪ψ, g⟫ = ⟪g, ψ⟫ := real_inner_comm _ _
  have h2 : ‖ψ - α • g‖ ^ 2 ≤ ((1 - α * ϱ / 2) * ‖ψ‖) ^ 2 := by
    rw [h1, hin]
    have hn := sq_nonneg ‖ψ‖
    have e3 : α ^ 2 * ‖g‖ ^ 2 ≤ α ^ 2 * (L ^ 2 * ‖ψ‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hg2 (sq_nonneg α)
    have e4 : α ^ 2 * (L ^ 2 * ‖ψ‖ ^ 2) ≤ α * ϱ * ‖ψ‖ ^ 2 := by
      have := mul_le_mul_of_nonneg_left hαL hα
      nlinarith
    have e5 : 2 * α * (ϱ * ‖ψ‖ ^ 2) ≤ 2 * α * ⟪g, ψ⟫ :=
      mul_le_mul_of_nonneg_left hmono (by linarith)
    nlinarith [sq_nonneg (α * ϱ), mul_nonneg (sq_nonneg (α * ϱ)) hn]
  have hnn : 0 ≤ (1 - α * ϱ / 2) * ‖ψ‖ := mul_nonneg (by linarith) (norm_nonneg _)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hnn two_ne_zero).1 h2

lemma enorm_le_of_sq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ℝ≥0∞) (t : ℝ) (ht : 0 < t)
    (h : ∫⁻ ω, f ω ^ 2 ∂P ≤ ENNReal.ofReal (t ^ 2)) :
    ∫⁻ ω, f ω ∂P ≤ ENNReal.ofReal t := by
  have hpt : ∀ x : ℝ≥0∞, x ≤ x ^ 2 * ENNReal.ofReal (1 / (2 * t)) + ENNReal.ofReal (t / 2) := by
    intro x
    by_cases hx : x = ⊤
    · subst hx
      have : ENNReal.ofReal (1 / (2 * t)) ≠ 0 := by
        rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
      rw [ENNReal.top_pow two_ne_zero, ENNReal.top_mul this, top_add]
    · have hx' : x = ENNReal.ofReal x.toReal := (ENNReal.ofReal_toReal hx).symm
      set r := x.toReal
      have hr : 0 ≤ r := ENNReal.toReal_nonneg
      rw [hx', ← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have : r ^ 2 * (1 / (2 * t)) + t / 2 - r = (r - t) ^ 2 / (2 * t) := by
        field_simp; ring
      have : 0 ≤ (r - t) ^ 2 / (2 * t) := by positivity
      linarith
  calc ∫⁻ ω, f ω ∂P ≤ ∫⁻ ω, (f ω ^ 2 * ENNReal.ofReal (1 / (2 * t)) + ENNReal.ofReal (t / 2)) ∂P :=
        lintegral_mono (fun ω => hpt (f ω))
    _ = (∫⁻ ω, f ω ^ 2 ∂P) * ENNReal.ofReal (1 / (2 * t)) + ENNReal.ofReal (t / 2) := by
        rw [lintegral_add_right _ measurable_const, lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
        simp
    _ ≤ ENNReal.ofReal (t ^ 2) * ENNReal.ofReal (1 / (2 * t)) + ENNReal.ofReal (t / 2) := by
        gcongr
    _ = ENNReal.ofReal t := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; field_simp; ring

end SPQOT3Aux


open Filter Topology

namespace SPQOT3Seq

noncomputable def Ssum (u w : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 k, (∏ j ∈ Finset.Ioc i k, (1 - u j)) * u i * w i

lemma Ssum_succ (u w : ℕ → ℝ) (k : ℕ) :
    Ssum u w (k + 1) = (1 - u (k + 1)) * Ssum u w k + u (k + 1) * w (k + 1) := by
  unfold Ssum
  rw [Finset.sum_Icc_succ_top (by omega), Finset.mul_sum]
  simp only [Finset.Ioc_self, Finset.prod_empty, one_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_Icc] at hi
  rw [Finset.prod_Ioc_succ_top (by omega)]
  ring

lemma Ssum_nonneg (u w : ℕ → ℝ) (hu0 : ∀ j, 1 ≤ j → 0 ≤ u j) (hu1 : ∀ j, 1 ≤ j → u j ≤ 1)
    (hw0 : ∀ j, 1 ≤ j → 0 ≤ w j) (k : ℕ) : 0 ≤ Ssum u w k := by
  unfold Ssum
  apply Finset.sum_nonneg
  intro i hi
  rw [Finset.mem_Icc] at hi
  refine mul_nonneg (mul_nonneg (Finset.prod_nonneg fun j hj => ?_) (hu0 i hi.1)) (hw0 i hi.1)
  rw [Finset.mem_Ioc] at hj
  linarith [hu1 j (by omega)]

lemma Ssum_add (u w₁ w₂ : ℕ → ℝ) (k : ℕ) :
    Ssum u (fun i => w₁ i + w₂ i) k = Ssum u w₁ k + Ssum u w₂ k := by
  unfold Ssum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _; ring

lemma cmp (u w x : ℕ → ℝ) (N : ℕ) (hu0 : ∀ j, 1 ≤ j → 0 ≤ u j) (hu1 : ∀ j, 1 ≤ j → u j ≤ 1)
    (hw0 : ∀ j, 1 ≤ j → 0 ≤ w j) (hbase : x (N + 1) ≤ u (N + 1) * w (N + 1))
    (hstep : ∀ k, N + 1 ≤ k → x (k + 1) ≤ (1 - u (k + 1)) * x k + u (k + 1) * w (k + 1)) :
    ∀ k, N + 1 ≤ k → x k ≤ Ssum u w k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    rw [Ssum_succ]
    have h1 := Ssum_nonneg u w hu0 hu1 hw0 N
    have h2 : 0 ≤ 1 - u (N + 1) := by linarith [hu1 (N + 1) (by omega)]
    nlinarith
  | succ k hk ih =>
    rw [Ssum_succ]
    have h2 : 0 ≤ 1 - u (k + 1) := by linarith [hu1 (k + 1) (by omega)]
    calc x (k + 1) ≤ (1 - u (k + 1)) * x k + u (k + 1) * w (k + 1) := hstep k hk
      _ ≤ _ := by gcongr

lemma rp_div (A B p q X : ℝ) (hX : 0 < X) (hB : B ≠ 0) :
    (A / X ^ p) / (B / X ^ q) = A / B * X ^ (-(p - q)) := by
  rw [Real.rpow_neg hX.le, Real.rpow_sub hX]
  have h1 : 0 < X ^ p := Real.rpow_pos_of_pos hX p
  have h2 : 0 < X ^ q := Real.rpow_pos_of_pos hX q
  field_simp

lemma rp_sq (A τ X : ℝ) (hX : 0 < X) : (A / X ^ τ) ^ 2 = A ^ 2 * X ^ (-(2 * τ)) := by
  rw [Real.rpow_neg hX.le, mul_comm 2 τ, Real.rpow_mul hX.le, Real.rpow_two]
  have h1 : 0 < X ^ τ := Real.rpow_pos_of_pos hX τ
  field_simp

lemma rp_sqrt (B C e τ X : ℝ) (hX : 0 < X) (hB : 0 ≤ B) (hC : C ≠ 0) :
    Real.sqrt (B / X ^ e) / (C / X ^ τ) = Real.sqrt B / C * X ^ (-(e / 2 - τ)) := by
  rw [Real.sqrt_div' B (Real.rpow_nonneg hX.le _), Real.sqrt_eq_rpow (X ^ e),
    ← Real.rpow_mul hX.le]
  rw [rp_div _ _ _ _ _ hX hC]
  ring_nf

lemma rp_pow_sq (X z : ℝ) (hX : 0 < X) : (X ^ z) ^ 2 = X ^ (2 * z) := by
  rw [mul_comm, Real.rpow_mul hX.le, Real.rpow_two]

lemma exp_neg_of_tendsto (f : ℕ → ℝ) (A e : ℝ) (hA : 0 < A)
    (hf : ∀ k : ℕ, f k = A * ((k : ℝ) + 1) ^ e) (ht : Tendsto f atTop (𝓝 0)) : e < 0 := by
  by_contra h
  push Not at h
  have hge : ∀ k : ℕ, A ≤ f k := by
    intro k
    rw [hf k]
    have : 1 ≤ ((k : ℝ) + 1) ^ e := Real.one_le_rpow (by linarith [k.cast_nonneg (α := ℝ)]) h
    nlinarith
  have := ge_of_tendsto' ht hge
  linarith

lemma exp_lt_of_summable (A e : ℝ) (hA : 0 < A)
    (hs : Summable (fun k : ℕ => A * ((k : ℝ) + 1) ^ e)) : e < -1 := by
  have h1 : Summable (fun k : ℕ => ((k : ℝ) + 1) ^ e) := by
    have := hs.mul_left A⁻¹
    refine this.congr (fun k => ?_)
    field_simp
  have h2 : Summable (fun k : ℕ => (((k + 1 : ℕ) : ℝ)) ^ e) := by
    refine h1.congr (fun k => ?_)
    push_cast; rfl
  have h3 : Summable (fun n : ℕ => (n : ℝ) ^ e) :=
    (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ e) 1).1 h2
  exact Real.summable_nat_rpow.1 h3

lemma kpow_le (k : ℕ) (hk : 1 ≤ k) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (k : ℝ) ^ (-s) ≤ 2 * ((k : ℝ) + 1) ^ (-s) := by
  have hk0 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hX : (0 : ℝ) < k := by linarith
  rw [Real.rpow_neg hX.le, Real.rpow_neg (by linarith)]
  have h1 : 0 < (k : ℝ) ^ s := Real.rpow_pos_of_pos hX s
  have h2 : ((k : ℝ) + 1) ^ s ≤ 2 * (k : ℝ) ^ s := by
    calc ((k : ℝ) + 1) ^ s ≤ (2 * (k : ℝ)) ^ s :=
          Real.rpow_le_rpow (by linarith) (by linarith) hs0
      _ = 2 ^ s * (k : ℝ) ^ s := Real.mul_rpow (by norm_num) hX.le
      _ ≤ 2 * (k : ℝ) ^ s := by
          gcongr
          calc (2:ℝ) ^ s ≤ 2 ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs1
            _ = 2 := Real.rpow_one 2
  have h3 : 0 < ((k : ℝ) + 1) ^ s := Real.rpow_pos_of_pos (by linarith) s
  rw [inv_le_iff_one_le_mul₀ h1]
  calc (1 : ℝ) = ((k : ℝ) + 1) ^ s * (((k : ℝ) + 1) ^ s)⁻¹ := by field_simp
    _ ≤ (2 * (k : ℝ) ^ s) * (((k : ℝ) + 1) ^ s)⁻¹ := by gcongr
    _ = _ := by ring

lemma fin_ineq (x S1 S2 S3 B1 B2 B3 A1 A2 A3 T1 T2 T3 : ℝ) (hx : x ≤ S1 + S2 + S3)
    (h1 : S1 ≤ B1) (h2 : S2 ≤ B2) (h3 : S3 ≤ B3) (m1 : B1 ≤ 2 * A1 * T1) (m2 : B2 ≤ 2 * A2 * T2)
    (m3 : B3 ≤ 2 * A3 * T3) (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2) (hA3 : 0 ≤ A3) (hT1 : 0 ≤ T1)
    (hT2 : 0 ≤ T2) (hT3 : 0 ≤ T3) : x ≤ 2 * (A1 + A2 + A3) * (T1 + T2 + T3) := by
  nlinarith [mul_nonneg hA1 hT2, mul_nonneg hA1 hT3, mul_nonneg hA2 hT1, mul_nonneg hA2 hT3,
      mul_nonneg hA3 hT1, mul_nonneg hA3 hT2]

end SPQOT3Seq


open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal RealInnerProductSpace
open QuantileSPQO.Rate SPQOT3Aux SPQOT3Seq

theorem solution {Ω : Type*} [m0 : MeasurableSpace Ω] {d : ℕ} (hd : 0 < d)
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (M : Model d) (Θ : Set (E d)) (Proj : E d → E d) (I : Set ℝ) (Pq : ℝ → ℝ)
    (α β γ c : ℕ → ℝ) (R : Run Ω d)
    (hΘ : IsConstraintSet Θ) (hM : IsQuantileModel M Θ)
    (hProj : SpectralProjGrad.Shared.IsProjOnto Θ Proj)
    (hrun : IsSPQORun P ℱ M Θ Proj I Pq α β γ c R)
    (hA1 : A1 P M R) (hA2 : A2 P ℱ R) (hA3a : A3a β c)
    (hA3b : A3b γ) (hA3c : A3c α) (hA3d : A3d α β γ)
    (hB1 : B1 P M R)
    (hB2 : B2 M Θ) (θstar : E d) (hB3 : B3 P M R θstar)
    (hpoly : PolySteps α β γ c)
    (hq2 : ∃ U : Set (E d), IsOpen U ∧ Θ ⊆ U ∧ ContDiffOn ℝ 2 M.qf U)
    (hstar : θstar ∈ interior Θ)
    (hstat : ∀ θ ∈ Θ, (∀ θ' ∈ Θ, 0 ≤ ⟪gradient M.qf θ, θ' - θ⟫) ↔ θ = θstar) :
    ∃ C : ℝ, ∀ᶠ k in atTop,
      ∫⁻ ω, ‖R.θ k ω - θstar‖ₑ ∂P
        ≤ ENNReal.ofReal (C * (α k / γ k + c k ^ 2 + Real.sqrt (β k) / c k)) := by
  obtain ⟨C5, hC5, hl5⟩ := lemma_5 hd P ℱ M Θ Proj I Pq α β γ c R hΘ hM hProj hrun hA1 hA2
    hA3a hA3b hA3c hA3d hB1 hB2 hpoly hq2
  obtain ⟨a, b, r, c₀, eα, eβ, eγ, τ, ha, hb, hr, hc0, ⟨heα0, heα1⟩, ⟨heβ0, heβ1⟩,
    ⟨heγ0, heγ1⟩, ⟨hτ0, hτ1⟩, hsteps⟩ := hpoly
  have hX : ∀ k : ℕ, (0:ℝ) < (k:ℝ) + 1 := fun k => by positivity
  have hαk : ∀ k, α k = a / ((k:ℝ) + 1) ^ eα := fun k => (hsteps k).1
  have hβk : ∀ k, β k = b / ((k:ℝ) + 1) ^ eβ := fun k => (hsteps k).2.1
  have hγk : ∀ k, γ k = r / ((k:ℝ) + 1) ^ eγ := fun k => (hsteps k).2.2.1
  have hck : ∀ k, c k = c₀ / ((k:ℝ) + 1) ^ τ := fun k => (hsteps k).2.2.2
  have hαpos : ∀ k, 0 < α k := fun k => by
    rw [hαk]; exact div_pos ha (Real.rpow_pos_of_pos (hX k) _)
  have hαle : ∀ k, α k ≤ a := fun k => by
    rw [hαk]
    exact div_le_self ha.le (Real.one_le_rpow (by linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]) heα0.le)
  have iαγ : ∀ k : ℕ, α k / γ k = a / r * ((k:ℝ) + 1) ^ (-(eα - eγ)) := fun k => by
    rw [hαk, hγk]; exact rp_div _ _ _ _ _ (hX k) hr.ne'
  have ic2 : ∀ k : ℕ, c k ^ 2 = c₀ ^ 2 * ((k:ℝ) + 1) ^ (-(2 * τ)) := fun k => by
    rw [hck]; exact rp_sq _ _ _ (hX k)
  have iβc : ∀ k : ℕ, Real.sqrt (β k) / c k = Real.sqrt b / c₀ * ((k:ℝ) + 1) ^ (-(eβ / 2 - τ)) :=
    fun k => by rw [hβk, hck]; exact rp_sqrt _ _ _ _ _ (hX k) hb.le hc0.ne'
  have hs1 : eγ < eα := by
    have := exp_neg_of_tendsto (fun k => α k / γ k) (a / r) (-(eα - eγ)) (by positivity) iαγ hA3d.1
    linarith
  have hs2 : 2 * τ - 2 * eβ < -1 := by
    apply exp_lt_of_summable ((b / c₀) ^ 2) (2 * τ - 2 * eβ) (by positivity)
    refine hA3a.2.2.2.congr (fun k => ?_)
    rw [hβk, hck, ← div_pow, rp_div _ _ _ _ _ (hX k) hc0.ne', mul_pow, rp_pow_sq _ _ (hX k)]
    ring_nf
  -- geometry
  have hθΘ : ∀ k ω, R.θ k ω ∈ Θ := by
    intro k ω
    induction k with
    | zero =>
      obtain ⟨θ₀, hθ₀, q₀, _, D₀, h⟩ := hrun.init
      rw [(h ω).1]; exact hθ₀
    | succ k _ => rw [hrun.eq22]; exact (hProj _).1
  have hsΘ : θstar ∈ Θ := interior_subset hstar
  have hg0 : gradient M.qf θstar = 0 := grad_zero hstar ((hstat θstar hsΘ).2 rfl)
  obtain ⟨L, hL, hLip⟩ := grad_lip hΘ.convex hΘ.isCompact hq2
  obtain ⟨ϱ, hϱ, hB3'⟩ := hB3
  obtain ⟨Rb, hRb⟩ : ∃ Rb, ∀ x ∈ Θ, ‖x‖ ≤ Rb := hΘ.isCompact.isBounded.exists_norm_le
  set ϱ' := min (ϱ / 2) (1 / (2 * a)) with hϱ'def
  have hϱ'pos : 0 < ϱ' := lt_min (by positivity) (by positivity)
  have hϱ'1 : ϱ' ≤ ϱ / 2 := min_le_left _ _
  have hϱ'2 : a * ϱ' ≤ 1 / 2 := by
    have : ϱ' ≤ 1 / (2 * a) := min_le_right _ _
    calc a * ϱ' ≤ a * (1 / (2 * a)) := mul_le_mul_of_nonneg_left this ha.le
      _ = 1 / 2 := by field_simp
  -- α → 0
  have hαt : Tendsto α atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => (k:ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have h3 := ((tendsto_rpow_neg_atTop heα0).comp h1).const_mul a
    simp only [mul_zero] at h3
    refine h3.congr (fun k => ?_)
    simp only [Function.comp, hαk k, Real.rpow_neg (hX k).le, div_eq_mul_inv]
  have hev0 : ∀ᶠ k in atTop, α k * L ^ 2 ≤ ϱ ∧ α k * ϱ ≤ 2 := by
    have e1 : ∀ᶠ k in atTop, α k < ϱ / L ^ 2 := hαt.eventually (gt_mem_nhds (by positivity))
    have e2 : ∀ᶠ k in atTop, α k < 2 / ϱ := hαt.eventually (gt_mem_nhds (by positivity))
    filter_upwards [e1, e2] with k h1 h2
    constructor
    · rw [lt_div_iff₀ (by positivity)] at h1; linarith
    · rw [lt_div_iff₀ hϱ] at h2; linarith
  obtain ⟨N, hN⟩ := (hev0.and hl5).exists_forall_of_atTop
  set rr : ℕ → ℝ := fun k => α k / γ k + c k ^ 2 + Real.sqrt (β k) / c k with hrrdef
  have hrr : ∀ k, 0 < rr k := by
    intro k
    have h1 : 0 < α k / γ k := div_pos (hαpos k) (hA3b.1 k)
    have h2 : 0 ≤ c k ^ 2 := sq_nonneg _
    have h3 : 0 ≤ Real.sqrt (β k) / c k := div_nonneg (Real.sqrt_nonneg _) (hA3a.1 k).2.le
    simp only [hrrdef]; linarith
  have hmeasθ : ∀ k, Measurable (R.θ k) := fun k =>
    ((hrun.adapted_θ k).mono (ℱ.le k)).measurable
  have hbd : ∀ k ω, ‖R.θ k ω - θstar‖ ≤ 2 * Rb := by
    intro k ω
    have h1 := hRb _ (hθΘ k ω)
    have h2 := hRb _ hsΘ
    calc ‖R.θ k ω - θstar‖ ≤ ‖R.θ k ω‖ + ‖θstar‖ := norm_sub_le _ _
      _ ≤ 2 * Rb := by linarith
  set x : ℕ → ℝ := fun k => (∫⁻ ω, ‖R.θ k ω - θstar‖ₑ ∂P).toReal with hxdef
  have hxfin : ∀ k, ∫⁻ ω, ‖R.θ k ω - θstar‖ₑ ∂P ≠ ⊤ := by
    intro k
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := 2 * Rb)) ?_
    calc ∫⁻ ω, ‖R.θ k ω - θstar‖ₑ ∂P ≤ ∫⁻ ω, ENNReal.ofReal (2 * Rb) ∂P :=
          lintegral_mono (fun ω => by
            rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hbd k ω))
      _ = ENNReal.ofReal (2 * Rb) := by simp
  have hx0 : ∀ k, 0 ≤ x k := fun k => ENNReal.toReal_nonneg
  set η : ℕ → Ω → E d := fun k ω => R.D k ω - gradient M.qf (R.θ k ω) with hηdef
  set y : ℕ → ℝ := fun k => (∫⁻ ω, ‖η k ω‖ₑ ∂P).toReal with hydef
  have hy : ∀ k, N ≤ k → ∫⁻ ω, ‖η k ω‖ₑ ∂P ≤ ENNReal.ofReal ((C5 + 1) * rr k) := by
    intro k hk
    have hrk := hrr k
    apply enorm_le_of_sq P _ _ (by positivity)
    refine (hN k hk).2.trans (ENNReal.ofReal_le_ofReal ?_)
    exact pow_le_pow_left₀ (by positivity) (by nlinarith) 2
  have hyfin : ∀ k, N ≤ k → ∫⁻ ω, ‖η k ω‖ₑ ∂P ≠ ⊤ := fun k hk =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hy k hk)
  have hyle : ∀ k, N ≤ k → y k ≤ (C5 + 1) * rr k := fun k hk =>
    ENNReal.toReal_le_of_le_ofReal (by have := hrr k; positivity) (hy k hk)
  -- one step, pathwise
  have hstep_ae : ∀ᵐ ω ∂P, ∀ k, N ≤ k →
      ‖R.θ (k + 1) ω - θstar‖ ≤ (1 - α k * ϱ') * ‖R.θ k ω - θstar‖ + α k * ‖η k ω‖ := by
    filter_upwards [hB3'] with ω hω k hk
    have hθk := hθΘ k ω
    rw [hrun.eq22]
    have h1 := proj_nonexp hΘ.convex hProj hsΘ (R.θ k ω - α k • R.D k ω)
    have hmono := strong_mono hϱ (hω k)
    have hlip := hLip _ hθk _ hsΘ
    have hcon := contraction (R.θ k ω - θstar) (gradient M.qf (R.θ k ω) - gradient M.qf θstar)
      (α k) ϱ L (hαpos k).le hmono hlip (hN k hk).1.1 (hN k hk).1.2 hL.le
    have e : R.θ k ω - α k • R.D k ω - θstar =
        ((R.θ k ω - θstar) - α k • (gradient M.qf (R.θ k ω) - gradient M.qf θstar))
          - α k • η k ω := by
      simp only [hηdef, hg0, sub_zero, smul_sub]; abel
    have hle2 : α k * ϱ' ≤ α k * ϱ / 2 := by
      have := mul_le_mul_of_nonneg_left hϱ'1 (hαpos k).le; linarith
    calc ‖Proj (R.θ k ω - α k • R.D k ω) - θstar‖ ≤ ‖R.θ k ω - α k • R.D k ω - θstar‖ := h1
      _ ≤ ‖(R.θ k ω - θstar) - α k • (gradient M.qf (R.θ k ω) - gradient M.qf θstar)‖
            + ‖α k • η k ω‖ := by rw [e]; exact norm_sub_le _ _
      _ ≤ (1 - α k * ϱ / 2) * ‖R.θ k ω - θstar‖ + α k * ‖η k ω‖ := by
          rw [norm_smul, Real.norm_of_nonneg (hαpos k).le]; linarith
      _ ≤ (1 - α k * ϱ') * ‖R.θ k ω - θstar‖ + α k * ‖η k ω‖ := by
          nlinarith [norm_nonneg (R.θ k ω - θstar)]
  -- one step, in mean
  have hrec : ∀ k, N ≤ k → x (k + 1) ≤ (1 - α k * ϱ') * x k + α k * y k := by
    intro k hk
    have h1m : 0 ≤ 1 - α k * ϱ' := by
      have := mul_le_mul_of_nonneg_right (hαle k) hϱ'pos.le; linarith
    have hle : ∫⁻ ω, ‖R.θ (k + 1) ω - θstar‖ₑ ∂P ≤
        ENNReal.ofReal (1 - α k * ϱ') * ∫⁻ ω, ‖R.θ k ω - θstar‖ₑ ∂P
          + ENNReal.ofReal (α k) * ∫⁻ ω, ‖η k ω‖ₑ ∂P := by
      calc ∫⁻ ω, ‖R.θ (k + 1) ω - θstar‖ₑ ∂P ≤
          ∫⁻ ω, (ENNReal.ofReal (1 - α k * ϱ') * ‖R.θ k ω - θstar‖ₑ
            + ENNReal.ofReal (α k) * ‖η k ω‖ₑ) ∂P := by
            apply lintegral_mono_ae
            filter_upwards [hstep_ae] with ω hω
            rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
              ← ENNReal.ofReal_mul h1m, ← ENNReal.ofReal_mul (hαpos k).le,
              ← ENNReal.ofReal_add (mul_nonneg h1m (norm_nonneg _))
                (mul_nonneg (hαpos k).le (norm_nonneg _))]
            exact ENNReal.ofReal_le_ofReal (hω k hk)
        _ = _ := by
            rw [lintegral_add_left (((hmeasθ k).sub_const θstar).enorm.const_mul _),
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hfin1 : ENNReal.ofReal (1 - α k * ϱ') * ∫⁻ ω, ‖R.θ k ω - θstar‖ₑ ∂P ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hxfin k)
    have hfin2 : ENNReal.ofReal (α k) * ∫⁻ ω, ‖η k ω‖ₑ ∂P ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hyfin k hk)
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin1, hfin2⟩) hle
    rw [ENNReal.toReal_add hfin1 hfin2, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal h1m, ENNReal.toReal_ofReal (hαpos k).le] at this
    exact this
  -- comparison sequence
  set u : ℕ → ℝ := fun j => a * ϱ' / (j : ℝ) ^ eα with hudef
  have hu_eq : ∀ k : ℕ, u (k + 1) = α k * ϱ' := by
    intro k; simp only [hudef]; push_cast; rw [hαk]; ring
  have hupos : ∀ j, 1 ≤ j → 0 < u j := by
    intro j hj
    have : (0:ℝ) < j := by exact_mod_cast hj
    simp only [hudef]; exact div_pos (by positivity) (Real.rpow_pos_of_pos this _)
  have hu0 : ∀ j, 1 ≤ j → 0 ≤ u j := fun j hj => (hupos j hj).le
  have hu1 : ∀ j, 1 ≤ j → u j ≤ 1 := by
    intro j hj
    have : (1:ℝ) ≤ j := by exact_mod_cast hj
    simp only [hudef]
    calc a * ϱ' / (j:ℝ) ^ eα ≤ a * ϱ' :=
          div_le_self (by positivity) (Real.one_le_rpow this heα0.le)
      _ ≤ 1 := by linarith
  set Kc := (C5 + 1) / ϱ' with hKc
  set K1 := Kc * (a / r) with hK1
  set K2 := Kc * c₀ ^ 2 with hK2
  set K3 := Kc * (Real.sqrt b / c₀) with hK3
  have hKc0 : 0 < Kc := by positivity
  have hK10 : 0 < K1 := by positivity
  have hK20 : 0 < K2 := by positivity
  have hK30 : 0 < K3 := by
    have : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
    positivity
  set bump : ℕ → ℝ := fun j => if j = N + 1 then x N / u (N + 1) else 0 with hbump
  have hbump0 : ∀ j, 0 ≤ bump j := by
    intro j; simp only [hbump]; split_ifs
    · exact div_nonneg (hx0 N) (hu0 _ (by omega))
    · exact le_rfl
  set w1 : ℕ → ℝ := fun j => K1 * (j : ℝ) ^ (-(eα - eγ)) + bump j with hw1
  set w2 : ℕ → ℝ := fun j => K2 * (j : ℝ) ^ (-(2 * τ)) with hw2
  set w3 : ℕ → ℝ := fun j => K3 * (j : ℝ) ^ (-(eβ / 2 - τ)) with hw3
  set w : ℕ → ℝ := fun j => (w1 j + w2 j) + w3 j with hw
  have hw_eq : ∀ k : ℕ, w (k + 1) = Kc * rr k + bump (k + 1) := by
    intro k
    simp only [hw, hw1, hw2, hw3, hrrdef, hK1, hK2, hK3]
    push_cast
    rw [iαγ k, ic2 k, iβc k]
    ring
  have hw0 : ∀ j, 1 ≤ j → 0 ≤ w j := by
    intro j hj
    have hj0 : (0:ℝ) < j := by exact_mod_cast hj
    simp only [hw, hw1, hw2, hw3]
    have := hbump0 j
    have h1 := Real.rpow_pos_of_pos hj0 (-(eα - eγ))
    have h2 := Real.rpow_pos_of_pos hj0 (-(2 * τ))
    have h3 := Real.rpow_pos_of_pos hj0 (-(eβ / 2 - τ))
    positivity
  have hW : ∀ k, N ≤ k → α k * y k ≤ u (k + 1) * (Kc * rr k) := by
    intro k hk
    rw [hu_eq, hKc]
    have := hyle k hk
    have e : α k * ϱ' * ((C5 + 1) / ϱ' * rr k) = α k * ((C5 + 1) * rr k) := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left this (hαpos k).le
  have hcmp := cmp u w x N hu0 hu1 hw0 (by
      have h1 := hrec N le_rfl
      have h2 := hW N le_rfl
      rw [hw_eq N]
      have hb : bump (N + 1) = x N / u (N + 1) := by simp [hbump]
      rw [hb, mul_add, mul_div_cancel₀ _ (hupos (N + 1) (by omega)).ne']
      have h3 : 0 ≤ u (N + 1) * x N := mul_nonneg (hu0 _ (by omega)) (hx0 N)
      rw [← hu_eq] at h1
      nlinarith)
    (by
      intro k hk
      have h1 := hrec k (by omega)
      have h2 := hW k (by omega)
      rw [← hu_eq] at h1
      have h3 : u (k + 1) * (Kc * rr k) ≤ u (k + 1) * w (k + 1) := by
        rw [hw_eq k]
        exact mul_le_mul_of_nonneg_left (by linarith [hbump0 (k + 1)]) (hu0 _ (by omega))
      linarith)
  -- Lemma 3, three times
  have hs1' : eα - eγ ∈ Set.Ioo (0:ℝ) 1 := ⟨by linarith, by linarith⟩
  have hs2' : 2 * τ ∈ Set.Ioo (0:ℝ) 1 := ⟨by linarith, by linarith⟩
  have hs3' : eβ / 2 - τ ∈ Set.Ioo (0:ℝ) 1 := ⟨by linarith, by linarith⟩
  have haϱ : 0 < a * ϱ' := by positivity
  have hpow_eq : ∀ (K s : ℝ) (i : ℕ), 1 ≤ i → K * (i : ℝ) ^ (-s) = K / (i : ℝ) ^ s := by
    intro K s i hi
    have : (0:ℝ) < i := by exact_mod_cast hi
    rw [Real.rpow_neg this.le, div_eq_mul_inv]
  obtain ⟨C1, hC1⟩ := lemma_3 (a * ϱ') eα (eα - eγ) haϱ ⟨heα0, heα1⟩ hs1' w1
    (fun i hi => by
      have hi0 : (0:ℝ) < i := by exact_mod_cast hi
      have := hbump0 i
      have h1 := Real.rpow_pos_of_pos hi0 (-(eα - eγ))
      simp only [hw1]; positivity)
    ⟨K1, by
      filter_upwards [eventually_ge_atTop (N + 2)] with i hi
      have hb : bump i = 0 := by simp only [hbump]; rw [if_neg (by omega)]
      simp only [hw1, hb, add_zero]
      rw [hpow_eq _ _ _ (by omega)]⟩
  obtain ⟨C2, hC2⟩ := lemma_3 (a * ϱ') eα (2 * τ) haϱ ⟨heα0, heα1⟩ hs2' w2
    (fun i hi => by
      have hi0 : (0:ℝ) < i := by exact_mod_cast hi
      have h1 := Real.rpow_pos_of_pos hi0 (-(2 * τ))
      simp only [hw2]; positivity)
    ⟨K2, by
      filter_upwards [eventually_ge_atTop 1] with i hi
      simp only [hw2]; rw [hpow_eq _ _ _ hi]⟩
  obtain ⟨C3, hC3⟩ := lemma_3 (a * ϱ') eα (eβ / 2 - τ) haϱ ⟨heα0, heα1⟩ hs3' w3
    (fun i hi => by
      have hi0 : (0:ℝ) < i := by exact_mod_cast hi
      have h1 := Real.rpow_pos_of_pos hi0 (-(eβ / 2 - τ))
      simp only [hw3]; positivity)
    ⟨K3, by
      filter_upwards [eventually_ge_atTop 1] with i hi
      simp only [hw3]; rw [hpow_eq _ _ _ hi]⟩
  have hsqb : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  refine ⟨2 * (max C1 0 * (r / a) + max C2 0 / c₀ ^ 2 + max C3 0 * (c₀ / Real.sqrt b)), ?_⟩
  filter_upwards [hC1, hC2, hC3, eventually_ge_atTop (N + 1)] with k h1 h2 h3 hk
  have hk1 : 1 ≤ k := by omega
  have hxk := hcmp k hk
  have hsplit : Ssum u w k = Ssum u w1 k + Ssum u w2 k + Ssum u w3 k := by
    simp only [hw]
    rw [Ssum_add u (fun i => w1 i + w2 i) w3, Ssum_add u w1 w2]
  have h1' : Ssum u w1 k ≤ C1 * (k : ℝ) ^ (-(eα - eγ)) := h1
  have h2' : Ssum u w2 k ≤ C2 * (k : ℝ) ^ (-(2 * τ)) := h2
  have h3' : Ssum u w3 k ≤ C3 * (k : ℝ) ^ (-(eβ / 2 - τ)) := h3
  -- convert k^{-s} into the rate terms
  have t1 : (k : ℝ) ^ (-(eα - eγ)) ≤ 2 * (r / a * (α k / γ k)) := by
    have := kpow_le k hk1 (eα - eγ) hs1'.1.le hs1'.2.le
    rw [iαγ k]
    calc (k : ℝ) ^ (-(eα - eγ)) ≤ 2 * ((k:ℝ) + 1) ^ (-(eα - eγ)) := this
      _ = _ := by field_simp
  have t2 : (k : ℝ) ^ (-(2 * τ)) ≤ 2 * (c k ^ 2 / c₀ ^ 2) := by
    have := kpow_le k hk1 (2 * τ) hs2'.1.le hs2'.2.le
    rw [ic2 k]
    calc (k : ℝ) ^ (-(2 * τ)) ≤ 2 * ((k:ℝ) + 1) ^ (-(2 * τ)) := this
      _ = _ := by field_simp
  have t3 : (k : ℝ) ^ (-(eβ / 2 - τ)) ≤ 2 * (c₀ / Real.sqrt b * (Real.sqrt (β k) / c k)) := by
    have := kpow_le k hk1 (eβ / 2 - τ) hs3'.1.le hs3'.2.le
    rw [iβc k]
    calc (k : ℝ) ^ (-(eβ / 2 - τ)) ≤ 2 * ((k:ℝ) + 1) ^ (-(eβ / 2 - τ)) := this
      _ = _ := by field_simp
  have hkp : ∀ s : ℝ, 0 ≤ (k : ℝ) ^ s := fun s => Real.rpow_nonneg (Nat.cast_nonneg k) s
  have m1 : C1 * (k : ℝ) ^ (-(eα - eγ)) ≤ max C1 0 * (2 * (r / a * (α k / γ k))) :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (hkp _)).trans
      (mul_le_mul_of_nonneg_left t1 (le_max_right _ _))
  have m2 : C2 * (k : ℝ) ^ (-(2 * τ)) ≤ max C2 0 * (2 * (c k ^ 2 / c₀ ^ 2)) :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (hkp _)).trans
      (mul_le_mul_of_nonneg_left t2 (le_max_right _ _))
  have m3 : C3 * (k : ℝ) ^ (-(eβ / 2 - τ)) ≤
      max C3 0 * (2 * (c₀ / Real.sqrt b * (Real.sqrt (β k) / c k))) :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (hkp _)).trans
      (mul_le_mul_of_nonneg_left t3 (le_max_right _ _))
  have hT1 : 0 ≤ α k / γ k := (div_pos (hαpos k) (hA3b.1 k)).le
  have hT2 : 0 ≤ c k ^ 2 := sq_nonneg _
  have hT3 : 0 ≤ Real.sqrt (β k) / c k := div_nonneg (Real.sqrt_nonneg _) (hA3a.1 k).2.le
  have hA1 : 0 ≤ max C1 0 * (r / a) := mul_nonneg (le_max_right _ _) (by positivity)
  have hA2 : 0 ≤ max C2 0 / c₀ ^ 2 := div_nonneg (le_max_right _ _) (by positivity)
  have hA3 : 0 ≤ max C3 0 * (c₀ / Real.sqrt b) := mul_nonneg (le_max_right _ _) (by positivity)
  have hfinal : x k ≤ 2 * (max C1 0 * (r / a) + max C2 0 / c₀ ^ 2 + max C3 0 * (c₀ / Real.sqrt b))
      * (α k / γ k + c k ^ 2 + Real.sqrt (β k) / c k) := by
    have e1 : max C1 0 * (2 * (r / a * (α k / γ k))) = 2 * (max C1 0 * (r / a)) * (α k / γ k) := by ring
    have e2 : max C2 0 * (2 * (c k ^ 2 / c₀ ^ 2)) = 2 * (max C2 0 / c₀ ^ 2) * c k ^ 2 := by ring
    have e3 : max C3 0 * (2 * (c₀ / Real.sqrt b * (Real.sqrt (β k) / c k)))
        = 2 * (max C3 0 * (c₀ / Real.sqrt b)) * (Real.sqrt (β k) / c k) := by ring
    rw [e1] at m1; rw [e2] at m2; rw [e3] at m3
    exact fin_ineq _ _ _ _ _ _ _ _ _ _ _ _ _ (hxk.trans (le_of_eq hsplit)) h1' h2' h3' m1 m2 m3
      hA1 hA2 hA3 hT1 hT2 hT3
  rw [← ENNReal.ofReal_toReal (hxfin k)]
  exact ENNReal.ofReal_le_ofReal hfinal
