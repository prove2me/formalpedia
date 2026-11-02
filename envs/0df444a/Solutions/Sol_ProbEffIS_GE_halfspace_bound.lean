-- Prove2me | solution 1 for ProbEffIS.GE.halfspace_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-02T02:08:54.017701+00:00
-- url     : https://prove2.me/submissions/96ce3228-d834-4d5c-a4ec-e3b2e87c6b83

import Mathlib
import Definitions.Def_ProbEffIS_GE_Defs

open MeasureTheory Filter Topology ProbabilityTheory
open scoped RealInnerProductSpace

namespace ProbEffIS.GE.HB

variable {d : ℕ}

/-- Hölder's inequality for the moment generating function. -/
lemma mgf_holder (m : Measure (Rd d)) (u v : Rd d) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    ∫⁻ y, ENNReal.ofReal (Real.exp (inner ℝ ((1 - t) • u + t • v) y)) ∂m ≤
      (∫⁻ y, ENNReal.ofReal (Real.exp (inner ℝ u y)) ∂m) ^ (1 - t) *
      (∫⁻ y, ENNReal.ofReal (Real.exp (inner ℝ v y)) ∂m) ^ t := by
  have h1t : 0 < 1 - t := by linarith
  set f : Rd d → ENNReal := fun y => ENNReal.ofReal (Real.exp (inner ℝ u y)) ^ (1 - t)
  set g : Rd d → ENNReal := fun y => ENNReal.ofReal (Real.exp (inner ℝ v y)) ^ t
  have hcont : ∀ w : Rd d, Continuous fun y : Rd d => Real.exp (inner ℝ w y) := fun w =>
    Real.continuous_exp.comp (continuous_const.inner continuous_id)
  have hf : AEMeasurable f m :=
    ((ENNReal.continuous_ofReal.comp (hcont u)).measurable.pow_const _).aemeasurable
  have hg : AEMeasurable g m :=
    ((ENNReal.continuous_ofReal.comp (hcont v)).measurable.pow_const _).aemeasurable
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq m
    (Real.holderConjugate_one_div h1t ht0 (by ring)) hf hg
  have hfg : ∀ y, (f * g) y = ENNReal.ofReal (Real.exp (inner ℝ ((1 - t) • u + t • v) y)) := by
    intro y
    simp only [Pi.mul_apply, f, g]
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le h1t.le,
      ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le ht0.le, ← ENNReal.ofReal_mul (by positivity),
      ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add, inner_add_left, inner_smul_left,
      inner_smul_left]
    congr 2
    simp only [RCLike.conj_to_real]
    ring
  have hfp : ∀ y, f y ^ (1 / (1 - t)) = ENNReal.ofReal (Real.exp (inner ℝ u y)) := by
    intro y
    simp only [f]
    rw [← ENNReal.rpow_mul, mul_one_div_cancel h1t.ne', ENNReal.rpow_one]
  have hgq : ∀ y, g y ^ (1 / t) = ENNReal.ofReal (Real.exp (inner ℝ v y)) := by
    intro y
    simp only [g]
    rw [← ENNReal.rpow_mul, mul_one_div_cancel ht0.ne', ENNReal.rpow_one]
  simp only [hfg, hfp, hgq, one_div_one_div] at hH
  exact hH

/-- Convexity of the scaled log-MGF for a fixed positive parameter. -/
lemma slmgf_convex (ν : ℝ → Measure (Rd d)) (γ : ℝ) (hγ : 0 < γ) (u v : Rd d) (t : ℝ)
    (ht0 : 0 < t) (ht1 : t < 1) :
    scaledLogMGF ν γ ((1 - t) • u + t • v) ≤
      ((1 - t : ℝ) : EReal) * scaledLogMGF ν γ u + (t : EReal) * scaledLogMGF ν γ v := by
  unfold scaledLogMGF
  have hγ' : (0 : EReal) ≤ ((γ⁻¹ : ℝ) : EReal) := by exact_mod_cast (inv_pos.2 hγ).le
  calc ((γ⁻¹ : ℝ) : EReal) * ENNReal.log
        (∫⁻ y, ENNReal.ofReal (Real.exp (inner ℝ ((1 - t) • u + t • v) y)) ∂(ν γ))
      ≤ ((γ⁻¹ : ℝ) : EReal) * ENNReal.log
        ((∫⁻ y, ENNReal.ofReal (Real.exp (inner ℝ u y)) ∂(ν γ)) ^ (1 - t) *
          (∫⁻ y, ENNReal.ofReal (Real.exp (inner ℝ v y)) ∂(ν γ)) ^ t) :=
        mul_le_mul_of_nonneg_left (ENNReal.log_monotone (mgf_holder _ u v t ht0 ht1)) hγ'
    _ = _ := by
        rw [ENNReal.log_mul_add, ENNReal.log_rpow, ENNReal.log_rpow,
          EReal.left_distrib_of_nonneg_of_ne_top hγ' (EReal.coe_ne_top _), mul_left_comm,
          mul_left_comm ((γ⁻¹ : ℝ) : EReal)]


lemma coe_mul_ne_top {c : ℝ} (hc : 0 < c) {x : EReal} (hx : x ≠ ⊤) : (c : EReal) * x ≠ ⊤ := by
  induction x using EReal.rec with
  | bot => rw [EReal.coe_mul_bot_of_pos hc]; exact bot_ne_top
  | coe x => rw [← EReal.coe_mul]; exact EReal.coe_ne_top _
  | top => exact absurd rfl hx

/-- Convexity of the limiting log-MGF on its effective domain. -/
lemma mu_convex (ν : ℝ → Measure (Rd d)) (μ : Rd d → EReal) (h1 : Assumption1 ν μ)
    (u v : Rd d) (hu : μ u ≠ ⊤) (hv : μ v ≠ ⊤) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    μ ((1 - t) • u + t • v) ≤ ((1 - t : ℝ) : EReal) * μ u + (t : EReal) * μ v := by
  have h1t : (0 : ℝ) < 1 - t := by linarith
  have hA := EReal.Tendsto.const_mul (h1.tendsto u) (a := ((1 - t : ℝ) : EReal))
    (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))
  have hB := EReal.Tendsto.const_mul (h1.tendsto v) (a := ((t : ℝ) : EReal))
    (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))
  have hR := (EReal.continuousAt_add (p := (((1 - t : ℝ) : EReal) * μ u, ((t : ℝ) : EReal) * μ v))
    (Or.inl (coe_mul_ne_top h1t hu)) (Or.inr (coe_mul_ne_top ht0 hv))).tendsto.comp
    (hA.prodMk_nhds hB)
  refine le_of_tendsto_of_tendsto (h1.tendsto _) hR ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with γ hγ
  exact slmgf_convex ν γ hγ u v t ht0 ht1

end ProbEffIS.GE.HB

open ProbEffIS.GE ProbEffIS.GE.HB in
theorem solution {d : ℕ} (ν : ℝ → Measure (Rd d))
    (μ : Rd d → EReal) (h1 : Assumption1 ν μ)
    (s a : Rd d) (hs : s ∈ interior (dom μ)) (hsa : gradE μ s = a) :
    rate μ a = ((inner ℝ s a : ℝ) : EReal) - μ s ∧
    ∀ x : Rd d, 0 ≤ inner ℝ s (x - a) → rate μ a ≤ rate μ x := by
  have hstop : μ s ≠ ⊤ := (interior_subset hs : s ∈ dom μ).ne
  have hmain : ∀ x, ((inner ℝ x a : ℝ) : EReal) - μ x ≤ ((inner ℝ s a : ℝ) : EReal) - μ s := by
    intro x
    by_cases hsbot : μ s = ⊥
    · rw [hsbot, EReal.coe_sub_bot]; exact le_top
    by_cases hxtop : μ x = ⊤
    · rw [hxtop, EReal.sub_top]; exact bot_le
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 isOpen_interior s hs
    have hdom : ∀ w ∈ Metric.ball s δ, μ w ≠ ⊤ := fun w hw =>
      (interior_subset (hball hw) : w ∈ dom μ).ne
    -- μ does not take the value ⊥ near s
    have hpos : ∀ w ∈ Metric.ball s δ, μ w ≠ ⊥ := by
      intro w hw hwb
      have hw' : (2 : ℝ) • s - w ∈ Metric.ball s δ := by
        rw [Metric.mem_ball, dist_eq_norm] at hw ⊢
        have : (2 : ℝ) • s - w - s = s - w := by module
        rw [this, norm_sub_rev]; exact hw
      have hc := mu_convex ν μ h1 w ((2 : ℝ) • s - w) (hdom w hw) (hdom _ hw') (1 / 2)
        (by norm_num) (by norm_num)
      have heq : (1 - 1 / 2 : ℝ) • w + (1 / 2 : ℝ) • ((2 : ℝ) • s - w) = s := by module
      rw [heq, hwb, EReal.coe_mul_bot_of_pos (by norm_num), EReal.bot_add] at hc
      exact hsbot (le_bot_iff.1 hc)
    set f : Rd d → ℝ := fun y => (μ y).toReal with hf_def
    have hdiff : DifferentiableAt ℝ f s :=
      h1.differentiableOn.differentiableAt (isOpen_interior.mem_nhds hs)
    have hgrad : HasGradientAt f a s := by
      rw [← hsa]; exact hdiff.hasGradientAt
    have hline : HasDerivAt (fun t : ℝ => f (s + t • (x - s))) (inner ℝ a (x - s)) 0 := by
      have h0 : HasDerivAt (fun t : ℝ => s + t • (x - s)) (x - s) 0 := by
        simpa using ((hasDerivAt_id (0:ℝ)).smul_const (x - s)).const_add s
      have hs0 : s + (0:ℝ) • (x - s) = s := by simp
      have hg' : HasFDerivAt f (InnerProductSpace.toDual ℝ (Rd d) a) (s + (0:ℝ) • (x - s)) := by
        rw [hs0]; exact hgrad.hasFDerivAt
      have := hg'.comp_hasDerivAt (0:ℝ) h0
      simp only [InnerProductSpace.toDual_apply_apply] at this
      exact this
    -- the segment stays in the ball for small t
    set t₀ : ℝ := min (1 / 2) (δ / (‖x - s‖ + 1)) with ht₀_def
    have ht₀ : 0 < t₀ := lt_min (by norm_num) (div_pos hδ (by positivity))
    have hseg : ∀ t : ℝ, 0 < t → t < t₀ → s + t • (x - s) ∈ Metric.ball s δ := by
      intro t ht htt
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos ht]
      have h2 : t < δ / (‖x - s‖ + 1) := lt_of_lt_of_le htt (min_le_right _ _)
      rw [lt_div_iff₀ (by positivity)] at h2
      nlinarith [norm_nonneg (x - s)]
    have hconv : ∀ t : ℝ, 0 < t → t < t₀ →
        μ (s + t • (x - s)) ≤ ((1 - t : ℝ) : EReal) * μ s + (t : EReal) * μ x := by
      intro t ht htt
      have h := mu_convex ν μ h1 s x hstop hxtop t ht
        (lt_of_lt_of_le htt ((min_le_left _ _).trans (by norm_num)))
      have heq : (1 - t) • s + t • x = s + t • (x - s) := by module
      rwa [heq] at h
    -- μ x is finite
    have hxbot : μ x ≠ ⊥ := by
      intro hxb
      have h := hconv (t₀ / 2) (by positivity) (by linarith)
      rw [hxb, EReal.coe_mul_bot_of_pos (by positivity), EReal.add_bot] at h
      exact hpos _ (hseg (t₀ / 2) (by positivity) (by linarith)) (le_bot_iff.1 h)
    have hμs : μ s = (f s : EReal) := (EReal.coe_toReal hstop hsbot).symm
    have hμx : μ x = (f x : EReal) := (EReal.coe_toReal hxtop hxbot).symm
    have hreal : ∀ t : ℝ, 0 < t → t < t₀ → f (s + t • (x - s)) ≤ (1 - t) * f s + t * f x := by
      intro t ht htt
      have hz := hseg t ht htt
      have hμz : μ (s + t • (x - s)) = (f (s + t • (x - s)) : EReal) :=
        (EReal.coe_toReal (hdom _ hz) (hpos _ hz)).symm
      have h := hconv t ht htt
      rw [hμz, hμs, hμx, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add,
        EReal.coe_le_coe_iff] at h
      exact h
    have hslope := hline.tendsto_slope_zero_right
    have hle : inner ℝ a (x - s) ≤ f x - f s := by
      refine le_of_tendsto hslope ?_
      have : ∀ᶠ t in 𝓝[>] (0:ℝ), t < t₀ := by
        exact nhdsWithin_le_nhds (gt_mem_nhds ht₀)
      filter_upwards [this, self_mem_nhdsWithin] with t htt (ht : 0 < t)
      have h := hreal t ht htt
      simp only [zero_add, zero_smul, add_zero, smul_eq_mul]
      rw [inv_mul_le_iff₀ ht]
      nlinarith
    rw [hμs, hμx, ← EReal.coe_sub, ← EReal.coe_sub, EReal.coe_le_coe_iff]
    rw [inner_sub_right] at hle
    have e1 := real_inner_comm a x
    have e2 := real_inner_comm a s
    linarith
  have hrate : rate μ a = ((inner ℝ s a : ℝ) : EReal) - μ s :=
    le_antisymm (iSup_le hmain) (le_iSup (fun x => ((inner ℝ x a : ℝ) : EReal) - μ x) s)
  refine ⟨hrate, fun x hx => ?_⟩
  rw [hrate]
  have hx' : inner ℝ s a ≤ inner ℝ s x := by rw [inner_sub_right] at hx; linarith
  calc ((inner ℝ s a : ℝ) : EReal) - μ s ≤ ((inner ℝ s x : ℝ) : EReal) - μ s :=
        EReal.sub_le_sub (EReal.coe_le_coe_iff.2 hx') le_rfl
    _ ≤ rate μ x := le_iSup (fun y => ((inner ℝ y x : ℝ) : EReal) - μ y) s
