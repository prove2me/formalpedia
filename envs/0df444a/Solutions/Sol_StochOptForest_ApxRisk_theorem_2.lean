-- Prove2me | solution 1 for StochOptForest.ApxRisk.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T07:41:30.352843+00:00
-- url     : https://prove2.me/submissions/5711e371-bb64-441d-96bd-280673fdd666

import Mathlib
import Definitions.Def_StochOptForest_ApxRisk_Model
import Theorems.Thm_StochOptForest_ApxRisk_theorem_9_uniform
import Theorems.Thm_StochOptForest_ApxRisk_fnorm_le_lip_diam
import Theorems.Thm_StochOptForest_ApxRisk_region_avg_derivatives
import Theorems.Thm_StochOptForest_ApxRisk_region_identity

open MeasureTheory StochOptForest.ApxRisk

namespace SOFThm2Red

lemma grad_sub {d : ℕ} {f g : Ed d → ℝ} {z : Ed d} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) :
    gradient (fun w => f w - g w) z = gradient f z - gradient g z := by
  unfold gradient
  rw [fderiv_fun_sub hf hg, map_sub]

lemma diff_grad {d : ℕ} {f : Ed d → ℝ} (hf : ContDiff ℝ 2 f) : Differentiable ℝ (gradient f) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (m := 1) (by norm_num)
  have h2 : ContDiff ℝ 1 (fun z => (InnerProductSpace.toDual ℝ (Ed d)).symm (fderiv ℝ f z)) :=
    (InnerProductSpace.toDual ℝ (Ed d)).symm.contDiff.comp h1
  exact h2.differentiable (by norm_num)

lemma hess_sub {d : ℕ} {f g : Ed d → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (z : Ed d) :
    hess (fun w => f w - g w) z = hess f z - hess g z := by
  have e : gradient (fun w => f w - g w) = fun w => gradient f w - gradient g w := by
    funext w
    exact grad_sub ((hf.differentiable (by norm_num)) w) ((hg.differentiable (by norm_num)) w)
  unfold hess
  rw [e, fderiv_fun_sub ((diff_grad hf) z) ((diff_grad hg) z)]

lemma cont_of_lip {p : ℕ} {E : Type*} [NormedAddCommGroup E] (g : Xp p → E) (L : ℝ)
    (h : ∀ x x', ‖g x - g x'‖ ≤ L * ‖x - x'‖) : Continuous g := by
  have : LipschitzWith (Real.toNNReal L) g := by
    refine LipschitzWith.of_dist_le_mul fun x x' => ?_
    rw [dist_eq_norm, dist_eq_norm]
    calc ‖g x - g x'‖ ≤ L * ‖x - x'‖ := h x x'
      _ ≤ (Real.toNNReal L : ℝ) * ‖x - x'‖ :=
        mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal L) (norm_nonneg _)
  exact this.continuous

lemma intOn_of_bdd {p : ℕ} {E : Type*} [NormedAddCommGroup E]
    (μ : Measure (Xp p)) [IsProbabilityMeasure μ] (g : Xp p → E) (hg : Continuous g)
    (R : Set (Xp p)) (hR : MeasurableSet R) (M : ℝ) (hb : ∀ x ∈ R, ‖g x‖ ≤ M) :
    IntegrableOn g R μ := by
  refine Measure.integrableOn_of_bounded (M := M) (measure_lt_top μ R).ne
    hg.aestronglyMeasurable ?_
  rw [ae_restrict_iff' hR]
  exact Filter.Eventually.of_forall hb

/-- Averaging a continuous function that stays within `K` of `v` on `R` stays within `K` of `v`. -/
lemma avg_sub_le {p : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure (Xp p)) [IsProbabilityMeasure μ] (g : Xp p → E) (hg : Continuous g)
    (R : Set (Xp p)) (hR : MeasurableSet R) (hpos : 0 < μ R) (v : E) (K : ℝ)
    (hb : ∀ x ∈ R, ‖g x - v‖ ≤ K) :
    ‖(μ R).toReal⁻¹ • (∫ x in R, g x ∂μ) - v‖ ≤ K := by
  have hfin : μ R < ⊤ := measure_lt_top μ R
  have hc : 0 < (μ R).toReal := ENNReal.toReal_pos hpos.ne' hfin.ne
  have hint : IntegrableOn g R μ := by
    refine Measure.integrableOn_of_bounded (M := ‖v‖ + K) hfin.ne
      hg.aestronglyMeasurable ?_
    rw [ae_restrict_iff' hR]
    refine Filter.Eventually.of_forall fun x hx => ?_
    calc ‖g x‖ = ‖(g x - v) + v‖ := by rw [sub_add_cancel]
      _ ≤ ‖g x - v‖ + ‖v‖ := norm_add_le _ _
      _ ≤ ‖v‖ + K := by linarith [hb x hx]
  have e1 : ∫ x in R, (g x - v) ∂μ = (∫ x in R, g x ∂μ) - (μ R).toReal • v := by
    rw [integral_sub hint (integrable_const v), setIntegral_const, measureReal_def]
  have e2 : (μ R).toReal⁻¹ • (∫ x in R, g x ∂μ) - v
      = (μ R).toReal⁻¹ • ∫ x in R, (g x - v) ∂μ := by
    rw [e1, smul_sub, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
  rw [e2, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
  have h3 := norm_setIntegral_le_of_norm_le_const hfin hb
  rw [measureReal_def] at h3
  calc (μ R).toReal⁻¹ * ‖∫ x in R, (g x - v) ∂μ‖ ≤ (μ R).toReal⁻¹ * (K * (μ R).toReal) :=
        mul_le_mul_of_nonneg_left h3 (inv_pos.mpr hc).le
    _ = K := by field_simp

end SOFThm2Red

open SOFThm2Red

theorem solution {p d : ℕ} (μ : Measure (Xp p)) [IsProbabilityMeasure μ]
    (cbar : Xp p → Ed d → ℝ) (L : ℝ) (xbar : Xp p) (zbar : Ed d)
    (hC2 : ∀ x, ContDiff ℝ 2 (cbar x)) (hLip : XLipschitz cbar L)
    (hanchor : IsUniqueMin (cbar xbar) zbar) (hpd : PosDefAt (cbar xbar) zbar)
    (hlev : ∃ α : ℝ, cbar xbar zbar < α ∧ Bornology.IsBounded {z | cbar xbar z ≤ α}) :
    ∀ ε > 0, ∃ δ > 0, ∀ R0 R1 R2 : Set (Xp p),
      MeasurableSet R1 → MeasurableSet R2 → Disjoint R1 R2 → R0 = R1 ∪ R2 →
      R0 ⊆ Metric.ball xbar δ → 0 < μ R1 → 0 < μ R2 →
      -- conditions 1–3 of Theorem 2, for both j = 1, 2
      (∀ Rj ∈ ({R1, R2} : Set (Set (Xp p))),
        -- condition 1: f₀ and f_j are twice continuously differentiable
        (ContDiff ℝ 2 (regionAvg μ cbar R0) ∧ ContDiff ℝ 2 (regionAvg μ cbar Rj)) ∧
        -- condition 2: the sublevel sets are nonempty and uniformly bounded for t ∈ [0,1]
        (∃ α : ℝ, ∃ C : Set (Ed d), Bornology.IsBounded C ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1,
          {z | regionAvg μ cbar R0 z + t * (regionAvg μ cbar Rj z - regionAvg μ cbar R0 z) ≤ α}.Nonempty ∧
          {z | regionAvg μ cbar R0 z + t * (regionAvg μ cbar Rj z - regionAvg μ cbar R0 z) ≤ α} ⊆ C) ∧
        -- condition 3: a unique minimizer with positive definite Hessian for every t ∈ [0,1]
        (∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ zt : Ed d,
          IsUniqueMin (fun z => regionAvg μ cbar R0 z + t * (regionAvg μ cbar Rj z - regionAvg μ cbar R0 z)) zt ∧
          PosDefAt (fun z => regionAvg μ cbar R0 z + t * (regionAvg μ cbar Rj z - regionAvg μ cbar R0 z)) zt)) →
      ∀ z0 : Ed d, IsUniqueMin (regionAvg μ cbar R0) z0 →
        |oracleCrit μ cbar R1 R2 - regionProb μ R0 * regionAvg μ cbar R0 z0
            - apxRiskCrit μ cbar R0 R1 R2 z0|
          ≤ ε * regionProb μ R0 * Metric.diam R0 ^ 2 := by
  intro ε hε
  have hε' : 0 < ε / (L ^ 2 + 1) := by positivity
  obtain ⟨η, hη, H9⟩ := theorem_9_uniform (cbar xbar) zbar (hC2 xbar) hanchor hpd hlev
    (ε / (L ^ 2 + 1)) hε'
  have hL1 : 0 < |L| + 1 := by positivity
  refine ⟨η / (2 * (|L| + 1)), by positivity, ?_⟩
  intro R0 R1 R2 hR1 hR2 hdisj hR0 hball hpos1 hpos2 hcond z0 hz0
  set δ := η / (2 * (|L| + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  have hLδ : |L| * δ ≤ η / 2 := by
    rw [hδ]
    rw [show |L| * (η / (2 * (|L| + 1))) = (η / 2) * (|L| / (|L| + 1)) by field_simp]
    have : |L| / (|L| + 1) ≤ 1 := by rw [div_le_one hL1]; linarith
    nlinarith
  have hR0m : MeasurableSet R0 := hR0 ▸ hR1.union hR2
  have hpos0 : 0 < μ R0 := by
    rw [hR0]; exact lt_of_lt_of_le hpos1 (measure_mono Set.subset_union_left)
  have hR0b : Bornology.IsBounded R0 := Metric.isBounded_ball.subset hball
  have hD : Metric.diam R0 ≤ 2 * δ :=
    (Metric.diam_mono hball Metric.isBounded_ball).trans (Metric.diam_ball hδpos.le)
  have hD0 : 0 ≤ Metric.diam R0 := Metric.diam_nonneg
  have hN : L * Metric.diam R0 ≤ η := by
    calc L * Metric.diam R0 ≤ |L| * Metric.diam R0 :=
          mul_le_mul_of_nonneg_right (le_abs_self L) hD0
      _ ≤ |L| * (2 * δ) := mul_le_mul_of_nonneg_left hD (abs_nonneg L)
      _ = 2 * (|L| * δ) := by ring
      _ ≤ η := by linarith
  -- points of `R0` are `δ`-close to `xbar`
  have hclose : ∀ x ∈ R0, L * ‖x - xbar‖ ≤ |L| * δ := by
    intro x hx
    have hx' : ‖x - xbar‖ < δ := by
      have := hball hx; rwa [Metric.mem_ball, dist_eq_norm] at this
    calc L * ‖x - xbar‖ ≤ |L| * ‖x - xbar‖ := mul_le_mul_of_nonneg_right (le_abs_self L) (norm_nonneg _)
      _ ≤ |L| * δ := mul_le_mul_of_nonneg_left hx'.le (abs_nonneg L)
  have c1 := hcond R1 (by simp)
  set f0 := regionAvg μ cbar R0 with hf0
  have hf0C2 : ContDiff ℝ 2 f0 := c1.1.1
  -- the Hessian of `f0` at `z0` is positive definite (condition 3 at `t = 0`)
  have hpd0 : PosDefAt f0 z0 := by
    obtain ⟨zt, hzt1, hzt2⟩ := c1.2.2 0 (by simp)
    have e : (fun z => f0 z + 0 * (regionAvg μ cbar R1 z - f0 z)) = f0 := by funext z; simp
    rw [e] at hzt1 hzt2
    have : zt = z0 := hz0.2 zt hzt1.1
    rwa [this] at hzt2
  -- continuity in `x` of the cost and its derivatives
  have hcv : ∀ z, Continuous fun x => cbar x z := fun z =>
    cont_of_lip (fun x => cbar x z) L (fun x x' => by rw [Real.norm_eq_abs]; exact (hLip z x x').1)
  have hcg : ∀ z, Continuous fun x => gradient (cbar x) z := fun z =>
    cont_of_lip (fun x => gradient (cbar x) z) L (fun x x' => (hLip z x x').2.1)
  have hch : ∀ z, Continuous fun x => hess (cbar x) z := fun z =>
    cont_of_lip (fun x => hess (cbar x) z) L (fun x x' => (hLip z x x').2.2)
  -- `f0` is `η`-close to `cbar xbar` in the norm (70)
  have hF0 : FNormLE (fun z => f0 z - cbar xbar z) η := by
    obtain ⟨_, hgr, hhe⟩ := region_avg_derivatives μ cbar L hC2 hLip R0 hR0m hR0b hpos0
    intro z
    refine ⟨?_, ?_, ?_⟩
    · have h := avg_sub_le μ (fun x => cbar x z) (hcv z) R0 hR0m hpos0 (cbar xbar z) (|L| * δ)
        (fun x hx => by
          rw [Real.norm_eq_abs]; exact (hLip z x xbar).1.trans (hclose x hx))
      rw [Real.norm_eq_abs, smul_eq_mul] at h
      have : f0 z = (μ R0).toReal⁻¹ * ∫ x in R0, cbar x z ∂μ := rfl
      show |f0 z - cbar xbar z| ≤ η
      rw [this]; linarith
    · rw [grad_sub ((hf0C2.differentiable (by norm_num)) z)
        (((hC2 xbar).differentiable (by norm_num)) z), hgr z]
      have h := avg_sub_le μ (fun x => gradient (cbar x) z) (hcg z) R0 hR0m hpos0
        (gradient (cbar xbar) z) (|L| * δ)
        (fun x hx => (hLip z x xbar).2.1.trans (hclose x hx))
      linarith
    · rw [hess_sub hf0C2 (hC2 xbar), hhe z]
      have h := avg_sub_le μ (fun x => hess (cbar x) z) (hch z) R0 hR0m hpos0
        (hess (cbar xbar) z) (|L| * δ)
        (fun x hx => (hLip z x xbar).2.2.trans (hclose x hx))
      linarith
  -- the gradient of `f0` vanishes at its minimizer
  have hg0 : gradient f0 z0 = 0 := by
    have : IsLocalMin f0 z0 := Filter.Eventually.of_forall hz0.1
    simp [gradient, this.fderiv_eq_zero]
  -- Theorem 9 (uniform) applied to `δf = f_j - f_0`
  have key : ∀ Rj ∈ ({R1, R2} : Set (Set (Xp p))), MeasurableSet Rj → Rj ⊆ R0 → 0 < μ Rj →
      |optVal (regionAvg μ cbar Rj) - regionAvg μ cbar Rj z0
        + (1 / 2) * newtonQuad f0 (regionAvg μ cbar Rj) z0|
        ≤ ε / (L ^ 2 + 1) * (L * Metric.diam R0) ^ 2 := by
    intro Rj hmem hRj hsub hposj
    have cj := hcond Rj hmem
    have hfjC2 : ContDiff ℝ 2 (regionAvg μ cbar Rj) := cj.1.2
    have hδC2 : ContDiff ℝ 2 (fun z => regionAvg μ cbar Rj z - f0 z) := hfjC2.sub hf0C2
    have hFN := fnorm_le_lip_diam μ cbar L hC2 hLip R0 Rj hR0m hRj hsub hR0b hposj
    have h := H9 f0 z0 hf0C2 hF0 hz0 hpd0 (L * Metric.diam R0) hN
      (fun z => regionAvg μ cbar Rj z - f0 z) hδC2 hFN
    have e1 : (fun z => f0 z + (regionAvg μ cbar Rj z - f0 z)) = regionAvg μ cbar Rj := by
      funext z; ring
    have e2 : newtonQuad f0 (fun z => regionAvg μ cbar Rj z - f0 z) z0
        = newtonQuad f0 (regionAvg μ cbar Rj) z0 := by
      unfold newtonQuad
      rw [grad_sub ((hfjC2.differentiable (by norm_num)) z0)
        ((hf0C2.differentiable (by norm_num)) z0), hg0, sub_zero]
    rw [e1, e2] at h
    have e3 : optVal (regionAvg μ cbar Rj) - f0 z0 - (regionAvg μ cbar Rj z0 - f0 z0)
        + 1 / 2 * newtonQuad f0 (regionAvg μ cbar Rj) z0
        = optVal (regionAvg μ cbar Rj) - regionAvg μ cbar Rj z0
        + (1 / 2) * newtonQuad f0 (regionAvg μ cbar Rj) z0 := by ring
    rw [e3] at h
    exact h
  have k1 := key R1 (by simp) hR1 (hR0 ▸ Set.subset_union_left) hpos1
  have k2 := key R2 (by simp) hR2 (hR0 ▸ Set.subset_union_right) hpos2
  -- the region identity `p₁f₁(z₀) + p₂f₂(z₀) = p₀f₀(z₀)`
  have hbdd : ∀ x ∈ R0, ‖cbar x z0‖ ≤ |cbar xbar z0| + |L| * δ := by
    intro x hx
    rw [Real.norm_eq_abs]
    have h1 := (hLip z0 x xbar).1
    have h2 := hclose x hx
    have h3 : |cbar x z0| ≤ |cbar x z0 - cbar xbar z0| + |cbar xbar z0| := by
      have := abs_add_le (cbar x z0 - cbar xbar z0) (cbar xbar z0)
      simpa using this
    linarith
  have hint1 := intOn_of_bdd μ _ (hcv z0) R1 hR1 _
    (fun x hx => hbdd x (hR0 ▸ Set.mem_union_left _ hx))
  have hint2 := intOn_of_bdd μ _ (hcv z0) R2 hR2 _
    (fun x hx => hbdd x (hR0 ▸ Set.mem_union_right _ hx))
  have hid := region_identity μ cbar R1 R2 hR1 hR2 hdisj hpos1 hpos2 z0 hint1 hint2
  rw [← hR0] at hid
  -- `p₀ = p₁ + p₂`
  have hp : regionProb μ R0 = regionProb μ R1 + regionProb μ R2 := by
    unfold regionProb
    rw [hR0, measure_union hdisj hR2,
      ENNReal.toReal_add (measure_lt_top μ R1).ne (measure_lt_top μ R2).ne]
  have hp1 : 0 ≤ regionProb μ R1 := ENNReal.toReal_nonneg
  have hp2 : 0 ≤ regionProb μ R2 := ENNReal.toReal_nonneg
  -- assemble
  unfold oracleCrit apxRiskCrit
  rw [← hf0]
  set p1 := regionProb μ R1
  set p2 := regionProb μ R2
  set p0 := regionProb μ R0
  set E1 := optVal (regionAvg μ cbar R1) - regionAvg μ cbar R1 z0
        + (1 / 2) * newtonQuad f0 (regionAvg μ cbar R1) z0
  set E2 := optVal (regionAvg μ cbar R2) - regionAvg μ cbar R2 z0
        + (1 / 2) * newtonQuad f0 (regionAvg μ cbar R2) z0
  have eq : p1 * optVal (regionAvg μ cbar R1) + p2 * optVal (regionAvg μ cbar R2) - p0 * f0 z0
      - -(1 / 2) * (p1 * newtonQuad f0 (regionAvg μ cbar R1) z0
        + p2 * newtonQuad f0 (regionAvg μ cbar R2) z0) = p1 * E1 + p2 * E2 := by
    rw [← hid]; simp only [E1, E2]; ring
  rw [eq]
  set B := ε / (L ^ 2 + 1) * (L * Metric.diam R0) ^ 2
  have hB : B ≤ ε * Metric.diam R0 ^ 2 := by
    have h1 : ε / (L ^ 2 + 1) * L ^ 2 ≤ ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
    calc B = (ε / (L ^ 2 + 1) * L ^ 2) * Metric.diam R0 ^ 2 := by simp only [B]; ring
      _ ≤ ε * Metric.diam R0 ^ 2 := mul_le_mul_of_nonneg_right h1 (by positivity)
  calc |p1 * E1 + p2 * E2| ≤ |p1 * E1| + |p2 * E2| := abs_add_le _ _
    _ = p1 * |E1| + p2 * |E2| := by rw [abs_mul, abs_mul, abs_of_nonneg hp1, abs_of_nonneg hp2]
    _ ≤ p1 * B + p2 * B := add_le_add (mul_le_mul_of_nonneg_left k1 hp1)
        (mul_le_mul_of_nonneg_left k2 hp2)
    _ = p0 * B := by rw [hp]; ring
    _ ≤ p0 * (ε * Metric.diam R0 ^ 2) := mul_le_mul_of_nonneg_left hB (by rw [hp]; positivity)
    _ = ε * p0 * Metric.diam R0 ^ 2 := by ring
