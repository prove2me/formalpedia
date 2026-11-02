-- Prove2me | solution 1 for StochKolmogorov.Persist.proposition_4_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-02T01:33:27.4292+00:00
-- url     : https://prove2.me/submissions/b64e2e87-9e08-428e-86ab-47a56c3163e4

import Mathlib
import Definitions.Def_StochKolmogorov_Persist_Model
import Definitions.Def_StochKolmogorov_Persist_Persistence
import Theorems.Thm_StochKolmogorov_Persist_lemma_3_1
import Theorems.Thm_StochKolmogorov_Persist_lemma_3_2
import Theorems.Thm_StochKolmogorov_Persist_lemma_3_5
import Theorems.Thm_StochKolmogorov_Persist_eq_4_11
import Theorems.Thm_StochKolmogorov_Persist_log_V_mean_le_occupation_phi
import Theorems.Thm_StochKolmogorov_Persist_occupation_phi_continuous

set_option autoImplicit false
set_option linter.all false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace P41G
open StochKolmogorov.Persist EthierKurtz

/-- Second-order Taylor upper bound from an upper bound on the second derivative. -/
theorem taylor_upper (φ : ℝ → ℝ) (θ₁ K : ℝ)
    (hd : ∀ s ∈ Ico (0:ℝ) θ₁, DifferentiableAt ℝ φ s ∧ DifferentiableAt ℝ (deriv φ) s)
    (h2 : ∀ s ∈ Ico (0:ℝ) θ₁, iteratedDeriv 2 φ s ≤ K) :
    ∀ θ ∈ Ico (0:ℝ) θ₁, φ θ ≤ φ 0 + θ * deriv φ 0 + K * θ ^ 2 / 2 := by
  intro θ hθ
  have hsub : Icc 0 θ ⊆ Ico 0 θ₁ := fun s hs => ⟨hs.1, lt_of_le_of_lt hs.2 hθ.2⟩
  have h2' : ∀ s ∈ Ico (0:ℝ) θ₁, deriv (deriv φ) s ≤ K := by
    intro s hs
    have := h2 s hs
    rwa [iteratedDeriv_succ, iteratedDeriv_one] at this
  have hD1 : ∀ s ∈ Icc 0 θ, HasDerivAt (fun s => deriv φ s - K * s) (deriv (deriv φ) s - K) s := by
    intro s hs
    exact ((hd s (hsub hs)).2.hasDerivAt.fun_sub ((hasDerivAt_id' s).const_mul K)).congr_deriv
      (by ring)
  have step1 : ∀ s ∈ Icc 0 θ, deriv φ s ≤ deriv φ 0 + K * s := by
    have hanti : AntitoneOn (fun s => deriv φ s - K * s) (Icc 0 θ) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc 0 θ)
      · intro s hs
        exact (hD1 s hs).continuousAt.continuousWithinAt
      · intro s hs
        rw [interior_Icc] at hs
        exact (hD1 s (Ioo_subset_Icc_self hs)).differentiableAt.differentiableWithinAt
      · intro s hs
        rw [interior_Icc] at hs
        rw [(hD1 s (Ioo_subset_Icc_self hs)).deriv]
        linarith [h2' s (hsub (Ioo_subset_Icc_self hs))]
    intro s hs
    have := hanti ⟨le_refl 0, hθ.1⟩ hs hs.1
    simp only [mul_zero, sub_zero] at this
    linarith
  have hD2 : ∀ s ∈ Icc 0 θ, HasDerivAt (fun s => φ s - s * deriv φ 0 - K * s ^ 2 / 2)
      (deriv φ s - deriv φ 0 - K * s) s := by
    intro s hs
    exact (((hd s (hsub hs)).1.hasDerivAt.fun_sub ((hasDerivAt_id' s).mul_const (deriv φ 0))).fun_sub
      (((hasDerivAt_pow 2 s).const_mul K).div_const 2)).congr_deriv (by norm_num <;> ring)
  have hanti2 : AntitoneOn (fun s => φ s - s * deriv φ 0 - K * s ^ 2 / 2) (Icc 0 θ) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 θ)
    · intro s hs
      exact (hD2 s hs).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      exact (hD2 s (Ioo_subset_Icc_self hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      rw [(hD2 s (Ioo_subset_Icc_self hs)).deriv]
      linarith [step1 s (Ioo_subset_Icc_self hs)]
  have := hanti2 ⟨le_refl 0, hθ.1⟩ ⟨hθ.1, le_refl θ⟩ hθ.1
  simp only [zero_mul, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    mul_zero, zero_div] at this
  linarith

theorem coord_continuous {n : ℕ} (i : Fin n) : Continuous (fun y : SDEState n => y i) := by
  fun_prop

theorem Vfun_measurable {n : ℕ} (c p : SDEState n) : Measurable (Vfun c p) := by
  unfold Vfun
  have hco : ∀ i : Fin n, Measurable (fun y : SDEState n => y i) :=
    fun i => (coord_continuous i).measurable
  refine Measurable.div ?_ ?_
  · exact measurable_const.add (Finset.measurable_sum _ fun i _ => measurable_const.mul (hco i))
  · exact Finset.measurable_prod _ fun i _ => (hco i).pow_const _

theorem Vfun_continuousAt {n : ℕ} (c p x : SDEState n) (hx : x ∈ openOrthant n) :
    ContinuousAt (Vfun c p) x := by
  unfold Vfun
  apply ContinuousAt.div
  · exact (continuous_const.add (continuous_finset_sum _ fun i _ =>
      continuous_const.mul (coord_continuous i))).continuousAt
  · apply tendsto_finset_prod
    intro i _
    exact ((coord_continuous i).continuousAt).rpow_const (Or.inl (hx i).ne')
  · exact (Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hx i) _).ne'

theorem rpow_eq_exp (v w t : ℝ) (hv : 0 < v) (hw : 0 < w) :
    Real.exp (t * (Real.log v - Real.log w)) = v ^ t * (w ^ t)⁻¹ := by
  rw [Real.rpow_def_of_pos hv, Real.rpow_def_of_pos hw, ← Real.exp_neg, ← Real.exp_add]
  congr 1
  ring

theorem mom_helper {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Z f : Ω → ℝ)
    (hZm : AEStronglyMeasurable Z P) (hfm : Measurable f) (t u A : ℝ) (hu : 0 ≤ u) (hA : 0 ≤ A)
    (hZ0 : ∀ ω, 0 ≤ Z ω) (hZf : ∀ᵐ ω ∂P, Z ω ≤ f ω ^ t * u)
    (hlin : ∫⁻ ω, ENNReal.ofReal (f ω ^ t) ∂P ≤ ENNReal.ofReal A) :
    Integrable Z P ∧ ∫ ω, Z ω ∂P ≤ A * u := by
  have hle : ∫⁻ ω, ENNReal.ofReal (Z ω) ∂P ≤ ENNReal.ofReal (A * u) := by
    calc ∫⁻ ω, ENNReal.ofReal (Z ω) ∂P
        ≤ ∫⁻ ω, ENNReal.ofReal (f ω ^ t) * ENNReal.ofReal u ∂P := by
          apply lintegral_mono_ae
          filter_upwards [hZf] with ω hω
          rw [← ENNReal.ofReal_mul' hu]
          exact ENNReal.ofReal_le_ofReal hω
      _ = (∫⁻ ω, ENNReal.ofReal (f ω ^ t) ∂P) * ENNReal.ofReal u :=
          lintegral_mul_const _ ((hfm.pow_const t).ennreal_ofReal)
      _ ≤ ENNReal.ofReal A * ENNReal.ofReal u := by gcongr
      _ = ENNReal.ofReal (A * u) := (ENNReal.ofReal_mul hA).symm
  have h0 : 0 ≤ᵐ[P] Z := ae_of_all _ hZ0
  have hfin : HasFiniteIntegral Z P :=
    (hasFiniteIntegral_iff_ofReal h0).2 (lt_of_le_of_lt hle ENNReal.ofReal_lt_top)
  refine ⟨⟨hZm, hfin⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae h0 hZm]
  exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg hA hu) hle

theorem abs_le_exp_add (z : ℝ) : |z| ≤ Real.exp z + Real.exp (-z) := by
  have h1 := Real.add_one_le_exp z
  have h2 := Real.add_one_le_exp (-z)
  have h3 := Real.exp_pos z
  have h4 := Real.exp_pos (-z)
  rcases le_total 0 z with h | h
  · rw [abs_of_nonneg h]; linarith
  · rw [abs_of_nonpos h]; linarith

set_option maxHeartbeats 1000000 in
/-- Glue for Proposition 4.1: from the moment bounds (3.6) and (4.11), face invariance, the Itô
inequality for `ln V`, continuity of the integrated `Φ`-occupation and Lemma 3.5. -/
theorem glue {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (C : Coeffs n) (X : SDEState n → ℝ≥0 → Ω → SDEState n) (c p : SDEState n)
    (hc : c ∈ openOrthant n) (δ₀ H M ρ Tstar Tmax : ℝ)
    (hδ₀ : 0 < δ₀) (hρ : 0 < ρ) (hTs : 0 < Tstar)
    (hmeasX : ∀ x ∈ openOrthant n, ∀ t, Measurable (X x t))
    (hface : ∀ x ∈ openOrthant n, ∀ t, ∀ᵐ ω ∂P, X x t ω ∈ openOrthant n)
    (hmom : ∀ x ∈ openOrthant n, ∀ t : ℝ≥0,
      ∫⁻ ω, ENNReal.ofReal (Vfun c p (X x t ω) ^ δ₀) ∂P ≤
        ENNReal.ofReal (Real.exp (δ₀ * H * t) * Vfun c p x ^ δ₀))
    (hhat : ∀ x ∈ openOrthant n, ∀ t : ℝ≥0,
      ∫⁻ ω, ENNReal.ofReal (Vfun c (-p) (X x t ω) ^ δ₀) ∂P ≤
        ENNReal.ofReal (Real.exp (δ₀ * H * t) * Vfun c (-p) x ^ δ₀))
    (hlog : ∀ x ∈ openOrthant n, ∀ T : ℝ, 0 < T →
      ∫ ω, Real.log (Vfun c p (X x T.toNNReal ω)) ∂P - Real.log (Vfun c p x) ≤
        T * ∫ y, Phi C c p y ∂(occMean P X x T))
    (hcont : ContinuousOn
      (fun q : SDEState n × ℝ => q.2 * ∫ y, Phi C c p y ∂(occMean P X q.1 q.2))
      (orthant n ×ˢ Ioi 0))
    (hT : ∀ T : ℝ, Tstar < T → ∀ x ∈ bdry n, l1 x ≤ M →
      ∫ y, Phi C c p y ∂(occMean P X x T) ≤ -ρ)
    (h35 : ∀ K₁ : ℝ, ∃ K₂ : ℝ, 0 < K₂ ∧ ∀ Y : Ω → ℝ,
      Integrable (fun ω => Real.exp (δ₀ * Y ω)) P →
      Integrable (fun ω => Real.exp (-δ₀ * Y ω)) P →
      ∫ ω, Real.exp (δ₀ * Y ω) ∂P + ∫ ω, Real.exp (-δ₀ * Y ω) ∂P ≤ K₁ →
        (∀ θ ∈ Set.Ico 0 (δ₀ / 2), DifferentiableAt ℝ (cgf Y P) θ ∧
          DifferentiableAt ℝ (deriv (cgf Y P)) θ) ∧
        deriv (cgf Y P) 0 = ∫ ω, Y ω ∂P ∧
        ∀ θ ∈ Set.Ico 0 (δ₀ / 2),
          0 ≤ iteratedDeriv 2 (cgf Y P) θ ∧ iteratedDeriv 2 (cgf Y P) θ ≤ K₂) :
    ∃ θ : ℝ, 0 < θ ∧ θ < δ₀ / 2 ∧ ∃ Kθ : ℝ, 0 < Kθ ∧
      ∀ T : ℝ, Tstar ≤ T → T ≤ Tmax → ∀ x ∈ openOrthant n, l1 x ≤ M →
        ∫⁻ ω, ENNReal.ofReal (Vfun c p (X x T.toNNReal ω) ^ θ) ∂P ≤
          ENNReal.ofReal (Vfun c p x ^ θ * Real.exp (-(1 / 2) * θ * ρ * T) + Kθ) := by
  classical
  -- pointwise algebra on the open orthant
  have hA : ∀ y ∈ openOrthant n, 1 ≤ 1 + ∑ i, c i * y i := fun y hy => by
    have : 0 ≤ ∑ i, c i * y i := Finset.sum_nonneg fun i _ => mul_nonneg (hc i).le (hy i).le
    linarith
  have hpi : ∀ y ∈ openOrthant n, 0 < ∏ i, y i ^ p i := fun y hy =>
    Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hy i) _
  have hVheq : ∀ y ∈ openOrthant n,
      Vfun c (-p) y = (1 + ∑ i, c i * y i) * ∏ i, y i ^ p i := by
    intro y hy
    unfold Vfun
    have : ∏ i, y i ^ (-p) i = (∏ i, y i ^ p i)⁻¹ := by
      rw [← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [show (-p) i = -(p i) by simp, Real.rpow_neg (hy i).le]
    rw [this, div_inv_eq_mul]
  have hVpos : ∀ y ∈ openOrthant n, 0 < Vfun c p y := fun y hy =>
    div_pos (by linarith [hA y hy]) (hpi y hy)
  have hinvle : ∀ y ∈ openOrthant n, (Vfun c p y)⁻¹ ≤ Vfun c (-p) y := by
    intro y hy
    rw [hVheq y hy]
    unfold Vfun
    rw [inv_div]
    calc (∏ i, y i ^ p i) / (1 + ∑ i, c i * y i) ≤ ∏ i, y i ^ p i :=
          div_le_self (hpi y hy).le (hA y hy)
      _ ≤ (1 + ∑ i, c i * y i) * ∏ i, y i ^ p i := le_mul_of_one_le_left (hpi y hy).le (hA y hy)
  have hprod : ∀ y ∈ openOrthant n,
      Vfun c (-p) y * Vfun c p y = (1 + ∑ i, c i * y i) ^ 2 := by
    intro y hy
    rw [hVheq y hy]
    unfold Vfun
    field_simp [(hpi y hy).ne']
  -- compactness: the region where the drift estimate fails is a compact subset of the interior
  set F : SDEState n × ℝ → ℝ := fun q => q.2 * ∫ y, Phi C c p y ∂(occMean P X q.1 q.2) with hF
  set g : SDEState n × ℝ → ℝ := fun q => F q + 3 / 4 * ρ * q.2 with hg
  set K0 : Set (SDEState n) := {x | x ∈ orthant n ∧ l1 x ≤ M} with hK0
  have hl1c : Continuous (fun x : SDEState n => l1 x) :=
    continuous_finset_sum _ fun i _ => (P41G.coord_continuous i).abs
  have hK0c : IsCompact K0 := by
    apply Metric.isCompact_of_isClosed_isBounded
    · have h1 : IsClosed (orthant n) := by
        have : orthant n = ⋂ i, {x : SDEState n | 0 ≤ x i} := by ext x; simp [orthant]
        rw [this]
        exact isClosed_iInter fun i => isClosed_le continuous_const (P41G.coord_continuous i)
      exact h1.inter (isClosed_le hl1c continuous_const)
    · rw [Metric.isBounded_iff_subset_closedBall 0]
      refine ⟨M, fun x hx => ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      refine le_trans ?_ hx.2
      rw [EuclideanSpace.norm_eq]
      have h0 : 0 ≤ l1 x := Finset.sum_nonneg fun i _ => abs_nonneg _
      calc √(∑ i, ‖x i‖ ^ 2) ≤ √((l1 x) ^ 2) := by
            apply Real.sqrt_le_sqrt
            simp only [Real.norm_eq_abs]
            exact Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => abs_nonneg _)
        _ = l1 x := Real.sqrt_sq h0
  set S : Set (SDEState n × ℝ) := K0 ×ˢ Icc Tstar Tmax with hSdef
  have hS : IsCompact S := hK0c.prod isCompact_Icc
  have hSsub : S ⊆ orthant n ×ˢ Ioi 0 := fun q hq => ⟨hq.1.1, lt_of_lt_of_le hTs hq.2.1⟩
  have hgc : ContinuousOn g S :=
    (hcont.mono hSsub).add (continuous_const.mul continuous_snd).continuousOn
  set Bad : Set (SDEState n × ℝ) := S ∩ g ⁻¹' Ici 0 with hBaddef
  have hBadc : IsCompact Bad :=
    hS.of_isClosed_subset (hgc.preimage_isClosed_of_isClosed hS.isClosed isClosed_Ici)
      inter_subset_left
  have hbd : ∀ x ∈ bdry n, l1 x ≤ M → ∀ T, Tstar ≤ T → F (x, T) ≤ -ρ * T := by
    intro x hx hxM T hT1
    rcases hT1.lt_or_eq with hlt | heq
    · have h1 := hT T hlt x hx hxM
      have h2 := mul_le_mul_of_nonneg_left h1 (lt_trans hTs hlt).le
      show T * _ ≤ _
      linarith
    · subst heq
      have hcw : ContinuousWithinAt (fun s => F (x, s)) (Ioi Tstar) Tstar := by
        have h1 := hcont (x, Tstar) ⟨hx.1, hTs⟩
        exact h1.comp (Continuous.prodMk continuous_const continuous_id).continuousWithinAt
          (fun s hs => ⟨hx.1, lt_trans hTs hs⟩)
      have hlim : Tendsto (fun s => -ρ * s) (𝓝[>] Tstar) (𝓝 (-ρ * Tstar)) :=
        ((continuous_const.mul continuous_id).tendsto Tstar).mono_left nhdsWithin_le_nhds
      refine le_of_tendsto_of_tendsto hcw.tendsto hlim ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      have h1 := hT s hs x hx hxM
      have h2 := mul_le_mul_of_nonneg_left h1 (lt_trans hTs hs).le
      show s * _ ≤ _
      linarith
  have hBadOpen : ∀ q ∈ Bad, q.1 ∈ openOrthant n := by
    rintro ⟨x, T⟩ ⟨⟨⟨hxo, hxM⟩, hT1, hT2⟩, hg0⟩
    by_contra hno
    have h1 := hbd x ⟨hxo, hno⟩ hxM T hT1
    have h2 : (0:ℝ) ≤ F (x, T) + 3 / 4 * ρ * T := hg0
    have h3 : 0 < ρ * T := mul_pos hρ (lt_of_lt_of_le hTs hT1)
    linarith
  have hBdd : BddAbove ((fun q : SDEState n × ℝ => Vfun c p q.1 ^ δ₀) '' Bad) := by
    apply hBadc.bddAbove_image
    intro q hq
    have h2 : ContinuousAt (Vfun c p) q.1 := P41G.Vfun_continuousAt c p q.1 (hBadOpen q hq)
    exact (ContinuousAt.rpow_const (h2.comp continuousAt_fst) (Or.inr hδ₀.le)).continuousWithinAt
  obtain ⟨B, hB⟩ := hBdd
  have hBq : ∀ q ∈ Bad, Vfun c p q.1 ^ δ₀ ≤ B := fun q hq => hB ⟨q, hq, rfl⟩
  -- constants
  set Hp := max H 0 with hHp
  set Cc := ∑ i, c i with hCc
  set E0 := Real.exp (δ₀ * Hp * max Tmax 0) with hE0
  set K₁ := E0 + E0 * ((1 + Cc * M) ^ 2) ^ δ₀ with hK₁
  obtain ⟨K₂, hK₂, h35'⟩ := h35 K₁
  set θ := min (δ₀ / 4) (ρ * Tstar / (2 * K₂)) with hθdef
  have hθ0 : 0 < θ := lt_min (by linarith) (by positivity)
  have hθ1 : θ ≤ δ₀ / 4 := min_le_left _ _
  have hθ2 : θ ≤ ρ * Tstar / (2 * K₂) := min_le_right _ _
  have hE0pos : 0 < E0 := Real.exp_pos _
  refine ⟨θ, hθ0, by linarith, 1 + E0 * max B 0,
    add_pos_of_pos_of_nonneg one_pos (mul_nonneg hE0pos.le (le_max_right _ _)), ?_⟩
  intro T hT1 hT2 x hx hxM
  have hT0 : 0 < T := lt_of_lt_of_le hTs hT1
  have hTT : ((T.toNNReal : ℝ≥0) : ℝ) = T := Real.coe_toNNReal T hT0.le
  have hEt : Real.exp (δ₀ * H * (T.toNNReal : ℝ)) ≤ E0 := by
    rw [hTT]
    apply Real.exp_le_exp.2
    have e1 : δ₀ * H * T ≤ δ₀ * Hp * T :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_max_left H 0) hδ₀.le) hT0.le
    have e2 : δ₀ * Hp * T ≤ δ₀ * Hp * max Tmax 0 :=
      mul_le_mul_of_nonneg_left (le_trans hT2 (le_max_left _ _))
        (mul_nonneg hδ₀.le (le_max_right _ _))
    linarith
  have hVx := hVpos x hx
  have hVXm : Measurable (fun ω => Vfun c p (X x T.toNNReal ω)) :=
    (P41G.Vfun_measurable c p).comp (hmeasX x hx _)
  by_cases hq : (x, T) ∈ Bad
  · -- far from the boundary: V(x) is bounded
    have hVB : Vfun c p x ^ δ₀ ≤ B := hBq _ hq
    have hpt : ∀ᵐ ω ∂P, ENNReal.ofReal (Vfun c p (X x T.toNNReal ω) ^ θ) ≤
        1 + ENNReal.ofReal (Vfun c p (X x T.toNNReal ω) ^ δ₀) := by
      filter_upwards [hface x hx T.toNNReal] with ω hω
      have hv := hVpos _ hω
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (Real.rpow_nonneg hv.le _)]
      apply ENNReal.ofReal_le_ofReal
      rcases le_total (Vfun c p (X x T.toNNReal ω)) 1 with h | h
      · have := Real.rpow_le_one hv.le h hθ0.le
        have := Real.rpow_nonneg hv.le δ₀
        linarith
      · have := Real.rpow_le_rpow_of_exponent_le h (show θ ≤ δ₀ by linarith)
        linarith
    calc ∫⁻ ω, ENNReal.ofReal (Vfun c p (X x T.toNNReal ω) ^ θ) ∂P
        ≤ ∫⁻ ω, (1 + ENNReal.ofReal (Vfun c p (X x T.toNNReal ω) ^ δ₀)) ∂P :=
          lintegral_mono_ae hpt
      _ = 1 + ∫⁻ ω, ENNReal.ofReal (Vfun c p (X x T.toNNReal ω) ^ δ₀) ∂P := by
          rw [lintegral_add_left measurable_const]
          simp
      _ ≤ 1 + ENNReal.ofReal (Real.exp (δ₀ * H * (T.toNNReal : ℝ)) * Vfun c p x ^ δ₀) := by
          gcongr
          exact hmom x hx _
      _ = ENNReal.ofReal (1 + Real.exp (δ₀ * H * (T.toNNReal : ℝ)) * Vfun c p x ^ δ₀) := by
          rw [ENNReal.ofReal_add zero_le_one
            (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hVx.le _)), ENNReal.ofReal_one]
      _ ≤ ENNReal.ofReal (Vfun c p x ^ θ * Real.exp (-(1 / 2) * θ * ρ * T) + (1 + E0 * max B 0)) := by
          apply ENNReal.ofReal_le_ofReal
          have h1 : Real.exp (δ₀ * H * (T.toNNReal : ℝ)) * Vfun c p x ^ δ₀ ≤ E0 * max B 0 :=
            mul_le_mul hEt (le_trans hVB (le_max_left _ _)) (Real.rpow_nonneg hVx.le _) hE0pos.le
          have h2 : 0 ≤ Vfun c p x ^ θ * Real.exp (-(1 / 2) * θ * ρ * T) :=
            mul_nonneg (Real.rpow_nonneg hVx.le _) (Real.exp_pos _).le
          linarith
  · -- near the boundary: the log-Laplace transform is negative at θ
    have hS' : (x, T) ∈ S := ⟨⟨fun i => (hx i).le, hxM⟩, hT1, hT2⟩
    have hgneg : F (x, T) + 3 / 4 * ρ * T < 0 := by
      by_contra h
      push Not at h
      exact hq ⟨hS', h⟩
    obtain ⟨Y, hYdef⟩ : ∃ Y : Ω → ℝ,
        Y = fun ω => Real.log (Vfun c p (X x T.toNNReal ω)) - Real.log (Vfun c p x) := ⟨_, rfl⟩
    have hYm : Measurable Y := by rw [hYdef]; exact (Real.measurable_log.comp hVXm).sub_const _
    -- exponential moments
    have hm1 := P41G.mom_helper P (fun ω => Real.exp (δ₀ * Y ω))
      (fun ω => Vfun c p (X x T.toNNReal ω)) (hYm.const_mul δ₀).exp.aestronglyMeasurable hVXm
      δ₀ (Vfun c p x ^ δ₀)⁻¹ (Real.exp (δ₀ * H * (T.toNNReal : ℝ)) * Vfun c p x ^ δ₀)
      (inv_nonneg.2 (Real.rpow_nonneg hVx.le _))
      (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hVx.le _))
      (fun ω => (Real.exp_pos _).le)
      (by
        filter_upwards [hface x hx T.toNNReal] with ω hω
        simp only [hYdef]; rw [P41G.rpow_eq_exp _ _ _ (hVpos _ hω) hVx])
      (hmom x hx _)
    have hVhx : 0 < Vfun c (-p) x := by rw [hVheq x hx]; exact mul_pos (by linarith [hA x hx]) (hpi x hx)
    have hVhXm : Measurable (fun ω => Vfun c (-p) (X x T.toNNReal ω)) :=
      (P41G.Vfun_measurable c (-p)).comp (hmeasX x hx _)
    have hm2 := P41G.mom_helper P (fun ω => Real.exp (-δ₀ * Y ω))
      (fun ω => Vfun c (-p) (X x T.toNNReal ω)) (hYm.const_mul (-δ₀)).exp.aestronglyMeasurable
      hVhXm δ₀ (Vfun c p x ^ δ₀) (Real.exp (δ₀ * H * (T.toNNReal : ℝ)) * Vfun c (-p) x ^ δ₀)
      (Real.rpow_nonneg hVx.le _)
      (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hVhx.le _))
      (fun ω => (Real.exp_pos _).le)
      (by
        filter_upwards [hface x hx T.toNNReal] with ω hω
        have hv := hVpos _ hω
        have e : -δ₀ * Y ω = δ₀ * (Real.log (Vfun c p x) - Real.log (Vfun c p (X x T.toNNReal ω))) := by
          simp only [hYdef]; ring
        rw [e, P41G.rpow_eq_exp _ _ _ hVx hv, mul_comm]
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hVx.le _)
        rw [← Real.inv_rpow hv.le]
        exact Real.rpow_le_rpow (inv_nonneg.2 hv.le) (hinvle _ hω) hδ₀.le)
      (hhat x hx _)
    -- the constant
    have hcx : 1 + ∑ i, c i * x i ≤ 1 + Cc * M := by
      have h1 : ∀ i, c i * x i ≤ c i * l1 x := fun i =>
        mul_le_mul_of_nonneg_left (le_trans (le_abs_self _)
          (Finset.single_le_sum (f := fun j => |x j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)))
          (hc i).le
      have h2 : ∑ i, c i * x i ≤ Cc * l1 x := by
        rw [hCc, Finset.sum_mul]; exact Finset.sum_le_sum fun i _ => h1 i
      have h3 : Cc * l1 x ≤ Cc * M :=
        mul_le_mul_of_nonneg_left hxM (Finset.sum_nonneg fun i _ => (hc i).le)
      linarith
    have hm2b : Real.exp (δ₀ * H * (T.toNNReal : ℝ)) * Vfun c (-p) x ^ δ₀ * Vfun c p x ^ δ₀ ≤
        E0 * ((1 + Cc * M) ^ 2) ^ δ₀ := by
      rw [mul_assoc, ← Real.mul_rpow hVhx.le hVx.le, hprod x hx]
      apply mul_le_mul hEt _ (Real.rpow_nonneg (sq_nonneg _) _) hE0pos.le
      apply Real.rpow_le_rpow (sq_nonneg _) _ hδ₀.le
      exact pow_le_pow_left₀ (by linarith [hA x hx]) hcx 2
    have hm1b : Real.exp (δ₀ * H * (T.toNNReal : ℝ)) * Vfun c p x ^ δ₀ * (Vfun c p x ^ δ₀)⁻¹ ≤ E0 := by
      rw [mul_assoc, mul_inv_cancel₀ (Real.rpow_pos_of_pos hVx _).ne', mul_one]
      exact hEt
    obtain ⟨hint1, hI1⟩ := hm1
    obtain ⟨hint2, hI2⟩ := hm2
    have hsum : ∫ ω, Real.exp (δ₀ * Y ω) ∂P + ∫ ω, Real.exp (-δ₀ * Y ω) ∂P ≤ K₁ := by
      rw [hK₁]; linarith
    obtain ⟨hdiff, hd0, hd2⟩ := h35' Y hint1 hint2 hsum
    -- the mean of Y
    have hYint : Integrable Y P := by
      refine Integrable.mono' ((hint1.add hint2).div_const δ₀) hYm.aestronglyMeasurable
        (ae_of_all _ fun ω => ?_)
      rw [Real.norm_eq_abs, le_div_iff₀ hδ₀]
      have := P41G.abs_le_exp_add (δ₀ * Y ω)
      rw [abs_mul, abs_of_pos hδ₀, neg_mul_eq_neg_mul] at this
      simpa [mul_comm] using this
    have hlogint : Integrable (fun ω => Real.log (Vfun c p (X x T.toNNReal ω))) P := by
      have : (fun ω => Real.log (Vfun c p (X x T.toNNReal ω))) =
          fun ω => Y ω + Real.log (Vfun c p x) := by
        funext ω; simp only [hYdef]; ring
      rw [this]; exact hYint.add (integrable_const _)
    have hmean : ∫ ω, Y ω ∂P ≤ F (x, T) := by
      have h1 := hlog x hx T hT0
      have h2 : ∫ ω, Y ω ∂P = ∫ ω, Real.log (Vfun c p (X x T.toNNReal ω)) ∂P - Real.log (Vfun c p x) := by
        simp only [hYdef]
        rw [integral_sub hlogint (integrable_const _)]
        simp
      rw [h2]; exact h1
    -- Taylor bound for the cgf
    have htay := P41G.taylor_upper (cgf Y P) (δ₀ / 2) K₂ hdiff (fun s hs => (hd2 s hs).2) θ
      ⟨hθ0.le, by linarith⟩
    have hc0 : cgf Y P 0 = 0 := by simp [cgf, mgf]
    have k1 : θ * (2 * K₂) ≤ ρ * Tstar := (le_div_iff₀ (by positivity)).1 hθ2
    have k2 : ρ * Tstar ≤ ρ * T := mul_le_mul_of_nonneg_left hT1 hρ.le
    have k3 : θ * deriv (cgf Y P) 0 ≤ θ * (-(3 / 4) * ρ * T) :=
      mul_le_mul_of_nonneg_left (by rw [hd0]; linarith) hθ0.le
    have k4 : K₂ * θ ^ 2 / 2 ≤ θ * (ρ * T) / 4 := by
      have := mul_le_mul_of_nonneg_left (k1.trans k2) hθ0.le
      nlinarith
    have hcgf : cgf Y P θ ≤ -(1 / 2) * θ * ρ * T := by
      rw [hc0] at htay
      nlinarith
    -- mgf at θ
    have hintθ : Integrable (fun ω => Real.exp (θ * Y ω)) P := by
      refine Integrable.mono' ((integrable_const 1).add hint1)
        (hYm.const_mul θ).exp.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      show Real.exp (θ * Y ω) ≤ 1 + Real.exp (δ₀ * Y ω)
      rcases le_total 0 (Y ω) with h | h
      · have := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (show θ ≤ δ₀ by linarith) h)
        linarith [zero_lt_one' ℝ]
      · have := Real.exp_le_exp.2 (mul_nonpos_of_nonneg_of_nonpos hθ0.le h)
        rw [Real.exp_zero] at this
        linarith [Real.exp_pos (δ₀ * Y ω)]
    have hmgf : mgf Y P θ ≤ Real.exp (-(1 / 2) * θ * ρ * T) := by
      have hpos : 0 < mgf Y P θ := mgf_pos hintθ
      rw [← Real.exp_log hpos]
      exact Real.exp_le_exp.2 hcgf
    -- conclusion
    have hae : ∀ᵐ ω ∂P, ENNReal.ofReal (Vfun c p (X x T.toNNReal ω) ^ θ) =
        ENNReal.ofReal (Vfun c p x ^ θ) * ENNReal.ofReal (Real.exp (θ * Y ω)) := by
      filter_upwards [hface x hx T.toNNReal] with ω hω
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hVx.le _)]
      simp only [hYdef]
      rw [P41G.rpow_eq_exp _ _ _ (hVpos _ hω) hVx]
      congr 1
      field_simp [(Real.rpow_pos_of_pos hVx θ).ne']
    calc ∫⁻ ω, ENNReal.ofReal (Vfun c p (X x T.toNNReal ω) ^ θ) ∂P
        = ∫⁻ ω, ENNReal.ofReal (Vfun c p x ^ θ) * ENNReal.ofReal (Real.exp (θ * Y ω)) ∂P :=
          lintegral_congr_ae hae
      _ = ENNReal.ofReal (Vfun c p x ^ θ) * ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * Y ω)) ∂P :=
          lintegral_const_mul _ (hYm.const_mul θ).exp.ennreal_ofReal
      _ = ENNReal.ofReal (Vfun c p x ^ θ) * ENNReal.ofReal (mgf Y P θ) := by
          rw [mgf, ofReal_integral_eq_lintegral_ofReal hintθ (ae_of_all _ fun ω => (Real.exp_pos _).le)]
      _ = ENNReal.ofReal (Vfun c p x ^ θ * mgf Y P θ) :=
          (ENNReal.ofReal_mul (Real.rpow_nonneg hVx.le _)).symm
      _ ≤ ENNReal.ofReal (Vfun c p x ^ θ * Real.exp (-(1 / 2) * θ * ρ * T) + (1 + E0 * max B 0)) := by
          apply ENNReal.ofReal_le_ofReal
          have := mul_le_mul_of_nonneg_left hmgf (Real.rpow_nonneg hVx.le θ)
          have : 0 ≤ E0 * max B 0 := mul_nonneg hE0pos.le (le_max_right _ _)
          linarith

end P41G

open MeasureTheory ProbabilityTheory Filter StochKolmogorov.Persist EthierKurtz in
theorem solution {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (h12 : Assumption12 P C X) (M : ℝ) (hMpos : 0 < M) (hM : IsRadiusM C c γb M)
    (δ₀ : ℝ) (hδ₀ : IsDelta0 C γb δ₀) (p : SDEState n) (hp : p ∈ openOrthant n) (hpδ : l1 p = δ₀)
    (ρ : ℝ) (hρ : 0 < ρ) (h41 : IsWeightedInvasionMin P C X p ρ)
    (Tstar : ℝ) (hTstar : 0 < Tstar)
    (hT : ∀ T : ℝ, Tstar < T → ∀ x ∈ bdry n, l1 x ≤ M →
      Integrable (Phi C c p) (occMean P X x T) ∧ ∫ y, Phi C c p y ∂(occMean P X x T) ≤ -ρ)
    (nstar : ℕ) (hnstar : Hconst C c γb δ₀ < γb * ((nstar : ℝ) - 1)) :
    ∃ θ : ℝ, 0 < θ ∧ θ < δ₀ / 2 ∧ ∃ Kθ : ℝ, 0 < Kθ ∧
      ∀ T : ℝ, Tstar ≤ T → T ≤ nstar * Tstar → ∀ x ∈ openOrthant n, l1 x ≤ M →
        ∫⁻ ω, ENNReal.ofReal (Vfun c p (X x T.toNNReal ω) ^ θ) ∂P ≤
          ENNReal.ofReal (Vfun c p x ^ θ * Real.exp (-(1 / 2) * θ * ρ * T) + Kθ) := by
  have hP : IsProbabilityMeasure P := hX.1
  have hB : IsStandardBrownian P B := hX.2.1
  have hsol := hX.2.2
  have hδ0 : 0 < δ₀ := hδ₀.1
  have hpδ' : l1 p ≤ δ₀ := hpδ.le
  obtain ⟨-, -, L3, L4⟩ := lemma_3_1 hn P C B hB c γb hA
  obtain ⟨H₁, H₂, -, hH₂, -, h38, hfel⟩ := lemma_3_2 hn P C B X hX c γb hA δ₀ hδ₀
  have hoo : ∀ x ∈ openOrthant n, x ∈ orthant n := fun x hx i => (hx i).le
  have hinv : ∀ x ∈ orthant n, ∀ᵐ ω ∂P, ∀ t, X x t ω ∈ orthant n := by
    intro x hx
    classical
    have hxI : x ∈ faceOpen (Finset.univ.filter fun i => 0 < x i) := by
      refine ⟨hx, fun i hi => ?_, fun i hi => (Finset.mem_filter.1 hi).2⟩
      have h0 : ¬ 0 < x i := fun h => hi (Finset.mem_filter.2 ⟨Finset.mem_univ i, h⟩)
      exact le_antisymm (not_lt.1 h0) (hx i)
    filter_upwards [L3 _ x hxI (X x) (hsol x hx)] with ω hω t using (hω t).1
  have hface : ∀ x ∈ openOrthant n, ∀ t, ∀ᵐ ω ∂P, X x t ω ∈ openOrthant n := by
    intro x hx t
    have hxI : x ∈ faceOpen (Finset.univ : Finset (Fin n)) :=
      ⟨hoo x hx, fun i hi => absurd (Finset.mem_univ i) hi, fun i _ => hx i⟩
    filter_upwards [L3 _ x hxI (X x) (hsol x (hoo x hx))] with ω hω using
      fun i => (hω t).2.2 i (Finset.mem_univ i)
  have hmeasX : ∀ x ∈ openOrthant n, ∀ t, Measurable (X x t) := fun x hx t =>
    (hsol x (hoo x hx)).1 t
  have hmom : ∀ x ∈ openOrthant n, ∀ t : ℝ≥0,
      ∫⁻ ω, ENNReal.ofReal (Vfun c p (X x t ω) ^ δ₀) ∂P ≤
        ENNReal.ofReal (Real.exp (δ₀ * Hconst C c γb δ₀ * t) * Vfun c p x ^ δ₀) := fun x hx t =>
    (L4 δ₀ hδ₀).2 p hp hpδ' x hx (X x) (hsol x (hoo x hx)) t
  have hhat := eq_4_11 hn P C B X hX c γb hA δ₀ hδ₀ p hp hpδ'
  have hlog := log_V_mean_le_occupation_phi hn P C B X hX c γb hA δ₀ hδ₀ p hp hpδ'
  have hcont := occupation_phi_continuous hn P C B X hX c γb hA δ₀ hδ₀ p hp hpδ' hinv H₂ hH₂
    h38 hfel
  refine P41G.glue P C X c p hA.2.2.1 δ₀ (Hconst C c γb δ₀) M ρ Tstar (nstar * Tstar) hδ0 hρ
    hTstar hmeasX hface hmom hhat hlog hcont (fun T hT' x hx hl => (hT T hT' x hx hl).2) ?_
  intro K₁
  obtain ⟨K₂, hK₂, h⟩ := lemma_3_5 δ₀ hδ0 K₁
  exact ⟨K₂, hK₂, fun Y h1 h2 h3 => h P Y h1 h2 h3⟩
