-- Prove2me | solution 1 for RenegingLD.MM1.lemma_6_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T16:46:42.149169+00:00
-- url     : https://prove2.me/submissions/809b2e55-0ec8-4017-9fff-8f37fee3179e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RenegingLD_MM1_Variational
import Theorems.Thm_RenegingLD_MM1_lemma_4_4
import Theorems.Thm_RenegingLD_MM1_note_4_IT_top

open RenegingLD.MM1
open MeasureTheory Filter Topology
open scoped ENNReal

theorem solution (lam mu θ : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (hθ : 0 < θ) (hlm : mu ≤ lam) (x0 T : ℝ) (hx0 : 0 ≤ x0) (hT : 0 < T) :
    (∀ γ₁ γ₂ : ℝ, 0 ≤ γ₁ → 0 ≤ γ₂ → ∀ a ∈ Set.Ioo (0 : ℝ) 1,
      Istar lam mu θ x0 (a * γ₁ + (1 - a) * γ₂) T ≤
        ENNReal.ofReal a * Istar lam mu θ x0 γ₁ T
          + ENNReal.ofReal (1 - a) * Istar lam mu θ x0 γ₂ T) ∧
    Istar lam mu θ x0 (gammaStar lam mu θ x0 T) T = 0 ∧
    AntitoneOn (fun γ => Istar lam mu θ x0 γ T) (Set.Icc 0 (gammaStar lam mu θ x0 T)) ∧
    MonotoneOn (fun γ => Istar lam mu θ x0 γ T) (Set.Ici (gammaStar lam mu θ x0 T)) := by
  ------------------------------------------------------------------
  -- Part A: convexity, from Lemma 4.4 and the note of §4.
  ------------------------------------------------------------------
  have conv : ∀ γ₁ γ₂ : ℝ, 0 ≤ γ₁ → 0 ≤ γ₂ → ∀ a ∈ Set.Ioo (0 : ℝ) 1,
      Istar lam mu θ x0 (a * γ₁ + (1 - a) * γ₂) T ≤
        ENNReal.ofReal a * Istar lam mu θ x0 γ₁ T
          + ENNReal.ofReal (1 - a) * Istar lam mu θ x0 γ₂ T := by
    intro g1 g2 _ _ a ha
    have ha0 : ENNReal.ofReal a ≠ 0 := by simp [ha.1]
    have hb0 : ENNReal.ofReal (1 - a) ≠ 0 := by simp; linarith [ha.2]
    have L44 := (lemma_4_4 lam mu θ hlam hmu hθ hlm x0 T hx0 hT).2
    unfold Istar
    simp only [ENNReal.mul_iInf_of_ne ha0 ENNReal.ofReal_ne_top,
      ENNReal.mul_iInf_of_ne hb0 ENNReal.ofReal_ne_top]
    refine ENNReal.le_iInf_add_iInf fun ξ1 ξ2 => ENNReal.le_iInf_add_iInf fun ζ1 ζ2 =>
      ENNReal.le_iInf_add_iInf fun h1 h2 => ?_
    by_cases hc1 : InCT x0 T ξ1 ζ1
    · by_cases hc2 : InCT x0 T ξ2 ζ2
      · obtain ⟨_, hle⟩ := L44 ξ1 ζ1 ξ2 ζ2 a ha hc1 hc2
        refine iInf_le_of_le _ (iInf_le_of_le _ (iInf_le_of_le ?_ hle))
        show a * ζ1 T + (1 - a) * ζ2 T = (a * g1 + (1 - a) * g2) * T
        rw [h1, h2]; ring
      · rw [note_4_IT_top lam mu θ hlam hmu hθ hlm x0 T hx0 hT ξ2 ζ2 hc2,
          ENNReal.mul_top hb0]
        simp
    · rw [note_4_IT_top lam mu θ hlam hmu hθ hlm x0 T hx0 hT ξ1 ζ1 hc1,
        ENNReal.mul_top ha0]
      simp
  ------------------------------------------------------------------
  -- Part B: the zero-cost (law of large numbers) path.
  ------------------------------------------------------------------
  set a := (lam - mu) / θ with ha_def
  have ha0 : 0 ≤ a := div_nonneg (by linarith) hθ.le
  set ξ0 : ℝ → ℝ := fun t => a + (x0 - a) * Real.exp (-θ * t) with hξ0
  set ζ0 : ℝ → ℝ := fun t => (lam - mu) * t + (x0 - a) * (1 - Real.exp (-θ * t)) with hζ0
  have hexp_le : ∀ t, 0 ≤ t → Real.exp (-θ * t) ≤ 1 := by
    intro t ht; rw [Real.exp_le_one_iff]; nlinarith
  have hξ0_nn : ∀ t, 0 ≤ t → 0 ≤ ξ0 t := by
    intro t ht
    have h1 := hexp_le t ht
    have h2 := Real.exp_pos (-θ * t)
    have : ξ0 t = a * (1 - Real.exp (-θ * t)) + x0 * Real.exp (-θ * t) := by
      simp only [hξ0]; ring
    rw [this]
    have := mul_nonneg ha0 (sub_nonneg.2 h1)
    have := mul_nonneg hx0 h2.le
    linarith
  have hζ0_nn : ∀ t, 0 ≤ t → 0 ≤ ζ0 t := by
    intro t ht
    have h1 := hexp_le t ht
    have h3 := Real.add_one_le_exp (-θ * t)
    have : ζ0 t = a * (θ * t - (1 - Real.exp (-θ * t))) + x0 * (1 - Real.exp (-θ * t)) := by
      simp only [hζ0, ha_def]; field_simp; ring
    rw [this]
    have := mul_nonneg ha0 (show 0 ≤ θ * t - (1 - Real.exp (-θ * t)) by linarith)
    have := mul_nonneg hx0 (sub_nonneg.2 h1)
    linarith
  -- integral of ξ0
  have hint : ∀ r : ℝ, θ * (∫ s in (0)..r, (1 : ℝ) * ξ0 s) = ζ0 r := by
    intro r
    have hderiv : ∀ x ∈ Set.uIcc 0 r,
        HasDerivAt (fun s => a * s - (x0 - a) * Real.exp (-θ * s) / θ) (1 * ξ0 x) x := by
      intro x _
      have h1 : HasDerivAt (fun s => -θ * s) (-θ) x := by
        simpa using (hasDerivAt_id x).const_mul (-θ)
      have h2 := (h1.exp).const_mul (x0 - a)
      have h3 : HasDerivAt (fun s => a * s - (x0 - a) * Real.exp (-θ * s) / θ)
          (a * 1 - (x0 - a) * (Real.exp (-θ * x) * -θ) / θ) x :=
        ((hasDerivAt_id x).const_mul a).sub (h2.div_const θ)
      refine h3.congr_deriv ?_
      simp only [hξ0]
      field_simp
      ring
    have hcont : Continuous fun s => (1 : ℝ) * ξ0 s := by
      simp only [hξ0]; fun_prop
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (hcont.intervalIntegrable _ _)]
    simp only [hζ0, ha_def]
    field_simp
    simp
    ring
  -- the control (1, 1, 1)
  set ϕ : (ℝ → ℝ) × (ℝ → ℝ) × (ℝ → ℝ) := (fun _ => 1, fun _ => 1, fun _ => 1) with hϕ
  have hpsi : ∀ r : ℝ, x0 + lam * (∫ s in (0)..r, ϕ.1 s) - mu * (∫ s in (0)..r, ϕ.2.1 s)
      - θ * (∫ s in (0)..r, ϕ.2.2 s * ξ0 s) = ξ0 r := by
    intro r
    have := hint r
    simp only [hϕ] at this ⊢
    rw [this]
    simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero, hζ0, hξ0]
    ring
  have hcξ : Continuous ξ0 := by simp only [hξ0]; fun_prop
  have hcζ : Continuous ζ0 := by simp only [hζ0]; fun_prop
  have hpath : IsPath T ξ0 ζ0 :=
    ⟨hcξ.continuousOn, hcζ.continuousOn, fun t ht => ⟨hξ0_nn t ht.1, hζ0_nn t ht.1⟩⟩
  have hU : ϕ ∈ U lam mu θ x0 T ξ0 ζ0 := by
    refine ⟨measurable_const, measurable_const, measurable_const, ?_, ?_, ?_, ?_, ?_⟩
    · intro s _; simp [hϕ]
    · exact intervalIntegrable_const
    · exact intervalIntegrable_const
    · simp only [hϕ, one_mul]; exact hcξ.intervalIntegrable _ _
    · intro t ht
      refine ⟨?_, ?_⟩
      · unfold skorokhod
        beta_reduce
        rw [hpsi t]
        have hne : Nonempty (Set.Icc (0 : ℝ) t) := ⟨⟨0, le_rfl, ht.1⟩⟩
        have hfun : (fun s : Set.Icc (0 : ℝ) t =>
            min (x0 + lam * (∫ u in (0)..(s : ℝ), ϕ.1 u) - mu * (∫ u in (0)..(s : ℝ), ϕ.2.1 u)
              - θ * (∫ u in (0)..(s : ℝ), ϕ.2.2 u * ξ0 u)) 0) = fun _ => 0 := by
          funext s
          rw [hpsi s]
          exact min_eq_right (hξ0_nn s s.2.1)
        rw [hfun, ciInf_const, sub_zero]
      · rw [← hint t]
  have hcost : cost lam mu θ T ξ0 ϕ = 0 := by
    simp [cost, hϕ, ell]
  have hIT : IT lam mu θ x0 T ξ0 ζ0 = 0 := by
    apply le_antisymm _ (zero_le)
    calc IT lam mu θ x0 T ξ0 ζ0 ≤ cost lam mu θ T ξ0 ϕ :=
          iInf_le_of_le hpath (iInf₂_le ϕ hU)
      _ = 0 := hcost
  have hζT : ζ0 T = gammaStar lam mu θ x0 T * T := by
    simp only [hζ0, gammaStar, ha_def]
    field_simp
    try ring
  have hzero : Istar lam mu θ x0 (gammaStar lam mu θ x0 T) T = 0 := by
    apply le_antisymm _ (zero_le)
    calc Istar lam mu θ x0 (gammaStar lam mu θ x0 T) T ≤ IT lam mu θ x0 T ξ0 ζ0 :=
          iInf_le_of_le ξ0 (iInf_le_of_le ζ0 (iInf_le_of_le hζT le_rfl))
      _ = 0 := hIT
  have hgs0 : 0 ≤ gammaStar lam mu θ x0 T := by
    have h := hζ0_nn T hT.le
    rw [hζT] at h
    exact nonneg_of_mul_nonneg_left h hT
  ------------------------------------------------------------------
  -- Part C: monotonicity from convexity + zero at γ*_T.
  ------------------------------------------------------------------
  set gs := gammaStar lam mu θ x0 T with hgs
  have key : ∀ g c : ℝ, 0 ≤ g → c ∈ Set.Ioo (0 : ℝ) 1 →
      Istar lam mu θ x0 (c * g + (1 - c) * gs) T ≤ Istar lam mu θ x0 g T := by
    intro g c hg hc
    calc Istar lam mu θ x0 (c * g + (1 - c) * gs) T
        ≤ ENNReal.ofReal c * Istar lam mu θ x0 g T
            + ENNReal.ofReal (1 - c) * Istar lam mu θ x0 gs T := conv g gs hg hgs0 c hc
      _ = ENNReal.ofReal c * Istar lam mu θ x0 g T := by rw [hzero, mul_zero, add_zero]
      _ ≤ Istar lam mu θ x0 g T :=
          mul_le_of_le_one_left zero_le (ENNReal.ofReal_le_one.2 hc.2.le)
  refine ⟨conv, hzero, ?_, ?_⟩
  · intro g1 hg1 g2 hg2 hle
    show Istar lam mu θ x0 g2 T ≤ Istar lam mu θ x0 g1 T
    rcases hle.eq_or_lt with h | h
    · rw [h]
    rcases hg2.2.eq_or_lt with h' | h'
    · rw [h', hzero]; exact zero_le
    have hlt : g1 < gs := h.trans h'
    have hc : (gs - g2) / (gs - g1) ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor
      · exact div_pos (by linarith) (by linarith)
      · rw [div_lt_one (by linarith)]; linarith
    have heq : g2 = (gs - g2) / (gs - g1) * g1 + (1 - (gs - g2) / (gs - g1)) * gs := by
      field_simp [show gs - g1 ≠ 0 by linarith]
      ring
    calc Istar lam mu θ x0 g2 T
        = Istar lam mu θ x0 ((gs - g2) / (gs - g1) * g1 + (1 - (gs - g2) / (gs - g1)) * gs) T :=
          congrArg (fun g => Istar lam mu θ x0 g T) heq
      _ ≤ Istar lam mu θ x0 g1 T := key g1 _ hg1.1 hc
  · intro g1 hg1 g2 hg2 hle
    show Istar lam mu θ x0 g1 T ≤ Istar lam mu θ x0 g2 T
    rcases hle.eq_or_lt with h | h
    · rw [h]
    rcases (Set.mem_Ici.1 hg1).eq_or_lt with h' | h'
    · rw [← h', hzero]; exact zero_le
    have hlt : gs < g2 := h'.trans h
    have hc : (g1 - gs) / (g2 - gs) ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor
      · exact div_pos (by linarith) (by linarith)
      · rw [div_lt_one (by linarith)]; linarith
    have heq : g1 = (g1 - gs) / (g2 - gs) * g2 + (1 - (g1 - gs) / (g2 - gs)) * gs := by
      field_simp [show g2 - gs ≠ 0 by linarith]
      ring
    calc Istar lam mu θ x0 g1 T
        = Istar lam mu θ x0 ((g1 - gs) / (g2 - gs) * g2 + (1 - (g1 - gs) / (g2 - gs)) * gs) T :=
          congrArg (fun g => Istar lam mu θ x0 g T) heq
      _ ≤ Istar lam mu θ x0 g2 T := key g2 _ (hgs0.trans hlt.le) hc
