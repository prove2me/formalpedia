-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P09.classical_noEvent
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T15:01:26.256003+00:00
-- url     : https://prove2.me/submissions/80348309-4d3b-4755-80b3-02b559f38f89

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P09
noncomputable section

open Filter MeasureTheory Topology

open scoped BigOperators ENNReal

open QAlgorithms.Papers.Independent.Next46.P09

universe u v

lemma g61b_pm_self {X : Type u} (x : X) : pointMass x x = 1 := by
  classical
  exact lp.single_apply_self 1 x 1

lemma g61b_pm_ne {X : Type u} {x y : X} (h : y ≠ x) : pointMass x y = 0 := by
  classical
  exact lp.single_apply_ne 1 x 1 h

lemma g61b_pm_norm {X : Type u} (x : X) : ‖pointMass x‖ = 1 := by
  classical
  have := lp.norm_single (E := fun _ : X => ℝ) (p := 1) (by norm_num) x (1 : ℝ)
  simpa [pointMass] using this

lemma g61b_coord {X : Type u} (f : ClassicalSpace X) (x : X) : |f x| ≤ ‖f‖ := by
  have := lp.norm_apply_le_norm (E := fun _ : X => ℝ) (p := 1) (by norm_num) f x
  simpa [Real.norm_eq_abs] using this

/-- additive continuous functions on NNReal are linear -/
lemma g61b_cauchy (L : NNReal → ℝ) (hadd : ∀ a b, L (a + b) = L a + L b)
    (hc : Continuous L) (t : NNReal) : L t = (t : ℝ) * L 1 := by
  have h0 : L 0 = 0 := by have := hadd 0 0; simp at this; linarith
  have hm : ∀ r : ℝ, max r 0 - max (-r) 0 = r := fun r => by
    rcases le_total r 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  let F : ℝ →+ ℝ :=
    { toFun := fun s => L s.toNNReal - L (-s).toNNReal
      map_zero' := by simp [h0]
      map_add' := by
        intro a b
        have key : (a + b).toNNReal + (-a).toNNReal + (-b).toNNReal =
            (-(a + b)).toNNReal + a.toNNReal + b.toNNReal := by
          apply NNReal.eq
          simp only [NNReal.coe_add, Real.coe_toNNReal']
          have h1 := hm (a + b); have h2 := hm a; have h3 := hm b
          linarith
        have := congrArg L key
        simp only [hadd] at this
        linarith }
  have hF : Continuous F :=
    (hc.comp continuous_real_toNNReal).sub
      (hc.comp (continuous_real_toNNReal.comp continuous_neg))
  have := map_real_smul F hF (t : ℝ) 1
  simp only [smul_eq_mul, mul_one] at this
  change L (t : ℝ).toNNReal - L (-(t : ℝ)).toNNReal =
    (t : ℝ) * (L (1 : ℝ).toNNReal - L (-(1 : ℝ)).toNNReal) at this
  have e1 : (-(t : ℝ)).toNNReal = 0 := by simp
  have e2 : (-(1 : ℝ)).toNNReal = 0 := by simp
  rw [e1, e2, h0, Real.toNNReal_coe, Real.toNNReal_one] at this
  linarith

theorem solution {X : Type u} [Countable X] (T : ClassicalNoEventSemigroup X) :
    ∃ mu : X → NNReal, ∀ (t : NNReal) (x : X),
      T.maps t (pointMass x) =
        Real.exp (-(t : ℝ) * (mu x : ℝ)) • pointMass x := by
  -- per-point analysis
  have main : ∀ x : X, ∃ m : NNReal, ∀ t : NNReal,
      T.maps t (pointMass x) = Real.exp (-(t : ℝ) * (m : ℝ)) • pointMass x := by
    intro x
    set δ := pointMass x with hδ
    -- near zero, the image is a multiple of δ with coefficient near 1
    obtain ⟨ε, hε, hεb⟩ := Metric.continuous_iff.1 (T.continuous δ) 0 1 one_pos
    have hnear : ∀ s : NNReal, (s : ℝ) < ε → T.maps s δ = (T.maps s δ x) • δ := by
      intro s hs
      have hd : ‖T.maps s δ - δ‖ < 1 := by
        have := hεb s (by simpa [NNReal.dist_eq] using hs)
        rwa [dist_eq_norm, T.initial] at this
      obtain ⟨a, y, hay⟩ := T.pure s x
      by_cases hyx : y = x
      · subst hyx
        rw [hay, hδ]; simp [g61b_pm_self]
      · exfalso
        have := g61b_coord (T.maps s δ - δ) x
        rw [hay] at this
        simp only [lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply,
          g61b_pm_ne (Ne.symm hyx), hδ, g61b_pm_self, smul_eq_mul, mul_zero, zero_sub,
          abs_neg, abs_one] at this
        rw [hay] at hd
        linarith
    -- powers
    have hpow : ∀ (s : NNReal) (c : ℝ), T.maps s δ = c • δ →
        ∀ k : ℕ, T.maps (k * s) δ = c ^ k • δ := by
      intro s c hs k
      induction k with
      | zero => simp [T.initial]
      | succ k ih =>
        have : ((k + 1 : ℕ) : NNReal) * s = s + (k : NNReal) * s := by push_cast; ring
        rw [this, T.semigroup, ContinuousLinearMap.comp_apply, ih, map_smul, hs, smul_smul,
          pow_succ, mul_comm]
    have hall : ∀ t : NNReal, T.maps t δ = (T.maps t δ x) • δ := by
      intro t
      obtain ⟨n, hn⟩ := exists_nat_gt ((t : ℝ) / ε)
      have hnpos : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hn
      set s : NNReal := t / n
      have hs : (s : ℝ) < ε := by
        simp only [s, NNReal.coe_div, NNReal.coe_natCast]
        rw [div_lt_iff₀ hnpos]; rw [div_lt_iff₀ hε] at hn; linarith
      have ht : t = (n : NNReal) * s := by
        simp only [s]; field_simp [show (n : NNReal) ≠ 0 by exact_mod_cast hnpos.ne']
      have := hpow s _ (hnear s hs) n
      rw [← ht] at this
      rw [this]; simp [g61b_pm_self, hδ]
    set c : NNReal → ℝ := fun t => T.maps t δ x with hc
    have hmul : ∀ s t, c (s + t) = c s * c t := by
      intro s t
      simp only [hc]
      rw [T.semigroup, ContinuousLinearMap.comp_apply, hall t, map_smul, hall s]
      simp [g61b_pm_self, hδ, mul_comm]
    have hcont : Continuous c := by
      rw [Metric.continuous_iff]
      intro t e he
      obtain ⟨d, hd, hdb⟩ := Metric.continuous_iff.1 (T.continuous δ) t e he
      refine ⟨d, hd, fun s hs => ?_⟩
      have := hdb s hs
      rw [Real.dist_eq]
      rw [dist_eq_norm] at this
      have h2 := g61b_coord (T.maps s δ - T.maps t δ) x
      simp only [lp.coeFn_sub, Pi.sub_apply] at h2
      exact lt_of_le_of_lt h2 this
    have hle1 : ∀ t, c t ≤ 1 := by
      intro t
      have h1 := g61b_coord (T.maps t δ) x
      have h2 := T.contraction t δ
      rw [hδ, g61b_pm_norm] at h2
      exact le_trans (le_abs_self _) (h1.trans h2)
    have hpos : ∀ t, 0 < c t := by
      intro t
      obtain ⟨n, hn⟩ := exists_nat_gt ((t : ℝ) / ε)
      have hnpos : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hn
      set s : NNReal := t / n
      have hs : (s : ℝ) < ε := by
        simp only [s, NNReal.coe_div, NNReal.coe_natCast]
        rw [div_lt_iff₀ hnpos]; rw [div_lt_iff₀ hε] at hn; linarith
      have ht : t = (n : NNReal) * s := by
        simp only [s]; field_simp [show (n : NNReal) ≠ 0 by exact_mod_cast hnpos.ne']
      have hcs : 0 < c s := by
        have hd : ‖T.maps s δ - δ‖ < 1 := by
          have := hεb s (by simpa [NNReal.dist_eq] using hs)
          rwa [dist_eq_norm, T.initial] at this
        have h2 := g61b_coord (T.maps s δ - δ) x
        simp only [lp.coeFn_sub, Pi.sub_apply, hδ, g61b_pm_self] at h2
        have := lt_of_le_of_lt h2 hd
        rw [abs_lt] at this
        simp only [hc]; linarith
      have := hpow s _ (hall s) n
      rw [← ht] at this
      have hv : c t = c s ^ n := by
        simp only [hc] at hcs ⊢
        rw [this]; simp [g61b_pm_self, hδ]
      rw [hv]; exact pow_pos hcs n
    set L : NNReal → ℝ := fun t => Real.log (c t)
    have hL : ∀ t, L t = (t : ℝ) * L 1 := g61b_cauchy L
      (fun a b => by simp only [L]; rw [hmul, Real.log_mul (hpos a).ne' (hpos b).ne'])
      (hcont.log fun t => (hpos t).ne')
    have hL1 : L 1 ≤ 0 := Real.log_nonpos (hpos 1).le (hle1 1)
    refine ⟨⟨-L 1, by linarith⟩, fun t => ?_⟩
    rw [hall t]
    congr 1
    change c t = _
    rw [← Real.exp_log (hpos t)]
    change Real.exp (L t) = _
    rw [hL t]; congr 1; change _ = -(t : ℝ) * (-L 1); ring
  choose mu hmu using main
  exact ⟨mu, fun t x => hmu x t⟩
