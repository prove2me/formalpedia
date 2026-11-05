-- Prove2me | solution 1 for ShortWDRODual.Tight.exists_eps_optimal_coupling
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T11:03:34.649345+00:00
-- url     : https://prove2.me/submissions/e710b549-eac3-4755-ba74-1172269e4324

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_Tight_Setting

namespace ShortWDRODual.Tight.EpsOptAux

open MeasureTheory ModelRiskOT.Duality

lemma rpow_unif {R p ε : ℝ} (hp : 0 < p) (hε : 0 < ε) :
    ∃ δ > 0, ∀ a b : ℝ, 0 ≤ a → a ≤ R → 0 ≤ b → b ≤ R → |a - b| < δ →
      |a ^ p - b ^ p| < ε := by
  have hu : UniformContinuousOn (fun t : ℝ => t ^ p) (Set.Icc 0 R) :=
    isCompact_Icc.uniformContinuousOn_of_continuous
      (continuous_id.rpow_const fun _ => Or.inr hp.le).continuousOn
  obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  refine ⟨δ, hδ, fun a b ha0 haR hb0 hbR hab => ?_⟩
  have := h a ⟨ha0, haR⟩ b ⟨hb0, hbR⟩ (by rwa [Real.dist_eq])
  rwa [Real.dist_eq] at this

lemma toReal_le_of_le {z : EReal} {r : ℝ} (hz : z ≠ ⊥) (h : z ≤ (r : EReal)) : z.toReal ≤ r := by
  have := EReal.toReal_le_toReal h hz (EReal.coe_ne_top r)
  simpa using this

lemma le_toReal_of_le {z : EReal} {r : ℝ} (hz : z ≠ ⊤) (h : (r : EReal) ≤ z) : r ≤ z.toReal := by
  have := EReal.toReal_le_toReal h (EReal.coe_ne_bot r) hz
  simpa using this

end ShortWDRODual.Tight.EpsOptAux

open MeasureTheory ModelRiskOT.Duality ShortWDRODual.Tight ShortWDRODual.Tight.EpsOptAux

theorem solution {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (Phat : Measure X) [IsProbabilityMeasure Phat]
    (htight : IsTightMeasureSet ({Phat} : Set (Measure X)))
    (f : X → ℝ) (hf : NullMeasurable f Phat)
    (hfint : ⊥ < extIntegral Phat (fun x => (f x : EReal)))
    (p : ℝ) (hp : 1 ≤ p) (lam : ℝ) (hlam : 0 ≤ lam)
    (hfin : extIntegral Phat (ShortWDRODual.Legendre.supFn (pWassIntegrand f lam p)) < ⊤)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T : X → X, Measurable T ∧
      ((-6 * ε : ℝ) : EReal) + extIntegral Phat (ShortWDRODual.Legendre.supFn (pWassIntegrand f lam p)) <
        extIntegral (Phat.map (fun x => (x, T x))) (pWassIntegrand f lam p) := by
  classical
  have hp0 : 0 < p := by linarith
  set φ := pWassIntegrand f lam p with hφdef
  set Φ := ShortWDRODual.Legendre.supFn φ with hΦdef
  have hφ : ∀ a b, φ (a, b) = ((f b - lam * dist a b ^ p : ℝ) : EReal) := fun a b => rfl
  have hφq : ∀ q : X × X, φ q = ((f q.2 - lam * dist q.1 q.2 ^ p : ℝ) : EReal) := fun q => rfl
  have hΦ : ∀ a, Φ a = ⨆ x, φ (a, x) := fun a => rfl
  have hc0 : ∀ a b : X, 0 ≤ lam * dist a b ^ p :=
    fun a b => mul_nonneg hlam (Real.rpow_nonneg dist_nonneg _)
  have hcself : ∀ a : X, lam * dist a a ^ p = 0 := fun a => by
    rw [dist_self, Real.zero_rpow hp0.ne', mul_zero]
  have hcont : ∀ x : X, Continuous fun a : X => ((f x - lam * dist a x ^ p : ℝ) : EReal) := by
    intro x
    refine continuous_coe_real_ereal.comp ?_
    refine continuous_const.sub (continuous_const.mul ?_)
    exact (continuous_id.dist continuous_const).rpow_const (fun _ => Or.inr hp0.le)
  have hΦm : Measurable Φ := by
    have : LowerSemicontinuous Φ := lowerSemicontinuous_iSup fun x => (hcont x).lowerSemicontinuous
    exact this.measurable
  have hfΦ : ∀ a, ((f a : ℝ) : EReal) ≤ Φ a := fun a => by
    refine le_trans (le_of_eq ?_) (le_iSup (fun x => φ (a, x)) a)
    rw [hφ, hcself, sub_zero]
  have hnegf : ∀ x, (-((f x : ℝ) : EReal)).toENNReal = ENNReal.ofReal (-f x) := fun x => by
    rw [← EReal.coe_neg, EReal.real_coe_toENNReal]
  -- finiteness of the basic integrals
  set A := ∫⁻ x, (Φ x).toENNReal ∂Phat with hAdef
  set B := ∫⁻ x, (-Φ x).toENNReal ∂Phat with hBdef
  set Bf := ∫⁻ x, (-((f x : ℝ) : EReal)).toENNReal ∂Phat with hBfdef
  have hBf : Bf ≠ ⊤ := by
    intro h
    unfold extIntegral at hfint
    rw [← hBfdef, h] at hfint
    simp at hfint
  have hBBf : B ≤ Bf := lintegral_mono fun x =>
    EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr (hfΦ x))
  have hB : B ≠ ⊤ := ne_top_of_le_ne_top hBf hBBf
  have hA : A ≠ ⊤ := by
    intro h
    have : extIntegral Phat Φ = ⊤ := by
      show ((A : EReal)) - (B : EReal) = ⊤
      rw [h, EReal.coe_ennreal_top, ← EReal.coe_ennreal_toReal hB]
      exact EReal.top_sub_coe _
    rw [this] at hfin
    exact lt_irrefl _ hfin
  have hfi : Integrable f Phat := by
    refine ⟨hf.aemeasurable.aestronglyMeasurable, ?_⟩
    show ∫⁻ x, ‖f x‖ₑ ∂Phat < ⊤
    have hpt : ∀ x, ‖f x‖ₑ ≤ (Φ x).toENNReal + (-((f x : ℝ) : EReal)).toENNReal := by
      intro x
      rw [Real.enorm_eq_ofReal_abs, hnegf]
      have h1 : ENNReal.ofReal (f x) ≤ (Φ x).toENNReal := by
        rw [← EReal.real_coe_toENNReal]; exact EReal.toENNReal_le_toENNReal (hfΦ x)
      rcases le_or_gt 0 (f x) with h | h
      · rw [abs_of_nonneg h]; exact le_trans h1 le_self_add
      · rw [abs_of_neg h]; exact le_add_self
    calc ∫⁻ x, ‖f x‖ₑ ∂Phat ≤ ∫⁻ x, ((Φ x).toENNReal + (-((f x : ℝ) : EReal)).toENNReal) ∂Phat :=
          lintegral_mono hpt
      _ = A + Bf := lintegral_add_left hΦm.ereal_toENNReal _
      _ < ⊤ := ENNReal.add_lt_top.mpr ⟨hA.lt_top, hBf.lt_top⟩
  -- a point where `Φ` is finite, hence `f` grows at most like `λ d^p`
  have hae : ∀ᵐ x ∂Phat, (Φ x).toENNReal < ⊤ := ae_lt_top hΦm.ereal_toENNReal hA
  obtain ⟨x0, hx0⟩ := hae.exists
  have hΦx0 : Φ x0 ≠ ⊤ := EReal.toENNReal_ne_top_iff.mp hx0.ne
  have hΦx0b : Φ x0 ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (hfΦ x0)
  set m := (Φ x0).toReal with hmdef
  have hfub : ∀ x, f x ≤ m + lam * dist x0 x ^ p := by
    intro x
    have h1 : φ (x0, x) ≤ Φ x0 := le_iSup (fun y => φ (x0, y)) x
    rw [hφ, ← EReal.coe_toReal hΦx0 hΦx0b, EReal.coe_le_coe_iff] at h1
    linarith
  -- tightness: a compact `K` carrying all but `ε` of `Φ⁺` and `f⁻`
  obtain ⟨δ1, hδ1, hδ1s⟩ := exists_pos_setLIntegral_lt_of_measure_lt hA
    (ε := ENNReal.ofReal ε) (by simpa using hε)
  obtain ⟨δ2, hδ2, hδ2s⟩ := exists_pos_setLIntegral_lt_of_measure_lt hBf
    (ε := ENNReal.ofReal ε) (by simpa using hε)
  set δ0 := min (min δ1 δ2) 1 with hδ0def
  have hδ0pos : 0 < δ0 := lt_min (lt_min hδ1 hδ2) one_pos
  have hδ0top : δ0 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  obtain ⟨K0, hK0c, hK0m⟩ := (isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp htight)
    (δ0 / 2) (ENNReal.half_pos hδ0pos.ne')
  set K := insert x0 K0 with hKdef
  have hKc : IsCompact K := hK0c.insert x0
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hx0K : x0 ∈ K := Set.mem_insert x0 K0
  have hKcompl : Phat Kᶜ < min δ1 δ2 := by
    have h1 : Phat Kᶜ ≤ δ0 / 2 :=
      le_trans (measure_mono (Set.compl_subset_compl.mpr (Set.subset_insert _ _))) (hK0m Phat rfl)
    have h2 : δ0 / 2 < δ0 := ENNReal.half_lt_self hδ0pos.ne' hδ0top
    exact lt_of_lt_of_le (lt_of_le_of_lt h1 h2) (min_le_left _ _)
  have hΦtail : ∫⁻ x in Kᶜ, (Φ x).toENNReal ∂Phat < ENNReal.ofReal ε :=
    hδ1s _ (lt_of_lt_of_le hKcompl (min_le_left _ _))
  have hftail : ∫⁻ x in Kᶜ, (-((f x : ℝ) : EReal)).toENNReal ∂Phat < ENNReal.ofReal ε :=
    hδ2s _ (lt_of_lt_of_le hKcompl (min_le_right _ _))
  obtain ⟨D, hD⟩ := (Metric.isBounded_iff_subset_closedBall x0).mp hKc.isBounded
  have hD0 : 0 ≤ D := by
    have := hD hx0K
    rwa [Metric.mem_closedBall, dist_self] at this
  -- the truncated suprema `Φ_k(x̂) = sup_{d(x, x0) ≤ D + k} φ(x̂, x)`
  obtain ⟨Φk, hΦk⟩ : ∃ Φk : ℕ → X → EReal, ∀ k a,
      Φk k a = ⨆ x : Metric.closedBall x0 (D + k), φ (a, x) := ⟨_, fun _ _ => rfl⟩
  have hΦkm : ∀ k, Measurable (Φk k) := by
    intro k
    have heq : Φk k = fun a => ⨆ x : Metric.closedBall x0 (D + k), φ (a, x) := funext (hΦk k)
    have : LowerSemicontinuous (Φk k) := by
      rw [heq]
      exact lowerSemicontinuous_iSup fun x => (hcont (x : X)).lowerSemicontinuous
    exact this.measurable
  have hΦkmono : ∀ k k', k ≤ k' → ∀ a, Φk k a ≤ Φk k' a := by
    intro k k' hk a
    rw [hΦk, hΦk]
    refine iSup_le fun x => ?_
    have hx : (x : X) ∈ Metric.closedBall x0 (D + k') :=
      Metric.closedBall_subset_closedBall (by have : (k : ℝ) ≤ k' := by exact_mod_cast hk
                                              linarith) x.2
    exact le_iSup (fun y : Metric.closedBall x0 (D + k') => φ (a, y)) ⟨x, hx⟩
  have hΦksup : ∀ a, (⨆ k, Φk k a) = Φ a := by
    intro a
    apply le_antisymm
    · refine iSup_le fun k => ?_
      rw [hΦk]
      exact iSup_le fun x => le_iSup (fun y => φ (a, y)) (x : X)
    · rw [hΦ]
      refine iSup_le fun x => ?_
      obtain ⟨k, hk⟩ := exists_nat_ge (dist x x0)
      have hx : x ∈ Metric.closedBall x0 (D + k) := by
        rw [Metric.mem_closedBall]; linarith
      refine le_trans ?_ (le_iSup _ k)
      rw [hΦk]
      exact le_iSup (fun y : Metric.closedBall x0 (D + k) => φ (a, y)) ⟨x, hx⟩
  have hΦkK : ∀ k, ∀ a ∈ K, ((f a : ℝ) : EReal) ≤ Φk k a := by
    intro k a ha
    have ha' : a ∈ Metric.closedBall x0 (D + k) :=
      Metric.closedBall_subset_closedBall (by linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]) (hD ha)
    rw [hΦk]
    refine le_trans (le_of_eq ?_)
      (le_iSup (fun y : Metric.closedBall x0 (D + k) => φ (a, y)) ⟨a, ha'⟩)
    show _ = φ (a, a)
    rw [hφ, hcself, sub_zero]
  obtain ⟨U, hU⟩ : ∃ U : ℕ → ℝ, ∀ k, U k = m + lam * (D + k) ^ p := ⟨_, fun _ => rfl⟩
  have hfU : ∀ k : ℕ, ∀ x ∈ Metric.closedBall x0 (D + k), f x ≤ U k := by
    intro k x hx
    have h1 := hfub x
    have hd : dist x0 x ≤ D + k := by rw [dist_comm]; exact hx
    have h2 : dist x0 x ^ p ≤ (D + k) ^ p := Real.rpow_le_rpow dist_nonneg hd hp0.le
    have h3 : lam * dist x0 x ^ p ≤ lam * (D + k) ^ p := mul_le_mul_of_nonneg_left h2 hlam
    rw [hU]; linarith
  have hΦkU : ∀ (k : ℕ) a, Φk k a ≤ ((U k : ℝ) : EReal) := by
    intro k a
    rw [hΦk]
    refine iSup_le fun x => ?_
    rw [hφ, EReal.coe_le_coe_iff]
    linarith [hfU k x x.2, hc0 a x]
  have hΦkne_top : ∀ k a, Φk k a ≠ ⊤ := fun k a =>
    ne_top_of_le_ne_top (EReal.coe_ne_top _) (hΦkU k a)
  have hΦkne_bot : ∀ k, ∀ a ∈ K, Φk k a ≠ ⊥ := fun k a ha =>
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (hΦkK k a ha)
  -- monotone convergence on `K`
  set a := ∫⁻ x in K, (Φ x).toENNReal ∂Phat with hadef
  set b := ∫⁻ x in K, (-Φ x).toENNReal ∂Phat with hbdef
  have ha_le : a ≤ A := setLIntegral_le_lintegral _ _
  have hb_le : b ≤ B := setLIntegral_le_lintegral _ _
  have hfinK : ∀ k, ∫⁻ x in K, (-Φk k x).toENNReal ∂Phat ≤ Bf := by
    intro k
    refine le_trans (setLIntegral_mono' hKm fun x hx => ?_) (setLIntegral_le_lintegral _ _)
    exact EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr (hΦkK k x hx))
  have hsupA : a = ⨆ k, ∫⁻ x in K, (Φk k x).toENNReal ∂Phat := by
    rw [← lintegral_iSup (fun k => (hΦkm k).ereal_toENNReal)
      (fun k k' h x => EReal.toENNReal_le_toENNReal (hΦkmono k k' h x))]
    refine lintegral_congr fun x => ?_
    rw [← hΦksup x]
    exact Monotone.map_iSup_of_continuousAt EReal.continuous_toENNReal.continuousAt
      (fun _ _ h => EReal.toENNReal_le_toENNReal h) EReal.toENNReal_bot
  have hinfB : b = ⨅ k, ∫⁻ x in K, (-Φk k x).toENNReal ∂Phat := by
    rw [← lintegral_iInf (f := fun k x => (-Φk k x).toENNReal) (fun k => (hΦkm k).neg.ereal_toENNReal)
      (fun k k' h x => EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr (hΦkmono k k' h x)))
      (ne_top_of_le_ne_top hBf (hfinK 0))]
    refine lintegral_congr fun x => ?_
    rw [← hΦksup x]
    exact Antitone.map_iSup_of_continuousAt (f := fun t : EReal => (-t).toENNReal)
      (EReal.continuous_toENNReal.comp continuous_neg).continuousAt
      (fun _ _ h => EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr h)) (by simp)
  have he2 : ENNReal.ofReal (ε / 2) ≠ 0 := by simpa using hε
  obtain ⟨k1, hk1⟩ : ∃ k, a ≤ ∫⁻ x in K, (Φk k x).toENNReal ∂Phat + ENNReal.ofReal (ε / 2) := by
    by_contra hcon
    push Not at hcon
    have hlt : ∀ k, ∫⁻ x in K, (Φk k x).toENNReal ∂Phat ≤ a - ENNReal.ofReal (ε / 2) := fun k =>
      (lt_tsub_iff_right.mpr (hcon k)).le
    have h1 : a ≤ a - ENNReal.ofReal (ε / 2) := by rw [hsupA]; exact iSup_le fun k => (hsupA ▸ hlt k)
    have hpos : ENNReal.ofReal (ε / 2) ≤ a := le_trans le_add_self (hcon 0).le
    have hane : a ≠ ⊤ := ne_top_of_le_ne_top hA ha_le
    have : a - ENNReal.ofReal (ε / 2) < a :=
      ENNReal.sub_lt_self hane (ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr he2) hpos)) he2
    exact absurd (lt_of_le_of_lt h1 this) (lt_irrefl _)
  obtain ⟨k2, hk2⟩ : ∃ k, ∫⁻ x in K, (-Φk k x).toENNReal ∂Phat ≤ b + ENNReal.ofReal (ε / 2) := by
    by_contra hcon
    push Not at hcon
    have h1 : b + ENNReal.ofReal (ε / 2) ≤ b := by rw [hinfB]; exact le_iInf fun k => (hinfB ▸ hcon k).le
    have hbne : b ≠ ⊤ := ne_top_of_le_ne_top hB hb_le
    exact absurd h1 (not_le.mpr (ENNReal.lt_add_right hbne he2))
  set k := max k1 k2 with hkdef
  set ak := ∫⁻ x in K, (Φk k x).toENNReal ∂Phat with hakdef
  set bk := ∫⁻ x in K, (-Φk k x).toENNReal ∂Phat with hbkdef
  have hak : a ≤ ak + ENNReal.ofReal (ε / 2) := by
    refine le_trans hk1 (add_le_add_left ?_ _)
    exact lintegral_mono fun x => EReal.toENNReal_le_toENNReal (hΦkmono k1 k (le_max_left _ _) x)
  have hbk : bk ≤ b + ENNReal.ofReal (ε / 2) := by
    refine le_trans ?_ hk2
    exact lintegral_mono fun x =>
      EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr (hΦkmono k2 k (le_max_right _ _) x))
  -- uniform continuity of `x̂ ↦ λ d(x̂, x)^p` on `K`, uniformly in `x ∈ B_r`
  set r : ℝ := D + k with hrdef
  have hr0 : 0 ≤ r := by rw [hrdef]; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  obtain ⟨δ, hδ, hδu⟩ := rpow_unif (R := D + r) hp0 (div_pos hε (by linarith : (0:ℝ) < lam + 1))
  have hcunif : ∀ a ∈ K, ∀ a' ∈ K, ∀ y ∈ Metric.closedBall x0 r, dist a a' < δ →
      |lam * dist a y ^ p - lam * dist a' y ^ p| < ε := by
    intro a ha a' ha' y hy haa'
    have hda : dist a y ≤ D + r := by
      have := dist_triangle a x0 y
      have h1 : dist a x0 ≤ D := hD ha
      have h2 : dist x0 y ≤ r := by rw [dist_comm]; exact hy
      linarith
    have hda' : dist a' y ≤ D + r := by
      have := dist_triangle a' x0 y
      have h1 : dist a' x0 ≤ D := hD ha'
      have h2 : dist x0 y ≤ r := by rw [dist_comm]; exact hy
      linarith
    have hdd : |dist a y - dist a' y| < δ := lt_of_le_of_lt (abs_dist_sub_le a a' y) haa'
    have h := hδu _ _ dist_nonneg hda dist_nonneg hda' hdd
    rw [← mul_sub, abs_mul, abs_of_nonneg hlam]
    have hl1 : 0 < lam + 1 := by linarith
    calc lam * |dist a y ^ p - dist a' y ^ p| ≤ lam * (ε / (lam + 1)) :=
          mul_le_mul_of_nonneg_left h.le hlam
      _ < ε := by
          rw [mul_div_assoc', div_lt_iff₀ hl1]; nlinarith
  -- near-optimal points
  have hsel : ∀ c : X, ∃ x ∈ Metric.closedBall x0 r,
      c ∈ K → (Φk k c).toReal - ε < f x - lam * dist c x ^ p := by
    intro c
    by_cases hcK : c ∈ K
    · obtain ⟨y, hy⟩ : ∃ y : ℝ, y = (Φk k c).toReal := ⟨_, rfl⟩
      have hlt : ((y - ε : ℝ) : EReal) < Φk k c := by
        have : Φk k c = (y : EReal) := by rw [hy, EReal.coe_toReal (hΦkne_top k c) (hΦkne_bot k c hcK)]
        rw [this, EReal.coe_lt_coe_iff]; linarith
      have hlt' : ((y - ε : ℝ) : EReal) < ⨆ x : Metric.closedBall x0 (D + k), φ (c, x) :=
        lt_of_lt_of_eq hlt (hΦk k c)
      obtain ⟨x, hx⟩ := lt_iSup_iff.mp hlt'
      refine ⟨x, x.2, fun _ => ?_⟩
      have hx' : ((y - ε : ℝ) : EReal) < ((f x - lam * dist c x ^ p : ℝ) : EReal) := hx
      rw [EReal.coe_lt_coe_iff, hy] at hx'
      exact hx'
    · exact ⟨x0, Metric.mem_closedBall_self hr0, fun h => absurd h hcK⟩
  choose xs hxsB hxs using hsel
  -- a finite `δ`-net of `K`, enumerated by `ℕ`
  obtain ⟨t, htK, htfin, hcov⟩ := finite_cover_balls_of_compact hKc hδ
  have htne : t.Nonempty := by
    have := hcov hx0K
    simp only [Set.mem_iUnion] at this
    obtain ⟨i, hi, _⟩ := this
    exact ⟨i, hi⟩
  obtain ⟨cen, hcen⟩ := htfin.countable.exists_eq_range htne
  have hcenK : ∀ n, cen n ∈ K := fun n => htK (by rw [hcen]; exact Set.mem_range_self n)
  have hcovn : ∀ a ∈ K, ∃ n, a ∈ Metric.ball (cen n) δ := by
    intro a ha
    have := hcov ha
    simp only [Set.mem_iUnion] at this
    obtain ⟨i, hi, hai⟩ := this
    rw [hcen] at hi
    obtain ⟨n, rfl⟩ := hi
    exact ⟨n, hai⟩
  -- the selection `T`: index `0` means `x̂ ∉ K` (then `T x̂ = x̂`), index `n+1` the `n`-th ball
  obtain ⟨P, hP0, hPs⟩ : ∃ P : ℕ → X → Prop, (∀ a, P 0 a ↔ a ∉ K) ∧
      (∀ n a, P (n + 1) a ↔ a ∈ Metric.ball (cen n) δ) :=
    ⟨fun n a => match n with
      | 0 => a ∉ K
      | n + 1 => a ∈ Metric.ball (cen n) δ, fun _ => Iff.rfl, fun _ _ => Iff.rfl⟩
  have hPm : ∀ n, MeasurableSet {a | P n a} := by
    intro n
    cases n with
    | zero =>
      have : {a | P 0 a} = Kᶜ := Set.ext fun a => hP0 a
      rw [this]; exact hKm.compl
    | succ n =>
      have : {a | P (n + 1) a} = Metric.ball (cen n) δ := Set.ext fun a => hPs n a
      rw [this]; exact measurableSet_ball
  have hex : ∀ a, ∃ n, P n a := by
    intro a
    by_cases ha : a ∈ K
    · obtain ⟨n, hn⟩ := hcovn a ha
      exact ⟨n + 1, (hPs n a).mpr hn⟩
    · exact ⟨0, (hP0 a).mpr ha⟩
  obtain ⟨F, hF0, hFs⟩ : ∃ F : ℕ → X → X, (∀ a, F 0 a = a) ∧ (∀ n a, F (n + 1) a = xs (cen n)) :=
    ⟨fun n a => match n with
      | 0 => a
      | n + 1 => xs (cen n), fun _ => rfl, fun _ _ => rfl⟩
  obtain ⟨W, hW0, hWs⟩ : ∃ W : ℕ → X → ℝ, (∀ a, W 0 a = 0) ∧
      (∀ n a, W (n + 1) a = f (xs (cen n)) - lam * dist a (xs (cen n)) ^ p) :=
    ⟨fun n a => match n with
      | 0 => 0
      | n + 1 => f (xs (cen n)) - lam * dist a (xs (cen n)) ^ p, fun _ => rfl, fun _ _ => rfl⟩
  have hFm : ∀ n, Measurable (F n) := by
    intro n
    cases n with
    | zero => rw [show F 0 = id from funext hF0]; exact measurable_id
    | succ n => rw [show F (n + 1) = fun _ => xs (cen n) from funext (hFs n)]; exact measurable_const
  have hWm : ∀ n, Measurable (W n) := by
    intro n
    cases n with
    | zero => rw [show W 0 = fun _ => 0 from funext hW0]; exact measurable_const
    | succ n =>
      rw [show W (n + 1) = fun a => f (xs (cen n)) - lam * dist a (xs (cen n)) ^ p from funext (hWs n)]
      exact (measurable_const.sub (measurable_const.mul
        ((continuous_id.dist continuous_const).rpow_const
          (fun _ => Or.inr hp0.le)).measurable))
  obtain ⟨idx, hidx⟩ : ∃ idx : X → ℕ, ∀ a, idx a = Nat.find (hex a) := ⟨_, fun _ => rfl⟩
  have hidxm : Measurable idx := by
    rw [show idx = fun a => Nat.find (hex a) from funext hidx]
    exact Measurable.find (f := fun n _ => n) (fun n => measurable_const) hPm hex
  obtain ⟨T, hT⟩ : ∃ T : X → X, ∀ a, T a = F (idx a) a := ⟨_, fun _ => rfl⟩
  have hTm : Measurable T := by
    rw [show T = fun a => F (Nat.find (hex a)) a from funext fun a => by rw [hT, hidx]]
    exact Measurable.find hFm hPm hex
  obtain ⟨w, hw⟩ : ∃ w : X → ℝ, ∀ a, w a = W (idx a) a := ⟨_, fun _ => rfl⟩
  have hwm : Measurable w := by
    rw [show w = fun a => W (Nat.find (hex a)) a from funext fun a => by rw [hw, hidx]]
    exact Measurable.find hWm hPm hex
  have hidx0 : ∀ a, a ∉ K → idx a = 0 := fun a ha => by
    rw [hidx]; exact (Nat.find_eq_zero (hex a)).mpr ((hP0 a).mpr ha)
  have hidxs : ∀ a, a ∈ K → ∃ n, idx a = n + 1 ∧ a ∈ Metric.ball (cen n) δ := by
    intro a ha
    have hspec := Nat.find_spec (hex a)
    rw [← hidx] at hspec
    have hne : idx a ≠ 0 := fun h => by
      rw [h, hP0] at hspec; exact hspec ha
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hne
    refine ⟨n, hn, ?_⟩
    rw [hn, hPs] at hspec
    exact hspec
  have hTout : ∀ a, a ∉ K → T a = a := fun a ha => by rw [hT, hidx0 a ha, hF0]
  have hwout : ∀ a, a ∉ K → w a = 0 := fun a ha => by rw [hw, hidx0 a ha, hW0]
  have hTin : ∀ a n, idx a = n + 1 →
      T a = xs (cen n) ∧ w a = f (xs (cen n)) - lam * dist a (xs (cen n)) ^ p := fun a n hn => by
    rw [hT, hw, hn, hFs, hWs]; exact ⟨rfl, rfl⟩
  -- the key pointwise estimate on `K`
  have hΦkfa : ∀ a ∈ K, f a ≤ (Φk k a).toReal := fun a ha =>
    le_toReal_of_le (hΦkne_top k a) (hΦkK k a ha)
  have hwK : ∀ a ∈ K, (Φk k a).toReal - 3 * ε ≤ w a := by
    intro a ha
    obtain ⟨n, hn, hball⟩ := hidxs a ha
    have hcK := hcenK n
    have hxB := hxsB (cen n)
    have h1 := hxs (cen n) hcK
    have hdist : dist a (cen n) < δ := by rw [Metric.mem_ball] at hball; exact hball
    have h2 := hcunif a ha (cen n) hcK (xs (cen n)) hxB hdist
    have h3 : (Φk k a).toReal ≤ (Φk k (cen n)).toReal + ε := by
      refine toReal_le_of_le (hΦkne_bot k a ha) ?_
      rw [hΦk k a]
      refine iSup_le fun y => ?_
      have hy := hcunif a ha (cen n) hcK y y.2 hdist
      have hle : φ (cen n, y) ≤ Φk k (cen n) := by
        rw [hΦk k (cen n)]
        exact le_iSup (fun z : Metric.closedBall x0 (D + k) => φ (cen n, z)) y
      rw [← EReal.coe_toReal (hΦkne_top k (cen n)) (hΦkne_bot k (cen n) hcK), hφ,
        EReal.coe_le_coe_iff] at hle
      rw [hφ, EReal.coe_le_coe_iff]
      linarith [(abs_lt.mp hy).1, (abs_lt.mp hy).2]
    rw [(hTin a n hn).2]
    linarith [(abs_lt.mp h2).1, (abs_lt.mp h2).2]
  -- integrability of `w` and of `Φ_k` on `K`
  have hwhi : ∀ a ∈ K, w a ≤ U k := by
    intro a ha
    obtain ⟨n, hn, _⟩ := hidxs a ha
    rw [(hTin a n hn).2]
    linarith [hfU k _ (hxsB (cen n)), hc0 a (xs (cen n))]
  have hwbound : ∀ a, |w a| ≤ |f a| + |U k| + 3 * ε := by
    intro a
    by_cases ha : a ∈ K
    · have hlo : f a - 3 * ε ≤ w a := by linarith [hwK a ha, hΦkfa a ha]
      have hhi := hwhi a ha
      rw [abs_le]
      constructor <;> linarith [abs_nonneg (f a), abs_nonneg (U k), le_abs_self (f a),
        neg_abs_le (f a), le_abs_self (U k), neg_abs_le (U k)]
    · rw [hwout a ha, abs_zero]; positivity
  have hwi : Integrable w Phat :=
    Integrable.mono' ((hfi.abs.add (integrable_const _)).add (integrable_const _))
      hwm.aestronglyMeasurable (ae_of_all _ fun a => by rw [Real.norm_eq_abs]; exact hwbound a)
  have hvi : Integrable (fun a => (Φk k a).toReal) (Phat.restrict K) := by
    refine Integrable.mono' ((hfi.abs.add (integrable_const |U k|)).restrict (s := K))
      ((hΦkm k).ereal_toReal.aestronglyMeasurable) ?_
    refine (ae_restrict_iff' hKm).mpr (ae_of_all _ fun a ha => ?_)
    show ‖(Φk k a).toReal‖ ≤ |f a| + |U k|
    rw [Real.norm_eq_abs]
    have h1 := hΦkfa a ha
    have h2 : (Φk k a).toReal ≤ U k := toReal_le_of_le (hΦkne_bot k a ha) (hΦkU k a)
    rw [abs_le]
    constructor <;> linarith [abs_nonneg (f a), abs_nonneg (U k), le_abs_self (f a),
      neg_abs_le (f a), le_abs_self (U k), neg_abs_le (U k)]
  -- `∫_K Φ_k = a_k - b_k`
  have hak_eq : ∫⁻ x in K, ENNReal.ofReal ((Φk k x).toReal) ∂Phat = ak := by
    refine setLIntegral_congr_fun hKm fun x hx => ?_
    exact (EReal.toENNReal_of_ne_top (hΦkne_top k x)).symm
  have hbk_eq : ∫⁻ x in K, ENNReal.ofReal (-(Φk k x).toReal) ∂Phat = bk := by
    refine setLIntegral_congr_fun hKm fun x hx => ?_
    have hne : -Φk k x ≠ ⊤ := by
      intro h; exact hΦkne_bot k x hx (EReal.neg_eq_top_iff.mp h)
    rw [EReal.toENNReal_of_ne_top hne, EReal.toReal_neg_eq]
  have hintv : ∫ x in K, (Φk k x).toReal ∂Phat = ak.toReal - bk.toReal := by
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hvi, hak_eq, hbk_eq]
  -- `∫ w ≥ ∫_K Φ_k - 3ε`
  have hintw : ∫ x in K, (Φk k x).toReal ∂Phat - 3 * ε ≤ ∫ x, w x ∂Phat := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hwout]
    have h1 : ∫ x in K, ((Φk k x).toReal - 3 * ε) ∂Phat ≤ ∫ x in K, w x ∂Phat :=
      setIntegral_mono_on (hvi.sub (integrable_const _)) hwi.integrableOn hKm hwK
    rw [integral_sub hvi (integrable_const _), setIntegral_const] at h1
    have h2 : Phat.real K ≤ 1 := measureReal_le_one
    have h3 : Phat.real K • (3 * ε) ≤ 3 * ε := by
      rw [smul_eq_mul]; nlinarith [measureReal_nonneg (μ := Phat) (s := K)]
    linarith
  -- the coupling and the lower bound on its positive part
  obtain ⟨g, hg⟩ : ∃ g : X → X × X, ∀ a, g a = (a, T a) := ⟨_, fun _ => rfl⟩
  have hgm : Measurable g := by
    rw [show g = fun a => (a, T a) from funext hg]; exact measurable_id.prodMk hTm
  have hgeq : (fun x => (x, T x)) = g := (funext hg).symm
  set G : Set (X × X) := ⋃ n : ℕ, (idx ⁻¹' {n + 1}) ×ˢ {xs (cen n)} with hGdef
  have hGm : MeasurableSet G := MeasurableSet.iUnion fun n =>
    (hidxm (measurableSet_singleton _)).prod (measurableSet_singleton _)
  set h : X × X → ENNReal := G.indicator (fun q => ENNReal.ofReal (w q.1)) with hhdef
  have hhm : Measurable h :=
    (ENNReal.measurable_ofReal.comp (hwm.comp measurable_fst)).indicator hGm
  have hhle : ∀ q, h q ≤ (φ q).toENNReal := by
    intro q
    by_cases hq : q ∈ G
    · rw [hhdef, Set.indicator_of_mem hq]
      rw [hGdef, Set.mem_iUnion] at hq
      obtain ⟨n, hn⟩ := hq
      rw [Set.mem_prod, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_singleton_iff] at hn
      rw [(hTin q.1 n hn.1).2, hφq, EReal.real_coe_toENNReal, hn.2]
    · rw [hhdef, Set.indicator_of_notMem hq]; exact bot_le
  have hhg : ∀ a, ENNReal.ofReal (w a) ≤ h (g a) := by
    intro a
    by_cases ha : a ∈ K
    · obtain ⟨n, hn, _⟩ := hidxs a ha
      have hmem : g a ∈ G := by
        rw [hGdef, Set.mem_iUnion]
        refine ⟨n, ?_⟩
        rw [hg, Set.mem_prod, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_singleton_iff]
        exact ⟨hn, (hTin a n hn).1⟩
      rw [hhdef, Set.indicator_of_mem hmem, hg]
    · rw [hwout a ha, ENNReal.ofReal_zero]; exact bot_le
  have hApos : ∫⁻ a, ENNReal.ofReal (w a) ∂Phat ≤ ∫⁻ q, (φ q).toENNReal ∂(Phat.map g) :=
    calc ∫⁻ a, ENNReal.ofReal (w a) ∂Phat ≤ ∫⁻ a, h (g a) ∂Phat := lintegral_mono hhg
      _ = ∫⁻ q, h q ∂(Phat.map g) := (lintegral_map hhm hgm).symm
      _ ≤ _ := lintegral_mono hhle
  -- the upper bound on its negative part
  set Cf := ∫⁻ x in Kᶜ, (-((f x : ℝ) : EReal)).toENNReal ∂Phat with hCfdef
  have hφg : ∀ a, (-φ (g a)).toENNReal ≤
      Kᶜ.indicator (fun x => (-((f x : ℝ) : EReal)).toENNReal) a + ENNReal.ofReal (-w a) := by
    intro a
    by_cases ha : a ∈ K
    · obtain ⟨n, hn, _⟩ := hidxs a ha
      have : φ (g a) = ((w a : ℝ) : EReal) := by
        rw [hg, hφ, (hTin a n hn).1, (hTin a n hn).2]
      rw [this, ← EReal.coe_neg, EReal.real_coe_toENNReal,
        Set.indicator_of_notMem (by simpa using ha), zero_add]
    · have : φ (g a) = ((f a : ℝ) : EReal) := by
        rw [hg, hφ, hTout a ha, hcself, sub_zero]
      rw [this, Set.indicator_of_mem (by simpa using ha)]
      exact le_self_add
  have hBneg : ∫⁻ q, (-φ q).toENNReal ∂(Phat.map g) ≤ Cf + ∫⁻ a, ENNReal.ofReal (-w a) ∂Phat :=
    calc ∫⁻ q, (-φ q).toENNReal ∂(Phat.map g) ≤ ∫⁻ a, (-φ (g a)).toENNReal ∂Phat :=
          lintegral_map_le _ _
      _ ≤ ∫⁻ a, (Kᶜ.indicator (fun x => (-((f x : ℝ) : EReal)).toENNReal) a +
            ENNReal.ofReal (-w a)) ∂Phat := lintegral_mono hφg
      _ = Cf + ∫⁻ a, ENNReal.ofReal (-w a) ∂Phat := by
          have hm : Measurable fun a => ENNReal.ofReal (-w a) := ENNReal.measurable_ofReal.comp hwm.neg
          rw [lintegral_add_right _ hm,
            lintegral_indicator hKm.compl]
  -- bookkeeping in `ℝ`
  set L := ∫⁻ a, ENNReal.ofReal (w a) ∂Phat with hLdef
  set N := ∫⁻ a, ENNReal.ofReal (-w a) ∂Phat with hNdef
  have hL : L ≠ ⊤ := ne_top_of_le_ne_top hwi.2.ne (lintegral_mono fun a => by
    rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (le_abs_self _))
  have hN : N ≠ ⊤ := ne_top_of_le_ne_top hwi.2.ne (lintegral_mono fun a => by
    rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (neg_le_abs _))
  have hintw' : ∫ x, w x ∂Phat = L.toReal - N.toReal :=
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hwi
  have hCf : Cf ≠ ⊤ := ne_top_of_lt hftail
  have hCfr : Cf.toReal < ε := ENNReal.toReal_lt_of_lt_ofReal hftail
  set tail := ∫⁻ x in Kᶜ, (Φ x).toENNReal ∂Phat with htaildef
  have hAsplit : A = a + tail := (lintegral_add_compl _ hKm).symm
  have htail : tail.toReal < ε := ENNReal.toReal_lt_of_lt_ofReal hΦtail
  have hane : a ≠ ⊤ := ne_top_of_le_ne_top hA ha_le
  have htailne : tail ≠ ⊤ := ne_top_of_lt hΦtail
  have hAr : A.toReal = a.toReal + tail.toReal := by
    rw [hAsplit, ENNReal.toReal_add hane htailne]
  have hbne : b ≠ ⊤ := ne_top_of_le_ne_top hB hb_le
  have hbr : b.toReal ≤ B.toReal := ENNReal.toReal_mono hB hb_le
  have hak_le : ak ≤ a := lintegral_mono fun x =>
    EReal.toENNReal_le_toENNReal ((le_iSup (fun j => Φk j x) k).trans (hΦksup x).le)
  have hakne : ak ≠ ⊤ := ne_top_of_le_ne_top hane hak_le
  have hbkne : bk ≠ ⊤ := ne_top_of_le_ne_top hBf (hfinK k)
  have hakr : a.toReal ≤ ak.toReal + ε / 2 := by
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hakne, ENNReal.ofReal_ne_top⟩) hak
    rwa [ENNReal.toReal_add hakne ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (by linarith)] at this
  have hbkr : bk.toReal ≤ b.toReal + ε / 2 := by
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hbne, ENNReal.ofReal_ne_top⟩) hbk
    rwa [ENNReal.toReal_add hbne ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (by linarith)] at this
  refine ⟨T, hTm, ?_⟩
  rw [hgeq]
  have hE : extIntegral Phat Φ = ((A.toReal - B.toReal : ℝ) : EReal) := by
    show (A : EReal) - (B : EReal) = _
    rw [EReal.coe_sub, EReal.coe_ennreal_toReal hA, EReal.coe_ennreal_toReal hB]
  have hEγ : ((L.toReal - (Cf.toReal + N.toReal) : ℝ) : EReal) ≤ extIntegral (Phat.map g) φ := by
    have h1 : ((L : EReal)) - ((Cf + N : ENNReal) : EReal) ≤ extIntegral (Phat.map g) φ :=
      EReal.sub_le_sub (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hApos)
        (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hBneg)
    have h2 : ((L : EReal)) - ((Cf + N : ENNReal) : EReal) =
        ((L.toReal - (Cf.toReal + N.toReal) : ℝ) : EReal) := by
      rw [EReal.coe_sub, ← ENNReal.toReal_add hCf hN, EReal.coe_ennreal_toReal hL,
        EReal.coe_ennreal_toReal (ENNReal.add_ne_top.mpr ⟨hCf, hN⟩)]
    rw [← h2]; exact h1
  refine lt_of_lt_of_le ?_ hEγ
  rw [hE, ← EReal.coe_add, EReal.coe_lt_coe_iff]
  linarith
