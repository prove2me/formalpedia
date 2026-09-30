-- Prove2me | solution 1 for Supermodularity.MDP.stochastically_supermodular_iff_integral_supermodular
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T10:23:47.159975+00:00
-- url     : https://prove2.me/submissions/c9d44252-13a3-4b6f-8a0a-f389907f3efd

import Mathlib
import Definitions.Def_Supermodularity_MDP_StochasticallySupermodularOn
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn

set_option autoImplicit false

open MeasureTheory in
lemma p5e60_toReal_ineq {a b c d : ENNReal} (h : a + b ≤ c + d) (ha : a ≠ ⊤) (hb : b ≠ ⊤)
    (hc : c ≠ ⊤) (hd : d ≠ ⊤) : a.toReal + b.toReal ≤ c.toReal + d.toReal := by
  rw [← ENNReal.toReal_add ha hb, ← ENNReal.toReal_add hc hd]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hc, hd⟩) h

open MeasureTheory in
lemma p5e60_upper_ineq {m n : ℕ} (T : Set (Fin m → ℝ))
    (μ : (Fin m → ℝ) → Measure (Fin n → ℝ)) (hμ : ∀ t, IsProbabilityMeasure (μ t))
    (hS : Supermodularity.MDP.StochasticallySupermodularOn T μ)
    {x y : Fin m → ℝ} (hx : x ∈ T) (hy : y ∈ T) {U : Set (Fin n → ℝ)} (hU : IsUpperSet U) :
    μ x U + μ y U ≤ μ (x ⊔ y) U + μ (x ⊓ y) U := by
  have hfin : ∀ t (A : Set (Fin n → ℝ)), μ t A ≠ ⊤ := fun t A => by
    have := hμ t; exact measure_ne_top _ _
  have h : (μ x U).toReal + (μ y U).toReal ≤ (μ (x ⊔ y) U).toReal + (μ (x ⊓ y) U).toReal :=
    hS hU hx hy
  rw [← ENNReal.toReal_add (hfin _ _) (hfin _ _), ← ENNReal.toReal_add (hfin _ _) (hfin _ _)] at h
  exact (ENNReal.toReal_le_toReal (ENNReal.add_ne_top.2 ⟨hfin _ _, hfin _ _⟩)
    (ENNReal.add_ne_top.2 ⟨hfin _ _, hfin _ _⟩)).1 h

open MeasureTheory in
lemma p5e60_lower_ineq {m n : ℕ} (T : Set (Fin m → ℝ))
    (μ : (Fin m → ℝ) → Measure (Fin n → ℝ)) (hμ : ∀ t, IsProbabilityMeasure (μ t))
    (hS : Supermodularity.MDP.StochasticallySupermodularOn T μ)
    {x y : Fin m → ℝ} (hx : x ∈ T) (hy : y ∈ T) {L : Set (Fin n → ℝ)} (hL : IsLowerSet L)
    (hLm : ∀ t, t = x ∨ t = y ∨ t = x ⊔ y ∨ t = x ⊓ y → NullMeasurableSet L (μ t)) :
    μ (x ⊔ y) L + μ (x ⊓ y) L ≤ μ x L + μ y L := by
  have hfin : ∀ t (A : Set (Fin n → ℝ)), μ t A ≠ ⊤ := fun t A => by
    have := hμ t; exact measure_ne_top _ _
  have h : (μ x Lᶜ).toReal + (μ y Lᶜ).toReal ≤ (μ (x ⊔ y) Lᶜ).toReal + (μ (x ⊓ y) Lᶜ).toReal :=
    hS hL.compl hx hy
  have e : ∀ t, (t = x ∨ t = y ∨ t = x ⊔ y ∨ t = x ⊓ y) →
      (μ t L).toReal = 1 - (μ t Lᶜ).toReal := fun t ht => by
    have := hμ t
    have h1 := measure_add_measure_compl₀ (hLm t ht)
    rw [measure_univ] at h1
    have h2 := congrArg ENNReal.toReal h1
    rw [ENNReal.toReal_add (hfin _ _) (hfin _ _)] at h2
    simp only [ENNReal.toReal_one] at h2
    linarith
  have hr : (μ (x ⊔ y) L).toReal + (μ (x ⊓ y) L).toReal ≤ (μ x L).toReal + (μ y L).toReal := by
    rw [e x (Or.inl rfl), e y (Or.inr (Or.inl rfl)), e (x ⊔ y) (Or.inr (Or.inr (Or.inl rfl))),
      e (x ⊓ y) (Or.inr (Or.inr (Or.inr rfl)))]
    linarith
  rw [← ENNReal.toReal_add (hfin _ _) (hfin _ _), ← ENNReal.toReal_add (hfin _ _) (hfin _ _)] at hr
  exact (ENNReal.toReal_le_toReal (ENNReal.add_ne_top.2 ⟨hfin _ _, hfin _ _⟩)
    (ENNReal.add_ne_top.2 ⟨hfin _ _, hfin _ _⟩)).1 hr

open MeasureTheory in
lemma p5e60_pos_ineq {m n : ℕ} (T : Set (Fin m → ℝ)) (hT : IsSublattice T)
    (μ : (Fin m → ℝ) → Measure (Fin n → ℝ)) (hμ : ∀ t, IsProbabilityMeasure (μ t))
    (hS : Supermodularity.MDP.StochasticallySupermodularOn T μ)
    (g : (Fin n → ℝ) → ℝ) (hg : Monotone g) (hg0 : ∀ w, 0 ≤ g w)
    (hgm : ∀ t ∈ T, AEMeasurable g (μ t)) {x y : Fin m → ℝ} (hx : x ∈ T) (hy : y ∈ T) :
    ∫⁻ w, ENNReal.ofReal (g w) ∂μ x + ∫⁻ w, ENNReal.ofReal (g w) ∂μ y ≤
      ∫⁻ w, ENNReal.ofReal (g w) ∂μ (x ⊔ y) + ∫⁻ w, ENNReal.ofReal (g w) ∂μ (x ⊓ y) := by
  have hsup : x ⊔ y ∈ T := hT.supClosed hx hy
  have hinf : x ⊓ y ∈ T := hT.infClosed hx hy
  have lc : ∀ t ∈ T, ∫⁻ w, ENNReal.ofReal (g w) ∂μ t =
      ∫⁻ s in Set.Ioi (0:ℝ), μ t {w | s < g w} :=
    fun t ht => lintegral_eq_lintegral_meas_lt (μ t) (ae_of_all _ hg0) (hgm t ht)
  have hup : ∀ s : ℝ, IsUpperSet {w | s < g w} := fun s a b hab ha => lt_of_lt_of_le ha (hg hab)
  have hmeas : ∀ t, Measurable (fun s : ℝ => μ t {w | s < g w}) := fun t =>
    Antitone.measurable (fun s s' hss' => measure_mono (fun w hw => lt_of_le_of_lt hss' hw))
  rw [lc x hx, lc y hy, lc _ hsup, lc _ hinf]
  calc _ ≤ ∫⁻ s in Set.Ioi (0:ℝ), (μ x {w | s < g w} + μ y {w | s < g w}) :=
        le_lintegral_add _ _
    _ ≤ ∫⁻ s in Set.Ioi (0:ℝ), (μ (x ⊔ y) {w | s < g w} + μ (x ⊓ y) {w | s < g w}) :=
        lintegral_mono fun s => p5e60_upper_ineq T μ hμ hS hx hy (hup s)
    _ = _ := lintegral_add_left (hmeas _) _

open MeasureTheory in
lemma p5e60_neg_ineq {m n : ℕ} (T : Set (Fin m → ℝ)) (hT : IsSublattice T)
    (μ : (Fin m → ℝ) → Measure (Fin n → ℝ)) (hμ : ∀ t, IsProbabilityMeasure (μ t))
    (hS : Supermodularity.MDP.StochasticallySupermodularOn T μ)
    (g : (Fin n → ℝ) → ℝ) (hg : Antitone g) (hg0 : ∀ w, 0 ≤ g w)
    (hgm : ∀ t ∈ T, AEMeasurable g (μ t)) {x y : Fin m → ℝ} (hx : x ∈ T) (hy : y ∈ T) :
    ∫⁻ w, ENNReal.ofReal (g w) ∂μ (x ⊔ y) + ∫⁻ w, ENNReal.ofReal (g w) ∂μ (x ⊓ y) ≤
      ∫⁻ w, ENNReal.ofReal (g w) ∂μ x + ∫⁻ w, ENNReal.ofReal (g w) ∂μ y := by
  have hsup : x ⊔ y ∈ T := hT.supClosed hx hy
  have hinf : x ⊓ y ∈ T := hT.infClosed hx hy
  have lc : ∀ t ∈ T, ∫⁻ w, ENNReal.ofReal (g w) ∂μ t =
      ∫⁻ s in Set.Ioi (0:ℝ), μ t {w | s < g w} :=
    fun t ht => lintegral_eq_lintegral_meas_lt (μ t) (ae_of_all _ hg0) (hgm t ht)
  have hlow : ∀ s : ℝ, IsLowerSet {w | s < g w} := fun s a b hab ha => lt_of_lt_of_le ha (hg hab)
  have hmeas : ∀ t, Measurable (fun s : ℝ => μ t {w | s < g w}) := fun t =>
    Antitone.measurable (fun s s' hss' => measure_mono (fun w hw => lt_of_le_of_lt hss' hw))
  have hT4 : ∀ t, t = x ∨ t = y ∨ t = x ⊔ y ∨ t = x ⊓ y → t ∈ T := by
    rintro t (rfl | rfl | rfl | rfl) <;> assumption
  have hnm : ∀ s : ℝ, ∀ t, t = x ∨ t = y ∨ t = x ⊔ y ∨ t = x ⊓ y →
      NullMeasurableSet {w | s < g w} (μ t) := fun s t ht =>
    nullMeasurableSet_lt aemeasurable_const (hgm t (hT4 t ht))
  rw [lc x hx, lc y hy, lc _ hsup, lc _ hinf]
  calc _ ≤ ∫⁻ s in Set.Ioi (0:ℝ), (μ (x ⊔ y) {w | s < g w} + μ (x ⊓ y) {w | s < g w}) :=
        le_lintegral_add _ _
    _ ≤ ∫⁻ s in Set.Ioi (0:ℝ), (μ x {w | s < g w} + μ y {w | s < g w}) :=
        lintegral_mono fun s => p5e60_lower_ineq T μ hμ hS hx hy (hlow s) (hnm s)
    _ = _ := lintegral_add_left (hmeas _) _

open MeasureTheory Supermodularity.MDP in
theorem solution {m n : ℕ}
    (T : Set (Fin m → ℝ)) (hT : IsSublattice T)
    (μ : (Fin m → ℝ) → Measure (Fin n → ℝ))
    (hμ : ∀ t, IsProbabilityMeasure (μ t)) :
    StochasticallySupermodularOn T μ ↔
      (∀ ⦃h : (Fin n → ℝ) → ℝ⦄, Monotone h →
        (∀ t ∈ T, Integrable h (μ t)) →
        Supermodularity.Monotonicity.SupermodularOn (fun t => ∫ w, h w ∂ (μ t)) T) := by
  constructor
  · intro hS h hh hint x hx y hy
    have hsup : x ⊔ y ∈ T := hT.supClosed hx hy
    have hinf : x ⊓ y ∈ T := hT.infClosed hx hy
    show ∫ w, h w ∂μ x + ∫ w, h w ∂μ y ≤ ∫ w, h w ∂μ (x ⊔ y) + ∫ w, h w ∂μ (x ⊓ y)
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hint x hx),
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hint y hy),
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hint _ hsup),
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hint _ hinf)]
    have ep : ∀ t, ∫⁻ w, ENNReal.ofReal (h w) ∂μ t =
        ∫⁻ w, ENNReal.ofReal (max (h w) 0) ∂μ t := fun t =>
      lintegral_congr fun w => by
        rcases le_total (h w) 0 with hw | hw
        · simp [max_eq_right hw, ENNReal.ofReal_of_nonpos hw]
        · simp [max_eq_left hw]
    have en : ∀ t, ∫⁻ w, ENNReal.ofReal (-h w) ∂μ t =
        ∫⁻ w, ENNReal.ofReal (max (-h w) 0) ∂μ t := fun t =>
      lintegral_congr fun w => by
        rcases le_total (-h w) 0 with hw | hw
        · simp [max_eq_right hw, ENNReal.ofReal_of_nonpos hw]
        · simp [max_eq_left hw]
    have P := p5e60_pos_ineq T hT μ hμ hS (fun w => max (h w) 0)
      (fun a b hab => max_le_max (hh hab) le_rfl) (fun w => le_max_right _ _)
      (fun t ht => (hint t ht).aemeasurable.max aemeasurable_const) hx hy
    have N := p5e60_neg_ineq T hT μ hμ hS (fun w => max (-h w) 0)
      (fun a b hab => max_le_max (neg_le_neg (hh hab)) le_rfl) (fun w => le_max_right _ _)
      (fun t ht => (hint t ht).aemeasurable.neg.max aemeasurable_const) hx hy
    simp only [← ep, ← en] at P N
    have fp : ∀ t ∈ T, ∫⁻ w, ENNReal.ofReal (h w) ∂μ t ≠ ⊤ := fun t ht =>
      (hint t ht).lintegral_lt_top.ne
    have fn : ∀ t ∈ T, ∫⁻ w, ENNReal.ofReal (-h w) ∂μ t ≠ ⊤ := fun t ht => by
      have := (hint t ht).neg.lintegral_lt_top
      simpa using this.ne
    have P' := p5e60_toReal_ineq P (fp x hx) (fp y hy) (fp _ hsup) (fp _ hinf)
    have N' := p5e60_toReal_ineq N (fn _ hsup) (fn _ hinf) (fn x hx) (fn y hy)
    linarith
  · intro H S hS x hx y hy
    have hsup : x ⊔ y ∈ T := hT.supClosed hx hy
    have hinf : x ⊓ y ∈ T := hT.infClosed hx hy
    show (μ x S).toReal + (μ y S).toReal ≤ (μ (x ⊔ y) S).toReal + (μ (x ⊓ y) S).toReal
    have hfin : ∀ t (A : Set (Fin n → ℝ)), μ t A ≠ ⊤ := fun t A => by
      have := hμ t; exact measure_ne_top _ _
    have := hμ (x ⊔ y)
    have := hμ (x ⊓ y)
    apply le_of_forall_pos_le_add
    intro ε hε
    have hβS : (μ (x ⊔ y) + μ (x ⊓ y)) S < (μ (x ⊔ y) + μ (x ⊓ y)) S + ENNReal.ofReal ε :=
      ENNReal.lt_add_right (measure_ne_top _ _) (by simpa using hε)
    obtain ⟨G, hSG, hGo, hG⟩ := Set.exists_isOpen_lt_of_lt S _ hβS
    let U : Set (Fin n → ℝ) := {a | ∀ b, a ≤ b → b ∈ G}
    have hUup : IsUpperSet U := fun a a' haa' ha b hb => ha b (haa'.trans hb)
    have hSU : S ⊆ U := fun a ha b hab => hSG (hS hab ha)
    have hUG : U ⊆ G := fun a ha => ha a le_rfl
    have hUc : Uᶜ = ⋃ k : ℕ,
        (lowerClosure (Gᶜ ∩ Metric.closedBall (0 : Fin n → ℝ) k) : Set (Fin n → ℝ)) := by
      ext a
      simp only [Set.mem_compl_iff, Set.mem_iUnion, SetLike.mem_coe, mem_lowerClosure,
        Set.mem_inter_iff, Metric.mem_closedBall, dist_zero_right, U, Set.mem_setOf_eq]
      constructor
      · intro ha
        by_contra hne
        apply ha
        intro b hab
        by_contra hbG
        obtain ⟨k, hk⟩ := exists_nat_ge ‖b‖
        exact hne ⟨k, b, ⟨hbG, hk⟩, hab⟩
      · rintro ⟨k, b, ⟨hbG, _⟩, hab⟩ ha
        exact hbG (ha b hab)
    have hUm : MeasurableSet U := by
      rw [← compl_compl U, hUc]
      refine (MeasurableSet.iUnion fun k => ?_).compl
      refine (IsClosed.lowerClosure_pi (hGo.isClosed_compl.inter Metric.isClosed_closedBall)
        ?_).measurableSet
      refine ⟨fun _ => (k : ℝ), fun b hb i => ?_⟩
      have h1 := hb.2
      rw [Metric.mem_closedBall, dist_zero_right] at h1
      exact (le_abs_self (b i)).trans ((norm_le_pi_norm b i).trans h1)
    have hmono : Monotone (U.indicator (1 : (Fin n → ℝ) → ℝ)) := by
      intro a b hab
      by_cases ha : a ∈ U
      · rw [Set.indicator_of_mem ha, Set.indicator_of_mem (hUup hab ha)]
        exact le_rfl
      · have h0 : U.indicator (1 : (Fin n → ℝ) → ℝ) a = 0 :=
          Set.indicator_apply_eq_zero.2 (fun h => absurd h ha)
        rw [h0]
        exact Set.indicator_nonneg (fun _ _ => zero_le_one) b
    have hint : ∀ t ∈ T, Integrable (U.indicator (1 : (Fin n → ℝ) → ℝ)) (μ t) := fun t _ => by
      have := hμ t; exact (integrable_const (1:ℝ)).indicator hUm
    have key : ∫ w, U.indicator 1 w ∂μ x + ∫ w, U.indicator 1 w ∂μ y ≤
        ∫ w, U.indicator 1 w ∂μ (x ⊔ y) + ∫ w, U.indicator 1 w ∂μ (x ⊓ y) :=
      H hmono hint hx hy
    simp only [integral_indicator_one hUm, measureReal_def] at key
    have hxU : (μ x S).toReal ≤ (μ x U).toReal := ENNReal.toReal_mono (hfin _ _) (measure_mono hSU)
    have hyU : (μ y S).toReal ≤ (μ y U).toReal := ENNReal.toReal_mono (hfin _ _) (measure_mono hSU)
    have hβU : (μ (x ⊔ y) + μ (x ⊓ y)) U ≤
        (μ (x ⊔ y) + μ (x ⊓ y)) S + ENNReal.ofReal ε :=
      ((measure_mono hUG).trans_lt hG).le
    simp only [Measure.add_apply] at hβU
    have hr := ENNReal.toReal_mono
      (ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hfin _ _, hfin _ _⟩, ENNReal.ofReal_ne_top⟩) hβU
    rw [ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨hfin _ _, hfin _ _⟩) ENNReal.ofReal_ne_top,
      ENNReal.toReal_add (hfin _ _) (hfin _ _), ENNReal.toReal_add (hfin _ _) (hfin _ _),
      ENNReal.toReal_ofReal hε.le] at hr
    linarith
