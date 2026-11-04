-- Prove2me | solution 1 for StochKolmogorov.Extinct.theorem_1_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-03T20:57:06.088482+00:00
-- url     : https://prove2.me/submissions/0ce347a0-227c-48cc-9f2a-f90e2f90b923

import Mathlib
import Definitions.Def_StochKolmogorov_Extinct_Extinction
import Definitions.Def_StochKolmogorov_Persist_Model
import Theorems.Thm_StochKolmogorov_Persist_markov_property
import Theorems.Thm_StochKolmogorov_Persist_lemma_3_2
import Theorems.Thm_StochKolmogorov_Extinct_lemma_3_1
import Theorems.Thm_StochKolmogorov_Extinct_inequalities_5_1_5_2
import Theorems.Thm_StochKolmogorov_Extinct_lemma_5_2
import Theorems.Thm_StochKolmogorov_Extinct_proposition_5_1
import Theorems.Thm_StochKolmogorov_Extinct_one_step_5_11_5_12
import Theorems.Thm_StochKolmogorov_Extinct_box_ball_window

/-! 43e412d4 StochKolmogorov.Extinct.theorem_1_2 -- helper library (relay s2). Not a solution yet:
lemmas N6 (ergodic boundary laws miss a species) and N4 (UI moment limit). -/

set_option autoImplicit false
set_option linter.all false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace ExtinctT12

open StochKolmogorov.Extinct EthierKurtz

/-- Restricting an invariant law to a set that the dynamics cannot leave or enter (mu-a.e.)
keeps the invariance identity. -/
theorem restrict_inv {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (mu : Measure (SDEState n)) (t : ℝ≥0)
    (hinv : ∀ A : Set (SDEState n), MeasurableSet A → ∫⁻ x, trans P X t x A ∂mu = mu A)
    (S : Set (SDEState n)) (hS : MeasurableSet S)
    (h1 : ∀ᵐ x ∂mu, x ∈ S → trans P X t x Sᶜ = 0)
    (h2 : ∀ᵐ x ∂mu, x ∈ Sᶜ → trans P X t x S = 0)
    (B : Set (SDEState n)) (hB : MeasurableSet B) :
    ∫⁻ x, trans P X t x B ∂(mu.restrict S) = mu.restrict S B := by
  have e1 : ∫⁻ x, trans P X t x B ∂(mu.restrict S)
      = ∫⁻ x, trans P X t x (B ∩ S) ∂(mu.restrict S) := by
    refine lintegral_congr_ae ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' hS]
    filter_upwards [h1] with x hx hxS
    have h0 : trans P X t x (B \ S) = 0 :=
      measure_mono_null (show B \ S ⊆ Sᶜ from fun y hy => hy.2) (hx hxS)
    rw [← measure_inter_add_sdiff B hS, h0, add_zero]
  have e3 : ∫⁻ x in Sᶜ, trans P X t x (B ∩ S) ∂mu = 0 := by
    have : ∫⁻ x in Sᶜ, trans P X t x (B ∩ S) ∂mu = ∫⁻ _x in Sᶜ, (0 : ℝ≥0∞) ∂mu := by
      refine lintegral_congr_ae ?_
      rw [Filter.EventuallyEq, ae_restrict_iff' hS.compl]
      filter_upwards [h2] with x hx hxS
      exact measure_mono_null Set.inter_subset_right (hx hxS)
    rw [this, lintegral_zero]
  have e2 := lintegral_add_compl (fun x => trans P X t x (B ∩ S)) (μ := mu) hS
  rw [e3, add_zero, hinv _ (hB.inter hS)] at e2
  rw [e1, e2, Measure.restrict_apply hB]

/-- The normalized restriction of an invariant law to a two-way closed set is invariant. -/
theorem isInvariant_restrict {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (mu : Measure (SDEState n))
    (hmu : IsInvariant P X mu) (S : Set (SDEState n)) (hS : MeasurableSet S) (hS0 : mu S ≠ 0)
    (h1 : ∀ t : ℝ≥0, ∀ᵐ x ∂mu, x ∈ S → trans P X t x Sᶜ = 0)
    (h2 : ∀ t : ℝ≥0, ∀ᵐ x ∂mu, x ∈ Sᶜ → trans P X t x S = 0) :
    IsInvariant P X ((mu S)⁻¹ • mu.restrict S) := by
  obtain ⟨hprob, horth, hinv⟩ := hmu
  refine ⟨⟨?_⟩, ?_, ?_⟩
  · rw [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul,
      ENNReal.inv_mul_cancel hS0 (measure_ne_top _ _)]
  · rw [Measure.smul_apply, smul_eq_mul]
    have : mu.restrict S (orthant n)ᶜ = 0 :=
      nonpos_iff_eq_zero.1 ((Measure.le_iff'.1 Measure.restrict_le_self _).trans horth.le)
    rw [this, mul_zero]
  · intro t B hB
    rw [lintegral_smul_measure, Measure.smul_apply,
      restrict_inv P X mu t (hinv t) S hS (h1 t) (h2 t) B hB, smul_eq_mul]

/-- N6: an ergodic invariant law carried by the boundary misses some species (`supp mu ≠ univ`).
Kernel-level hypotheses: a Markov-kernel version of each `trans t` on the orthant, and invariance of
the closed coordinate faces `{y i = 0}`. -/
theorem bdryErgodic_supp_ne_univ {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hker : ∀ t : ℝ≥0, ∃ κ : Kernel (SDEState n) (SDEState n), IsMarkovKernel κ ∧
        ∀ x ∈ orthant n, κ x = trans P X t x)
    (hface : ∀ t : ℝ≥0, ∀ x ∈ orthant n, ∀ i : Fin n, x i = 0 →
        trans P X t x {y : SDEState n | y i = 0}ᶜ = 0)
    (mu : Measure (SDEState n)) (hmu : mu ∈ bdryErgodic P X) :
    supp mu ≠ Finset.univ := by
  intro hsupp
  obtain ⟨⟨hI, herg⟩, hopen⟩ := hmu
  have hI' := hI
  obtain ⟨hprob, horth, hinv⟩ := hI'
  have hae : ∀ᵐ x ∂mu, x ∈ orthant n := mem_ae_iff.2 horth
  have hcover : orthant n ⊆ openOrthant n ∪ ⋃ i, {y : SDEState n | y i = 0} := by
    intro y hy
    by_cases h : y ∈ openOrthant n
    · exact Or.inl h
    · right
      simp only [openOrthant, Set.mem_setOf_eq, not_forall, not_lt] at h
      obtain ⟨i, hi⟩ := h
      exact Set.mem_iUnion.2 ⟨i, le_antisymm hi (hy i)⟩
  have hex : ∃ i : Fin n, mu {y : SDEState n | y i = 0} ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hU : (Set.univ : Set (SDEState n)) ⊆
        (orthant n)ᶜ ∪ (openOrthant n ∪ ⋃ i, {y : SDEState n | y i = 0}) := by
      intro y _
      by_cases hy : y ∈ orthant n
      · exact Or.inr (hcover hy)
      · exact Or.inl hy
    have h0 : mu Set.univ = 0 :=
      measure_mono_null hU (measure_union_null horth (measure_union_null hopen
        (measure_iUnion_null hcon)))
    rw [measure_univ] at h0
    exact one_ne_zero h0
  obtain ⟨i, hA0⟩ := hex
  set A : Set (SDEState n) := {y : SDEState n | y i = 0} with hAdef
  have hAm : MeasurableSet A :=
    (isClosed_eq (PiLp.continuous_apply 2 _ i) continuous_const).measurableSet
  have hAc0 : mu Aᶜ ≠ 0 := by
    have hi : i ∈ supp mu := hsupp ▸ Finset.mem_univ i
    simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    intro h
    refine hi (measure_mono_null ?_ h)
    intro y hy
    simp only [hAdef, Set.mem_compl_iff, Set.mem_setOf_eq]
    exact ne_of_gt hy
  -- the closed face can be entered from outside only on a null set
  have hd : ∀ t : ℝ≥0, ∀ᵐ x ∂mu, x ∈ Aᶜ → trans P X t x A = 0 := by
    intro t
    obtain ⟨κ, hκ, hκx⟩ := hker t
    have hκae : ∀ᵐ x ∂mu, κ x = trans P X t x := by
      filter_upwards [hae] with x hx using hκx x hx
    have hfm : Measurable (fun x => κ x A) := κ.measurable_coe hAm
    have hint : ∫⁻ x, κ x A ∂mu = mu A := by
      rw [← hinv t A hAm]
      exact lintegral_congr_ae (by filter_upwards [hκae] with x hx using by rw [hx])
    have hA1 : ∫⁻ x in A, κ x A ∂mu = mu A := by
      have : ∫⁻ x in A, κ x A ∂mu = ∫⁻ _x in A, (1 : ℝ≥0∞) ∂mu := by
        refine lintegral_congr_ae ?_
        rw [Filter.EventuallyEq, ae_restrict_iff' hAm]
        filter_upwards [hae] with x hx hxA
        have hc : κ x Aᶜ = 0 := by rw [hκx x hx]; exact hface t x hx i hxA
        exact (prob_compl_eq_zero_iff hAm).1 hc
      rw [this, lintegral_one, Measure.restrict_apply_univ]
    have hsplit := lintegral_add_compl (fun x => κ x A) (μ := mu) hAm
    rw [hA1, hint] at hsplit
    have hz : ∫⁻ x in Aᶜ, κ x A ∂mu = 0 := by
      have h' : mu A + ∫⁻ x in Aᶜ, κ x A ∂mu = mu A + 0 := by rw [add_zero]; exact hsplit
      exact (ENNReal.add_right_inj (measure_ne_top mu A)).1 h'
    rw [lintegral_eq_zero_iff hfm] at hz
    have hz' : ∀ᵐ x ∂(mu.restrict Aᶜ), κ x A = 0 := hz
    rw [ae_restrict_iff' hAm.compl] at hz'
    filter_upwards [hz', hae] with x hx hxo hxA
    rw [← hκx x hxo]
    exact hx hxA
  have h1 : ∀ t : ℝ≥0, ∀ᵐ x ∂mu, x ∈ A → trans P X t x Aᶜ = 0 := by
    intro t
    filter_upwards [hae] with x hx hxA using hface t x hx i hxA
  have inv1 := isInvariant_restrict P X mu hI A hAm hA0 h1 hd
  have inv2 := isInvariant_restrict P X mu hI Aᶜ hAm.compl hAc0
    (fun t => by simpa only [compl_compl] using hd t)
    (fun t => by simpa only [compl_compl] using h1 t)
  set a : ℝ≥0 := (mu A).toNNReal with hadef
  have ha : (a : ℝ≥0∞) = mu A := ENNReal.coe_toNNReal (measure_ne_top _ _)
  have ha0 : 0 < a := ENNReal.toNNReal_pos hA0 (measure_ne_top _ _)
  have hcompl : mu Aᶜ = 1 - mu A := prob_compl_eq_one_sub hAm
  have hlt : mu A < 1 := by
    have : (0 : ℝ≥0∞) < 1 - mu A := by rw [← hcompl]; exact pos_iff_ne_zero.2 hAc0
    exact tsub_pos_iff_lt.1 this
  have ha1 : a < 1 := by
    have : (a : ℝ≥0∞) < ((1 : ℝ≥0) : ℝ≥0∞) := by rw [ha]; simpa using hlt
    exact ENNReal.coe_lt_coe.1 this
  have h1a : ((1 - a : ℝ≥0) : ℝ≥0∞) = mu Aᶜ := by
    rw [ENNReal.coe_sub, ENNReal.coe_one, ha, hcompl]
  have hdec : mu = (a : ℝ≥0∞) • ((mu A)⁻¹ • mu.restrict A)
      + ((1 - a : ℝ≥0) : ℝ≥0∞) • ((mu Aᶜ)⁻¹ • mu.restrict Aᶜ) := by
    rw [h1a, ha, smul_smul, smul_smul, ENNReal.mul_inv_cancel hA0 (measure_ne_top _ _),
      ENNReal.mul_inv_cancel hAc0 (measure_ne_top _ _), one_smul, one_smul,
      Measure.restrict_add_restrict_compl hAm]
  have heq := herg _ _ inv1 inv2 a ha0 ha1 hdec
  have hbad : ((mu A)⁻¹ • mu.restrict A) Aᶜ = 0 := by
    rw [Measure.smul_apply, Measure.restrict_apply hAm.compl, Set.compl_inter_self,
      measure_empty, smul_zero]
  rw [heq] at hbad
  exact hAc0 hbad

/-- Pointwise bound behind the uniform-integrability step N4. -/
theorem min_rpow_le {n : ℕ} (hn : 0 < n) (c : SDEState n) (hc : c ∈ openOrthant n)
    (δ₀ δ η R : ℝ) (hδ : 0 < δ) (hδδ₀ : δ < δ₀) (hη : 0 < η) (hR : 0 < R)
    (y : SDEState n) (hy : y ∈ orthant n) :
    (⨅ i : Fin n, y i) ^ δ ≤ η ^ δ
      + R ^ δ * ({z : SDEState n | ∀ i, η ≤ z i ∧ z i ≤ R}.indicator (fun _ => (1 : ℝ)) y)
      + ((1 + ∑ i, c i * y i) / (⨅ i : Fin n, c i)) ^ δ₀ / R ^ (δ₀ - δ) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hm_le : ∀ k, (⨅ i : Fin n, y i) ≤ y k := fun k => ciInf_le (Finite.bddBelow_range _) k
  have hm_nn : 0 ≤ ⨅ i : Fin n, y i := le_ciInf (fun i => hy i)
  obtain ⟨i0, hi0⟩ := exists_eq_ciInf_of_finite (f := fun i : Fin n => c i)
  have hcm_pos : 0 < ⨅ i : Fin n, c i := by rw [← hi0]; exact hc i0
  have hcm_le : ∀ i, (⨅ i : Fin n, c i) ≤ c i := fun i => ciInf_le (Finite.bddBelow_range _) i
  have hsum : ∀ k, c k * y k ≤ ∑ i, c i * y i := fun k =>
    Finset.single_le_sum (f := fun i => c i * y i) (fun i _ => mul_nonneg (hc i).le (hy i))
      (Finset.mem_univ k)
  set u := 1 + ∑ i, c i * y i with hu
  set cm := ⨅ i : Fin n, c i with hcm
  set m := ⨅ i : Fin n, y i with hm
  have hu1 : 1 ≤ u := by
    have : 0 ≤ ∑ i, c i * y i := Finset.sum_nonneg (fun i _ => mul_nonneg (hc i).le (hy i))
    linarith
  have hv0 : 0 ≤ u / cm := div_nonneg (by linarith) hcm_pos.le
  have hT3 : 0 ≤ (u / cm) ^ δ₀ / R ^ (δ₀ - δ) :=
    div_nonneg (Real.rpow_nonneg hv0 _) (Real.rpow_nonneg hR.le _)
  have hT1 : 0 ≤ η ^ δ := Real.rpow_nonneg hη.le _
  by_cases hK : y ∈ {z : SDEState n | ∀ i, η ≤ z i ∧ z i ≤ R}
  · rw [Set.indicator_of_mem hK, mul_one]
    have : m ^ δ ≤ R ^ δ :=
      Real.rpow_le_rpow hm_nn ((hm_le ⟨0, hn⟩).trans (hK ⟨0, hn⟩).2) hδ.le
    linarith
  · rw [Set.indicator_of_notMem hK, mul_zero, add_zero]
    simp only [Set.mem_setOf_eq, not_forall] at hK
    obtain ⟨i, hi⟩ := hK
    by_cases hηi : η ≤ y i
    · have hRi : R < y i := by
        by_contra h
        exact hi ⟨hηi, not_lt.1 h⟩
      have hRv : R < u / cm := by
        rw [lt_div_iff₀ hcm_pos]
        have h1 : R * cm < y i * c i := by
          calc R * cm < y i * cm := mul_lt_mul_of_pos_right hRi hcm_pos
            _ ≤ y i * c i := mul_le_mul_of_nonneg_left (hcm_le i) (hy i)
        have h2 := hsum i
        nlinarith
      have hmv : m ≤ u / cm := by
        rw [le_div_iff₀ hcm_pos]
        have h1 : m * cm ≤ y i * c i := by
          calc m * cm ≤ y i * cm := mul_le_mul_of_nonneg_right (hm_le i) hcm_pos.le
            _ ≤ y i * c i := mul_le_mul_of_nonneg_left (hcm_le i) (hy i)
        have h2 := hsum i
        nlinarith
      have hvpos : 0 < u / cm := hR.trans hRv
      have h3 : m ^ δ ≤ (u / cm) ^ δ := Real.rpow_le_rpow hm_nn hmv hδ.le
      have h4 : (u / cm) ^ δ ≤ (u / cm) ^ δ₀ / R ^ (δ₀ - δ) := by
        rw [le_div_iff₀ (Real.rpow_pos_of_pos hR _)]
        calc (u / cm) ^ δ * R ^ (δ₀ - δ) ≤ (u / cm) ^ δ * (u / cm) ^ (δ₀ - δ) :=
              mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow hR.le hRv.le (by linarith)) (Real.rpow_nonneg hv0 _)
          _ = (u / cm) ^ δ₀ := by rw [← Real.rpow_add hvpos]; congr 1; ring
      linarith
    · have : m ^ δ ≤ η ^ δ :=
        Real.rpow_le_rpow hm_nn ((hm_le i).trans (not_le.1 hηi).le) hδ.le
      linarith

/-- N4 core (uniform integrability): an orthant-valued family with a uniform `δ₀`-moment bound of
`1 + c·Y` whose mass on every interior box tends to `0` has `E (min_i Y_i)^δ → 0` for `δ < δ₀`. -/
theorem moment_limit_core {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : ℝ≥0 → Ω → SDEState n) (hYm : ∀ t, Measurable (Y t))
    (horth : ∀ t, ∀ᵐ ω ∂P, Y t ω ∈ orthant n)
    (c : SDEState n) (hc : c ∈ openOrthant n) (δ₀ H : ℝ) (hH : 0 ≤ H)
    (hmom : ∀ t, ∫⁻ ω, ENNReal.ofReal ((1 + ∑ i, c i * Y t ω i) ^ δ₀) ∂P ≤ ENNReal.ofReal H)
    (htr : ∀ η R : ℝ, 0 < η → Tendsto (fun t : ℝ≥0 =>
      (P ((Y t) ⁻¹' {z : SDEState n | ∀ i, η ≤ z i ∧ z i ≤ R})).toReal) atTop (𝓝 0))
    (δ : ℝ) (hδ : 0 < δ) (hδδ₀ : δ < δ₀) :
    (∀ t, Integrable (fun ω => (⨅ i : Fin n, Y t ω i) ^ δ) P) ∧
      Tendsto (fun t : ℝ≥0 => ∫ ω, (⨅ i : Fin n, Y t ω i) ^ δ ∂P) atTop (𝓝 0) := by
  have hcoord : ∀ i : Fin n, Measurable (fun y : SDEState n => y i) :=
    fun i => (PiLp.continuous_apply 2 _ i).measurable
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set cm := ⨅ i : Fin n, c i with hcm
  obtain ⟨i0, hi0⟩ := exists_eq_ciInf_of_finite (f := fun i : Fin n => c i)
  have hcm_pos : 0 < cm := by rw [hcm, ← hi0]; exact hc i0
  have hum : ∀ t, Measurable (fun ω => 1 + ∑ i, c i * Y t ω i) := fun t =>
    measurable_const.add (Finset.measurable_sum _
      (fun i _ => measurable_const.mul ((hcoord i).comp (hYm t))))
  have hu_nn : ∀ t, ∀ᵐ ω ∂P, 0 ≤ 1 + ∑ i, c i * Y t ω i := fun t => by
    filter_upwards [horth t] with ω hω
    have : 0 ≤ ∑ i, c i * Y t ω i :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (hc i).le (hω i))
    linarith
  have hupos : ∀ t, 0 ≤ᵐ[P] (fun ω => (1 + ∑ i, c i * Y t ω i) ^ δ₀) := fun t => by
    filter_upwards [hu_nn t] with ω hω using Real.rpow_nonneg hω _
  have huint : ∀ t, Integrable (fun ω => (1 + ∑ i, c i * Y t ω i) ^ δ₀) P := fun t =>
    ⟨((hum t).pow_const δ₀).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (hupos t)).2
        (lt_of_le_of_lt (hmom t) ENNReal.ofReal_lt_top)⟩
  have hule : ∀ t, ∫ ω, (1 + ∑ i, c i * Y t ω i) ^ δ₀ ∂P ≤ H := fun t => by
    rw [integral_eq_lintegral_of_nonneg_ae (hupos t)
      ((hum t).pow_const δ₀).aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hH (hmom t)
  have hvint : ∀ t, Integrable (fun ω => ((1 + ∑ i, c i * Y t ω i) / cm) ^ δ₀) P := fun t => by
    refine ((huint t).div_const (cm ^ δ₀)).congr ?_
    filter_upwards [hu_nn t] with ω hω
    rw [Real.div_rpow hω hcm_pos.le]
  have hvle : ∀ t, ∫ ω, ((1 + ∑ i, c i * Y t ω i) / cm) ^ δ₀ ∂P ≤ H / cm ^ δ₀ := fun t => by
    have e : ∫ ω, ((1 + ∑ i, c i * Y t ω i) / cm) ^ δ₀ ∂P
        = (∫ ω, (1 + ∑ i, c i * Y t ω i) ^ δ₀ ∂P) / cm ^ δ₀ := by
      rw [← integral_div]
      refine integral_congr_ae ?_
      filter_upwards [hu_nn t] with ω hω
      rw [Real.div_rpow hω hcm_pos.le]
    rw [e]
    exact div_le_div_of_nonneg_right (hule t) (Real.rpow_nonneg hcm_pos.le _)
  have hmm : ∀ t, Measurable (fun ω => (⨅ i : Fin n, Y t ω i) ^ δ) := fun t =>
    (Measurable.iInf (fun i => (hcoord i).comp (hYm t))).pow_const δ
  have hKm : ∀ η R : ℝ, MeasurableSet {z : SDEState n | ∀ i, η ≤ z i ∧ z i ≤ R} := fun η R => by
    have e : {z : SDEState n | ∀ i, η ≤ z i ∧ z i ≤ R}
        = ⋂ i, ({z : SDEState n | η ≤ z i} ∩ {z | z i ≤ R}) := by
      ext z; simp
    rw [e]
    exact MeasurableSet.iInter fun i =>
      (measurableSet_le measurable_const (hcoord i)).inter
        (measurableSet_le (hcoord i) measurable_const)
  have hbd : ∀ (t : ℝ≥0) (η R : ℝ), 0 < η → 0 < R →
      Integrable (fun ω => (⨅ i : Fin n, Y t ω i) ^ δ) P ∧
      ∫ ω, (⨅ i : Fin n, Y t ω i) ^ δ ∂P ≤ η ^ δ
        + R ^ δ * (P ((Y t) ⁻¹' {z : SDEState n | ∀ i, η ≤ z i ∧ z i ≤ R})).toReal
        + (H / cm ^ δ₀) / R ^ (δ₀ - δ) := by
    intro t η R hη hR
    set K := {z : SDEState n | ∀ i, η ≤ z i ∧ z i ≤ R} with hK
    have hpre : MeasurableSet ((Y t) ⁻¹' K) := hYm t (hKm η R)
    have hI1 : Integrable (fun ω => R ^ δ * (((Y t) ⁻¹' K).indicator (fun _ => (1 : ℝ)) ω)) P :=
      ((integrable_const (1 : ℝ)).indicator hpre).const_mul _
    have hI2 : Integrable (fun ω => ((1 + ∑ i, c i * Y t ω i) / cm) ^ δ₀ / R ^ (δ₀ - δ)) P :=
      (hvint t).div_const _
    have hgint : Integrable (fun ω => η ^ δ
        + R ^ δ * (((Y t) ⁻¹' K).indicator (fun _ => (1 : ℝ)) ω)
        + ((1 + ∑ i, c i * Y t ω i) / cm) ^ δ₀ / R ^ (δ₀ - δ)) P :=
      ((integrable_const _).add hI1).add hI2
    have hpt : ∀ᵐ ω ∂P, (⨅ i : Fin n, Y t ω i) ^ δ ≤ η ^ δ
        + R ^ δ * (((Y t) ⁻¹' K).indicator (fun _ => (1 : ℝ)) ω)
        + ((1 + ∑ i, c i * Y t ω i) / cm) ^ δ₀ / R ^ (δ₀ - δ) := by
      filter_upwards [horth t] with ω hω
      have h := min_rpow_le hn c hc δ₀ δ η R hδ hδδ₀ hη hR (Y t ω) hω
      have hi : ((Y t) ⁻¹' K).indicator (fun _ => (1 : ℝ)) ω
          = K.indicator (fun _ => (1 : ℝ)) (Y t ω) := rfl
      rw [hi]
      exact h
    have hint : Integrable (fun ω => (⨅ i : Fin n, Y t ω i) ^ δ) P := by
      refine Integrable.mono' hgint (hmm t).aestronglyMeasurable ?_
      filter_upwards [hpt, horth t] with ω h1 h2
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (le_ciInf fun i => h2 i) _)]
      exact h1
    refine ⟨hint, ?_⟩
    have e : ∫ ω, (η ^ δ + R ^ δ * (((Y t) ⁻¹' K).indicator (fun _ => (1 : ℝ)) ω)
        + ((1 + ∑ i, c i * Y t ω i) / cm) ^ δ₀ / R ^ (δ₀ - δ)) ∂P
        = η ^ δ + R ^ δ * (P ((Y t) ⁻¹' K)).toReal
          + (∫ ω, ((1 + ∑ i, c i * Y t ω i) / cm) ^ δ₀ ∂P) / R ^ (δ₀ - δ) := by
      have hA : Integrable (fun ω => η ^ δ
          + R ^ δ * (((Y t) ⁻¹' K).indicator (fun _ => (1 : ℝ)) ω)) P :=
        (integrable_const _).add hI1
      rw [integral_add hA hI2,
        integral_add (integrable_const _) hI1, integral_const, integral_const_mul,
        integral_indicator_const _ hpre, integral_div]
      simp [measureReal_def]
    calc ∫ ω, (⨅ i : Fin n, Y t ω i) ^ δ ∂P
        ≤ ∫ ω, (η ^ δ + R ^ δ * (((Y t) ⁻¹' K).indicator (fun _ => (1 : ℝ)) ω)
          + ((1 + ∑ i, c i * Y t ω i) / cm) ^ δ₀ / R ^ (δ₀ - δ)) ∂P :=
          integral_mono_ae hint hgint hpt
      _ = η ^ δ + R ^ δ * (P ((Y t) ⁻¹' K)).toReal
          + (∫ ω, ((1 + ∑ i, c i * Y t ω i) / cm) ^ δ₀ ∂P) / R ^ (δ₀ - δ) := e
      _ ≤ η ^ δ + R ^ δ * (P ((Y t) ⁻¹' K)).toReal + (H / cm ^ δ₀) / R ^ (δ₀ - δ) := by
          have := div_le_div_of_nonneg_right (hvle t) (Real.rpow_nonneg hR.le (δ₀ - δ))
          linarith
  refine ⟨fun t => (hbd t 1 1 one_pos one_pos).1, ?_⟩
  have hF0 : ∀ t : ℝ≥0, 0 ≤ ∫ ω, (⨅ i : Fin n, Y t ω i) ^ δ ∂P := fun t =>
    integral_nonneg_of_ae (by
      filter_upwards [horth t] with ω hω using Real.rpow_nonneg (le_ciInf fun i => hω i) _)
  rw [tendsto_order]
  refine ⟨fun a ha => Eventually.of_forall fun t => lt_of_lt_of_le ha (hF0 t), fun ε hε => ?_⟩
  have hη0 : Tendsto (fun η : ℝ => η ^ δ) (𝓝[>] 0) (𝓝 0) := by
    have h := (Real.continuousAt_rpow_const 0 δ (Or.inr hδ.le)).tendsto
    rw [Real.zero_rpow hδ.ne'] at h
    exact tendsto_nhdsWithin_of_tendsto_nhds h
  obtain ⟨η, hηε, hη⟩ :=
    ((hη0.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 3))).and
      self_mem_nhdsWithin).exists
  have hR0 : Tendsto (fun R : ℝ => (H / cm ^ δ₀) / R ^ (δ₀ - δ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_rpow_atTop (by linarith))
  obtain ⟨R, hRε, hR⟩ :=
    ((hR0.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 3))).and
      (eventually_gt_atTop 0)).exists
  have hp : Tendsto (fun t : ℝ≥0 => R ^ δ *
      (P ((Y t) ⁻¹' {z : SDEState n | ∀ i, η ≤ z i ∧ z i ≤ R})).toReal) atTop (𝓝 0) := by
    simpa using (htr η R hη).const_mul (R ^ δ)
  filter_upwards [hp.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 3))] with t ht
  have := (hbd t η R hη hR).2
  linarith

/-- Chapman-Kolmogorov in integral form (nonnegative test functions) from an interior start. -/
theorem lint_ck {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hker : ∀ t : ℝ≥0, ∃ κ : Kernel (SDEState n) (SDEState n), IsMarkovKernel κ ∧
        ∀ x ∈ orthant n, κ x = trans P X t x)
    (hCK : ∀ (s t : ℝ≥0) (x : SDEState n), x ∈ orthant n → ∀ A : Set (SDEState n),
        MeasurableSet A → trans P X (s + t) x A = ∫⁻ y, trans P X t y A ∂(trans P X s x))
    (hOO : ∀ (t : ℝ≥0) (x : SDEState n), x ∈ openOrthant n →
        trans P X t x (openOrthant n)ᶜ = 0)
    (r t : ℝ≥0) (x : SDEState n) (hx : x ∈ openOrthant n)
    (f : SDEState n → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ y, f y ∂(trans P X (r + t) x)
      = ∫⁻ y, (∫⁻ z, f z ∂(trans P X t y)) ∂(trans P X r x) := by
  obtain ⟨κ, -, hκ⟩ := hker t
  have hxo : x ∈ orthant n := fun i => (hx i).le
  have hae : ∀ᵐ y ∂(trans P X r x), y ∈ orthant n := by
    have h1 : ∀ᵐ y ∂(trans P X r x), y ∈ openOrthant n := mem_ae_iff.2 (hOO r x hx)
    filter_upwards [h1] with y hy using fun i => (hy i).le
  have hb : trans P X (r + t) x = (trans P X r x).bind κ := by
    ext A hA
    rw [Measure.bind_apply hA κ.measurable.aemeasurable, hCK r t x hxo A hA]
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with y hy
    rw [hκ y hy]
  rw [hb, Measure.lintegral_bind κ.measurable.aemeasurable hf.aemeasurable]
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with y hy
  rw [hκ y hy]

/-- N3: interior transience from a bounded `τ`-superharmonic `W` that is maximal (`= ς`) on `K'`
and drops by `d` in one `τ`-step from `K'`, plus a short-time stay `K → K'`. Kernel level only. -/
theorem transience_core {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hXm : ∀ x ∈ orthant n, ∀ t, Measurable (X x t))
    (hker : ∀ t : ℝ≥0, ∃ κ : Kernel (SDEState n) (SDEState n), IsMarkovKernel κ ∧
        ∀ x ∈ orthant n, κ x = trans P X t x)
    (hCK : ∀ (s t : ℝ≥0) (x : SDEState n), x ∈ orthant n → ∀ A : Set (SDEState n),
        MeasurableSet A → trans P X (s + t) x A = ∫⁻ y, trans P X t y A ∂(trans P X s x))
    (hOO : ∀ (t : ℝ≥0) (x : SDEState n), x ∈ openOrthant n →
        trans P X t x (openOrthant n)ᶜ = 0)
    (W : SDEState n → ℝ) (hWm : Measurable W) (ς : ℝ) (hW0 : ∀ x, 0 ≤ W x)
    (hWς : ∀ x, W x ≤ ς) (τ : ℝ≥0) (hτ : 0 < τ)
    (hsup : ∀ x ∈ openOrthant n, ∫ ω, W (X x τ ω) ∂P ≤ W x)
    (K K' : Set (SDEState n)) (hKm : MeasurableSet K) (hK'm : MeasurableSet K')
    (hWK : ∀ x ∈ K', W x = ς) (d : ℝ) (hd : 0 < d)
    (hdec : ∀ y ∈ K', ∫ ω, W (X y τ ω) ∂P ≤ ς - d)
    (hwin : ∃ s₁ s₂ : ℝ≥0, s₁ < s₂ ∧ ∃ p : ℝ, 0 < p ∧ ∀ y ∈ K, ∀ s : ℝ≥0, s₁ ≤ s → s ≤ s₂ →
      p ≤ (trans P X s y K').toReal) :
    ∀ x ∈ openOrthant n, Tendsto (fun t : ℝ≥0 => (trans P X t x K).toReal) atTop (𝓝 0) := by
  intro x hx
  have hxo : x ∈ orthant n := fun i => (hx i).le
  have hprob : ∀ (t : ℝ≥0) (y : SDEState n), y ∈ orthant n →
      IsProbabilityMeasure (trans P X t y) :=
    fun t y hy => Measure.isProbabilityMeasure_map (hXm y hy t).aemeasurable
  have hVm : Measurable (fun y => ENNReal.ofReal (W y)) := hWm.ennreal_ofReal
  have hlV : ∀ (t : ℝ≥0) (y : SDEState n), y ∈ orthant n →
      ∫⁻ z, ENNReal.ofReal (W z) ∂(trans P X t y) = ENNReal.ofReal (∫ ω, W (X y t ω) ∂P) := by
    intro t y hy
    have := hprob t y hy
    have hi : ∫ ω, W (X y t ω) ∂P = ∫ z, W z ∂(trans P X t y) := by
      rw [StochKolmogorov.Extinct.trans, integral_map (hXm y hy t).aemeasurable hWm.aestronglyMeasurable]
    rw [hi, ofReal_integral_eq_lintegral_ofReal]
    · exact (integrable_const ς).mono' hWm.aestronglyMeasurable
        (ae_of_all _ fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (hW0 z)]; exact hWς z)
    · exact ae_of_all _ (fun z => hW0 z)
  have hGfin : ∀ r : ℝ≥0, ∫⁻ z, ENNReal.ofReal (W z) ∂(trans P X r x) ≤ ENNReal.ofReal ς := by
    intro r
    have := hprob r x hxo
    calc ∫⁻ z, ENNReal.ofReal (W z) ∂(trans P X r x)
        ≤ ∫⁻ _z, ENNReal.ofReal ς ∂(trans P X r x) :=
          lintegral_mono fun z => ENNReal.ofReal_le_ofReal (hWς z)
      _ = ENNReal.ofReal ς := by rw [lintegral_const, measure_univ, mul_one]
  have hς0 : 0 ≤ ς := (hW0 x).trans (hWς x)
  set g : ℝ≥0 → ℝ := fun r => (∫⁻ z, ENNReal.ofReal (W z) ∂(trans P X r x)).toReal with hg
  have hg0 : ∀ r, 0 ≤ g r := fun r => ENNReal.toReal_nonneg
  have hgς : ∀ r, g r ≤ ς := fun r => ENNReal.toReal_le_of_le_ofReal hς0 (hGfin r)
  have hstep : ∀ r : ℝ≥0, g (r + τ) + d * (trans P X r x K').toReal ≤ g r := by
    intro r
    have := hprob r x hxo
    have hΦ : ∀ᵐ y ∂(trans P X r x), (∫⁻ z, ENNReal.ofReal (W z) ∂(trans P X τ y))
        + K'.indicator (fun _ => ENNReal.ofReal d) y ≤ ENNReal.ofReal (W y) := by
      have h1 : ∀ᵐ y ∂(trans P X r x), y ∈ openOrthant n := mem_ae_iff.2 (hOO r x hx)
      filter_upwards [h1] with y hy
      have hyo : y ∈ orthant n := fun i => (hy i).le
      rw [hlV τ y hyo]
      by_cases hyK : y ∈ K'
      · rw [Set.indicator_of_mem hyK, hWK y hyK,
          ← ENNReal.ofReal_add (integral_nonneg fun ω => hW0 _) hd.le]
        exact ENNReal.ofReal_le_ofReal (by linarith [hdec y hyK])
      · rw [Set.indicator_of_notMem hyK, add_zero]
        exact ENNReal.ofReal_le_ofReal (hsup y hy)
    have hlin : ∫⁻ z, ENNReal.ofReal (W z) ∂(trans P X (r + τ) x)
        + ENNReal.ofReal d * trans P X r x K'
        ≤ ∫⁻ z, ENNReal.ofReal (W z) ∂(trans P X r x) := by
      rw [lint_ck P X hker hCK hOO r τ x hx _ hVm, ← lintegral_indicator_const hK'm,
        ← lintegral_add_right _ (measurable_const.indicator hK'm)]
      exact lintegral_mono_ae hΦ
    have hfin1 : ∫⁻ z, ENNReal.ofReal (W z) ∂(trans P X (r + τ) x) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hGfin _)
    have hfin2 : ENNReal.ofReal d * trans P X r x K' ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
    have h2 := ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hGfin r)) hlin
    rw [ENNReal.toReal_add hfin1 hfin2, ENNReal.toReal_mul, ENNReal.toReal_ofReal hd.le] at h2
    exact h2
  obtain ⟨s₁, s₂, hs12, p, hp, hst⟩ := hwin
  set u₀ : ℝ≥0 := s₂ - s₁ with hu₀def
  have hu₀ : 0 < u₀ := tsub_pos_of_lt hs12
  set N : ℕ := ⌈τ / u₀⌉₊ + 1 with hNdef
  have hNpos : (0 : ℝ≥0) < (N : ℝ≥0) := by
    rw [hNdef]; exact_mod_cast Nat.succ_pos _
  set h : ℝ≥0 := τ / N with hhdef
  have hh0 : 0 < h := div_pos hτ hNpos
  have hNh : (N : ℝ≥0) * h = τ := by
    rw [hhdef, mul_div_assoc', mul_div_cancel_left₀ τ hNpos.ne']
  have hhu : h ≤ u₀ := by
    rw [hhdef, div_le_iff₀ hNpos]
    have h1 : τ / u₀ ≤ (N : ℝ≥0) := by
      have h2 : ((⌈τ / u₀⌉₊ : ℕ) : ℝ≥0) ≤ (N : ℝ≥0) := by
        rw [hNdef]; exact_mod_cast Nat.le_succ _
      exact (Nat.le_ceil (τ / u₀)).trans h2
    rw [div_le_iff₀ hu₀] at h1
    rw [mul_comm]; exact h1
  have hstep' : ∀ q : ℕ, g (((q + N : ℕ) : ℝ≥0) * h)
      + d * (trans P X ((q : ℝ≥0) * h) x K').toReal ≤ g ((q : ℝ≥0) * h) := by
    intro q
    have e : ((q + N : ℕ) : ℝ≥0) * h = (q : ℝ≥0) * h + τ := by
      rw [← hNh]; push_cast; ring
    rw [e]; exact hstep _
  have htel : ∀ M : ℕ, d * ∑ q ∈ Finset.range M, (trans P X ((q : ℝ≥0) * h) x K').toReal
      ≤ ∑ q ∈ Finset.range N, g ((q : ℝ≥0) * h)
        - ∑ q ∈ Finset.range N, g (((M + q : ℕ) : ℝ≥0) * h) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      have e1 := Finset.sum_range_succ' (fun i => g (((M + i : ℕ) : ℝ≥0) * h)) N
      have e2 := Finset.sum_range_succ (fun i => g (((M + i : ℕ) : ℝ≥0) * h)) N
      have e3 : ∑ i ∈ Finset.range N, g (((M + (i + 1) : ℕ) : ℝ≥0) * h)
          = ∑ q ∈ Finset.range N, g (((M + 1 + q : ℕ) : ℝ≥0) * h) :=
        Finset.sum_congr rfl fun i _ => by rw [show M + (i + 1) = M + 1 + i by omega]
      have e4 := hstep' M
      simp only [Nat.add_zero] at e1
      rw [Finset.sum_range_succ, mul_add]
      linarith
  have hbnn : ∀ q : ℕ, 0 ≤ (trans P X ((q : ℝ≥0) * h) x K').toReal :=
    fun q => ENNReal.toReal_nonneg
  have hpart : ∀ M : ℕ, ∑ q ∈ Finset.range M, (trans P X ((q : ℝ≥0) * h) x K').toReal
      ≤ N * ς / d := by
    intro M
    have h1 := htel M
    have h2 : ∑ q ∈ Finset.range N, g ((q : ℝ≥0) * h) ≤ N * ς := by
      have := Finset.sum_le_sum (s := Finset.range N) fun q _ => hgς ((q : ℝ≥0) * h)
      simpa using this
    have h3 : 0 ≤ ∑ q ∈ Finset.range N, g (((M + q : ℕ) : ℝ≥0) * h) :=
      Finset.sum_nonneg fun q _ => hg0 _
    rw [le_div_iff₀ hd, mul_comm]
    linarith
  have hb : Tendsto (fun q : ℕ => (trans P X ((q : ℝ≥0) * h) x K').toReal) atTop (𝓝 0) :=
    (summable_of_sum_range_le hbnn hpart).tendsto_atTop_zero
  have hq : Tendsto (fun t : ℝ≥0 => ⌈(t + s₁) / h⌉₊) atTop atTop := by
    refine tendsto_atTop_atTop.2 fun b => ⟨(b : ℝ≥0) * h, fun a ha => ?_⟩
    have h1 : (b : ℝ≥0) ≤ (a + s₁) / h := by
      rw [le_div_iff₀ hh0]; exact ha.trans le_self_add
    exact Nat.cast_le.1 (h1.trans (Nat.le_ceil _))
  have hbound : ∀ t : ℝ≥0, (trans P X t x K).toReal
      ≤ (trans P X (((⌈(t + s₁) / h⌉₊ : ℕ) : ℝ≥0) * h) x K').toReal / p := by
    intro t
    set q := ⌈(t + s₁) / h⌉₊ with hqdef
    have hq1 : t + s₁ ≤ (q : ℝ≥0) * h := by rw [← div_le_iff₀ hh0]; exact Nat.le_ceil _
    have hq2 : (q : ℝ≥0) * h < t + s₁ + h := by
      have h1 := Nat.ceil_lt_add_one (by positivity : (0 : ℝ≥0) ≤ (t + s₁) / h)
      calc (q : ℝ≥0) * h < ((t + s₁) / h + 1) * h := mul_lt_mul_of_pos_right h1 hh0
        _ = t + s₁ + h := by rw [add_mul, div_mul_cancel₀ _ hh0.ne', one_mul]
    set u := (q : ℝ≥0) * h - t with hu
    have htq : t ≤ (q : ℝ≥0) * h := le_self_add.trans hq1
    have htu : t + u = (q : ℝ≥0) * h := add_tsub_cancel_of_le htq
    have hu1 : s₁ ≤ u := by rw [hu]; exact le_tsub_of_add_le_left hq1
    have hu2 : u ≤ s₂ := by
      rw [hu, tsub_le_iff_left]
      have h3 : t + s₁ + h ≤ t + s₂ := by
        calc t + s₁ + h ≤ t + s₁ + u₀ := by gcongr
          _ = t + s₂ := by rw [hu₀def, add_assoc, add_tsub_cancel_of_le hs12.le]
      exact (hq2.trans_le h3).le
    have := hprob t x hxo
    have := hprob ((q : ℝ≥0) * h) x hxo
    have hE : ENNReal.ofReal p * trans P X t x K ≤ trans P X ((q : ℝ≥0) * h) x K' := by
      rw [← htu, hCK t u x hxo K' hK'm, ← setLIntegral_const]
      refine le_trans ?_ (setLIntegral_le_lintegral K _)
      refine lintegral_mono_ae ?_
      rw [ae_restrict_iff' hKm]
      exact ae_of_all _ fun y hy => ENNReal.ofReal_le_of_le_toReal (hst y hy u hu1 hu2)
    have h2 := ENNReal.toReal_mono (measure_ne_top _ _) hE
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hp.le] at h2
    rw [le_div_iff₀ hp]
    linarith
  have hlim : Tendsto (fun t : ℝ≥0 =>
      (trans P X (((⌈(t + s₁) / h⌉₊ : ℕ) : ℝ≥0) * h) x K').toReal / p) atTop (𝓝 0) := by
    simpa using (hb.comp hq).div_const p
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun t => ENNReal.toReal_nonneg) hbound

/-- Chapman-Kolmogorov iteration of a one-step minorisation onto `Bl ⊆ Bx`. -/
theorem iterate_window {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hXm : ∀ x ∈ orthant n, ∀ t, Measurable (X x t))
    (hCK : ∀ (s t : ℝ≥0) (x : SDEState n), x ∈ orthant n → ∀ A : Set (SDEState n),
        MeasurableSet A → trans P X (s + t) x A = ∫⁻ y, trans P X t y A ∂(trans P X s x))
    (Bx Bl : Set (SDEState n)) (hBl : Bl ⊆ Bx) (hBlm : MeasurableSet Bl)
    (hBxo : Bx ⊆ orthant n) (T : ℝ≥0) (p : ℝ) (hp : 0 ≤ p)
    (hwin : ∀ y ∈ Bx, p ≤ (trans P X T y Bl).toReal) :
    ∀ m : ℕ, ∀ y ∈ Bx, p ^ (m + 1) ≤ (trans P X (((m + 1 : ℕ) : ℝ≥0) * T) y Bl).toReal := by
  have hprob : ∀ (t : ℝ≥0) (y : SDEState n), y ∈ orthant n →
      IsProbabilityMeasure (trans P X t y) :=
    fun t y hy => Measure.isProbabilityMeasure_map (hXm y hy t).aemeasurable
  intro m
  induction m with
  | zero => intro y hy; simpa using hwin y hy
  | succ m ih =>
    intro y hy
    have hyo := hBxo hy
    have := hprob (((m + 1 : ℕ) : ℝ≥0) * T) y hyo
    have := hprob (((m + 1 + 1 : ℕ) : ℝ≥0) * T) y hyo
    have e : (((m + 1 + 1 : ℕ) : ℝ≥0) * T) = ((m + 1 : ℕ) : ℝ≥0) * T + T := by push_cast; ring
    have hE : ENNReal.ofReal p * trans P X (((m + 1 : ℕ) : ℝ≥0) * T) y Bl
        ≤ trans P X (((m + 1 + 1 : ℕ) : ℝ≥0) * T) y Bl := by
      rw [e, hCK _ T y hyo Bl hBlm, ← setLIntegral_const]
      refine le_trans ?_ (setLIntegral_le_lintegral Bl _)
      refine lintegral_mono_ae ?_
      rw [ae_restrict_iff' hBlm]
      exact ae_of_all _ fun w hw => ENNReal.ofReal_le_of_le_toReal (hwin w (hBl hw))
    have h2 := ENNReal.toReal_mono (measure_ne_top _ _) hE
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hp] at h2
    have h3 := mul_le_mul_of_nonneg_left (ih y hy) hp
    calc p ^ (m + 1 + 1) = p * p ^ (m + 1) := by ring
      _ ≤ _ := h3.trans h2

/-- A window minorisation on `[T₀/2, T₀]` gives a minorisation at every time `s ≥ T₀/2`. -/
theorem fixed_time_window {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hXm : ∀ x ∈ orthant n, ∀ t, Measurable (X x t))
    (hCK : ∀ (s t : ℝ≥0) (x : SDEState n), x ∈ orthant n → ∀ A : Set (SDEState n),
        MeasurableSet A → trans P X (s + t) x A = ∫⁻ y, trans P X t y A ∂(trans P X s x))
    (Bx Bl : Set (SDEState n)) (hBl : Bl ⊆ Bx) (hBlm : MeasurableSet Bl)
    (hBxo : Bx ⊆ orthant n) (T₀ : ℝ≥0) (hT₀ : 0 < T₀) (p : ℝ) (hp : 0 < p)
    (hwin : ∀ T : ℝ≥0, T₀ / 2 ≤ T → T ≤ T₀ → ∀ y ∈ Bx, p ≤ (trans P X T y Bl).toReal)
    (s : ℝ≥0) (hs : T₀ / 2 ≤ s) :
    ∃ q : ℝ, 0 < q ∧ ∀ y ∈ Bx, q ≤ (trans P X s y Bl).toReal := by
  have hT₀R : (0 : ℝ) < T₀ := NNReal.coe_pos.2 hT₀
  have hsR : (T₀ : ℝ) / 2 ≤ s := by
    have := NNReal.coe_le_coe.2 hs; simpa using this
  have hspos : (0 : ℝ) < s := by linarith
  set k : ℕ := ⌈(s : ℝ) / T₀⌉₊ with hk
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 (by
    rw [hk]; exact (Nat.ceil_pos.2 (div_pos hspos hT₀R)).ne')
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk1
  have hkup : (s : ℝ) / T₀ ≤ k := Nat.le_ceil _
  have hklo : (k : ℝ) < s / T₀ + 1 := Nat.ceil_lt_add_one (div_pos hspos hT₀R).le
  obtain ⟨m, hm⟩ : ∃ m : ℕ, k = m + 1 := ⟨k - 1, by omega⟩
  set T : ℝ≥0 := s / (k : ℝ≥0) with hT
  have hTR : (T : ℝ) = s / k := by rw [hT]; push_cast; ring
  have hTle : T ≤ T₀ := by
    rw [← NNReal.coe_le_coe, hTR, div_le_iff₀ hkR]
    rw [div_le_iff₀ hT₀R] at hkup
    linarith
  have hTge : T₀ / 2 ≤ T := by
    rw [← NNReal.coe_le_coe, hTR, NNReal.coe_div, le_div_iff₀ hkR]
    have h1 : (k : ℝ) * T₀ < s + T₀ := by
      have := mul_lt_mul_of_pos_right hklo hT₀R
      rwa [add_mul, div_mul_cancel₀ _ hT₀R.ne', one_mul] at this
    push_cast
    have h2 : (T₀ : ℝ) / 2 * k = (k * T₀) / 2 := by ring
    rw [h2]
    by_cases hsT0 : (s : ℝ) ≤ T₀
    · have hk1' : k ≤ 1 := Nat.ceil_le.2 (by
        rw [Nat.cast_one, div_le_one hT₀R]; exact hsT0)
      have hk' : (k : ℝ) = 1 := by exact_mod_cast le_antisymm hk1' hk1
      rw [hk']; linarith
    · linarith
  have hsT : ((m + 1 : ℕ) : ℝ≥0) * T = s := by
    rw [← hm, hT, mul_div_cancel₀]
    exact_mod_cast (Nat.one_le_iff_ne_zero.1 hk1)
  refine ⟨p ^ (m + 1), pow_pos hp _, fun y hy => ?_⟩
  have := iterate_window P X hXm hCK Bx Bl hBl hBlm hBxo T p hp.le
    (fun y hy => hwin T hTge hTle y hy) m y hy
  rwa [hsT] at this

end ExtinctT12

/-! Relay s3: glue lemmas (superharmonic iteration, the cap `CU > 0`, `U_θ` bounds). -/
namespace ExtinctT12

open StochKolmogorov.Extinct EthierKurtz

/-- A `τ`-superharmonic bounded `W` is `(m+1)τ`-superharmonic (Chapman-Kolmogorov). -/
theorem sup_iterate {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hXm : ∀ x ∈ orthant n, ∀ t, Measurable (X x t))
    (hker : ∀ t : ℝ≥0, ∃ κ : Kernel (SDEState n) (SDEState n), IsMarkovKernel κ ∧
        ∀ x ∈ orthant n, κ x = trans P X t x)
    (hCK : ∀ (s t : ℝ≥0) (x : SDEState n), x ∈ orthant n → ∀ A : Set (SDEState n),
        MeasurableSet A → trans P X (s + t) x A = ∫⁻ y, trans P X t y A ∂(trans P X s x))
    (hOO : ∀ (t : ℝ≥0) (x : SDEState n), x ∈ openOrthant n →
        trans P X t x (openOrthant n)ᶜ = 0)
    (W : SDEState n → ℝ) (hWm : Measurable W) (ς : ℝ) (hW0 : ∀ x, 0 ≤ W x)
    (hWς : ∀ x, W x ≤ ς) (τ : ℝ≥0)
    (hsup : ∀ x ∈ openOrthant n, ∫ ω, W (X x τ ω) ∂P ≤ W x) :
    ∀ m : ℕ, ∀ x ∈ openOrthant n, ∫ ω, W (X x (((m + 1 : ℕ) : ℝ≥0) * τ) ω) ∂P ≤ W x := by
  have hprob : ∀ (t : ℝ≥0) (y : SDEState n), y ∈ orthant n →
      IsProbabilityMeasure (trans P X t y) :=
    fun t y hy => Measure.isProbabilityMeasure_map (hXm y hy t).aemeasurable
  have hVm : Measurable (fun y => ENNReal.ofReal (W y)) := hWm.ennreal_ofReal
  have hlV : ∀ (t : ℝ≥0) (y : SDEState n), y ∈ orthant n →
      ∫⁻ z, ENNReal.ofReal (W z) ∂(trans P X t y) = ENNReal.ofReal (∫ ω, W (X y t ω) ∂P) := by
    intro t y hy
    have := hprob t y hy
    have hi : ∫ ω, W (X y t ω) ∂P = ∫ z, W z ∂(trans P X t y) := by
      rw [StochKolmogorov.Extinct.trans, integral_map (hXm y hy t).aemeasurable hWm.aestronglyMeasurable]
    rw [hi, ofReal_integral_eq_lintegral_ofReal]
    · exact (integrable_const ς).mono' hWm.aestronglyMeasurable
        (ae_of_all _ fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (hW0 z)]; exact hWς z)
    · exact ae_of_all _ (fun z => hW0 z)
  have key : ∀ m : ℕ, ∀ x ∈ openOrthant n,
      ∫⁻ z, ENNReal.ofReal (W z) ∂(trans P X (((m + 1 : ℕ) : ℝ≥0) * τ) x)
        ≤ ENNReal.ofReal (W x) := by
    intro m
    induction m with
    | zero =>
      intro x hx
      have hxo : x ∈ orthant n := fun i => (hx i).le
      have e0 : (((0 + 1 : ℕ) : ℝ≥0) * τ) = τ := by simp
      rw [e0, hlV τ x hxo]
      exact ENNReal.ofReal_le_ofReal (hsup x hx)
    | succ m ih =>
      intro x hx
      have e : (((m + 1 + 1 : ℕ) : ℝ≥0) * τ) = ((m + 1 : ℕ) : ℝ≥0) * τ + τ := by push_cast; ring
      rw [e, lint_ck P X hker hCK hOO _ τ x hx _ hVm]
      refine le_trans ?_ (ih x hx)
      refine lintegral_mono_ae ?_
      have h1 : ∀ᵐ y ∂(trans P X (((m + 1 : ℕ) : ℝ≥0) * τ) x), y ∈ openOrthant n :=
        mem_ae_iff.2 (hOO _ x hx)
      filter_upwards [h1] with y hy
      have hyo : y ∈ orthant n := fun i => (hy i).le
      rw [hlV τ y hyo]
      exact ENNReal.ofReal_le_ofReal (hsup y hy)
  intro m x hx
  have hxo : x ∈ orthant n := fun i => (hx i).le
  have := key m x hx
  rw [hlV _ x hxo] at this
  exact (ENNReal.ofReal_le_ofReal_iff (hW0 x)).1 this

theorem one_add_pos {n : ℕ} (c : SDEState n) (hc : c ∈ openOrthant n) (x : SDEState n)
    (hx : x ∈ orthant n) : 1 ≤ 1 + ∑ i, c i * x i := by
  have : 0 ≤ ∑ i, c i * x i :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hc i).le (hx i))
  linarith

/-- The cap constant is positive once the weights on the face sum to at most one. -/
theorem CU_pos {n : ℕ} (c : SDEState n) (hc : c ∈ openOrthant n) (mu : Measure (SDEState n))
    (phat : Fin n → ℝ) (hph : ∀ i ∈ supp mu, 0 ≤ phat i) (hsum : ∑ i ∈ supp mu, phat i ≤ 1) :
    0 < CU c mu phat := by
  unfold CU
  set g : SDEState n → ℝ := fun x => (∏ i ∈ supp mu, x i ^ phat i) / (1 + ∑ i, c i * x i) with hg
  set o : SDEState n := WithLp.toLp 2 (fun _ => (1 : ℝ)) with ho_def
  have hoi : ∀ i, o i = 1 := fun i => by simp [o]
  have ho : o ∈ openOrthant n := fun i => by rw [hoi]; exact one_pos
  set L : ℝ := ∑ i, (c i)⁻¹ + 1 with hL
  have hL1 : 1 ≤ L := by
    have : 0 ≤ ∑ i, (c i)⁻¹ := Finset.sum_nonneg (fun i _ => (inv_pos.2 (hc i)).le)
    linarith
  have hbdd : BddAbove (g '' openOrthant n) := by
    refine ⟨L, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have hxo : x ∈ orthant n := fun i => (hx i).le
    set u := 1 + ∑ i, c i * x i with hu
    have hu1 : 1 ≤ u := one_add_pos c hc x hxo
    have hu0 : 0 < u := by linarith
    have hxj : ∀ j, x j ≤ u * L := by
      intro j
      have h1 : c j * x j ≤ ∑ i, c i * x i :=
        Finset.single_le_sum (f := fun i => c i * x i)
          (fun i _ => mul_nonneg (hc i).le (hxo i)) (Finset.mem_univ j)
      have h2 : (c j)⁻¹ ≤ L := by
        have : (c j)⁻¹ ≤ ∑ i, (c i)⁻¹ :=
          Finset.single_le_sum (f := fun i => (c i)⁻¹) (fun i _ => (inv_pos.2 (hc i)).le)
            (Finset.mem_univ j)
        linarith
      have h3 : x j = (c j)⁻¹ * (c j * x j) := by field_simp [(hc j).ne']
      rw [h3]
      calc (c j)⁻¹ * (c j * x j) ≤ L * u := by
            refine mul_le_mul h2 (by linarith) (mul_nonneg (hc j).le (hxo j)) (by linarith)
        _ = u * L := by ring
    have huL : 1 ≤ u * L := by nlinarith
    have hprod : ∏ i ∈ supp mu, x i ^ phat i ≤ ∏ i ∈ supp mu, (u * L) ^ phat i :=
      Finset.prod_le_prod (fun i _ => Real.rpow_nonneg (hxo i) _)
        (fun i hi => Real.rpow_le_rpow (hxo i) (hxj i) (hph i hi))
    have hpow : ∏ i ∈ supp mu, (u * L) ^ phat i = (u * L) ^ (∑ i ∈ supp mu, phat i) :=
      (Real.rpow_sum_of_pos (by linarith) _ _).symm
    have hle1 : (u * L) ^ (∑ i ∈ supp mu, phat i) ≤ u * L := by
      calc (u * L) ^ (∑ i ∈ supp mu, phat i) ≤ (u * L) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le huL hsum
        _ = u * L := Real.rpow_one _
    show (∏ i ∈ supp mu, x i ^ phat i) / u ≤ L
    rw [div_le_iff₀ hu0]
    calc ∏ i ∈ supp mu, x i ^ phat i ≤ u * L := hprod.trans (hpow ▸ hle1)
      _ = L * u := by ring
  have hgo : 0 < g o := by
    have h1 : 0 < ∏ i ∈ supp mu, o i ^ phat i :=
      Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (ho i) _)
    have h2 : 0 < 1 + ∑ i, c i * o i := by
      have := one_add_pos c hc o (fun i => (ho i).le); linarith
    exact div_pos h1 h2
  exact lt_of_lt_of_le hgo (le_csSup hbdd ⟨o, ho, rfl⟩)

theorem Ui_pos {n : ℕ} (c : SDEState n) (hc : c ∈ openOrthant n) (mu : Measure (SDEState n))
    (phat : Fin n → ℝ) (pcheck : ℝ) (i : Fin n) (x : SDEState n) (hx : x ∈ openOrthant n) :
    0 < Ui c mu phat pcheck i x := by
  unfold Ui
  have h1 := one_add_pos c hc x (fun j => (hx j).le)
  have h2 : 0 < ∏ j ∈ supp mu, x j ^ phat j :=
    Finset.prod_pos (fun j _ => Real.rpow_pos_of_pos (hx j) _)
  exact div_pos (mul_pos (by linarith) (Real.rpow_pos_of_pos (hx i) _)) h2

theorem Utheta_nonneg {n : ℕ} (c : SDEState n) (hc : c ∈ openOrthant n)
    (mu : Measure (SDEState n)) (phat : Fin n → ℝ) (pcheck θ : ℝ) (x : SDEState n)
    (hx : x ∈ openOrthant n) : 0 ≤ Utheta c mu phat pcheck θ x :=
  Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (Ui_pos c hc mu phat pcheck i x hx).le _)

/-- Explicit lower bound of `U_θ` on a box `[a,b]ⁿ` (`0 < a`, `1 ≤ b`) via one missing species. -/
theorem Utheta_lower {n : ℕ} (c : SDEState n) (hc : c ∈ openOrthant n)
    (mu : Measure (SDEState n)) (phat : Fin n → ℝ) (hph : ∀ i ∈ supp mu, 0 ≤ phat i)
    (pcheck θ : ℝ) (hpc : 0 ≤ pcheck) (hθ : 0 ≤ θ) (i0 : Fin n) (hi0 : i0 ∉ supp mu)
    (a b : ℝ) (ha : 0 < a) (y : SDEState n) (hy : ∀ k, a ≤ y k ∧ y k ≤ b) :
    (a ^ pcheck / ∏ j ∈ supp mu, b ^ phat j) ^ θ ≤ Utheta c mu phat pcheck θ y := by
  have hyo : y ∈ openOrthant n := fun k => lt_of_lt_of_le ha (hy k).1
  have hterm : Ui c mu phat pcheck i0 y ^ θ ≤ Utheta c mu phat pcheck θ y := by
    unfold Utheta
    exact Finset.single_le_sum (f := fun i => Ui c mu phat pcheck i y ^ θ)
      (fun i _ => Real.rpow_nonneg (Ui_pos c hc mu phat pcheck i y hyo).le _)
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi0⟩)
  refine le_trans ?_ hterm
  have hden : 0 < ∏ j ∈ supp mu, y j ^ phat j :=
    Finset.prod_pos (fun j _ => Real.rpow_pos_of_pos (hyo j) _)
  have hdle : ∏ j ∈ supp mu, y j ^ phat j ≤ ∏ j ∈ supp mu, b ^ phat j :=
    Finset.prod_le_prod (fun j _ => Real.rpow_nonneg (hyo j).le _)
      (fun j hj => Real.rpow_le_rpow (hyo j).le (hy j).2 (hph j hj))
  have hnum : a ^ pcheck ≤ (1 + ∑ j, c j * y j) * y i0 ^ pcheck := by
    have h1 := one_add_pos c hc y (fun j => (hyo j).le)
    have h2 : a ^ pcheck ≤ y i0 ^ pcheck := Real.rpow_le_rpow ha.le (hy i0).1 hpc
    have h3 : 0 ≤ y i0 ^ pcheck := Real.rpow_nonneg (hyo i0).le _
    nlinarith
  have hlb : a ^ pcheck / ∏ j ∈ supp mu, b ^ phat j ≤ Ui c mu phat pcheck i0 y := by
    unfold Ui
    exact div_le_div₀ (le_trans (Real.rpow_nonneg ha.le _) hnum) hnum hden hdle
  exact Real.rpow_le_rpow (div_nonneg (Real.rpow_nonneg ha.le _)
    (Finset.prod_nonneg (fun j _ => Real.rpow_nonneg (le_trans ha.le (hy j).1 |>.trans (hy j).2) _))) hlb hθ

end ExtinctT12

/-! Relay s3, glue part 2: continuity of `U_θ` at a boundary point, a nearby interior point,
the drop bound, and interior transience of every box (`transience_main`). -/
namespace ExtinctT12

open StochKolmogorov.Extinct EthierKurtz

theorem Utheta_measurable {n : ℕ} (c : SDEState n) (mu : Measure (SDEState n))
    (phat : Fin n → ℝ) (pcheck θ : ℝ) : Measurable (Utheta c mu phat pcheck θ) := by
  have hcoord : ∀ k, Measurable (fun y : SDEState n => y k) :=
    fun k => (PiLp.continuous_apply 2 _ k).measurable
  unfold Utheta Ui
  refine Finset.measurable_sum _ (fun i _ => ?_)
  refine Measurable.pow_const ?_ _
  refine Measurable.div ?_ ?_
  · exact (measurable_const.add (Finset.measurable_sum _
      (fun j _ => measurable_const.mul (hcoord j)))).mul ((hcoord i).pow_const _)
  · exact Finset.measurable_prod _ (fun j _ => (hcoord j).pow_const _)

theorem Utheta_small {n : ℕ} (c : SDEState n) (mu : Measure (SDEState n)) (phat : Fin n → ℝ)
    (pcheck θ : ℝ) (hpc : 0 < pcheck) (hθ : 0 < θ) (ε : ℝ) (hε : 0 < ε) :
    ∃ r0 : ℝ, 0 < r0 ∧ ∀ y : SDEState n,
      dist y (WithLp.toLp 2 (fun k => if k ∈ supp mu then (1:ℝ) else 0) : SDEState n) < r0 →
      Utheta c mu phat pcheck θ y < ε := by
  set z0 : SDEState n := WithLp.toLp 2 (fun k => if k ∈ supp mu then (1:ℝ) else 0) with hz0
  have hz0i : ∀ k, z0 k = if k ∈ supp mu then (1:ℝ) else 0 := fun k => by simp [z0]
  have hcoord : ∀ k, ContinuousAt (fun y : SDEState n => y k) z0 :=
    fun k => (PiLp.continuous_apply 2 _ k).continuousAt
  have hnum : Continuous (fun y : SDEState n => 1 + ∑ j, c j * y j) :=
    continuous_const.add (continuous_finset_sum _
      fun j _ => continuous_const.mul (PiLp.continuous_apply 2 _ j))
  have hden : ContinuousAt (fun y : SDEState n => ∏ j ∈ supp mu, y j ^ phat j) z0 :=
    tendsto_finset_prod (f := fun j (y : SDEState n) => y j ^ phat j) _ (fun j hj =>
      (hcoord j).rpow_const (Or.inl (by rw [hz0i, if_pos hj]; exact one_ne_zero)))
  have hden0 : (∏ j ∈ supp mu, z0 j ^ phat j) ≠ 0 := by
    rw [Finset.prod_eq_one (fun j hj => by rw [hz0i, if_pos hj, Real.one_rpow])]
    exact one_ne_zero
  have hU : ContinuousAt (fun y => Utheta c mu phat pcheck θ y) z0 := by
    unfold Utheta Ui
    exact tendsto_finset_sum _ (fun i _ =>
      (((hnum.continuousAt.mul ((hcoord i).rpow_const (Or.inr hpc.le))).div hden hden0).rpow_const
        (Or.inr hθ.le)))
  have hU0 : Utheta c mu phat pcheck θ z0 = 0 := by
    unfold Utheta
    refine Finset.sum_eq_zero (fun i hi => ?_)
    have hi' : i ∉ supp mu := (Finset.mem_filter.1 hi).2
    have : z0 i = 0 := by rw [hz0i, if_neg hi']
    unfold Ui
    rw [this, Real.zero_rpow hpc.ne', mul_zero, zero_div, Real.zero_rpow hθ.ne']
  obtain ⟨r0, hr0, h⟩ := Metric.continuousAt_iff.1 hU ε hε
  refine ⟨r0, hr0, fun y hy => ?_⟩
  have := h hy
  rw [hU0, Real.dist_eq, sub_zero] at this
  exact lt_of_le_of_lt (le_abs_self _) this

theorem near_point {n : ℕ} (S : Finset (Fin n)) (r0 : ℝ) (hr0 : 0 < r0) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧
      dist (WithLp.toLp 2 (fun k => if k ∈ S then (1:ℝ) else s) : SDEState n)
        (WithLp.toLp 2 (fun k => if k ∈ S then (1:ℝ) else 0) : SDEState n) < r0 / 2 := by
  have hn1 : (0:ℝ) < (n:ℝ) + 1 := by positivity
  set s : ℝ := min 1 (r0 / (2 * ((n:ℝ) + 1))) with hs
  have hs0 : 0 < s := lt_min one_pos (div_pos hr0 (by positivity))
  have hs1 : s ≤ 1 := min_le_left _ _
  have hs2 : s ≤ r0 / (2 * ((n:ℝ) + 1)) := min_le_right _ _
  refine ⟨s, hs0, hs1, ?_⟩
  rw [EuclideanSpace.dist_eq]
  have hsum : ∑ k : Fin n, dist ((WithLp.toLp 2 (fun k => if k ∈ S then (1:ℝ) else s) :
      SDEState n) k) ((WithLp.toLp 2 (fun k => if k ∈ S then (1:ℝ) else 0) : SDEState n) k) ^ 2
        ≤ (n:ℝ) * s ^ 2 := by
    calc _ ≤ ∑ _k : Fin n, s ^ 2 := Finset.sum_le_sum (fun k _ => by
            by_cases hk : k ∈ S <;> simp [hk, Real.dist_eq, abs_of_pos hs0] <;> positivity)
      _ = (n:ℝ) * s ^ 2 := by simp
  rw [Real.sqrt_lt' (by positivity)]
  have h3 : ((n:ℝ) + 1) * s ≤ r0 / 2 := by
    rw [le_div_iff₀ (by positivity)] at hs2
    linarith
  have h4 : (n:ℝ) * s ^ 2 < (((n:ℝ) + 1) * s) ^ 2 := by
    have := mul_pos (by positivity : (0:ℝ) < (n:ℝ) ^ 2 + n + 1) (pow_pos hs0 2)
    nlinarith [this]
  have h5 : (((n:ℝ) + 1) * s) ^ 2 ≤ (r0 / 2) ^ 2 := pow_le_pow_left₀ (by positivity) h3 2
  linarith

theorem coord_close {n : ℕ} (y z : SDEState n) (r : ℝ) (h : dist y z < r) (k : Fin n) :
    z k - r < y k ∧ y k < z k + r := by
  have h1 := PiLp.norm_apply_le (y - z) k
  rw [PiLp.sub_apply, Real.norm_eq_abs, ← dist_eq_norm] at h1
  have h2 := abs_lt.1 (lt_of_le_of_lt h1 h)
  constructor <;> linarith [h2.1, h2.2]

theorem drop_bound {n : ℕ} (ν : Measure (SDEState n)) [IsProbabilityMeasure ν]
    (W : SDEState n → ℝ) (hWm : Measurable W) (ς : ℝ) (hW0 : ∀ x, 0 ≤ W x)
    (hWς : ∀ x, W x ≤ ς) (Bl : Set (SDEState n)) (hBlm : MeasurableSet Bl)
    (hBl : ∀ z ∈ Bl, W z ≤ ς / 2) :
    ∫ z, W z ∂ν ≤ ς - ς / 2 * (ν Bl).toReal := by
  have hI1 : Integrable W ν := (integrable_const ς).mono' hWm.aestronglyMeasurable
    (ae_of_all _ fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (hW0 z)]; exact hWς z)
  have hI2 : Integrable (fun z => ς / 2 * Bl.indicator (fun _ => (1:ℝ)) z) ν :=
    ((integrable_const (1:ℝ)).indicator hBlm).const_mul (ς / 2)
  have hpt : ∀ z, W z ≤ ς - ς / 2 * Bl.indicator (fun _ => (1:ℝ)) z := by
    intro z
    by_cases hz : z ∈ Bl
    · rw [Set.indicator_of_mem hz]; have := hBl z hz; linarith
    · rw [Set.indicator_of_notMem hz]; have := hWς z; linarith
  calc ∫ z, W z ∂ν ≤ ∫ z, (ς - ς / 2 * Bl.indicator (fun _ => (1:ℝ)) z) ∂ν :=
        integral_mono hI1 ((integrable_const ς).sub hI2) hpt
    _ = ς - ς / 2 * (ν Bl).toReal := by
        rw [integral_sub (integrable_const ς) hI2, integral_const, integral_const_mul,
          integral_indicator hBlm, setIntegral_const]
        simp [Measure.real]

end ExtinctT12

namespace ExtinctT12

open StochKolmogorov.Extinct EthierKurtz

/-- Interior transience of every box `[η, R]ⁿ`, from the capped Lyapunov function `Ũ_θ`
(one-step superharmonic for every smaller cap level) and box-to-ball accessibility. -/
theorem transience_main {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hXm : ∀ x ∈ orthant n, ∀ t, Measurable (X x t))
    (hker : ∀ t : ℝ≥0, ∃ κ : Kernel (SDEState n) (SDEState n), IsMarkovKernel κ ∧
        ∀ x ∈ orthant n, κ x = trans P X t x)
    (hCK : ∀ (s t : ℝ≥0) (x : SDEState n), x ∈ orthant n → ∀ A : Set (SDEState n),
        MeasurableSet A → trans P X (s + t) x A = ∫⁻ y, trans P X t y A ∂(trans P X s x))
    (hOO : ∀ (t : ℝ≥0) (x : SDEState n), x ∈ openOrthant n →
        trans P X t x (openOrthant n)ᶜ = 0)
    (hcore : ∀ α β : ℝ, 0 < α → α ≤ β → ∀ z : SDEState n, (∀ l, α ≤ z l ∧ z l ≤ β) →
      ∀ r : ℝ, 0 < r → ∃ T₀ : ℝ≥0, 0 < T₀ ∧ ∃ p : ℝ, 0 < p ∧ ∀ T : ℝ≥0, T₀ / 2 ≤ T → T ≤ T₀ →
        ∀ y : SDEState n, (∀ l, α ≤ y l ∧ y l ≤ β) → p ≤ (trans P X T y (Metric.ball z r)).toReal)
    (c : SDEState n) (hc : c ∈ openOrthant n) (mu : Measure (SDEState n))
    (i0 : Fin n) (hi0 : i0 ∉ supp mu)
    (phat : Fin n → ℝ) (hph : ∀ i ∈ supp mu, 0 ≤ phat i) (hsum : ∑ i ∈ supp mu, phat i ≤ 1)
    (pcheck θ : ℝ) (hpc : 0 < pcheck) (hθ : 0 < θ) (τ : ℝ≥0) (hτ : 0 < τ)
    (δe : ℝ) (hδe : 0 < δe)
    (hone : ∀ δ' : ℝ, 0 < δ' → δ' ≤ δe → ∀ x ∈ openOrthant n,
      ∫ ω, Utilde c mu phat pcheck θ δ' (X x τ ω) ∂P ≤ Utilde c mu phat pcheck θ δ' x)
    (η R : ℝ) (hη : 0 < η) :
    ∀ x ∈ openOrthant n, Tendsto (fun t : ℝ≥0 =>
      (trans P X t x {z : SDEState n | ∀ i, η ≤ z i ∧ z i ≤ R}).toReal) atTop (𝓝 0) := by
  classical
  intro x hx
  by_cases hηR : R < η
  · have hKe : {z : SDEState n | ∀ i, η ≤ z i ∧ z i ≤ R} = ∅ := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      have := h ⟨0, hn⟩
      linarith [this.1, this.2]
    simp [hKe]
  have hηR' : η ≤ R := le_of_not_gt hηR
  have hprob : ∀ (t : ℝ≥0) (y : SDEState n), y ∈ orthant n →
      IsProbabilityMeasure (trans P X t y) :=
    fun t y hy => Measure.isProbabilityMeasure_map (hXm y hy t).aemeasurable
  have hcoordm : ∀ k, Measurable (fun y : SDEState n => y k) :=
    fun k => (PiLp.continuous_apply 2 _ k).measurable
  have hboxm : ∀ a b : ℝ, MeasurableSet {z : SDEState n | ∀ i, a ≤ z i ∧ z i ≤ b} := by
    intro a b
    have : {z : SDEState n | ∀ i, a ≤ z i ∧ z i ≤ b} =
        ⋂ i, (fun y : SDEState n => y i) ⁻¹' Set.Icc a b := by
      ext z; simp
    rw [this]
    exact MeasurableSet.iInter (fun i => hcoordm i measurableSet_Icc)
  have hOm : MeasurableSet (openOrthant n) := by
    have : openOrthant n = ⋂ i, (fun y : SDEState n => y i) ⁻¹' Set.Ioi 0 := by
      ext z; simp [openOrthant]
    rw [this]
    exact MeasurableSet.iInter (fun i => hcoordm i measurableSet_Ioi)
  have haeO : ∀ t : ℝ≥0, ∀ y ∈ openOrthant n, ∀ᵐ ω ∂P, X y t ω ∈ openOrthant n := by
    intro t y hy
    have hyo : y ∈ orthant n := fun i => (hy i).le
    have h := hOO t y hy
    rw [StochKolmogorov.Extinct.trans, Measure.map_apply (hXm y hyo t) hOm.compl] at h
    exact ae_iff.2 h
  -- the boxes K ⊆ K'
  set K : Set (SDEState n) := {z : SDEState n | ∀ i, η ≤ z i ∧ z i ≤ R} with hK
  set K' : Set (SDEState n) := {z : SDEState n | ∀ i, η / 2 ≤ z i ∧ z i ≤ R + 1} with hK'
  have hK'O : ∀ y ∈ K', y ∈ openOrthant n := fun y hy i => by
    have := (hy i).1; linarith
  -- lower bound of U_θ on K' and the cap level δ'
  set m0 : ℝ := ((η / 2) ^ pcheck / ∏ j ∈ supp mu, (R + 1) ^ phat j) ^ θ with hm0
  have hR1 : 0 < R + 1 := by linarith
  have hm0pos : 0 < m0 := Real.rpow_pos_of_pos (div_pos (Real.rpow_pos_of_pos (by linarith) _)
    (Finset.prod_pos (fun j _ => Real.rpow_pos_of_pos hR1 _))) _
  have hlowK' : ∀ y ∈ K', m0 ≤ Utheta c mu phat pcheck θ y := fun y hy =>
    Utheta_lower c hc mu phat hph pcheck θ hpc.le hθ.le i0 hi0 (η / 2) (R + 1) (by linarith) y hy
  have hCU := CU_pos c hc mu phat hph hsum
  set A : ℝ := m0 * (CU c mu phat) ^ θ with hA
  have hApos : 0 < A := mul_pos hm0pos (Real.rpow_pos_of_pos hCU _)
  have hpθ : 0 < pcheck * θ := mul_pos hpc hθ
  set δ' : ℝ := min δe (A ^ (1 / (pcheck * θ))) with hδ'
  have hδ'pos : 0 < δ' := lt_min hδe (Real.rpow_pos_of_pos hApos _)
  have hδ'le : δ' ≤ δe := min_le_left _ _
  set ς : ℝ := varsigma c mu phat pcheck θ δ' with hς
  have hςpos : 0 < ς := div_pos (Real.rpow_pos_of_pos hδ'pos _) (Real.rpow_pos_of_pos hCU _)
  have hςm0 : ς ≤ m0 := by
    have h1 : δ' ^ (pcheck * θ) ≤ A := by
      calc δ' ^ (pcheck * θ) ≤ (A ^ (1 / (pcheck * θ))) ^ (pcheck * θ) :=
            Real.rpow_le_rpow hδ'pos.le (min_le_right _ _) hpθ.le
        _ = A := by
            rw [← Real.rpow_mul hApos.le, one_div, inv_mul_cancel₀ hpθ.ne', Real.rpow_one]
    show δ' ^ (pcheck * θ) / (CU c mu phat) ^ θ ≤ m0
    rw [div_le_iff₀ (Real.rpow_pos_of_pos hCU _)]
    exact h1
  -- the bounded superharmonic function
  obtain ⟨W, hWdef⟩ : ∃ W : SDEState n → ℝ, W = fun y =>
      if y ∈ openOrthant n then Utilde c mu phat pcheck θ δ' y else ς := ⟨_, rfl⟩
  have hWm : Measurable W := by
    rw [hWdef]
    exact Measurable.ite hOm (measurable_const.min (Utheta_measurable c mu phat pcheck θ))
      measurable_const
  have hW0 : ∀ y, 0 ≤ W y := by
    intro y
    rw [hWdef]
    dsimp only
    split_ifs with hy
    · exact le_min hςpos.le (Utheta_nonneg c hc mu phat pcheck θ y hy)
    · exact hςpos.le
  have hWς : ∀ y, W y ≤ ς := by
    intro y
    rw [hWdef]
    dsimp only
    split_ifs with hy
    · exact min_le_left _ _
    · exact le_rfl
  have hWK' : ∀ y ∈ K', W y = ς := by
    intro y hy
    rw [hWdef]
    dsimp only
    rw [if_pos (hK'O y hy)]
    exact min_eq_left (hςm0.trans (hlowK' y hy))
  have hsup : ∀ y ∈ openOrthant n, ∫ ω, W (X y τ ω) ∂P ≤ W y := by
    intro y hy
    have e : ∫ ω, W (X y τ ω) ∂P = ∫ ω, Utilde c mu phat pcheck θ δ' (X y τ ω) ∂P :=
      integral_congr_ae ((haeO τ y hy).mono fun ω hω => by simp only [hWdef, if_pos hω])
    rw [e]
    have e2 : W y = Utilde c mu phat pcheck θ δ' y := by simp only [hWdef, if_pos hy]
    rw [e2]
    exact hone δ' hδ'pos hδ'le y hy
  -- a small ball where W ≤ ς/2, inside a big box Bx ⊇ K'
  obtain ⟨r0, hr0, hsmall⟩ := Utheta_small c mu phat pcheck θ hpc hθ (ς / 2) (by linarith)
  obtain ⟨s, hs0, hs1, hdist⟩ := near_point (supp mu) r0 hr0
  set zs : SDEState n := WithLp.toLp 2 (fun k => if k ∈ supp mu then (1:ℝ) else s) with hzs
  have hzsi : ∀ k, zs k = if k ∈ supp mu then (1:ℝ) else s := fun k => by simp [zs]
  have hzs_lo : ∀ k, s ≤ zs k := fun k => by rw [hzsi]; split_ifs <;> linarith
  have hzs_hi : ∀ k, zs k ≤ 1 := fun k => by rw [hzsi]; split_ifs <;> linarith
  set rs : ℝ := min (r0 / 2) (s / 2) with hrs
  have hrs0 : 0 < rs := lt_min (by linarith) (by linarith)
  set a : ℝ := min (η / 2) (s / 2) with ha
  have ha0 : 0 < a := lt_min (by linarith) (by linarith)
  set b : ℝ := max (R + 1) 2 with hb
  set Bx : Set (SDEState n) := {z : SDEState n | ∀ i, a ≤ z i ∧ z i ≤ b} with hBx
  set Bl : Set (SDEState n) := Metric.ball zs rs with hBl
  have hBlBx : Bl ⊆ Bx := by
    intro y hy k
    have h := coord_close y zs rs hy k
    have h1 : rs ≤ s / 2 := min_le_right _ _
    have h2 : a ≤ s / 2 := min_le_right _ _
    have h3 : (2:ℝ) ≤ b := le_max_right _ _
    constructor <;> linarith [hzs_lo k, hzs_hi k, h.1, h.2]
  have hBxO : ∀ y ∈ Bx, y ∈ openOrthant n := fun y hy i => lt_of_lt_of_le ha0 (hy i).1
  have hBxo : Bx ⊆ orthant n := fun y hy i => (hBxO y hy i).le
  have hK'Bx : K' ⊆ Bx := by
    intro y hy k
    have h1 : a ≤ η / 2 := min_le_left _ _
    have h2 : R + 1 ≤ b := le_max_left _ _
    exact ⟨h1.trans (hy k).1, (hy k).2.trans h2⟩
  have hWBl : ∀ y ∈ Bl, W y ≤ ς / 2 := by
    intro y hy
    have hyO := hBxO y (hBlBx hy)
    have hd : dist y (WithLp.toLp 2 (fun k => if k ∈ supp mu then (1:ℝ) else 0) : SDEState n)
        < r0 := by
      have h1 : dist y zs < r0 / 2 := lt_of_lt_of_le hy (min_le_left _ _)
      linarith [dist_triangle y zs
        (WithLp.toLp 2 (fun k => if k ∈ supp mu then (1:ℝ) else 0) : SDEState n)]
    have := hsmall y hd
    rw [hWdef]
    dsimp only
    rw [if_pos hyO]
    exact (min_le_right _ _).trans this.le
  have hzsBx : ∀ l, a ≤ zs l ∧ zs l ≤ b := fun l => by
    have h2 : a ≤ s / 2 := min_le_right _ _
    have h3 : (2:ℝ) ≤ b := le_max_right _ _
    constructor <;> linarith [hzs_lo l, hzs_hi l]
  have hab : a ≤ b := by
    have h2 : a ≤ s / 2 := min_le_right _ _
    have h3 : (2:ℝ) ≤ b := le_max_right _ _
    linarith
  obtain ⟨T0, hT0, p0, hp0, hwin0⟩ := hcore a b ha0 hab zs hzsBx rs hrs0
  -- the time step τ' = (m+1)τ ≥ T0/2
  set m : ℕ := ⌈(T0 : ℝ) / (2 * τ)⌉₊ with hm
  set τ' : ℝ≥0 := ((m + 1 : ℕ) : ℝ≥0) * τ with hτ'
  have hτR : (0 : ℝ) < τ := NNReal.coe_pos.2 hτ
  have hτ'ge : T0 / 2 ≤ τ' := by
    rw [← NNReal.coe_le_coe]
    have h1 : (T0 : ℝ) / (2 * τ) ≤ m := Nat.le_ceil _
    have h2 : (T0 : ℝ) / 2 = (T0 : ℝ) / (2 * τ) * τ := by field_simp
    have h3 : ((τ' : ℝ≥0) : ℝ) = ((m : ℝ) + 1) * τ := by rw [hτ']; push_cast; ring
    rw [h3, NNReal.coe_div, NNReal.coe_ofNat, h2]
    have := mul_le_mul_of_nonneg_right h1 hτR.le
    nlinarith
  have hτ'pos : 0 < τ' := mul_pos (Nat.cast_pos.2 (Nat.succ_pos m)) hτ
  obtain ⟨q, hq, hqB⟩ := fixed_time_window P X hXm hCK Bx Bl hBlBx Metric.isOpen_ball.measurableSet
    hBxo T0 hT0 p0 hp0 (fun T h1 h2 y hy => hwin0 T h1 h2 y hy) τ' hτ'ge
  have hdec : ∀ y ∈ K', ∫ ω, W (X y τ' ω) ∂P ≤ ς - ς / 2 * q := by
    intro y hy
    have hyo : y ∈ orthant n := hBxo (hK'Bx hy)
    haveI := hprob τ' y hyo
    have hi : ∫ ω, W (X y τ' ω) ∂P = ∫ z, W z ∂(trans P X τ' y) := by
      rw [StochKolmogorov.Extinct.trans,
        integral_map (hXm y hyo τ').aemeasurable hWm.aestronglyMeasurable]
    rw [hi]
    refine le_trans (drop_bound _ W hWm ς hW0 hWς Bl Metric.isOpen_ball.measurableSet hWBl) ?_
    have := hqB y (hK'Bx hy)
    have : ς / 2 * q ≤ ς / 2 * (trans P X τ' y Bl).toReal :=
      mul_le_mul_of_nonneg_left this (by linarith)
    linarith
  -- the window K → K'
  set z1 : SDEState n := WithLp.toLp 2 (fun _ => η) with hz1
  have hz1i : ∀ k, z1 k = η := fun k => by simp [z1]
  set r1 : ℝ := min (η / 2) 1 with hr1
  have hr10 : 0 < r1 := lt_min (by linarith) one_pos
  obtain ⟨T1, hT1, p1, hp1, hwin1⟩ := hcore η R hη hηR' z1
    (fun l => by rw [hz1i]; exact ⟨le_rfl, hηR'⟩) r1 hr10
  have hball1 : Metric.ball z1 r1 ⊆ K' := by
    intro y hy k
    have h := coord_close y z1 r1 hy k
    rw [hz1i] at h
    have h1 : r1 ≤ η / 2 := min_le_left _ _
    have h2 : r1 ≤ 1 := min_le_right _ _
    constructor <;> linarith [h.1, h.2]
  have hwin : ∃ s₁ s₂ : ℝ≥0, s₁ < s₂ ∧ ∃ p : ℝ, 0 < p ∧ ∀ y ∈ K, ∀ s : ℝ≥0, s₁ ≤ s → s ≤ s₂ →
      p ≤ (trans P X s y K').toReal := by
    refine ⟨T1 / 2, T1, ?_, p1, hp1, fun y hy t h1 h2 => ?_⟩
    · rw [← NNReal.coe_lt_coe, NNReal.coe_div, NNReal.coe_ofNat]
      linarith [NNReal.coe_pos.2 hT1]
    · have hyo : y ∈ orthant n := fun i => le_trans hη.le (hy i).1
      haveI := hprob t y hyo
      exact (hwin1 t h1 h2 y hy).trans
        (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hball1))
  exact transience_core P X hXm hker hCK hOO W hWm ς hW0 hWς τ' hτ'pos
    (sup_iterate P X hXm hker hCK hOO W hWm ς hW0 hWς τ hsup m) K K' (hboxm η R)
    (hboxm (η / 2) (R + 1)) hWK' (ς / 2 * q) (by positivity) hdec hwin x hx

end ExtinctT12

namespace ExtinctT12

open EthierKurtz

/-- The same coefficients, read in the `Persist` copy of the model. -/
def toP {n : ℕ} (C : StochKolmogorov.Extinct.Coeffs n) : StochKolmogorov.Persist.Coeffs n :=
  ⟨C.f, C.g, C.Γ⟩

open StochKolmogorov.Extinct in
theorem box_measurable {n : ℕ} (a b : ℝ) :
    MeasurableSet {z : SDEState n | ∀ i, a ≤ z i ∧ z i ≤ b} := by
  have hcoordm : ∀ k, Measurable (fun y : SDEState n => y k) :=
    fun k => (PiLp.continuous_apply 2 _ k).measurable
  have : {z : SDEState n | ∀ i, a ≤ z i ∧ z i ≤ b} =
      ⋂ i, (fun y : SDEState n => y i) ⁻¹' Set.Icc a b := by
    ext z; simp
  rw [this]
  exact MeasurableSet.iInter (fun i => hcoordm i measurableSet_Icc)

open StochKolmogorov.Extinct in
/-- Assembly: Theorem 1.2 (5.5) from the sibling estimates of §5, the Markov structure,
the uniform moment bound and box-to-ball accessibility (`hcore`). -/
theorem assembled {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (hX : IsSolutionFamily P C B X)
    (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (mu : Measure (SDEState n)) (h13 : Assumption13 P C X mu)
    (δ₀ : ℝ) (hδ₀ : IsDelta0 C γb δ₀)
    (hcore : ∀ α β : ℝ, 0 < α → α ≤ β → ∀ z : SDEState n, (∀ l, α ≤ z l ∧ z l ≤ β) →
      ∀ r : ℝ, 0 < r → ∃ T₀ : ℝ≥0, 0 < T₀ ∧ ∃ p : ℝ, 0 < p ∧ ∀ T : ℝ≥0, T₀ / 2 ≤ T → T ≤ T₀ →
        ∀ y : SDEState n, (∀ l, α ≤ y l ∧ y l ≤ β) →
          p ≤ (trans P X T y (Metric.ball z r)).toReal) :
    ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ x ∈ openOrthant n,
      (∀ t : ℝ≥0, Integrable (fun ω => (⨅ i : Fin n, X x t ω i) ^ δ) P) ∧
        Tendsto (fun t : ℝ≥0 => ∫ ω, (⨅ i : Fin n, X x t ω i) ^ δ ∂P)
          atTop (𝓝 0) := by
  intro δ hδ hδδ₀ x hx
  haveI : IsProbabilityMeasure P := hX.1
  have hc : c ∈ openOrthant n := hA.2.2.1
  have hγ : 0 < γb := hA.2.2.2.1
  have hxo : x ∈ orthant n := fun i => (hx i).le
  have hXm : ∀ y ∈ orthant n, ∀ t, Measurable (X y t) := fun y hy t => (hX.2.2 y hy).1 t
  have hcoordm : ∀ k, Measurable (fun y : SDEState n => y k) :=
    fun k => (PiLp.continuous_apply 2 _ k).measurable
  -- Markov structure (Persist copy of the model)
  obtain ⟨hker, hCK, hOrth, hOO⟩ :=
    StochKolmogorov.Persist.markov_property P (toP C) B X hX c γb hA
  -- closed faces are invariant (Lemma 3.1, face part)
  have hface : ∀ t : ℝ≥0, ∀ y ∈ orthant n, ∀ i : Fin n, y i = 0 →
      trans P X t y {z : SDEState n | z i = 0}ᶜ = 0 := by
    intro t y hy i hyi
    have h31 := (lemma_3_1 hn P C B X hX c γb hA δ₀ hδ₀).2.1
      (Finset.univ.filter (fun j => 0 < y j)) y hy (fun j => by simp)
    have hi : i ∉ Finset.univ.filter (fun j => 0 < y j) := by simp [hyi]
    have hae : ∀ᵐ ω ∂P, X y t ω i = 0 := h31.mono fun ω hω => (hω t).2 i hi
    have hm : MeasurableSet {z : SDEState n | z i = 0} := hcoordm i (measurableSet_singleton 0)
    rw [StochKolmogorov.Extinct.trans, Measure.map_apply (hXm y hy t) hm.compl]
    exact ae_iff.1 hae
  have hsupp := bdryErgodic_supp_ne_univ P X hker hface mu h13.1
  obtain ⟨i0, hi0⟩ : ∃ i0, i0 ∉ supp mu := by
    by_contra h
    push_neg at h
    exact hsupp (Finset.eq_univ_iff_forall.2 h)
  -- the constants of §5
  obtain ⟨phat, hphat1, hphat2, pcheck, hpc0, hpcδ, ρe, hρe, h52⟩ :=
    inequalities_5_1_5_2 hn P C B X hX c γb hA mu h13 δ₀ hδ₀
  have hA' := hA
  obtain ⟨-, -, -, -, ε, hε, R0, hR0⟩ := hA'
  set M : ℝ := max R0 1 with hMdef
  have hM : IsRadiusM C c γb M := ⟨lt_of_lt_of_le one_pos (le_max_right _ _),
    fun y hy hMy => by have := hR0 y hy ((le_max_left _ _).trans hMy); linarith⟩
  obtain ⟨ne, hne'⟩ := exists_nat_gt (max (Hconst C c γb δ₀ / γb + 1) 1)
  have hne1 : (1 : ℝ) < ne := lt_of_le_of_lt (le_max_right _ _) hne'
  have hne : Hconst C c γb δ₀ < γb * ((ne : ℝ) - 1) := by
    have h1 : Hconst C c γb δ₀ / γb < (ne : ℝ) - 1 := by
      have := lt_of_le_of_lt (le_max_left _ _) hne'; linarith
    have h2 := (div_lt_iff₀ hγ).1 h1
    linarith [mul_comm ((ne : ℝ) - 1) γb]
  obtain ⟨Te, hTe, δe, hδe, h53⟩ := lemma_5_2 hn P C B X hX c γb hA mu h13 M hM δ₀ hδ₀ phat
    ⟨hphat1, hphat2⟩ pcheck ⟨hpc0, hpcδ⟩ ρe hρe h52 ne hne
  obtain ⟨θ, hθ0, hθδ, hcontract⟩ := proposition_5_1 hn P C B X hX c γb hA mu h13 M hM δ₀ hδ₀
    phat ⟨hphat1, hphat2⟩ pcheck ⟨hpc0, hpcδ⟩ ρe hρe ne hne Te δe hTe hδe h53
  set τ : ℝ≥0 := ((ne : ℝ) * Te).toNNReal with hτdef
  have hτ : 0 < τ := Real.toNNReal_pos.2 (mul_pos (by linarith) hTe)
  have hone : ∀ δ' : ℝ, 0 < δ' → δ' ≤ δe → ∀ y ∈ openOrthant n,
      ∫ ω, Utilde c mu phat pcheck θ δ' (X y τ ω) ∂P ≤ Utilde c mu phat pcheck θ δ' y := by
    intro δ' h1 h2 y hy
    exact (one_step_5_11_5_12 hn P C B X hX c γb hA mu h13
      M hM δ₀ hδ₀ phat ⟨hphat1, hphat2⟩ pcheck ⟨hpc0, hpcδ⟩ ρe hρe ne hne Te δ' θ hTe h1
      ⟨hθ0, hθδ⟩ (fun T hT z hz hzM hzδ => hcontract T hT z hz hzM
        (fun i hi => lt_of_lt_of_le (hzδ i hi) h2)) y hy).2
  have hδ₀1 : δ₀ < 1 := lt_of_lt_of_le hδ₀.2.1 (min_le_right _ _)
  have htr := transience_main hn P X hXm hker hCK hOO hcore c hc mu i0 hi0 phat
    (fun i hi => (hphat1 i hi).1.le) (hphat2.trans hδ₀1.le) pcheck θ hpc0 hθ0 τ hτ δe hδe hone
  -- the uniform δ₀-moment bound (Persist Lemma 3.2)
  have hδP : StochKolmogorov.Persist.IsDelta0 (toP C) γb δ₀ :=
    ⟨hδ₀.1, lt_of_lt_of_le hδ₀.2.1 (min_le_left _ _), hδ₀.2.2⟩
  obtain ⟨H₁, H₂, hH₁, -, hm1, -, -⟩ :=
    StochKolmogorov.Persist.lemma_3_2 hn P (toP C) B X hX c γb
      hA δ₀ hδP
  set u : ℝ := 1 + ∑ i, c i * x i with hu
  have hu0 : 0 ≤ u := by have := one_add_pos c hc x hxo; linarith
  have huδ : 0 ≤ u ^ δ₀ := Real.rpow_nonneg hu0 _
  have hmom : ∀ t : ℝ≥0, ∫⁻ ω, ENNReal.ofReal ((1 + ∑ i, c i * X x t ω i) ^ δ₀) ∂P
      ≤ ENNReal.ofReal (H₁ + u ^ δ₀) := by
    intro t
    rcases eq_or_ne t 0 with h0 | hne0
    · subst h0
      have hX0 : X x 0 =ᵐ[P] (fun _ => x) := (hX.2.2 x hxo).2.2.2.1
      have e : ∫⁻ ω, ENNReal.ofReal ((1 + ∑ i, c i * X x 0 ω i) ^ δ₀) ∂P
          = ∫⁻ _ω, ENNReal.ofReal (u ^ δ₀) ∂P :=
        lintegral_congr_ae (hX0.mono fun ω hω => by dsimp only at hω ⊢; rw [hω])
      rw [e, lintegral_const, measure_univ, mul_one]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    · have hpos : 0 < t := pos_iff_ne_zero.2 hne0
      refine (hm1 x hxo t hpos).trans (ENNReal.ofReal_le_ofReal ?_)
      have hexp : Real.exp (-δ₀ * γb * t) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : 0 ≤ δ₀ * γb * (t : ℝ) := mul_nonneg (mul_nonneg hδ₀.1.le hγ.le) t.2
        linarith
      have := mul_le_mul_of_nonneg_left hexp huδ
      linarith
  have hOrthm : MeasurableSet (orthant n) := by
    have : orthant n = ⋂ i, (fun y : SDEState n => y i) ⁻¹' Set.Ici 0 := by
      ext z; simp [orthant]
    rw [this]
    exact MeasurableSet.iInter (fun i => hcoordm i measurableSet_Ici)
  have horth : ∀ t, ∀ᵐ ω ∂P, X x t ω ∈ orthant n := by
    intro t
    have h : StochKolmogorov.Extinct.trans P X t x (orthant n)ᶜ = 0 := hOrth t x hxo
    rw [StochKolmogorov.Extinct.trans, Measure.map_apply (hXm x hxo t) hOrthm.compl] at h
    exact ae_iff.2 h
  have htr' : ∀ η R : ℝ, 0 < η → Tendsto (fun t : ℝ≥0 =>
      (P ((X x t) ⁻¹' {z : SDEState n | ∀ i, η ≤ z i ∧ z i ≤ R})).toReal) atTop (𝓝 0) := by
    intro η R hη
    refine (htr η R hη x hx).congr (fun t => ?_)
    rw [StochKolmogorov.Extinct.trans, Measure.map_apply (hXm x hxo t) (box_measurable η R)]
  exact moment_limit_core hn P (X x) (hXm x hxo) horth c hc δ₀ (H₁ + u ^ δ₀)
    (by linarith) hmom htr' δ hδ hδδ₀

end ExtinctT12


open MeasureTheory ProbabilityTheory Filter in
open scoped ENNReal NNReal Topology BigOperators in
open StochKolmogorov.Extinct EthierKurtz in
theorem solution {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (hX : IsSolutionFamily P C B X)
    (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (mu : Measure (SDEState n)) (h13 : Assumption13 P C X mu)
    (δ₀ : ℝ) (hδ₀ : IsDelta0 C γb δ₀) :
    ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ x ∈ openOrthant n,
      (∀ t : ℝ≥0, Integrable (fun ω => (⨅ i : Fin n, X x t ω i) ^ δ) P) ∧
        Tendsto (fun t : ℝ≥0 => ∫ ω, (⨅ i : Fin n, X x t ω i) ^ δ ∂P)
          atTop (𝓝 0) := by
  exact ExtinctT12.assembled hn P C B X hX c γb hA mu h13 δ₀ hδ₀
    (fun α β hα hαβ z hz r hr => box_ball_window P C B X hX c γb hA α β hα hαβ z hz r hr)
