-- Prove2me | solution 1 for SPOBounds.Margin.margin_generalization_bound
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-07T22:21:44.986+00:00
-- url     : https://prove2.me/submissions/be78e88b-4727-45c3-a870-3cfa938cbcd4

-- SPDX-License-Identifier: Apache-2.0
-- Complete proof of Prove2Me 149f2a0a-5027-4822-bd48-fae4061ebf39.
-- Reused accepted contributions are attributed beside their full proof bodies.
import Definitions.Def_SPOBounds_Margin_Degeneracy
import Definitions.Def_SPOBounds_Margin_Model
import Definitions.Def_SPOBounds_Margin_Rademacher
import Mathlib

set_option autoImplicit false


-- BEGIN MODULE AttributedSPO
section

section
-- Prove2me | solution 1 for SPOBounds.Margin.oracle_lipschitz_like
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T10:58:27.777958+00:00
-- url     : https://prove2.me/submissions/28031a28-cc1a-4c6d-a93e-72ede8ffcbac


set_option autoImplicit false

open SPOBounds.Margin in
theorem checked_oracle_lipschitz_like {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (S : Set E) (_hS : S.Nonempty) (_hSc : IsCompact S) (_hSv : Convex ℝ S) (_hSnt : S.Nontrivial)
    (w : StrongDual ℝ E → E) (hw : IsOracle S w)
    (μ : ℝ) (hμ : 0 < μ) (hstr : StrengthProperty S μ w)
    (c₁ c₂ : StrongDual ℝ E) :
    μ * min (nu S c₁) (nu S c₂) * ‖w c₁ - w c₂‖ ≤ ‖c₁ - c₂‖ := by
  have h1 := hstr c₁ (w c₂) (hw c₂).1
  have h2 := hstr c₂ (w c₁) (hw c₁).1
  have hn1 : 0 ≤ nu S c₁ := Metric.infDist_nonneg
  have hn2 : 0 ≤ nu S c₂ := Metric.infDist_nonneg
  set d := ‖w c₁ - w c₂‖ with hd
  have hd1 : ‖w c₂ - w c₁‖ = d := norm_sub_rev _ _
  rw [hd1] at h1
  have hcs : (c₁ - c₂) (w c₂ - w c₁) ≤ ‖c₁ - c₂‖ * d := by
    have := (c₁ - c₂).le_opNorm (w c₂ - w c₁)
    rw [hd1, Real.norm_eq_abs] at this
    exact le_trans (le_abs_self _) this
  have hsum : c₁ (w c₂ - w c₁) + c₂ (w c₁ - w c₂) = (c₁ - c₂) (w c₂ - w c₁) := by
    simp only [sub_apply, map_sub]
    ring
  have hmin : min (nu S c₁) (nu S c₂) ≤ (nu S c₁ + nu S c₂) / 2 := by
    have := min_le_left (nu S c₁) (nu S c₂)
    have := min_le_right (nu S c₁) (nu S c₂)
    linarith
  have hd0 : 0 ≤ d := norm_nonneg _
  have hm0 : 0 ≤ min (nu S c₁) (nu S c₂) := le_min hn1 hn2
  have key : μ * min (nu S c₁) (nu S c₂) * d * d ≤ ‖c₁ - c₂‖ * d := by
    have e1 : μ * min (nu S c₁) (nu S c₂) * d * d ≤ μ * ((nu S c₁ + nu S c₂) / 2) * d ^ 2 := by
      have : μ * min (nu S c₁) (nu S c₂) ≤ μ * ((nu S c₁ + nu S c₂) / 2) :=
        mul_le_mul_of_nonneg_left hmin hμ.le
      nlinarith [mul_nonneg hd0 hd0]
    nlinarith
  rcases hd0.eq_or_lt with h | h
  · rw [← h]; simp
  · exact le_of_mul_le_mul_right key h

end

section
-- Prove2me | solution 1 for SPOBounds.Margin.margin_loss_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T12:39:13.540865+00:00
-- url     : https://prove2.me/submissions/9a887562-f213-4cf4-a109-0f0535c8407b


set_option autoImplicit false

open SPOBounds.Margin in
theorem p71dfcbfc_oracle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (w : StrongDual ℝ E → E) (hw : IsOracle S w)
    (μ : ℝ) (hμ : 0 < μ) (hstr : StrengthProperty S μ w)
    (c₁ c₂ : StrongDual ℝ E) :
    μ * min (nu S c₁) (nu S c₂) * ‖w c₁ - w c₂‖ ≤ ‖c₁ - c₂‖ := by
  have h1 := hstr c₁ (w c₂) (hw c₂).1
  have h2 := hstr c₂ (w c₁) (hw c₁).1
  have hn1 : 0 ≤ nu S c₁ := Metric.infDist_nonneg
  have hn2 : 0 ≤ nu S c₂ := Metric.infDist_nonneg
  set d := ‖w c₁ - w c₂‖ with hd
  have hd1 : ‖w c₂ - w c₁‖ = d := norm_sub_rev _ _
  rw [hd1] at h1
  have hcs : (c₁ - c₂) (w c₂ - w c₁) ≤ ‖c₁ - c₂‖ * d := by
    have := (c₁ - c₂).le_opNorm (w c₂ - w c₁)
    rw [hd1, Real.norm_eq_abs] at this
    exact le_trans (le_abs_self _) this
  have hsum : c₁ (w c₂ - w c₁) + c₂ (w c₁ - w c₂) = (c₁ - c₂) (w c₂ - w c₁) := by
    simp only [sub_apply, map_sub]
    ring
  have hmin : min (nu S c₁) (nu S c₂) ≤ (nu S c₁ + nu S c₂) / 2 := by
    have := min_le_left (nu S c₁) (nu S c₂)
    have := min_le_right (nu S c₁) (nu S c₂)
    linarith
  have hd0 : 0 ≤ d := norm_nonneg _
  have hm0 : 0 ≤ min (nu S c₁) (nu S c₂) := le_min hn1 hn2
  have key : μ * min (nu S c₁) (nu S c₂) * d * d ≤ ‖c₁ - c₂‖ * d := by
    have e1 : μ * min (nu S c₁) (nu S c₂) * d * d ≤ μ * ((nu S c₁ + nu S c₂) / 2) * d ^ 2 := by
      have : μ * min (nu S c₁) (nu S c₂) ≤ μ * ((nu S c₁ + nu S c₂) / 2) :=
        mul_le_mul_of_nonneg_left hmin hμ.le
      nlinarith [mul_nonneg hd0 hd0]
    nlinarith
  rcases hd0.eq_or_lt with h | h
  · rw [← h]; simp
  · exact le_of_mul_le_mul_right key h

open SPOBounds.Margin in
theorem p71dfcbfc_rep {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (w : StrongDual ℝ E → E) (γ : ℝ) (hγ : 0 < γ) (chat c : StrongDual ℝ E) :
    marginLoss S w γ chat c =
      omega S c - min (nu S chat / γ) 1 * (omega S c - spoLoss w chat c) := by
  unfold marginLoss
  split_ifs with h
  · have : 1 ≤ nu S chat / γ := by rw [le_div_iff₀ hγ]; linarith
    rw [min_eq_right this]; ring
  · have : nu S chat / γ ≤ 1 := by rw [div_le_iff₀ hγ]; linarith
    rw [min_eq_left this]; ring

open SPOBounds.Margin in
theorem p71dfcbfc_bounds {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (hSc : IsCompact S) (w : StrongDual ℝ E → E) (hw : IsOracle S w)
    (chat c : StrongDual ℝ E) :
    0 ≤ spoLoss w chat c ∧ spoLoss w chat c ≤ omega S c := by
  have hcont : Continuous (fun v => c v) := c.continuous
  have himg : IsCompact ((fun v => c v) '' S) := hSc.image hcont
  have hb1 : BddAbove ((fun v => c v) '' S) := himg.bddAbove
  have hb2 : BddBelow ((fun v => c v) '' S) := himg.bddBelow
  have m1 : c (w chat) ∈ (fun v => c v) '' S := ⟨w chat, (hw chat).1, rfl⟩
  have m2 : c (w c) ∈ (fun v => c v) '' S := ⟨w c, (hw c).1, rfl⟩
  have s1 := le_csSup hb1 m1
  have s2 := csInf_le hb2 m2
  unfold spoLoss omega
  refine ⟨?_, ?_⟩
  · have := (hw c).2 (w chat) (hw chat).1
    linarith
  · linarith

open SPOBounds.Margin in
theorem checked_margin_loss_lipschitz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (S : Set E) (_hS : S.Nonempty) (hSc : IsCompact S) (_hSv : Convex ℝ S) (_hSnt : S.Nontrivial)
    (w : StrongDual ℝ E → E) (hw : IsOracle S w)
    (μ : ℝ) (hμ : 0 < μ) (hstr : StrengthProperty S μ w)
    (γ : ℝ) (hγ : 0 < γ) (c c₁ c₂ : StrongDual ℝ E) :
    |marginLoss S w γ c₁ c - marginLoss S w γ c₂ c| ≤
      (‖c‖ + μ * omega S c) / (γ * μ) * ‖c₁ - c₂‖ := by
  -- general one-sided statement, then symmetrize
  have main : ∀ a b : StrongDual ℝ E,
      min (nu S a / γ) 1 ≤ min (nu S b / γ) 1 →
      |marginLoss S w γ a c - marginLoss S w γ b c| ≤
        (‖c‖ + μ * omega S c) / (γ * μ) * ‖a - b‖ := by
    intro a b hab
    rw [p71dfcbfc_rep S w γ hγ a c, p71dfcbfc_rep S w γ hγ b c]
    set t1 := min (nu S a / γ) 1 with ht1
    set t2 := min (nu S b / γ) 1 with ht2
    set Ω := omega S c with hΩ
    set D := ‖a - b‖ with hD
    obtain ⟨ha0, ha1⟩ := p71dfcbfc_bounds S hSc w hw a c
    obtain ⟨hb0, hb1⟩ := p71dfcbfc_bounds S hSc w hw b c
    have hna : 0 ≤ nu S a := Metric.infDist_nonneg
    have hnb : 0 ≤ nu S b := Metric.infDist_nonneg
    have hD0 : 0 ≤ D := norm_nonneg _
    -- nu is 1-Lipschitz
    have hnuL : |nu S a - nu S b| ≤ D := by
      have e1 : nu S a ≤ nu S b + dist a b := Metric.infDist_le_infDist_add_dist
      have e2 : nu S b ≤ nu S a + dist b a := Metric.infDist_le_infDist_add_dist
      rw [dist_eq_norm] at e1 e2
      rw [norm_sub_rev] at e2
      rw [abs_le]; constructor <;> linarith
    have htL : |t1 - t2| ≤ D / γ := by
      have := abs_min_sub_min_le_max (nu S a / γ) 1 (nu S b / γ) 1
      rw [sub_self, abs_zero] at this
      have e : |nu S a / γ - nu S b / γ| = |nu S a - nu S b| / γ := by
        rw [← sub_div, abs_div, abs_of_pos hγ]
      have e2 : |nu S a / γ - nu S b / γ| ≤ D / γ := by
        rw [e]; exact div_le_div_of_nonneg_right hnuL hγ.le
      have e3 : max |nu S a / γ - nu S b / γ| 0 ≤ D / γ :=
        max_le e2 (div_nonneg hD0 hγ.le)
      linarith
    have ht10 : 0 ≤ t1 := le_min (div_nonneg hna hγ.le) zero_le_one
    have ht1a : t1 ≤ nu S a / γ := min_le_left _ _
    have ht1b : t1 ≤ nu S b / γ := le_trans hab (min_le_left _ _)
    have ht1m : t1 * γ ≤ min (nu S a) (nu S b) := by
      rw [le_min_iff]; constructor
      · rw [← le_div_iff₀ hγ]; exact ht1a
      · rw [← le_div_iff₀ hγ]; exact ht1b
    -- oracle bound
    have hor := p71dfcbfc_oracle S w hw μ hμ hstr a b
    set d := ‖w a - w b‖ with hd
    have hd0 : 0 ≤ d := norm_nonneg _
    have hspo : |spoLoss w a c - spoLoss w b c| ≤ ‖c‖ * d := by
      unfold spoLoss
      have : c (w a) - c (w c) - (c (w b) - c (w c)) = c (w a - w b) := by
        rw [map_sub]; ring
      rw [this, ← Real.norm_eq_abs]
      exact c.le_opNorm _
    -- t1 * d ≤ D / (γ μ)
    have htd : t1 * d * (γ * μ) ≤ D := by
      have : μ * (t1 * γ) * d ≤ μ * min (nu S a) (nu S b) * d := by
        apply mul_le_mul_of_nonneg_right _ hd0
        exact mul_le_mul_of_nonneg_left ht1m hμ.le
      nlinarith
    -- the decomposition
    have hdec : Ω - t1 * (Ω - spoLoss w a c) - (Ω - t2 * (Ω - spoLoss w b c)) =
        (t2 - t1) * (Ω - spoLoss w b c) + t1 * (spoLoss w a c - spoLoss w b c) := by ring
    rw [hdec]
    have hg : |Ω - spoLoss w b c| ≤ Ω := by
      rw [abs_le]; constructor <;> linarith
    have hΩ0 : 0 ≤ Ω := by linarith
    have T1 : |(t2 - t1) * (Ω - spoLoss w b c)| ≤ D / γ * Ω := by
      rw [abs_mul, abs_sub_comm]
      exact mul_le_mul htL hg (abs_nonneg _) (div_nonneg hD0 hγ.le)
    have T2 : |t1 * (spoLoss w a c - spoLoss w b c)| ≤ t1 * (‖c‖ * d) := by
      rw [abs_mul, abs_of_nonneg ht10]
      exact mul_le_mul_of_nonneg_left hspo ht10
    have hγμ : 0 < γ * μ := mul_pos hγ hμ
    have T2' : t1 * (‖c‖ * d) ≤ ‖c‖ * D / (γ * μ) := by
      rw [le_div_iff₀ hγμ]
      have := mul_le_mul_of_nonneg_left htd (norm_nonneg c)
      nlinarith
    have hfin : D / γ * Ω + ‖c‖ * D / (γ * μ) = (‖c‖ + μ * Ω) / (γ * μ) * D := by
      field_simp
      ring
    calc |(t2 - t1) * (Ω - spoLoss w b c) + t1 * (spoLoss w a c - spoLoss w b c)|
        ≤ |(t2 - t1) * (Ω - spoLoss w b c)| + |t1 * (spoLoss w a c - spoLoss w b c)| :=
          abs_add_le _ _
      _ ≤ D / γ * Ω + ‖c‖ * D / (γ * μ) := by linarith
      _ = (‖c‖ + μ * Ω) / (γ * μ) * D := hfin
  rcases le_total (min (nu S c₁ / γ) 1) (min (nu S c₂ / γ) 1) with h | h
  · exact main c₁ c₂ h
  · rw [abs_sub_comm, norm_sub_rev]
    exact main c₂ c₁ h

end

section
-- Prove2me | solution 1 for UnderstandingML.mcdiarmid_inequality_pi
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-26T16:13:38.101916+00:00
-- url     : https://prove2.me/submissions/9902e733-32ce-4ede-9846-827c76b3fae5


open MeasureTheory ProbabilityTheory

namespace UnderstandingML.McDiarmidAux

variable {V : Type*} [MeasurableSpace V]

omit [MeasurableSpace V] in
/-- A function with bounded differences `cᵢ` varies by at most `∑ cᵢ`. -/
lemma abs_sub_le_sum {n : ℕ} (f : (Fin n → V) → ℝ) (c : Fin n → ℝ)
    (hc : ∀ (x : Fin n → V) (i : Fin n) (v : V), |f x - f (Function.update x i v)| ≤ c i)
    (x y : Fin n → V) : |f x - f y| ≤ ∑ i, c i := by
  classical
  let z : Finset (Fin n) → Fin n → V := fun s i ↦ if i ∈ s then y i else x i
  have key : ∀ s : Finset (Fin n), |f x - f (z s)| ≤ ∑ i ∈ s, c i := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [z]
    | insert a s ha ih =>
      have hz : z (insert a s) = Function.update (z s) a (y a) := by
        funext i
        by_cases hi : i = a
        · subst hi; simp [z]
        · simp [z, hi]
      rw [hz, Finset.sum_insert ha]
      calc |f x - f (Function.update (z s) a (y a))|
          ≤ |f x - f (z s)| + |f (z s) - f (Function.update (z s) a (y a))| := abs_sub_le _ _ _
        _ ≤ ∑ i ∈ s, c i + c a := add_le_add ih (hc _ _ _)
        _ = c a + ∑ i ∈ s, c i := add_comm _ _
  have : z Finset.univ = y := by funext i; simp [z]
  simpa [this] using key Finset.univ

lemma nonempty_of_prob (μ : Measure V) [IsProbabilityMeasure μ] : Nonempty V := by
  by_contra hV
  rw [not_nonempty_iff] at hV
  have := measure_univ (μ := μ)
  rw [Set.univ_eq_empty_iff.2 hV, measure_empty] at this
  exact zero_ne_one this

/-- **Hoeffding's lemma for a function of one variable with range at most `c`.** -/
lemma integral_exp_le_of_range {μ : Measure V} [IsProbabilityMeasure μ] (g : V → ℝ)
    (hg : Measurable g) (c : ℝ) (hc : ∀ z z', g z - g z' ≤ c) (t : ℝ) :
    ∫ z, Real.exp (t * (g z - ∫ z', g z' ∂μ)) ∂μ ≤ Real.exp (t ^ 2 * c ^ 2 / 8) := by
  have hne : Nonempty V := nonempty_of_prob μ
  set z0 : V := hne.some
  have hc0 : 0 ≤ c := by simpa using hc z0 z0
  have hbA : BddAbove (Set.range g) := ⟨g z0 + c, by
    rintro _ ⟨z, rfl⟩; have := hc z z0; linarith⟩
  have hbB : BddBelow (Set.range g) := ⟨g z0 - c, by
    rintro _ ⟨z, rfl⟩; have := hc z0 z; linarith⟩
  have hgi : Integrable g μ := by
    refine Integrable.of_bound hg.aestronglyMeasurable (|g z0| + c) ?_
    refine Filter.Eventually.of_forall (fun z ↦ ?_)
    rw [Real.norm_eq_abs, abs_le]
    have h1 := hc z z0; have h2 := hc z0 z
    constructor <;> cases abs_cases (g z0) <;> linarith
  set E := ∫ z', g z' ∂μ
  set a := (⨅ z, g z) - E
  set b := (⨆ z, g z) - E
  have hab : b - a ≤ c := by
    have : (⨆ z, g z) ≤ (⨅ z, g z) + c := by
      refine ciSup_le (fun z ↦ ?_)
      have : g z - c ≤ ⨅ z, g z := le_ciInf (fun z' ↦ by have := hc z z'; linarith)
      linarith
    simp only [a, b]; linarith
  have hab0 : 0 ≤ b - a := by
    have : (⨅ z, g z) ≤ ⨆ z, g z := (ciInf_le hbB z0).trans (le_ciSup hbA z0)
    simp only [a, b]; linarith
  have hsub := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (μ := μ)
    (X := fun z ↦ g z - E) (a := a) (b := b) (hg.sub measurable_const).aemeasurable
    (Filter.Eventually.of_forall (fun z ↦ ⟨by simp only [a]; linarith [ciInf_le hbB z],
      by simp only [b]; linarith [le_ciSup hbA z]⟩))
    (by rw [integral_sub hgi (integrable_const _), integral_const, probReal_univ, one_smul,
      sub_self])
  have := hsub.mgf_le t
  unfold mgf at this
  refine this.trans (Real.exp_le_exp.2 ?_)
  have e : (((‖b - a‖₊ / 2) ^ 2 : NNReal) : ℝ) = ((b - a) / 2) ^ 2 := by
    simp [Real.norm_of_nonneg hab0]
  rw [e]
  have : (b - a) ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ hab0 hab 2
  nlinarith [sq_nonneg t]

/-- **The exponential-moment bound behind McDiarmid's inequality**, by induction on the number
of coordinates. -/
theorem integral_exp_le : ∀ (n : ℕ) (μ : Fin n → Measure V) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (Fin n → V) → ℝ), Measurable f → ∀ (c : Fin n → ℝ),
    (∀ (x : Fin n → V) (i : Fin n) (v : V), |f x - f (Function.update x i v)| ≤ c i) →
    ∀ t : ℝ, ∫ x, Real.exp (t * (f x - ∫ y, f y ∂(Measure.pi μ))) ∂(Measure.pi μ) ≤
      Real.exp (t ^ 2 * (∑ i, c i ^ 2) / 8) := by
  intro n
  induction n with
  | zero =>
    intro μ _ f _ c _ t
    simp [integral_unique]
  | succ n ih =>
    intro μ _ f hf c hc t
    set P := Measure.pi μ with hP
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ V) 0 with he
    set ν := Measure.pi (fun j : Fin n ↦ μ (Fin.succAbove 0 j)) with hν
    have hp : MeasurePreserving e P ((μ 0).prod ν) := measurePreserving_piFinSuccAbove μ 0
    have hsymm : ∀ p : V × (Fin n → V), e.symm p = Fin.cons p.1 p.2 := by
      intro p
      rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
      funext j
      rw [Fin.insertNthEquiv_apply, Fin.insertNth_zero']
    have hint : ∀ φ : (Fin (n + 1) → V) → ℝ,
        ∫ x, φ x ∂P = ∫ p, φ (Fin.cons p.1 p.2) ∂((μ 0).prod ν) := by
      intro φ
      rw [← (hp.symm e).integral_comp']
      simp only [hsymm]
    -- notation for the sections
    set g : V → (Fin n → V) → ℝ := fun z y ↦ f (Fin.cons z y) with hg
    have hgm : Measurable (Function.uncurry g) := by
      have : Function.uncurry g = f ∘ e.symm := by
        funext p; simp only [Function.comp, hsymm]; rfl
      rw [this]; exact hf.comp e.symm.measurable
    have hne : Nonempty V := nonempty_of_prob (μ 0)
    set v0 : V := hne.some
    set x0 : Fin (n + 1) → V := fun _ ↦ v0
    have hfb : ∀ x, |f x| ≤ |f x0| + ∑ i, c i := by
      intro x
      have := abs_sub_le_sum f c hc x x0
      have h2 := abs_sub_abs_le_abs_sub (f x) (f x0)
      linarith
    set B := |f x0| + ∑ i, c i
    have hgb : ∀ z y, |g z y| ≤ B := fun z y ↦ hfb _
    have hgz : ∀ y, Measurable (fun z ↦ g z y) := fun y ↦ hgm.comp (measurable_id.prodMk measurable_const)
    have hgzi : ∀ y, Integrable (fun z ↦ g z y) (μ 0) := fun y ↦
      Integrable.of_bound (hgz y).aestronglyMeasurable B
        (Filter.Eventually.of_forall (fun z ↦ by rw [Real.norm_eq_abs]; exact hgb z y))
    set h : (Fin n → V) → ℝ := fun y ↦ ∫ z, g z y ∂(μ 0) with hh
    have hhm : Measurable h := (hgm.stronglyMeasurable.integral_prod_left).measurable
    have hhb : ∀ y, |h y| ≤ B := by
      intro y
      have := norm_integral_le_of_norm_le_const (μ := μ 0) (f := fun z ↦ g z y) (C := B)
        (Filter.Eventually.of_forall (fun z ↦ by rw [Real.norm_eq_abs]; exact hgb z y))
      rwa [probReal_univ, mul_one, Real.norm_eq_abs] at this
    -- bounded differences of `h`
    have hhc : ∀ (y : Fin n → V) (j : Fin n) (w : V),
        |h y - h (Function.update y j w)| ≤ c (Fin.succAbove 0 j) := by
      intro y j w
      simp only [hh]
      rw [← integral_sub (hgzi y) (hgzi _)]
      have := norm_integral_le_of_norm_le_const (μ := μ 0)
        (f := fun z ↦ g z y - g z (Function.update y j w)) (C := c (Fin.succAbove 0 j))
        (Filter.Eventually.of_forall (fun z ↦ by
          rw [Real.norm_eq_abs]
          simp only [hg, Fin.cons_update, Fin.succAbove_zero]
          exact hc _ _ _))
      rwa [probReal_univ, mul_one, Real.norm_eq_abs] at this
    have IH := ih (fun j ↦ μ (Fin.succAbove 0 j)) h hhm (fun j ↦ c (Fin.succAbove 0 j)) hhc t
    -- integrability of bounded functions of `g`
    have hexpb : ∀ (r K : ℝ), |r| ≤ K → ‖Real.exp (t * r)‖ ≤ Real.exp (|t| * K) := by
      intro r K hr
      rw [Real.norm_eq_abs, Real.abs_exp]
      refine Real.exp_le_exp.2 ((le_abs_self _).trans ?_)
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hr (abs_nonneg t)
    have hEhb : ∀ E : ℝ, |E| ≤ B → ∀ z y, |g z y - E| ≤ 2 * B := by
      intro E hE z y
      have := hgb z y
      calc |g z y - E| ≤ |g z y| + |E| := abs_sub _ _
        _ ≤ 2 * B := by linarith
    have hfi : Integrable (fun p : V × (Fin n → V) ↦ f (Fin.cons p.1 p.2)) ((μ 0).prod ν) :=
      Integrable.of_bound hgm.aestronglyMeasurable B
        (Filter.Eventually.of_forall (fun p ↦ by rw [Real.norm_eq_abs]; exact hgb p.1 p.2))
    -- the mean of `f` is the mean of `h`
    have hEf : ∫ y, f y ∂P = ∫ y, h y ∂ν := by
      rw [hint f, integral_prod_symm _ hfi]
    set Eh := ∫ y, h y ∂ν with hEh
    have hEhB : |Eh| ≤ B := by
      have := norm_integral_le_of_norm_le_const (μ := ν) (f := h) (C := B)
        (Filter.Eventually.of_forall (fun y ↦ by rw [Real.norm_eq_abs]; exact hhb y))
      have hνP : IsProbabilityMeasure ν := by rw [hν]; infer_instance
      rwa [probReal_univ, mul_one, Real.norm_eq_abs] at this
    have hFi : Integrable (fun p : V × (Fin n → V) ↦ Real.exp (t * (g p.1 p.2 - Eh)))
        ((μ 0).prod ν) :=
      Integrable.of_bound
        ((Real.measurable_exp.comp (measurable_const.mul
          (hgm.sub measurable_const))).aestronglyMeasurable) (Real.exp (|t| * (2 * B)))
        (Filter.Eventually.of_forall (fun p ↦ hexpb _ _ (hEhb Eh hEhB p.1 p.2)))
    have hνP : IsProbabilityMeasure ν := by rw [hν]; infer_instance
    have hHi : Integrable (fun y ↦ Real.exp (t * (h y - Eh)) * Real.exp (t ^ 2 * c 0 ^ 2 / 8)) ν :=
      (Integrable.of_bound
        ((Real.measurable_exp.comp (measurable_const.mul
          (hhm.sub measurable_const))).aestronglyMeasurable) (Real.exp (|t| * (2 * B)))
        (Filter.Eventually.of_forall (fun y ↦ hexpb _ _ (by
          have := hhb y
          calc |h y - Eh| ≤ |h y| + |Eh| := abs_sub _ _
            _ ≤ 2 * B := by linarith)))).mul_const _
    -- the one-step bound
    have hstep : ∀ y, ∫ z, Real.exp (t * (g z y - Eh)) ∂(μ 0) ≤
        Real.exp (t * (h y - Eh)) * Real.exp (t ^ 2 * c 0 ^ 2 / 8) := by
      intro y
      have e1 : ∀ z, Real.exp (t * (g z y - Eh)) =
          Real.exp (t * (h y - Eh)) * Real.exp (t * (g z y - h y)) := by
        intro z; rw [← Real.exp_add]; congr 1; ring
      simp only [e1]
      rw [integral_const_mul]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      refine integral_exp_le_of_range (fun z ↦ g z y) (hgz y) (c 0) (fun z z' ↦ ?_) t
      have := hc (Fin.cons z y) 0 z'
      rw [Fin.update_cons_zero] at this
      exact (le_abs_self _).trans this
    calc ∫ x, Real.exp (t * (f x - ∫ y, f y ∂P)) ∂P
        = ∫ p, Real.exp (t * (g p.1 p.2 - Eh)) ∂((μ 0).prod ν) := by
          rw [hEf, hint (fun x ↦ Real.exp (t * (f x - Eh)))]
      _ = ∫ y, ∫ z, Real.exp (t * (g z y - Eh)) ∂(μ 0) ∂ν := integral_prod_symm _ hFi
      _ ≤ ∫ y, Real.exp (t * (h y - Eh)) * Real.exp (t ^ 2 * c 0 ^ 2 / 8) ∂ν := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun y ↦ ?_)) hHi
            (Filter.Eventually.of_forall hstep)
          exact integral_nonneg (fun z ↦ (Real.exp_pos _).le)
      _ = Real.exp (t ^ 2 * c 0 ^ 2 / 8) * ∫ y, Real.exp (t * (h y - Eh)) ∂ν := by
          rw [integral_mul_const, mul_comm]
      _ ≤ Real.exp (t ^ 2 * c 0 ^ 2 / 8) *
            Real.exp (t ^ 2 * (∑ j : Fin n, c (Fin.succAbove 0 j) ^ 2) / 8) :=
          mul_le_mul_of_nonneg_left IH (Real.exp_pos _).le
      _ = Real.exp (t ^ 2 * (∑ i, c i ^ 2) / 8) := by
          rw [← Real.exp_add, Fin.sum_univ_succ]
          simp only [Fin.succAbove_zero]
          congr 1; ring

/-- McDiarmid's one-sided tail bound, in sub-Gaussian form. -/
lemma hasSubgaussianMGF_sub_integral {m : ℕ} (μ : Fin m → Measure V)
    [∀ i, IsProbabilityMeasure (μ i)] (f : (Fin m → V) → ℝ) (hf : Measurable f) (c : ℝ)
    (hc : ∀ (x : Fin m → V) (i : Fin m) (v : V), |f x - f (Function.update x i v)| ≤ c) :
    HasSubgaussianMGF (fun x ↦ f x - ∫ y, f y ∂(Measure.pi μ)) ⟨m * c ^ 2 / 4, by positivity⟩
      (Measure.pi μ) := by
  set P := Measure.pi μ
  have hsum : ∀ x y, |f x - f y| ≤ m * c := by
    intro x y
    simpa using abs_sub_le_sum f (fun _ ↦ c) hc x y
  have hfi : ∀ x, Integrable (fun y ↦ f x - f y) P := fun x ↦
    Integrable.of_bound (measurable_const.sub hf).aestronglyMeasurable (m * c)
      (Filter.Eventually.of_forall (fun y ↦ by rw [Real.norm_eq_abs]; exact hsum x y))
  have hXb : ∀ x, |f x - ∫ y, f y ∂P| ≤ m * c := by
    intro x
    have hfint : Integrable f P := by
      have := (hfi x).sub (integrable_const (f x))
      refine this.neg.congr (Filter.Eventually.of_forall (fun y ↦ ?_))
      simp
    have e : f x - ∫ y, f y ∂P = ∫ y, (f x - f y) ∂P := by
      rw [integral_sub (integrable_const _) hfint, integral_const, probReal_univ, one_smul]
    rw [e]
    have := norm_integral_le_of_norm_le_const (μ := P) (f := fun y ↦ f x - f y) (C := m * c)
      (Filter.Eventually.of_forall (fun y ↦ by rw [Real.norm_eq_abs]; exact hsum x y))
    rwa [probReal_univ, mul_one, Real.norm_eq_abs] at this
  refine ⟨fun t ↦ ?_, fun t ↦ ?_⟩
  · refine Integrable.of_bound
      ((Real.measurable_exp.comp (measurable_const.mul
        (hf.sub measurable_const))).aestronglyMeasurable) (Real.exp (|t| * (m * c))) ?_
    refine Filter.Eventually.of_forall (fun x ↦ ?_)
    rw [Real.norm_eq_abs, Real.abs_exp]
    refine Real.exp_le_exp.2 ((le_abs_self _).trans ?_)
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hXb x) (abs_nonneg t)
  · unfold mgf
    refine (integral_exp_le m μ f hf (fun _ ↦ c) hc t).trans (le_of_eq ?_)
    show Real.exp (t ^ 2 * (∑ _i : Fin m, c ^ 2) / 8) = Real.exp ((m * c ^ 2 / 4) * t ^ 2 / 2)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring_nf

end UnderstandingML.McDiarmidAux

open UnderstandingML.McDiarmidAux in
theorem checked_mcdiarmid_inequality_pi {V : Type*} [MeasurableSpace V] (m : ℕ) (μ : Fin m → Measure V)
    [∀ i, IsProbabilityMeasure (μ i)] (f : (Fin m → V) → ℝ) (hf : Measurable f) (c : ℝ)
    (hc : ∀ (x : Fin m → V) (i : Fin m) (v : V), |f x - f (Function.update x i v)| ≤ c)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    Measure.pi μ {x | c * Real.sqrt (Real.log (2 / δ) * m / 2) <
      |f x - ∫ y, f y ∂(Measure.pi μ)|} ≤ ENNReal.ofReal δ := by
  classical
  set P := Measure.pi μ with hP
  set E := ∫ y, f y ∂P with hE
  set ε := c * Real.sqrt (Real.log (2 / δ) * m / 2) with hε
  have hsum : ∀ x y, |f x - f y| ≤ m * c := by
    intro x y
    simpa using abs_sub_le_sum f (fun _ ↦ c) hc x y
  have hlog : 0 < Real.log (2 / δ) :=
    Real.log_pos (by rw [lt_div_iff₀ hδ]; linarith)
  by_cases hC : 0 < (m : ℝ) * c ^ 2
  · have hm : (0 : ℝ) < m := by
      rcases (Nat.cast_nonneg m : (0 : ℝ) ≤ m).lt_or_eq with h | h
      · exact h
      · rw [← h, zero_mul] at hC; exact absurd hC (lt_irrefl 0)
    have hne : Nonempty V := nonempty_of_prob (μ ⟨0, by exact_mod_cast hm⟩)
    have hc0 : 0 ≤ c := by
      have x : Fin m → V := fun _ ↦ hne.some
      exact (abs_nonneg _).trans (hc x ⟨0, by exact_mod_cast hm⟩ hne.some)
    have hε0 : 0 ≤ ε := by positivity
    -- the two one-sided bounds
    have h1 := (hasSubgaussianMGF_sub_integral μ f hf c hc).measure_ge_le hε0
    have hc' : ∀ (x : Fin m → V) (i : Fin m) (v : V),
        |(fun x ↦ -f x) x - (fun x ↦ -f x) (Function.update x i v)| ≤ c := by
      intro x i v
      show |-f x - -f (Function.update x i v)| ≤ c
      rw [show -f x - -f (Function.update x i v) = -(f x - f (Function.update x i v)) by ring,
        abs_neg]
      exact hc x i v
    have h2 := (hasSubgaussianMGF_sub_integral μ (fun x ↦ -f x) hf.neg c hc').measure_ge_le
      hε0
    have hcne : c ≠ 0 := by
      rintro rfl; simp at hC
    have hbound : Real.exp (-ε ^ 2 / (2 * (m * c ^ 2 / 4))) = δ / 2 := by
      have hε2 : ε ^ 2 = c ^ 2 * (Real.log (2 / δ) * m / 2) := by
        rw [hε, mul_pow, Real.sq_sqrt (by positivity)]
      rw [hε2]
      have : -(c ^ 2 * (Real.log (2 / δ) * m / 2)) / (2 * (m * c ^ 2 / 4)) =
          -Real.log (2 / δ) := by
        field_simp
        ring
      rw [this, Real.exp_neg, Real.exp_log (by positivity)]
      field_simp
    replace h1 := h1.trans (le_of_eq hbound)
    replace h2 := h2.trans (le_of_eq hbound)
    have hsub : {x | ε < |f x - E|} ⊆
        {x | ε ≤ f x - E} ∪ {x | ε ≤ (fun x ↦ -f x) x - ∫ y, (fun x ↦ -f x) y ∂P} := by
      intro x hx
      simp only [Set.mem_ofPred_eq] at hx
      rw [integral_neg]
      rcases le_or_gt 0 (f x - E) with h | h
      · left; simp only [Set.mem_ofPred_eq]; rw [abs_of_nonneg h] at hx; linarith
      · right; simp only [Set.mem_ofPred_eq]; rw [abs_of_neg h] at hx; linarith
    calc P {x | ε < |f x - E|}
        ≤ P ({x | ε ≤ f x - E} ∪ {x | ε ≤ (fun x ↦ -f x) x - ∫ y, (fun x ↦ -f x) y ∂P}) :=
          measure_mono hsub
      _ ≤ P {x | ε ≤ f x - E} + P {x | ε ≤ (fun x ↦ -f x) x - ∫ y, (fun x ↦ -f x) y ∂P} :=
          measure_union_le _ _
      _ = ENNReal.ofReal (P.real {x | ε ≤ f x - E}) + ENNReal.ofReal
            (P.real {x | ε ≤ (fun x ↦ -f x) x - ∫ y, (fun x ↦ -f x) y ∂P}) := by
          rw [ofReal_measureReal, ofReal_measureReal]
      _ ≤ ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) :=
          add_le_add (ENNReal.ofReal_le_ofReal h1) (ENNReal.ofReal_le_ofReal h2)
      _ = ENNReal.ofReal δ := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
  · -- degenerate case: `m c = 0`, so `f` is constant and the event is empty
    have hmc : (m : ℝ) * c = 0 := by
      have h0 : (m : ℝ) * c ^ 2 = 0 := le_antisymm (not_lt.1 hC) (by positivity)
      rcases mul_eq_zero.1 h0 with h | h
      · rw [h, zero_mul]
      · rw [pow_eq_zero_iff two_ne_zero] at h; rw [h, mul_zero]
    have hε0 : ε = 0 := by
      rcases mul_eq_zero.1 hmc with h | h
      · rw [hε, h]; simp
      · rw [hε, h, zero_mul]
    have hconst : ∀ x, f x - E = 0 := by
      intro x
      have hfx : ∀ y, f y = f x := fun y ↦ by
        have := hsum y x; rw [hmc] at this; linarith [abs_nonneg (f y - f x), abs_le.1 this]
      rw [hE, integral_congr_ae (Filter.Eventually.of_forall hfx), integral_const, probReal_univ,
        one_smul, sub_self]
    have : {x | ε < |f x - E|} = ∅ := by
      ext x; simp [hconst x, hε0]
    rw [this, measure_empty]
    simp

end

end
-- END MODULE AttributedSPO

-- BEGIN MODULE MarginGeometry
section

set_option autoImplicit false

open MeasureTheory

namespace SPOBounds.Margin.Proof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma omega_oracle (S : Set E) (w : StrongDual ℝ E → E) (hw : IsOracle S w)
    (c : StrongDual ℝ E) : omega S c = c (w (-c)) - c (w c) := by
  have hmax : IsGreatest (c '' S) (c (w (-c))) := by
    refine ⟨⟨w (-c), (hw (-c)).1, rfl⟩, ?_⟩
    rintro y ⟨v, hv, rfl⟩
    have h := (hw (-c)).2 v hv
    simp only [neg_apply] at h
    linarith
  have hmin : IsLeast (c '' S) (c (w c)) :=
    ⟨⟨w c, (hw c).1, rfl⟩, by rintro y ⟨v, hv, rfl⟩; exact (hw c).2 v hv⟩
  exact congrArg₂ (· - ·) hmax.csSup_eq hmin.csInf_eq

lemma omega_nonneg (S : Set E) (w : StrongDual ℝ E → E) (hw : IsOracle S w)
    (c : StrongDual ℝ E) : 0 ≤ omega S c := by
  rw [omega_oracle S w hw]
  exact sub_nonneg.mpr ((hw c).2 (w (-c)) (hw (-c)).1)

lemma sub_le_omega (S : Set E) (w : StrongDual ℝ E → E) (hw : IsOracle S w)
    (c : StrongDual ℝ E) {u v : E} (hu : u ∈ S) (hv : v ∈ S) :
    c u - c v ≤ omega S c := by
  rw [omega_oracle S w hw]
  have h1 := (hw (-c)).2 u hu
  have h2 := (hw c).2 v hv
  simp only [neg_apply] at h1
  linarith

lemma omega_norm_bound (S : Set E) (w : StrongDual ℝ E → E) (hw : IsOracle S w)
    (R : ℝ) (hR : ∀ v ∈ S, ‖v‖ ≤ R) (c : StrongDual ℝ E) :
    omega S c ≤ 2 * R * ‖c‖ := by
  rw [omega_oracle S w hw, ← map_sub]
  have hn : ‖w (-c) - w c‖ ≤ 2 * R :=
    (norm_sub_le _ _).trans (by linarith [hR (w (-c)) (hw (-c)).1, hR (w c) (hw c).1])
  calc
    c (w (-c) - w c) ≤ ‖c (w (-c) - w c)‖ := by
      rw [Real.norm_eq_abs]
      exact le_abs_self _
    _ ≤ ‖c‖ * ‖w (-c) - w c‖ := c.le_opNorm _
    _ ≤ ‖c‖ * (2 * R) := mul_le_mul_of_nonneg_left hn (norm_nonneg _)
    _ = 2 * R * ‖c‖ := by ring

lemma omega_lipschitz_bound (S : Set E) (w : StrongDual ℝ E → E) (hw : IsOracle S w)
    (R : ℝ) (hR : ∀ v ∈ S, ‖v‖ ≤ R) (a b : StrongDual ℝ E) :
    |omega S a - omega S b| ≤ 2 * R * ‖a - b‖ := by
  have hmain (a b : StrongDual ℝ E) : omega S a - omega S b ≤ 2 * R * ‖a - b‖ := by
    have h1 := sub_le_omega S w hw b (hw (-a)).1 (hw a).1
    have he := omega_oracle S w hw a
    have hn : ‖w (-a) - w a‖ ≤ 2 * R :=
      (norm_sub_le _ _).trans (by linarith [hR (w (-a)) (hw (-a)).1, hR (w a) (hw a).1])
    have hbnd : (a - b) (w (-a) - w a) ≤ 2 * R * ‖a - b‖ := by
      calc
        (a - b) (w (-a) - w a) ≤ ‖(a - b) (w (-a) - w a)‖ := by
          rw [Real.norm_eq_abs]
          exact le_abs_self _
        _ ≤ ‖a - b‖ * ‖w (-a) - w a‖ := (a - b).le_opNorm _
        _ ≤ ‖a - b‖ * (2 * R) := mul_le_mul_of_nonneg_left hn (norm_nonneg _)
        _ = 2 * R * ‖a - b‖ := by ring
    simp only [sub_apply, map_sub] at hbnd
    linarith
  rw [abs_le]
  constructor
  · have h := hmain b a
    rw [norm_sub_rev] at h
    linarith
  · exact hmain a b

lemma omega_continuous (S : Set E) (hS : Bornology.IsBounded S)
    (w : StrongDual ℝ E → E) (hw : IsOracle S w) : Continuous (omega S) := by
  obtain ⟨R, hR⟩ := hS.exists_norm_le
  have hR0 : 0 ≤ R := (norm_nonneg (w 0)).trans (hR (w 0) (hw 0).1)
  have hLip : LipschitzWith ⟨2 * R, by positivity⟩ (omega S) := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    rw [Real.dist_eq, dist_eq_norm]
    change |omega S a - omega S b| ≤ 2 * R * ‖a - b‖
    exact omega_lipschitz_bound S w hw R hR a b
  exact hLip.continuous

lemma costSet_bounds (S : Set E) (hS : Bornology.IsBounded S)
    (w : StrongDual ℝ E → E) (hw : IsOracle S w)
    (C : Set (StrongDual ℝ E)) (hC : C.Nonempty) (hCb : Bornology.IsBounded C) :
    0 ≤ omegaSet S C ∧ 0 ≤ rhoSet C ∧
      (∀ c ∈ C, omega S c ≤ omegaSet S C) ∧ (∀ c ∈ C, ‖c‖ ≤ rhoSet C) := by
  obtain ⟨R, hR⟩ := hS.exists_norm_le
  obtain ⟨K, hK⟩ := hCb.exists_norm_le
  have hR0 : 0 ≤ R := (norm_nonneg (w 0)).trans (hR (w 0) (hw 0).1)
  have hbo : BddAbove (omega S '' C) := ⟨2 * R * K, by
    rintro y ⟨c, hc, rfl⟩
    exact (omega_norm_bound S w hw R hR c).trans
      (mul_le_mul_of_nonneg_left (hK c hc) (by positivity))⟩
  have hbr : BddAbove ((fun c : StrongDual ℝ E => ‖c‖) '' C) :=
    ⟨K, by rintro y ⟨c, hc, rfl⟩; exact hK c hc⟩
  have ho (c : StrongDual ℝ E) (hc : c ∈ C) : omega S c ≤ omegaSet S C :=
    le_csSup hbo ⟨c, hc, rfl⟩
  have hr (c : StrongDual ℝ E) (hc : c ∈ C) : ‖c‖ ≤ rhoSet C :=
    le_csSup hbr ⟨c, hc, rfl⟩
  obtain ⟨c, hc⟩ := hC
  exact ⟨(omega_nonneg S w hw c).trans (ho c hc), (norm_nonneg c).trans (hr c hc), ho, hr⟩

lemma marginLoss_bounds (S : Set E) (hSc : IsCompact S)
    (w : StrongDual ℝ E → E) (hw : IsOracle S w)
    (γ : ℝ) (hγ : 0 < γ) (chat c : StrongDual ℝ E) :
    spoLoss w chat c ≤ marginLoss S w γ chat c ∧
      marginLoss S w γ chat c ∈ Set.Icc 0 (omega S c) := by
  have hspo := p71dfcbfc_bounds S hSc w hw chat c
  have hn : 0 ≤ nu S chat := Metric.infDist_nonneg
  have ht0 : 0 ≤ min (nu S chat / γ) 1 := le_min (by positivity) zero_le_one
  have ht1 : min (nu S chat / γ) 1 ≤ 1 := min_le_right _ _
  rw [p71dfcbfc_rep S w γ hγ chat c]
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hspo.2)]
  · constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hspo.2)]
    · nlinarith [mul_nonneg ht0 (sub_nonneg.mpr hspo.2)]

end SPOBounds.Margin.Proof

end
-- END MODULE MarginGeometry

-- BEGIN MODULE AEHoeffding
section

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter

namespace SPOBounds.Margin.Proof

variable {Z : Type*} [MeasurableSpace Z] {μ : Measure Z}

lemma bounded_measurable_version (f : Z → ℝ) (hf : AEMeasurable f μ)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ᵐ z ∂μ, |f z| ≤ B) :
    ∃ g : Z → ℝ, Measurable g ∧ (∀ z, |g z| ≤ B) ∧ f =ᵐ[μ] g := by
  let g : Z → ℝ := fun z => max (-B) (min B (hf.mk f z))
  refine ⟨g, measurable_const.max (measurable_const.min hf.measurable_mk), ?_, ?_⟩
  · intro z
    rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  · filter_upwards [hf.ae_eq_mk, hb] with z hz hbz
    dsimp [g]
    rw [← hz, min_eq_right (abs_le.mp hbz).2, max_eq_right (abs_le.mp hbz).1]

lemma ae_range_interval [IsProbabilityMeasure μ] (g : Z → ℝ)
    (B : ℝ) (hb : ∀ z, |g z| ≤ B) (c : ℝ)
    (hc : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, g y - g x ≤ c) :
    ∀ᵐ z ∂μ, g z ∈ Set.Icc (essSup g μ - c) (essSup g μ) := by
  have hup : IsBoundedUnder (· ≤ ·) (ae μ) g := by
    change ∃ b, ∀ᵐ z ∂μ, g z ≤ b
    exact ⟨B, Eventually.of_forall (fun z => (abs_le.mp (hb z)).2)⟩
  have hco : IsCoboundedUnder (· ≤ ·) (ae μ) g :=
    isCoboundedUnder_le_of_le (ae μ) (fun z => (abs_le.mp (hb z)).1)
  filter_upwards [ae_le_essSup hup, hc] with z hz hcz
  refine ⟨?_, hz⟩
  have h := essSup_le_of_ae_le (g z + c)
    (hcz.mono (fun y hy => by linarith)) hco
  linarith

lemma integral_exp_le_of_ae_range [IsProbabilityMeasure μ] (g : Z → ℝ)
    (hg : Measurable g) (B : ℝ) (hb : ∀ z, |g z| ≤ B)
    (c : ℝ) (hc0 : 0 ≤ c)
    (hc : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, g y - g x ≤ c) (t : ℝ) :
    ∫ z, Real.exp (t * (g z - ∫ y, g y ∂μ)) ∂μ ≤
      Real.exp (t ^ 2 * c ^ 2 / 8) := by
  have hsub := hasSubgaussianMGF_of_mem_Icc hg.aemeasurable
    (ae_range_interval g B hb c hc)
  have h := hsub.mgf_le t
  unfold mgf at h
  convert h using 1
  congr 1
  have he : essSup g μ - (essSup g μ - c) = c := by ring
  simp only [he, NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat, coe_nnnorm,
    Real.norm_of_nonneg hc0]
  ring

lemma integral_abs_le_bound [IsProbabilityMeasure μ] (f : Z → ℝ) (B : ℝ)
    (hb : ∀ᵐ z ∂μ, |f z| ≤ B) : |∫ z, f z ∂μ| ≤ B := by
  have h := norm_integral_le_of_norm_le_const (μ := μ) (f := f) (C := B)
    (hb.mono (fun z hz => by simpa only [Real.norm_eq_abs] using hz))
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using h

lemma integrable_exp_of_abs_bound [IsFiniteMeasure μ] (f : Z → ℝ)
    (hf : AEMeasurable f μ) (B : ℝ) (hb : ∀ᵐ z ∂μ, |f z| ≤ B) (t : ℝ) :
    Integrable (fun z => Real.exp (t * f z)) μ := by
  refine Integrable.of_bound ((aemeasurable_const.mul hf).exp).aestronglyMeasurable
    (Real.exp (|t| * B)) ?_
  filter_upwards [hb] with z hz
  rw [Real.norm_eq_abs, Real.abs_exp]
  apply Real.exp_le_exp.mpr
  calc t * f z ≤ |t * f z| := le_abs_self _
    _ = |t| * |f z| := abs_mul _ _
    _ ≤ |t| * B := mul_le_mul_of_nonneg_left hz (abs_nonneg _)

end SPOBounds.Margin.Proof

end
-- END MODULE AEHoeffding

-- BEGIN MODULE SampleSensitivity
section

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter

namespace SPOBounds.Margin.Proof

variable {Z : Type*} [MeasurableSpace Z]

noncomputable abbrev sampleLaw (μ : Measure Z) (n : ℕ) : Measure (Fin n → Z) :=
  Measure.pi (fun _ : Fin n => μ)

def AESensitivity (μ : Measure Z) {n : ℕ} (f : (Fin n → Z) → ℝ)
    (c : Fin n → ℝ) : Prop :=
  ∀ i, ∀ᵐ x ∂sampleLaw μ n, ∀ᵐ z ∂μ,
    |f x - f (Function.update x i z)| ≤ c i

lemma measurePreserving_cons (μ : Measure Z) [IsProbabilityMeasure μ] (n : ℕ) :
    MeasurePreserving (fun p : Z × (Fin n → Z) => Fin.cons p.1 p.2)
      (μ.prod (sampleLaw μ n)) (sampleLaw μ (n + 1)) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Z) 0
  have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm e
  convert hp using 1
  funext p
  rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
  funext j
  rw [Fin.insertNthEquiv_apply, Fin.insertNth_zero']

lemma integral_sample_cons (μ : Measure Z) [IsProbabilityMeasure μ] (n : ℕ)
    (φ : (Fin (n + 1) → Z) → ℝ) :
    ∫ x, φ x ∂sampleLaw μ (n + 1) =
      ∫ p, φ (Fin.cons p.1 p.2) ∂(μ.prod (sampleLaw μ n)) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Z) 0
  have hp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0
  rw [← (hp.symm e).integral_comp']
  congr 1
  funext p
  congr 1
  rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
  funext j
  rw [Fin.insertNthEquiv_apply, Fin.insertNth_zero']

lemma ae_update_sample (μ : Measure Z) [IsProbabilityMeasure μ] {n : ℕ}
    (i : Fin n) {P : (Fin n → Z) → Prop} (hP : ∀ᵐ x ∂sampleLaw μ n, P x) :
    ∀ᵐ x ∂sampleLaw μ n, ∀ᵐ z ∂μ, P (Function.update x i z) := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Z) i
    have hp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) i
    have hpair : ∀ᵐ p ∂μ.prod (sampleLaw μ n), P (e.symm p) :=
      (hp.symm e).quasiMeasurePreserving.ae hP
    have hswap : ∀ᵐ p ∂(sampleLaw μ n).prod μ, P (e.symm (p.2, p.1)) :=
      Measure.measurePreserving_swap.quasiMeasurePreserving.ae hpair
    have htail := Measure.ae_ae_of_ae_prod hswap
    have hproj : MeasurePreserving (fun x => (e x).2)
        (sampleLaw μ (n + 1)) (sampleLaw μ n) :=
      measurePreserving_snd.comp hp
    have hx := hproj.quasiMeasurePreserving.ae htail
    have he : ∀ x z, e.symm (z, (e x).2) = Function.update x i z := by
      intro x z
      change i.insertNth z (i.removeNth x) = Function.update x i z
      exact Fin.insertNth_removeNth i z x
    simpa only [he] using hx

lemma AESensitivity.congr (μ : Measure Z) [IsProbabilityMeasure μ] {n : ℕ}
    {f g : (Fin n → Z) → ℝ} {c : Fin n → ℝ}
    (hc : AESensitivity μ f c) (hfg : f =ᵐ[sampleLaw μ n] g) :
    AESensitivity μ g c := by
  intro i
  filter_upwards [hc i, hfg, ae_update_sample μ i hfg] with x hx hxe hzu
  filter_upwards [hx, hzu] with z hz hze
  rwa [hxe, hze] at hz

lemma AESensitivity.of_forall (μ : Measure Z) {n : ℕ}
    (f : (Fin n → Z) → ℝ) (c : Fin n → ℝ)
    (hc : ∀ x i z, |f x - f (Function.update x i z)| ≤ c i) :
    AESensitivity μ f c := by
  intro i
  exact Eventually.of_forall (fun x => Eventually.of_forall (fun z => hc x i z))

lemma sensitivity_cons (μ : Measure Z) [IsProbabilityMeasure μ] {n : ℕ}
    (f : (Fin (n + 1) → Z) → ℝ) (c : Fin (n + 1) → ℝ)
    (hc : AESensitivity μ f c) (i : Fin (n + 1)) :
    ∀ᵐ z ∂μ, ∀ᵐ y ∂sampleLaw μ n, ∀ᵐ w ∂μ,
      |f (Fin.cons z y) - f (Function.update (Fin.cons z y) i w)| ≤ c i := by
  exact Measure.ae_ae_of_ae_prod
    ((measurePreserving_cons μ n).quasiMeasurePreserving.ae (hc i))

end SPOBounds.Margin.Proof

end
-- END MODULE SampleSensitivity

-- BEGIN MODULE ProductAE
section

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter

namespace SPOBounds.Margin.Proof

variable {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]

lemma measurableSet_ae_section (ν : Measure B) [SFinite ν] (P : A × B → Prop)
    (hP : MeasurableSet {p | P p}) :
    MeasurableSet {a | ∀ᵐ b ∂ν, P (a, b)} := by
  simp only [ae_iff]
  have hm : Measurable (fun a => ν {b | ¬ P (a, b)}) :=
    measurable_measure_prodMk_left hP.compl
  exact measurableSet_eq_fun hm measurable_const

lemma ae_triple_swap_front (μ : Measure A) (ν : Measure B) (ρ : Measure C)
    [SFinite μ] [SFinite ν] [SFinite ρ] (P : A → B → C → Prop)
    (hP : MeasurableSet {p : (A × B) × C | P p.1.1 p.1.2 p.2})
    (h : ∀ᵐ a ∂μ, ∀ᵐ b ∂ν, ∀ᵐ c ∂ρ, P a b c) :
    ∀ᵐ b ∂ν, ∀ᵐ a ∂μ, ∀ᵐ c ∂ρ, P a b c := by
  exact (Measure.ae_ae_comm
    (measurableSet_ae_section ρ (fun p : (A × B) × C => P p.1.1 p.1.2 p.2) hP)).mp h

lemma ae_triple_rotate (μ : Measure A) (ν : Measure B) (ρ : Measure C)
    [SFinite μ] [SFinite ν] [SFinite ρ] (P : A → B → C → Prop)
    (hP : MeasurableSet {p : (A × B) × C | P p.1.1 p.1.2 p.2})
    (h : ∀ᵐ a ∂μ, ∀ᵐ b ∂ν, ∀ᵐ c ∂ρ, P a b c) :
    ∀ᵐ b ∂ν, ∀ᵐ c ∂ρ, ∀ᵐ a ∂μ, P a b c := by
  filter_upwards [ae_triple_swap_front μ ν ρ P hP h] with b hb
  apply (Measure.ae_ae_comm (μ := μ) (ν := ρ) (p := fun a c => P a b c) ?_).mp hb
  exact hP.preimage (by fun_prop : Measurable (fun p : A × C => ((p.1, b), p.2)))

end SPOBounds.Margin.Proof

end
-- END MODULE ProductAE

-- BEGIN MODULE SensitivitySections
section

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter

namespace SPOBounds.Margin.Proof

variable {Z : Type*} [MeasurableSpace Z]

lemma first_section_range (μ : Measure Z) [IsProbabilityMeasure μ] {n : ℕ}
    (f : (Fin (n + 1) → Z) → ℝ) (hf : Measurable f)
    (c : Fin (n + 1) → ℝ) (hc : AESensitivity μ f c) :
    ∀ᵐ y ∂sampleLaw μ n, ∀ᵐ z ∂μ, ∀ᵐ w ∂μ,
      f (Fin.cons w y) - f (Fin.cons z y) ≤ c 0 := by
  have hgm : Measurable (fun p : Z × (Fin n → Z) => f (Fin.cons p.1 p.2)) :=
    hf.comp (measurePreserving_cons μ n).measurable
  have hm : MeasurableSet {p : (Z × (Fin n → Z)) × Z |
      |f (Fin.cons p.1.1 p.1.2) - f (Fin.cons p.2 p.1.2)| ≤ c 0} := by
    apply measurableSet_le _ measurable_const
    exact ((hgm.comp measurable_fst).sub
      (hgm.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))).abs
  have h := sensitivity_cons μ f c hc 0
  simp only [Fin.update_cons_zero] at h
  have hs := ae_triple_swap_front μ (sampleLaw μ n) μ
    (fun z y w => |f (Fin.cons z y) - f (Fin.cons w y)| ≤ c 0) hm h
  filter_upwards [hs] with y hy
  filter_upwards [hy] with z hz
  filter_upwards [hz] with w hw
  linarith [(abs_le.mp hw).1]

lemma integrated_sensitivity (μ : Measure Z) [IsProbabilityMeasure μ] {n : ℕ}
    (f : (Fin (n + 1) → Z) → ℝ) (hf : Measurable f)
    (B : ℝ) (hb : ∀ x, |f x| ≤ B)
    (c : Fin (n + 1) → ℝ) (hc : AESensitivity μ f c) :
    AESensitivity μ (fun y => ∫ z, f (Fin.cons z y) ∂μ) (fun i => c i.succ) := by
  have hgm : Measurable (fun p : Z × (Fin n → Z) => f (Fin.cons p.1 p.2)) :=
    hf.comp (measurePreserving_cons μ n).measurable
  have hgi : ∀ y, Integrable (fun z => f (Fin.cons z y)) μ := by
    intro y
    exact Integrable.of_bound (hgm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      B (Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hb (Fin.cons z y)))
  intro i
  have hm : MeasurableSet {p : (Z × (Fin n → Z)) × Z |
      |f (Fin.cons p.1.1 p.1.2) -
        f (Fin.cons p.1.1 (Function.update p.1.2 i p.2))| ≤ c i.succ} := by
    apply measurableSet_le _ measurable_const
    have hm₂ : Measurable (fun p : (Z × (Fin n → Z)) × Z =>
        (p.1.1, Function.update p.1.2 i p.2)) := by fun_prop
    exact ((hgm.comp measurable_fst).sub (hgm.comp hm₂)).abs
  have h : ∀ᵐ z ∂μ, ∀ᵐ y ∂sampleLaw μ n, ∀ᵐ w ∂μ,
      |f (Fin.cons z y) - f (Fin.cons z (Function.update y i w))| ≤ c i.succ := by
    simpa only [Fin.cons_update] using sensitivity_cons μ f c hc i.succ
  have hs := ae_triple_rotate μ (sampleLaw μ n) μ
    (fun z y w => |f (Fin.cons z y) -
      f (Fin.cons z (Function.update y i w))| ≤ c i.succ) hm h
  filter_upwards [hs] with y hy
  filter_upwards [hy] with w hw
  rw [← integral_sub (hgi y) (hgi (Function.update y i w))]
  exact integral_abs_le_bound _ _ hw

end SPOBounds.Margin.Proof

end
-- END MODULE SensitivitySections

-- BEGIN MODULE AEMcDiarmidMGF
section

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter

namespace SPOBounds.Margin.Proof

/- The finite-product exponential-moment induction follows the complete accepted proof by
@Gabewhigham of UnderstandingML.mcdiarmid_inequality_pi, preserved in AttributedSPO.
Here the sensitivities hold only almost everywhere on independent replacement couplings.
The new scalar essential-range and section-transport lemmas retain the sharp constant. -/
theorem mgf_le_measurable_bounded {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) [IsProbabilityMeasure μ] :
    ∀ (n : ℕ) (f : (Fin n → Z) → ℝ), Measurable f →
      ∀ B : ℝ, (∀ x, |f x| ≤ B) → ∀ c : Fin n → ℝ,
      (∀ i, 0 ≤ c i) → AESensitivity μ f c → ∀ t : ℝ,
      ∫ x, Real.exp (t * (f x - ∫ y, f y ∂sampleLaw μ n)) ∂sampleLaw μ n ≤
        Real.exp (t ^ 2 * (∑ i, c i ^ 2) / 8) := by
  intro n
  induction n with
  | zero =>
    intro f _ B _ c _ _ t
    simp [integral_unique]
  | succ n ih =>
    intro f hf B hb c hc0 hc t
    let ν := sampleLaw μ n
    let g : Z → (Fin n → Z) → ℝ := fun z y => f (Fin.cons z y)
    have hgm : Measurable (Function.uncurry g) :=
      hf.comp (measurePreserving_cons μ n).measurable
    have hgb : ∀ z y, |g z y| ≤ B := fun z y => hb (Fin.cons z y)
    have hgz : ∀ y, Measurable (fun z => g z y) :=
      fun y => hgm.comp (measurable_id.prodMk measurable_const)
    let h : (Fin n → Z) → ℝ := fun y => ∫ z, g z y ∂μ
    have hhm : Measurable h := (hgm.stronglyMeasurable.integral_prod_left).measurable
    have hhb : ∀ y, |h y| ≤ B := fun y =>
      integral_abs_le_bound (fun z => g z y) B (Eventually.of_forall (fun z => hgb z y))
    have hhc : AESensitivity μ h (fun i => c i.succ) :=
      integrated_sensitivity μ f hf B hb c hc
    have hIH := ih h hhm B hhb (fun i => c i.succ) (fun i => hc0 i.succ) hhc t
    have hfi : Integrable (Function.uncurry g) (μ.prod ν) :=
      Integrable.of_bound hgm.aestronglyMeasurable B
        (Eventually.of_forall (fun p => by
          rw [Real.norm_eq_abs]
          change |g p.1 p.2| ≤ B
          exact hgb p.1 p.2))
    have hEf : ∫ y, f y ∂sampleLaw μ (n + 1) = ∫ y, h y ∂ν := by
      rw [integral_sample_cons μ n f]
      exact integral_prod_symm _ hfi
    let E := ∫ y, h y ∂ν
    have hEb : |E| ≤ B := integral_abs_le_bound h B (Eventually.of_forall hhb)
    have hsub : ∀ z y, |g z y - E| ≤ 2 * B := by
      intro z y
      calc |g z y - E| ≤ |g z y| + |E| := abs_sub _ _
        _ ≤ 2 * B := by linarith [hgb z y]
    have hFi : Integrable (fun p : Z × (Fin n → Z) => Real.exp (t * (g p.1 p.2 - E)))
        (μ.prod ν) :=
      integrable_exp_of_abs_bound _ (hgm.sub measurable_const).aemeasurable (2 * B)
        (Eventually.of_forall (fun p => hsub p.1 p.2)) t
    have hHi : Integrable (fun y => Real.exp (t * (h y - E)) *
        Real.exp (t ^ 2 * c 0 ^ 2 / 8)) ν := by
      apply Integrable.mul_const
      refine integrable_exp_of_abs_bound _ (hhm.sub measurable_const).aemeasurable (2 * B) ?_ t
      exact Eventually.of_forall (fun y => (abs_sub _ _).trans (by linarith [hhb y]))
    have hstep : ∀ᵐ y ∂ν, ∫ z, Real.exp (t * (g z y - E)) ∂μ ≤
        Real.exp (t * (h y - E)) * Real.exp (t ^ 2 * c 0 ^ 2 / 8) := by
      filter_upwards [first_section_range μ f hf c hc] with y hy
      have he : ∀ z, Real.exp (t * (g z y - E)) =
          Real.exp (t * (h y - E)) * Real.exp (t * (g z y - h y)) := by
        intro z
        rw [← Real.exp_add]
        congr 1
        ring
      simp only [he]
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left
        (integral_exp_le_of_ae_range (g · y) (hgz y) B (fun z => hgb z y)
          (c 0) (hc0 0) hy t) (Real.exp_pos _).le
    calc
      ∫ x, Real.exp (t * (f x - ∫ y, f y ∂sampleLaw μ (n + 1)))
          ∂sampleLaw μ (n + 1)
          = ∫ p, Real.exp (t * (g p.1 p.2 - E)) ∂(μ.prod ν) := by
            rw [hEf, integral_sample_cons μ n]
      _ = ∫ y, ∫ z, Real.exp (t * (g z y - E)) ∂μ ∂ν := integral_prod_symm _ hFi
      _ ≤ ∫ y, Real.exp (t * (h y - E)) * Real.exp (t ^ 2 * c 0 ^ 2 / 8) ∂ν :=
        integral_mono_of_nonneg
          (Eventually.of_forall (fun y => integral_nonneg (fun z => (Real.exp_pos _).le)))
          hHi hstep
      _ = Real.exp (t ^ 2 * c 0 ^ 2 / 8) * ∫ y, Real.exp (t * (h y - E)) ∂ν := by
        rw [integral_mul_const, mul_comm]
      _ ≤ Real.exp (t ^ 2 * c 0 ^ 2 / 8) *
          Real.exp (t ^ 2 * (∑ i : Fin n, c i.succ ^ 2) / 8) :=
        mul_le_mul_of_nonneg_left hIH (Real.exp_pos _).le
      _ = Real.exp (t ^ 2 * (∑ i, c i ^ 2) / 8) := by
        rw [← Real.exp_add, Fin.sum_univ_succ]
        congr 1
        ring

end SPOBounds.Margin.Proof

end
-- END MODULE AEMcDiarmidMGF

-- BEGIN MODULE AEMcDiarmid
section

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter

namespace SPOBounds.Margin.Proof

variable {Z : Type*} [MeasurableSpace Z]

theorem ae_subgaussian (μ : Measure Z) [IsProbabilityMeasure μ] {n : ℕ}
    (f : (Fin n → Z) → ℝ) (hf : AEMeasurable f (sampleLaw μ n))
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ᵐ x ∂sampleLaw μ n, |f x| ≤ B)
    (c : Fin n → ℝ) (hc0 : ∀ i, 0 ≤ c i) (hc : AESensitivity μ f c) :
    HasSubgaussianMGF (fun x => f x - ∫ y, f y ∂sampleLaw μ n)
      ⟨(∑ i, c i ^ 2) / 4, by positivity⟩ (sampleLaw μ n) := by
  obtain ⟨g, hgm, hgb, hfg⟩ := bounded_measurable_version f hf B hB hb
  have hgc := hc.congr μ hfg
  have hE : ∫ x, f x ∂sampleLaw μ n = ∫ x, g x ∂sampleLaw μ n := integral_congr_ae hfg
  have hEb : |∫ x, f x ∂sampleLaw μ n| ≤ B := integral_abs_le_bound f B hb
  refine ⟨fun t => ?_, fun t => ?_⟩
  · refine integrable_exp_of_abs_bound _ (hf.sub_const _) (2 * B) ?_ t
    filter_upwards [hb] with x hx
    exact (abs_sub _ _).trans (by linarith)
  · unfold mgf
    rw [hE]
    calc
      ∫ x, Real.exp (t * (f x - ∫ y, g y ∂sampleLaw μ n)) ∂sampleLaw μ n
          = ∫ x, Real.exp (t * (g x - ∫ y, g y ∂sampleLaw μ n)) ∂sampleLaw μ n :=
        integral_congr_ae (hfg.mono (fun x hx => by
          dsimp only
          rw [hx]))
      _ ≤ Real.exp (t ^ 2 * (∑ i, c i ^ 2) / 8) :=
        mgf_le_measurable_bounded μ n g hgm B hgb c hc0 hgc t
      _ = Real.exp (((⟨(∑ i, c i ^ 2) / 4, by positivity⟩ : NNReal) : ℝ) * t ^ 2 / 2) := by
        congr 1
        ring

theorem ae_mcdiarmid_tail (μ : Measure Z) [IsProbabilityMeasure μ] (n : ℕ)
    (hn : 0 < n) (f : (Fin n → Z) → ℝ)
    (hf : AEMeasurable f (sampleLaw μ n))
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ᵐ x ∂sampleLaw μ n, |f x| ≤ B)
    (b : ℝ) (hb0 : 0 ≤ b) (hc : AESensitivity μ f (fun _ => b / n))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    sampleLaw μ n {x | (∫ y, f y ∂sampleLaw μ n) +
      b * Real.sqrt (Real.log (1 / δ) / (2 * n)) < f x} ≤ ENNReal.ofReal δ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsg : HasSubgaussianMGF (fun x => f x - ∫ y, f y ∂sampleLaw μ n)
      ⟨b ^ 2 / (4 * n), by positivity⟩ (sampleLaw μ n) := by
    have he : (⟨(∑ _i : Fin n, (b / n) ^ 2) / 4, by positivity⟩ : NNReal) =
        ⟨b ^ 2 / (4 * n), by positivity⟩ := by
      apply Subtype.ext
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    rw [← he]
    exact ae_subgaussian μ f hf B hB hb (fun _ => b / n) (fun _ => by positivity) hc
  by_cases hbn : b = 0
  · subst b
    have hz : HasSubgaussianMGF (fun x => f x - ∫ y, f y ∂sampleLaw μ n)
        0 (sampleLaw μ n) := by
      have he : (⟨(0 : ℝ) ^ 2 / (4 * n), by positivity⟩ : NNReal) = 0 := by
        apply Subtype.ext
        simp
      rwa [he] at hsg
    have he : ∀ᵐ x ∂sampleLaw μ n, ¬ ((∫ y, f y ∂sampleLaw μ n) < f x) := by
      filter_upwards [hz.ae_eq_zero_of_hasSubgaussianMGF_zero] with x hx
      change f x - (∫ y, f y ∂sampleLaw μ n) = 0 at hx
      linarith
    have hzero : sampleLaw μ n {x | (∫ y, f y ∂sampleLaw μ n) < f x} = 0 := by
      simpa only [ae_iff, not_not] using he
    simpa only [zero_mul, add_zero, hzero] using (show (0 : ENNReal) ≤ ENNReal.ofReal δ from bot_le)
  · let ε := b * Real.sqrt (Real.log (1 / δ) / (2 * n))
    have hlog : 0 < Real.log (1 / δ) := Real.log_pos (by
      rw [lt_div_iff₀ hδ]
      simpa using hδ1)
    have hε0 : 0 ≤ ε := by dsimp [ε]; positivity
    have htail := hsg.measure_ge_le hε0
    have he : Real.exp (-ε ^ 2 / (2 * (b ^ 2 / (4 * n)))) = δ := by
      have hε2 : ε ^ 2 = b ^ 2 * (Real.log (1 / δ) / (2 * n)) := by
        dsimp [ε]
        rw [mul_pow, Real.sq_sqrt (by positivity)]
      rw [hε2]
      have heq : -(b ^ 2 * (Real.log (1 / δ) / (2 * n))) /
          (2 * (b ^ 2 / (4 * n))) = -Real.log (1 / δ) := by
        field_simp
        ring
      rw [heq, Real.exp_neg, Real.exp_log (by positivity)]
      field_simp
    have hreal : (sampleLaw μ n).real
        {x | ε ≤ f x - ∫ y, f y ∂sampleLaw μ n} ≤ δ := by
      exact htail.trans (le_of_eq he)
    calc
      sampleLaw μ n {x | (∫ y, f y ∂sampleLaw μ n) + ε < f x}
          ≤ sampleLaw μ n {x | ε ≤ f x - ∫ y, f y ∂sampleLaw μ n} := by
        apply measure_mono
        intro x hx
        change (∫ y, f y ∂sampleLaw μ n) + ε < f x at hx
        change ε ≤ f x - ∫ y, f y ∂sampleLaw μ n
        linarith
      _ = ENNReal.ofReal ((sampleLaw μ n).real
          {x | ε ≤ f x - ∫ y, f y ∂sampleLaw μ n}) := by rw [ofReal_measureReal]
      _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal hreal

end SPOBounds.Margin.Proof

end
-- END MODULE AEMcDiarmid

-- BEGIN MODULE BoundedLossBasics
section

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter

namespace SPOBounds.Margin.Proof

variable {Z H : Type*} [MeasurableSpace Z]

noncomputable def meanLoss (loss : H → Z → ℝ) {n : ℕ} (h : H) (s : Fin n → Z) : ℝ :=
  (1 / n : ℝ) * ∑ i, loss h (s i)

noncomputable def lossRisk (μ : Measure Z) (loss : H → Z → ℝ) (h : H) : ℝ :=
  ∫ z, loss h z ∂μ

noncomputable def lossDeviation (μ : Measure Z) (loss : H → Z → ℝ) {n : ℕ}
    (s : Fin n → Z) : ℝ := ⨆ h, lossRisk μ loss h - meanLoss loss h s

noncomputable def lossSignedSup (loss : H → Z → ℝ) {n : ℕ}
    (σ : Fin n → Bool) (s : Fin n → Z) : ℝ :=
  ⨆ h, (1 / n : ℝ) * ∑ i, (if σ i then (1 : ℝ) else -1) * loss h (s i)

noncomputable def lossRademacher (loss : H → Z → ℝ) {n : ℕ} (s : Fin n → Z) : ℝ :=
  (1 / 2 ^ n : ℝ) * ∑ σ : Fin n → Bool, lossSignedSup loss σ s

lemma bounded_ciSup {ι : Type*} [Nonempty ι] (f : ι → ℝ) (b : ℝ)
    (hf : ∀ i, |f i| ≤ b) : |⨆ i, f i| ≤ b := by
  have hb : BddAbove (Set.range f) := ⟨b, by rintro _ ⟨i, rfl⟩; exact (abs_le.mp (hf i)).2⟩
  rw [abs_le]
  constructor
  · obtain ⟨i⟩ := ‹Nonempty ι›
    exact (abs_le.mp (hf i)).1.trans (le_ciSup hb i)
  · exact ciSup_le (fun i => (abs_le.mp (hf i)).2)

omit [MeasurableSpace Z] in
lemma meanLoss_bounds (loss : H → Z → ℝ) (b : ℝ)
    (hb : ∀ h z, loss h z ∈ Set.Icc 0 b) {n : ℕ} (hn : 0 < n)
    (h : H) (s : Fin n → Z) : meanLoss loss h s ∈ Set.Icc 0 b := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun i _ => (hb h (s i)).1))
  · have hs : ∑ i, loss h (s i) ≤ n * b := by
      calc ∑ i, loss h (s i) ≤ ∑ _i : Fin n, b := Finset.sum_le_sum (fun i _ => (hb h (s i)).2)
        _ = n * b := by simp
    dsimp [meanLoss]
    calc (1 / n : ℝ) * ∑ i, loss h (s i) ≤ (1 / n : ℝ) * (n * b) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ = b := by field_simp

lemma loss_integrable (μ : Measure Z) [IsProbabilityMeasure μ]
    (loss : H → Z → ℝ) (hm : ∀ h, Measurable (loss h))
    (b : ℝ) (hb : ∀ h z, loss h z ∈ Set.Icc 0 b) (h : H) :
    Integrable (loss h) μ :=
  Integrable.of_bound (hm h).aestronglyMeasurable b (Eventually.of_forall (fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hb h z).1]
    exact (hb h z).2))

lemma lossRisk_bounds (μ : Measure Z) [IsProbabilityMeasure μ]
    (loss : H → Z → ℝ) (hm : ∀ h, Measurable (loss h))
    (b : ℝ) (hb : ∀ h z, loss h z ∈ Set.Icc 0 b) (h : H) :
    lossRisk μ loss h ∈ Set.Icc 0 b := by
  constructor
  · exact integral_nonneg (fun z => (hb h z).1)
  · have hi := integral_mono (loss_integrable μ loss hm b hb h) (integrable_const b)
      (fun z => (hb h z).2)
    simpa [lossRisk] using hi

lemma deviation_component_bound (μ : Measure Z) [IsProbabilityMeasure μ]
    (loss : H → Z → ℝ) (hm : ∀ h, Measurable (loss h))
    (b : ℝ) (hb : ∀ h z, loss h z ∈ Set.Icc 0 b) {n : ℕ} (hn : 0 < n)
    (h : H) (s : Fin n → Z) : |lossRisk μ loss h - meanLoss loss h s| ≤ b := by
  have hr := lossRisk_bounds μ loss hm b hb h
  have he := meanLoss_bounds loss b hb hn h s
  rw [abs_le]
  constructor <;> linarith [hr.1, hr.2, he.1, he.2]

lemma lossDeviation_bound [Nonempty H] (μ : Measure Z) [IsProbabilityMeasure μ]
    (loss : H → Z → ℝ) (hm : ∀ h, Measurable (loss h))
    (b : ℝ) (hb : ∀ h z, loss h z ∈ Set.Icc 0 b) {n : ℕ} (hn : 0 < n)
    (s : Fin n → Z) : |lossDeviation μ loss s| ≤ b :=
  bounded_ciSup _ b (fun h => deviation_component_bound μ loss hm b hb hn h s)

omit [MeasurableSpace Z] in
lemma meanLoss_update (loss : H → Z → ℝ) {n : ℕ} (h : H)
    (s : Fin n → Z) (i : Fin n) (z : Z) :
    meanLoss loss h s - meanLoss loss h (Function.update s i z) =
      (1 / n : ℝ) * (loss h (s i) - loss h z) := by
  classical
  have he : ∑ j, (loss h (s j) - loss h (Function.update s i z j)) =
      loss h (s i) - loss h z := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Function.update_of_ne hji]
    · simp
  dsimp [meanLoss]
  rw [← mul_sub, ← Finset.sum_sub_distrib, he]

omit [MeasurableSpace Z] in
lemma meanLoss_update_bound (loss : H → Z → ℝ) (b : ℝ)
    (hb : ∀ h z, loss h z ∈ Set.Icc 0 b) {n : ℕ} (h : H)
    (s : Fin n → Z) (i : Fin n) (z : Z) :
    |meanLoss loss h s - meanLoss loss h (Function.update s i z)| ≤ b / n := by
  rw [meanLoss_update, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / n)]
  have he : |loss h (s i) - loss h z| ≤ b := by
    rw [abs_le]
    constructor <;> linarith [(hb h (s i)).1, (hb h (s i)).2, (hb h z).1, (hb h z).2]
  calc (1 / n : ℝ) * |loss h (s i) - loss h z| ≤ (1 / n : ℝ) * b :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = b / n := by ring

lemma lossDeviation_sensitivity [Nonempty H] (μ : Measure Z) [IsProbabilityMeasure μ]
    (loss : H → Z → ℝ) (hm : ∀ h, Measurable (loss h))
    (b : ℝ) (hb : ∀ h z, loss h z ∈ Set.Icc 0 b) {n : ℕ} (hn : 0 < n) :
    AESensitivity μ (fun s : Fin n → Z => lossDeviation μ loss s) (fun _ => b / n) := by
  apply AESensitivity.of_forall
  intro s i z
  have hbd (x : Fin n → Z) :
      BddAbove (Set.range (fun h => lossRisk μ loss h - meanLoss loss h x)) :=
    ⟨b, by rintro _ ⟨h, rfl⟩; exact (le_abs_self _).trans (deviation_component_bound μ loss hm b hb hn h x)⟩
  have hstep (x y : Fin n → Z) (he : ∀ h, |meanLoss loss h x - meanLoss loss h y| ≤ b / n) :
      lossDeviation μ loss x ≤ lossDeviation μ loss y + b / n := by
    apply ciSup_le
    intro h
    have hy := le_ciSup (hbd y) h
    have hd := (abs_le.mp (he h)).1
    change lossRisk μ loss h - meanLoss loss h y ≤ lossDeviation μ loss y at hy
    linarith
  rw [abs_le]
  constructor
  · have h := hstep (Function.update s i z) s (fun h => by
      rw [abs_sub_comm]
      exact meanLoss_update_bound loss b hb h s i z)
    linarith
  · have h := hstep s (Function.update s i z) (fun h => meanLoss_update_bound loss b hb h s i z)
    linarith

end SPOBounds.Margin.Proof

end
-- END MODULE BoundedLossBasics

-- BEGIN MODULE SampleSwap
section

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter

namespace SPOBounds.Margin.Proof

variable {Z : Type*} [MeasurableSpace Z]

def sampleSwap {n : ℕ} (σ : Fin n → Bool)
    (p : (Fin n → Z) × (Fin n → Z)) : (Fin n → Z) × (Fin n → Z) :=
  (fun i => if σ i then p.2 i else p.1 i,
   fun i => if σ i then p.1 i else p.2 i)

lemma sampleSwap_preserving (μ : Measure Z) [IsProbabilityMeasure μ] {n : ℕ}
    (σ : Fin n → Bool) :
    MeasurePreserving (sampleSwap (Z := Z) σ)
      ((sampleLaw μ n).prod (sampleLaw μ n)) ((sampleLaw μ n).prod (sampleLaw μ n)) := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow Z Z (Fin n)
  have he := measurePreserving_arrowProdEquivProdArrow Z Z (Fin n)
    (fun _ => μ) (fun _ => μ)
  let k : Fin n → Z × Z → Z × Z := fun i p => if σ i then p.swap else p
  have hk : ∀ i, MeasurePreserving (k i) (μ.prod μ) (μ.prod μ) := by
    intro i
    cases hs : σ i
    · have heq : k i = id := by funext p; simp [k, hs]
      rw [heq]
      exact MeasurePreserving.id (μ.prod μ)
    · simpa [k, hs] using (Measure.measurePreserving_swap (μ := μ) (ν := μ))
  have hp := measurePreserving_pi (fun _ : Fin n => μ.prod μ) (fun _ => μ.prod μ) hk
  convert he.comp (hp.comp (he.symm e)) using 1
  funext p
  apply Prod.ext
  · funext i
    change (if σ i then p.2 i else p.1 i) =
      (if σ i then (p.2 i, p.1 i) else (p.1 i, p.2 i)).1
    split <;> rfl
  · funext i
    change (if σ i then p.1 i else p.2 i) =
      (if σ i then (p.2 i, p.1 i) else (p.1 i, p.2 i)).2
    split <;> rfl

lemma sampleSwap_first_preserving (μ : Measure Z) [IsProbabilityMeasure μ] {n : ℕ}
    (σ : Fin n → Bool) :
    MeasurePreserving (fun p : (Fin n → Z) × (Fin n → Z) => (sampleSwap σ p).1)
      ((sampleLaw μ n).prod (sampleLaw μ n)) (sampleLaw μ n) :=
  measurePreserving_fst.comp (sampleSwap_preserving μ σ)

lemma sampleSwap_second_preserving (μ : Measure Z) [IsProbabilityMeasure μ] {n : ℕ}
    (σ : Fin n → Bool) :
    MeasurePreserving (fun p : (Fin n → Z) × (Fin n → Z) => (sampleSwap σ p).2)
      ((sampleLaw μ n).prod (sampleLaw μ n)) (sampleLaw μ n) :=
  measurePreserving_snd.comp (sampleSwap_preserving μ σ)

end SPOBounds.Margin.Proof

end
-- END MODULE SampleSwap

-- BEGIN MODULE SignedLoss
section

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter

namespace SPOBounds.Margin.Proof

variable {Z H : Type*} [MeasurableSpace Z]

omit [MeasurableSpace Z] in
lemma signed_component_bound (loss : H → Z → ℝ) (b : ℝ)
    (hb : ∀ h z, loss h z ∈ Set.Icc 0 b) {n : ℕ} (hn : 0 < n)
    (h : H) (σ : Fin n → Bool) (s : Fin n → Z) :
    |(1 / n : ℝ) * ∑ i, (if σ i then (1 : ℝ) else -1) * loss h (s i)| ≤ b := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : |∑ i, (if σ i then (1 : ℝ) else -1) * loss h (s i)| ≤ n * b := by
    calc
      |∑ i, (if σ i then (1 : ℝ) else -1) * loss h (s i)|
          ≤ ∑ i, |(if σ i then (1 : ℝ) else -1) * loss h (s i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, b := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul, abs_of_nonneg (hb h (s i)).1]
        cases σ i <;> simpa using (hb h (s i)).2
      _ = n * b := by simp
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / n)]
  calc (1 / n : ℝ) * |∑ i, (if σ i then (1 : ℝ) else -1) * loss h (s i)|
      ≤ (1 / n : ℝ) * (n * b) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = b := by field_simp

omit [MeasurableSpace Z] in
lemma lossSignedSup_bound [Nonempty H] (loss : H → Z → ℝ) (b : ℝ)
    (hb : ∀ h z, loss h z ∈ Set.Icc 0 b) {n : ℕ} (hn : 0 < n)
    (σ : Fin n → Bool) (s : Fin n → Z) : |lossSignedSup loss σ s| ≤ b :=
  bounded_ciSup _ b (fun h => signed_component_bound loss b hb hn h σ s)

lemma meanLoss_measurable (loss : H → Z → ℝ) (hm : ∀ h, Measurable (loss h))
    {n : ℕ} (h : H) : Measurable (fun s : Fin n → Z => meanLoss loss h s) := by
  dsimp [meanLoss]
  fun_prop

lemma integral_comp_preserving {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} {f : A → B} (hp : MeasurePreserving f μ ν)
    (g : B → ℝ) (hg : AEMeasurable g ν) :
    ∫ x, g (f x) ∂μ = ∫ y, g y ∂ν := by
  calc ∫ x, g (f x) ∂μ = ∫ y, g y ∂μ.map f :=
      (integral_map hp.aemeasurable (by rw [hp.map_eq]; exact hg.aestronglyMeasurable)).symm
    _ = ∫ y, g y ∂ν := by rw [hp.map_eq]

lemma meanLoss_integrable (μ : Measure Z) [IsProbabilityMeasure μ]
    (loss : H → Z → ℝ) (hm : ∀ h, Measurable (loss h))
    (b : ℝ) (hb : ∀ h z, loss h z ∈ Set.Icc 0 b) {n : ℕ} (hn : 0 < n) (h : H) :
    Integrable (fun s : Fin n → Z => meanLoss loss h s) (sampleLaw μ n) :=
  Integrable.of_bound (meanLoss_measurable loss hm h).aestronglyMeasurable b
    (Eventually.of_forall (fun s => by
      rw [Real.norm_eq_abs, abs_of_nonneg (meanLoss_bounds loss b hb hn h s).1]
      exact (meanLoss_bounds loss b hb hn h s).2))

lemma integral_meanLoss (μ : Measure Z) [IsProbabilityMeasure μ]
    (loss : H → Z → ℝ) (hm : ∀ h, Measurable (loss h))
    (b : ℝ) (hb : ∀ h z, loss h z ∈ Set.Icc 0 b) {n : ℕ} (hn : 0 < n) (h : H) :
    ∫ s : Fin n → Z, meanLoss loss h s ∂sampleLaw μ n = lossRisk μ loss h := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hi (i : Fin n) : Integrable (fun s : Fin n → Z => loss h (s i)) (sampleLaw μ n) :=
    (measurePreserving_eval (fun _ : Fin n => μ) i).integrable_comp_of_integrable
      (loss_integrable μ loss hm b hb h)
  have he (i : Fin n) : ∫ s : Fin n → Z, loss h (s i) ∂sampleLaw μ n = lossRisk μ loss h :=
    integral_comp_preserving (measurePreserving_eval (fun _ : Fin n => μ) i) (loss h) (hm h).aemeasurable
  dsimp [meanLoss]
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => hi i)]
  simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

omit [MeasurableSpace Z] in
lemma sign_majorant [Nonempty H] (loss : H → Z → ℝ) (b : ℝ)
    (hb : ∀ h z, loss h z ∈ Set.Icc 0 b) {n : ℕ} (hn : 0 < n)
    (σ : Fin n → Bool) (s t : Fin n → Z) (h : H) :
    meanLoss loss h t - meanLoss loss h s ≤
      lossSignedSup loss σ (sampleSwap σ (s, t)).1 +
      lossSignedSup loss (fun i => !(σ i)) (sampleSwap σ (s, t)).2 := by
  have hbd (τ : Fin n → Bool) (x : Fin n → Z) :
      BddAbove (Set.range (fun h => (1 / n : ℝ) *
        ∑ i, (if τ i then (1 : ℝ) else -1) * loss h (x i))) :=
    ⟨b, by rintro _ ⟨h, rfl⟩; exact (le_abs_self _).trans (signed_component_bound loss b hb hn h τ x)⟩
  have h1 := le_ciSup (hbd σ (sampleSwap σ (s, t)).1) h
  have h2 := le_ciSup (hbd (fun i => !(σ i)) (sampleSwap σ (s, t)).2) h
  have he : meanLoss loss h t - meanLoss loss h s =
      (1 / n : ℝ) * ∑ i, (if σ i then (1 : ℝ) else -1) * loss h ((sampleSwap σ (s, t)).1 i) +
      (1 / n : ℝ) * ∑ i, (if !(σ i) then (1 : ℝ) else -1) * loss h ((sampleSwap σ (s, t)).2 i) := by
    dsimp [meanLoss]
    rw [← mul_sub, ← Finset.sum_sub_distrib, ← mul_add, ← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    cases hs : σ i <;> simp [sampleSwap, hs] <;> ring
  rw [he]
  exact add_le_add h1 h2

end SPOBounds.Margin.Proof

end
-- END MODULE SignedLoss

-- BEGIN MODULE LossSymmetrization
section

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter

namespace SPOBounds.Margin.Proof

variable {Z H : Type*} [MeasurableSpace Z] [Nonempty H]

lemma signedSup_integrable (μ : Measure Z) [IsProbabilityMeasure μ]
    (loss : H → Z → ℝ) (b : ℝ) (hb : ∀ h z, loss h z ∈ Set.Icc 0 b)
    {n : ℕ} (hn : 0 < n) (σ : Fin n → Bool)
    (hA : AEMeasurable (lossSignedSup loss σ) (sampleLaw μ n)) :
    Integrable (lossSignedSup loss σ) (sampleLaw μ n) :=
  Integrable.of_bound hA.aestronglyMeasurable b (Eventually.of_forall (fun s => by
    simpa only [Real.norm_eq_abs] using lossSignedSup_bound loss b hb hn σ s))

theorem symmetrization_fixed_sign (μ : Measure Z) [IsProbabilityMeasure μ]
    (loss : H → Z → ℝ) (hm : ∀ h, Measurable (loss h))
    (b : ℝ) (hb : ∀ h z, loss h z ∈ Set.Icc 0 b) {n : ℕ} (hn : 0 < n)
    (hΦ : AEMeasurable (fun s : Fin n → Z => lossDeviation μ loss s) (sampleLaw μ n))
    (hA : ∀ σ : Fin n → Bool, AEMeasurable (lossSignedSup loss σ) (sampleLaw μ n))
    (σ : Fin n → Bool) :
    ∫ s, lossDeviation μ loss s ∂sampleLaw μ n ≤
      (∫ s, lossSignedSup loss σ s ∂sampleLaw μ n) +
      ∫ s, lossSignedSup loss (fun i => !(σ i)) s ∂sampleLaw μ n := by
  let P := sampleLaw μ n
  let F : (Fin n → Z) × (Fin n → Z) → ℝ := fun p =>
    lossSignedSup loss σ (sampleSwap σ p).1 +
    lossSignedSup loss (fun i => !(σ i)) (sampleSwap σ p).2
  have hi1 : Integrable (fun p => lossSignedSup loss σ (sampleSwap σ p).1) (P.prod P) :=
    (sampleSwap_first_preserving μ σ).integrable_comp_of_integrable
    (signedSup_integrable μ loss b hb hn σ (hA σ))
  have hi2 : Integrable (fun p => lossSignedSup loss (fun i => !(σ i)) (sampleSwap σ p).2)
      (P.prod P) := (sampleSwap_second_preserving μ σ).integrable_comp_of_integrable
    (signedSup_integrable μ loss b hb hn (fun i => !(σ i)) (hA _))
  have hFI : Integrable F (P.prod P) := hi1.add hi2
  have hdevI : Integrable (fun s : Fin n → Z => lossDeviation μ loss s) P :=
    Integrable.of_bound hΦ.aestronglyMeasurable b (Eventually.of_forall (fun s => by
      simpa only [Real.norm_eq_abs] using lossDeviation_bound μ loss hm b hb hn s))
  have hsec : ∀ᵐ s ∂P, lossDeviation μ loss s ≤ ∫ t, F (s, t) ∂P := by
    filter_upwards [hFI.prod_right_ae] with s hs
    apply ciSup_le
    intro h
    calc
      lossRisk μ loss h - meanLoss loss h s =
          ∫ t, (meanLoss loss h t - meanLoss loss h s) ∂P := by
        rw [integral_sub (meanLoss_integrable μ loss hm b hb hn h) (integrable_const _),
          integral_meanLoss μ loss hm b hb hn h, integral_const, probReal_univ, one_smul]
      _ ≤ ∫ t, F (s, t) ∂P :=
        integral_mono ((meanLoss_integrable μ loss hm b hb hn h).sub (integrable_const _)) hs
          (fun t => sign_majorant loss b hb hn σ s t h)
  calc
    ∫ s, lossDeviation μ loss s ∂P ≤ ∫ s, ∫ t, F (s, t) ∂P ∂P :=
      integral_mono_ae hdevI hFI.integral_prod_left hsec
    _ = ∫ p, F p ∂P.prod P := (integral_prod _ hFI).symm
    _ = (∫ s, lossSignedSup loss σ s ∂P) +
        ∫ s, lossSignedSup loss (fun i => !(σ i)) s ∂P := by
      rw [show (fun p => F p) = (fun p =>
        lossSignedSup loss σ (sampleSwap σ p).1 +
        lossSignedSup loss (fun i => !(σ i)) (sampleSwap σ p).2) from rfl]
      rw [integral_add hi1 hi2,
        integral_comp_preserving (sampleSwap_first_preserving μ σ) _ (hA σ),
        integral_comp_preserving (sampleSwap_second_preserving μ σ) _ (hA _)]

theorem loss_symmetrization (μ : Measure Z) [IsProbabilityMeasure μ]
    (loss : H → Z → ℝ) (hm : ∀ h, Measurable (loss h))
    (b : ℝ) (hb : ∀ h z, loss h z ∈ Set.Icc 0 b) {n : ℕ} (hn : 0 < n)
    (hΦ : AEMeasurable (fun s : Fin n → Z => lossDeviation μ loss s) (sampleLaw μ n))
    (hA : ∀ σ : Fin n → Bool, AEMeasurable (lossSignedSup loss σ) (sampleLaw μ n)) :
    ∫ s, lossDeviation μ loss s ∂sampleLaw μ n ≤
      2 * ∫ s, lossRademacher loss s ∂sampleLaw μ n := by
  classical
  let e : (Fin n → Bool) ≃ (Fin n → Bool) :=
    { toFun := fun σ i => !(σ i)
      invFun := fun σ i => !(σ i)
      left_inv := by intro σ; funext i; simp
      right_inv := by intro σ; funext i; simp }
  have hsum : (∑ σ : Fin n → Bool, ∫ s, lossSignedSup loss (fun i => !(σ i)) s ∂sampleLaw μ n) =
      ∑ σ : Fin n → Bool, ∫ s, lossSignedSup loss σ s ∂sampleLaw μ n :=
    e.sum_comp (fun σ => ∫ s, lossSignedSup loss σ s ∂sampleLaw μ n)
  have hrad : ∫ s, lossRademacher loss s ∂sampleLaw μ n =
      (1 / 2 ^ n : ℝ) * ∑ σ : Fin n → Bool, ∫ s, lossSignedSup loss σ s ∂sampleLaw μ n := by
    dsimp [lossRademacher]
    rw [integral_const_mul, integral_finsetSum _ (fun σ _ => signedSup_integrable μ loss b hb hn σ (hA σ))]
  have hi := Finset.sum_le_sum (s := Finset.univ) (fun σ _ =>
    symmetrization_fixed_sign μ loss hm b hb hn hΦ hA σ)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] at hi
  calc
    ∫ s, lossDeviation μ loss s ∂sampleLaw μ n =
        (1 / 2 ^ n : ℝ) * (2 ^ n * ∫ s, lossDeviation μ loss s ∂sampleLaw μ n) := by field_simp
    _ ≤ (1 / 2 ^ n : ℝ) * ∑ σ : Fin n → Bool,
        ((∫ s, lossSignedSup loss σ s ∂sampleLaw μ n) +
        ∫ s, lossSignedSup loss (fun i => !(σ i)) s ∂sampleLaw μ n) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = 2 * ∫ s, lossRademacher loss s ∂sampleLaw μ n := by
      rw [Finset.sum_add_distrib, hsum, hrad]
      ring

end SPOBounds.Margin.Proof

end
-- END MODULE LossSymmetrization

-- BEGIN MODULE BoundedLossGeneralization
section

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter

namespace SPOBounds.Margin.Proof

variable {Z H : Type*} [MeasurableSpace Z] [Nonempty H]

lemma lossRademacher_integrable (μ : Measure Z) [IsProbabilityMeasure μ]
    (loss : H → Z → ℝ) (b : ℝ) (hb : ∀ h z, loss h z ∈ Set.Icc 0 b)
    {n : ℕ} (hn : 0 < n)
    (hA : ∀ σ : Fin n → Bool, AEMeasurable (lossSignedSup loss σ) (sampleLaw μ n)) :
    Integrable (fun s : Fin n → Z => lossRademacher loss s) (sampleLaw μ n) := by
  exact (integrable_finsetSum _ (fun σ _ => signedSup_integrable μ loss b hb hn σ (hA σ))).const_mul _

theorem bounded_loss_generalization (μ : Measure Z) [IsProbabilityMeasure μ]
    (loss : H → Z → ℝ) (hm : ∀ h, Measurable (loss h))
    (b : ℝ) (hb0 : 0 ≤ b) (hb : ∀ h z, loss h z ∈ Set.Icc 0 b)
    (n : ℕ) (hn : 0 < n)
    (hΦ : AEMeasurable (fun s : Fin n → Z => lossDeviation μ loss s) (sampleLaw μ n))
    (hA : ∀ σ : Fin n → Bool, AEMeasurable (lossSignedSup loss σ) (sampleLaw μ n))
    (C : ℝ) (hC : (∫ s, lossRademacher loss s ∂sampleLaw μ n) ≤ C)
    (δ : ℝ) (hδ : 0 < δ) :
    sampleLaw μ n {s | ∃ h, ¬ (lossRisk μ loss h ≤ meanLoss loss h s +
      2 * C + b * Real.sqrt (Real.log (1 / δ) / (2 * n)))} ≤ ENNReal.ofReal δ := by
  by_cases hδ1 : δ < 1
  · have hmean : (∫ s, lossDeviation μ loss s ∂sampleLaw μ n) ≤ 2 * C :=
      (loss_symmetrization μ loss hm b hb hn hΦ hA).trans
        (mul_le_mul_of_nonneg_left hC (by norm_num))
    have htail := ae_mcdiarmid_tail μ n hn (fun s => lossDeviation μ loss s) hΦ
      b hb0 (Eventually.of_forall (lossDeviation_bound μ loss hm b hb hn))
      b hb0 (lossDeviation_sensitivity μ loss hm b hb hn) δ hδ hδ1
    refine (measure_mono ?_).trans htail
    rintro s ⟨h, hh⟩
    have hbd : BddAbove (Set.range (fun h => lossRisk μ loss h - meanLoss loss h s)) :=
      ⟨b, by rintro _ ⟨h, rfl⟩; exact (le_abs_self _).trans (deviation_component_bound μ loss hm b hb hn h s)⟩
    have hle := le_ciSup hbd h
    change lossRisk μ loss h - meanLoss loss h s ≤ lossDeviation μ loss s at hle
    change (∫ y, lossDeviation μ loss y ∂sampleLaw μ n) +
      b * Real.sqrt (Real.log (1 / δ) / (2 * n)) < lossDeviation μ loss s
    push Not at hh
    linarith
  · calc sampleLaw μ n {s | ∃ h, ¬ (lossRisk μ loss h ≤ meanLoss loss h s +
        2 * C + b * Real.sqrt (Real.log (1 / δ) / (2 * n)))}
        ≤ sampleLaw μ n Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
      _ ≤ ENNReal.ofReal δ := by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (not_lt.mp hδ1)

end SPOBounds.Margin.Proof

end
-- END MODULE BoundedLossGeneralization

-- BEGIN MODULE ClippedMargin
section

namespace SPOBounds.Margin.Proof

open MeasureTheory Filter

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def clippedMargin (S : Set E) (w : StrongDual ℝ E → E) (γ : ℝ)
    (C : Set (StrongDual ℝ E)) (H : Set (X → StrongDual ℝ E))
    (f : H) (z : X × StrongDual ℝ E) : ℝ :=
  max 0 (min (omegaSet S C) (marginLoss S w γ (f.val z.1) z.2))

theorem clippedMargin_bounds (S : Set E) (w : StrongDual ℝ E → E) (γ : ℝ)
    (C : Set (StrongDual ℝ E)) (H : Set (X → StrongDual ℝ E)) (hM : 0 ≤ omegaSet S C)
    (f : H) (z : X × StrongDual ℝ E) : clippedMargin S w γ C H f z ∈ Set.Icc 0 (omegaSet S C) :=
  ⟨le_max_left _ _, max_le hM (min_le_left _ _)⟩

theorem clippedMargin_eq_of_mem (S : Set E) (hSc : IsCompact S)
    (w : StrongDual ℝ E → E) (hw : IsOracle S w) (γ : ℝ) (hγ : 0 < γ)
    (C : Set (StrongDual ℝ E)) (hC : C.Nonempty) (hCb : Bornology.IsBounded C)
    (H : Set (X → StrongDual ℝ E)) (f : H) (z : X × StrongDual ℝ E) (hz : z.2 ∈ C) :
    clippedMargin S w γ C H f z = marginLoss S w γ (f.val z.1) z.2 := by
  have hb := (marginLoss_bounds S hSc w hw γ hγ (f.val z.1) z.2).2
  have hu := (costSet_bounds S hSc.isBounded w hw C hC hCb).2.2.1 z.2 hz
  exact (congrArg (max 0) (min_eq_right (hb.2.trans hu))).trans (max_eq_right hb.1)

variable [MeasurableSpace X] [MeasurableSpace (StrongDual ℝ E)] [BorelSpace (StrongDual ℝ E)]

theorem marginLoss_measurable (S : Set E) (hSc : IsCompact S)
    (w : StrongDual ℝ E → E) (hw : IsOracle S w) (γ : ℝ)
    (f : X → StrongDual ℝ E) (hf : Measurable f)
    (hℓ : Measurable (fun z : X × StrongDual ℝ E => spoLoss w (f z.1) z.2)) :
    Measurable (fun z : X × StrongDual ℝ E => marginLoss S w γ (f z.1) z.2) := by
  classical
  have hν : Measurable (fun z : X × StrongDual ℝ E => nu S (f z.1)) :=
    (Metric.continuous_infDist_pt (degenerate S)).measurable.comp (hf.comp measurable_fst)
  have hω : Measurable (fun z : X × StrongDual ℝ E => omega S z.2) :=
    (omega_continuous S hSc.isBounded w hw).measurable.comp measurable_snd
  exact Measurable.ite (measurableSet_lt measurable_const hν) hℓ
    (((hν.div_const γ).mul hℓ).add ((measurable_const.sub (hν.div_const γ)).mul hω))

theorem clippedMargin_measurable (S : Set E) (hSc : IsCompact S)
    (w : StrongDual ℝ E → E) (hw : IsOracle S w) (γ : ℝ)
    (C : Set (StrongDual ℝ E)) (H : Set (X → StrongDual ℝ E))
    (hf : ∀ f ∈ H, Measurable f)
    (hℓ : ∀ f ∈ H, Measurable (fun z : X × StrongDual ℝ E => spoLoss w (f z.1) z.2))
    (f : H) : Measurable (clippedMargin S w γ C H f) :=
  measurable_const.max (measurable_const.min
    (marginLoss_measurable S hSc w hw γ f.val (hf f.val f.property) (hℓ f.val f.property)))

omit [BorelSpace (StrongDual ℝ E)] in
section

theorem clippedMargin_ae_all (S : Set E) (hSc : IsCompact S)
    (w : StrongDual ℝ E → E) (hw : IsOracle S w) (γ : ℝ) (hγ : 0 < γ)
    (C : Set (StrongDual ℝ E)) (hC : C.Nonempty) (hCb : Bornology.IsBounded C)
    (H : Set (X → StrongDual ℝ E)) (D : Measure (X × StrongDual ℝ E))
    (hDC : ∀ᵐ z ∂D, z.2 ∈ C) :
    ∀ᵐ z ∂D, ∀ f : H, clippedMargin S w γ C H f z = marginLoss S w γ (f.val z.1) z.2 := by
  filter_upwards [hDC] with z hz f
  exact clippedMargin_eq_of_mem S hSc w hw γ hγ C hC hCb H f z hz

theorem clippedMargin_risk_eq (S : Set E) (hSc : IsCompact S)
    (w : StrongDual ℝ E → E) (hw : IsOracle S w) (γ : ℝ) (hγ : 0 < γ)
    (C : Set (StrongDual ℝ E)) (hC : C.Nonempty) (hCb : Bornology.IsBounded C)
    (H : Set (X → StrongDual ℝ E)) (D : Measure (X × StrongDual ℝ E))
    (hDC : ∀ᵐ z ∂D, z.2 ∈ C) (f : H) :
    lossRisk D (clippedMargin S w γ C H) f = marginRisk S w γ D f.val := by
  apply integral_congr_ae
  filter_upwards [clippedMargin_ae_all S hSc w hw γ hγ C hC hCb H D hDC] with z hz
  exact hz f

theorem clippedMargin_sample_all (S : Set E) (hSc : IsCompact S)
    (w : StrongDual ℝ E → E) (hw : IsOracle S w) (γ : ℝ) (hγ : 0 < γ)
    (C : Set (StrongDual ℝ E)) (hC : C.Nonempty) (hCb : Bornology.IsBounded C)
    (H : Set (X → StrongDual ℝ E)) (D : Measure (X × StrongDual ℝ E)) [IsProbabilityMeasure D]
    (hDC : ∀ᵐ z ∂D, z.2 ∈ C) (n : ℕ) :
    ∀ᵐ s : Fin n → X × StrongDual ℝ E ∂sampleLaw D n, ∀ i, ∀ f : H,
      clippedMargin S w γ C H f (s i) = marginLoss S w γ (f.val (s i).1) (s i).2 := by
  have hh : ∀ i : Fin n, ∀ᵐ s : Fin n → X × StrongDual ℝ E ∂sampleLaw D n, (s i).2 ∈ C :=
    fun i => (measurePreserving_eval (fun _ : Fin n => D) i).quasiMeasurePreserving.ae hDC
  filter_upwards [ae_all_iff.mpr hh] with s hs i f
  exact clippedMargin_eq_of_mem S hSc w hw γ hγ C hC hCb H f (s i) (hs i)

theorem clippedMargin_mean_ae (S : Set E) (hSc : IsCompact S)
    (w : StrongDual ℝ E → E) (hw : IsOracle S w) (γ : ℝ) (hγ : 0 < γ)
    (C : Set (StrongDual ℝ E)) (hC : C.Nonempty) (hCb : Bornology.IsBounded C)
    (H : Set (X → StrongDual ℝ E)) (D : Measure (X × StrongDual ℝ E)) [IsProbabilityMeasure D]
    (hDC : ∀ᵐ z ∂D, z.2 ∈ C) (n : ℕ) :
    ∀ᵐ s : Fin n → X × StrongDual ℝ E ∂sampleLaw D n, ∀ f : H,
      meanLoss (clippedMargin S w γ C H) f s = empMarginRisk S w γ f.val s := by
  filter_upwards [clippedMargin_sample_all S hSc w hw γ hγ C hC hCb H D hDC n] with s hs f
  unfold meanLoss empMarginRisk
  congr 1
  exact Finset.sum_congr rfl (fun i _ => hs i f)

theorem clippedMargin_signed_ae (S : Set E) (hSc : IsCompact S)
    (w : StrongDual ℝ E → E) (hw : IsOracle S w) (γ : ℝ) (hγ : 0 < γ)
    (C : Set (StrongDual ℝ E)) (hC : C.Nonempty) (hCb : Bornology.IsBounded C)
    (H : Set (X → StrongDual ℝ E)) (D : Measure (X × StrongDual ℝ E)) [IsProbabilityMeasure D]
    (hDC : ∀ᵐ z ∂D, z.2 ∈ C) (n : ℕ) (σ : Fin n → Bool) :
    lossSignedSup (clippedMargin S w γ C H) σ =ᵐ[sampleLaw D n] marginSignedSup S w γ H σ := by
  filter_upwards [clippedMargin_sample_all S hSc w hw γ hγ C hC hCb H D hDC n] with s hs
  unfold lossSignedSup marginSignedSup
  congr 1
  funext f
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [hs i f]

theorem clippedMargin_deviation_ae (S : Set E) (hSc : IsCompact S)
    (w : StrongDual ℝ E → E) (hw : IsOracle S w) (γ : ℝ) (hγ : 0 < γ)
    (C : Set (StrongDual ℝ E)) (hC : C.Nonempty) (hCb : Bornology.IsBounded C)
    (H : Set (X → StrongDual ℝ E)) (D : Measure (X × StrongDual ℝ E)) [IsProbabilityMeasure D]
    (hDC : ∀ᵐ z ∂D, z.2 ∈ C) (n : ℕ) :
    (fun s : Fin n → X × StrongDual ℝ E => lossDeviation D (clippedMargin S w γ C H) s)
      =ᵐ[sampleLaw D n] marginSupDeviation S w γ D H := by
  filter_upwards [clippedMargin_mean_ae S hSc w hw γ hγ C hC hCb H D hDC n] with s hs
  unfold lossDeviation marginSupDeviation
  congr 1
  funext f
  rw [clippedMargin_risk_eq S hSc w hw γ hγ C hC hCb H D hDC f, hs f]

theorem clippedMargin_rademacher_ae (S : Set E) (hSc : IsCompact S)
    (w : StrongDual ℝ E → E) (hw : IsOracle S w) (γ : ℝ) (hγ : 0 < γ)
    (C : Set (StrongDual ℝ E)) (hC : C.Nonempty) (hCb : Bornology.IsBounded C)
    (H : Set (X → StrongDual ℝ E)) (D : Measure (X × StrongDual ℝ E)) [IsProbabilityMeasure D]
    (hDC : ∀ᵐ z ∂D, z.2 ∈ C) (n : ℕ) :
    (fun s : Fin n → X × StrongDual ℝ E => lossRademacher (clippedMargin S w γ C H) s)
      =ᵐ[sampleLaw D n] empRademacherMargin S w γ H := by
  have hh := ae_all_iff.mpr (fun σ : Fin n → Bool =>
    clippedMargin_signed_ae S hSc w hw γ hγ C hC hCb H D hDC n σ)
  filter_upwards [hh] with s hs
  unfold lossRademacher empRademacherMargin
  congr 1
  exact Finset.sum_congr rfl (fun σ _ => hs σ)

end

theorem spoRisk_le_clippedMargin_risk (S : Set E) (hSc : IsCompact S)
    (w : StrongDual ℝ E → E) (hw : IsOracle S w) (γ : ℝ) (hγ : 0 < γ)
    (C : Set (StrongDual ℝ E)) (hC : C.Nonempty) (hCb : Bornology.IsBounded C)
    (H : Set (X → StrongDual ℝ E)) (D : Measure (X × StrongDual ℝ E)) [IsProbabilityMeasure D]
    (hDC : ∀ᵐ z ∂D, z.2 ∈ C)
    (hf : ∀ f ∈ H, Measurable f)
    (hℓ : ∀ f ∈ H, Measurable (fun z : X × StrongDual ℝ E => spoLoss w (f z.1) z.2))
    (f : H) : spoRisk D w f.val ≤ lossRisk D (clippedMargin S w γ C H) f := by
  have hM := costSet_bounds S hSc.isBounded w hw C hC hCb
  have hi : Integrable (fun z : X × StrongDual ℝ E => spoLoss w (f.val z.1) z.2) D := by
    apply Integrable.of_bound (hℓ f.val f.property).aestronglyMeasurable (omegaSet S C)
    filter_upwards [hDC] with z hz
    have hb := p71dfcbfc_bounds S hSc w hw (f.val z.1) z.2
    rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
    exact hb.2.trans (hM.2.2.1 z.2 hz)
  have hc := loss_integrable D (clippedMargin S w γ C H)
    (clippedMargin_measurable S hSc w hw γ C H hf hℓ) (omegaSet S C)
    (clippedMargin_bounds S w γ C H hM.1) f
  apply integral_mono_ae hi hc
  filter_upwards [clippedMargin_ae_all S hSc w hw γ hγ C hC hCb H D hDC] with z hz
  rw [hz f]
  exact (marginLoss_bounds S hSc w hw γ hγ (f.val z.1) z.2).1

end SPOBounds.Margin.Proof

end
-- END MODULE ClippedMargin

-- BEGIN MODULE FiniteAverage
section

namespace SPOBounds.Margin.Proof

open scoped BigOperators

noncomputable def fmean {ι : Type*} [Fintype ι] (f : ι → ℝ) : ℝ := 𝔼 i, f i

theorem fmean_eq {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    fmean f = (∑ i, f i) / Fintype.card ι := Fintype.expect_eq_sum_div_card f

theorem fmean_congr {ι : Type*} [Fintype ι] {f g : ι → ℝ} (h : ∀ i, f i = g i) :
    fmean f = fmean g := congrArg fmean (funext h)

@[simp] theorem fmean_const {ι : Type*} [Fintype ι] [Nonempty ι] (c : ℝ) :
    fmean (fun _ : ι => c) = c := Fintype.expect_const c

theorem fmean_add {ι : Type*} [Fintype ι] (f g : ι → ℝ) :
    fmean (fun i => f i + g i) = fmean f + fmean g := Finset.expect_add_distrib _ _ _

theorem fmean_sub {ι : Type*} [Fintype ι] (f g : ι → ℝ) :
    fmean (fun i => f i - g i) = fmean f - fmean g := Finset.expect_sub_distrib _ _ _

theorem fmean_mul {ι : Type*} [Fintype ι] (c : ℝ) (f : ι → ℝ) :
    fmean (fun i => c * f i) = c * fmean f := (Finset.mul_expect _ _ _).symm

theorem fmean_mul_right {ι : Type*} [Fintype ι] (f : ι → ℝ) (c : ℝ) :
    fmean (fun i => f i * c) = fmean f * c := (Finset.expect_mul _ _ _).symm

theorem fmean_div {ι : Type*} [Fintype ι] (f : ι → ℝ) (c : ℝ) :
    fmean (fun i => f i / c) = fmean f / c := (Finset.expect_div _ _ _).symm

theorem fmean_neg {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    fmean (fun i => -f i) = -fmean f := by
  simpa only [neg_one_mul] using fmean_mul (-1) f

theorem fmean_sum {ι κ : Type*} [Fintype ι] [Fintype κ] (f : ι → κ → ℝ) :
    fmean (fun i => ∑ j, f i j) = ∑ j, fmean (fun i => f i j) :=
  Finset.expect_sum_comm _ _ _

theorem fmean_nonneg {ι : Type*} [Fintype ι] {f : ι → ℝ} (h : ∀ i, 0 ≤ f i) :
    0 ≤ fmean f := Finset.expect_nonneg (fun i _ => h i)

theorem fmean_mono {ι : Type*} [Fintype ι] {f g : ι → ℝ} (h : ∀ i, f i ≤ g i) :
    fmean f ≤ fmean g := Finset.expect_le_expect (fun i _ => h i)

theorem fmean_equiv {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (f : κ → ℝ) :
    fmean (fun i => f (e i)) = fmean f := Fintype.expect_equiv e _ _ (fun _ => rfl)

theorem fmean_prod {ι κ : Type*} [Fintype ι] [Fintype κ] (f : ι × κ → ℝ) :
    fmean f = fmean (fun i => fmean (fun j => f (i,j))) := by
  unfold fmean
  rw [← Finset.univ_product_univ, Finset.expect_product]

theorem fmean_bool (f : Bool → ℝ) : fmean f = (f false + f true) / 2 := by
  rw [fmean_eq]
  simp [add_comm]

abbrev SignCube (n : ℕ) := Fin n → Bool

theorem cubeMean_eq {n : ℕ} (f : SignCube n → ℝ) :
    fmean f = (1 / 2^n : ℝ) * ∑ x, f x := by
  rw [fmean_eq]
  simp [SignCube, div_eq_mul_inv, mul_comm]

theorem cubeMean_cons {n : ℕ} (f : SignCube (n+1) → ℝ) :
    fmean f = (fmean (fun x => f (Fin.cons false x)) +
      fmean (fun x => f (Fin.cons true x))) / 2 := by
  have h := fmean_equiv (Fin.consEquiv (fun _ : Fin (n+1) => Bool)) f
  rw [fmean_prod, fmean_bool] at h
  exact h.symm

theorem cubeMean_zero (f : SignCube 0 → ℝ) : fmean f = f Fin.elim0 := by
  have he : f = fun _ => f Fin.elim0 := funext fun x => congrArg f (Subsingleton.elim x Fin.elim0)
  rw [he, fmean_const]

end SPOBounds.Margin.Proof

end
-- END MODULE FiniteAverage

-- BEGIN MODULE CubeGeometry
section

namespace SPOBounds.Margin.Proof

open scoped BigOperators

def cubeNeg {n : ℕ} (x : SignCube n) : SignCube n := fun i => !(x i)
def cubeFlip {n : ℕ} (i : Fin n) (x : SignCube n) : SignCube n := Function.update x i (!(x i))

theorem cubeNeg_involutive {n : ℕ} : Function.Involutive (@cubeNeg n) := by
  intro x
  funext i
  simp [cubeNeg]

def cubeNegEquiv (n : ℕ) : SignCube n ≃ SignCube n :=
  { toFun := cubeNeg, invFun := cubeNeg, left_inv := cubeNeg_involutive,
    right_inv := cubeNeg_involutive }

theorem cubeMean_negCube {n : ℕ} (f : SignCube n → ℝ) :
    fmean (fun x => f (cubeNeg x)) = fmean f := fmean_equiv (cubeNegEquiv n) f

theorem cubeMean_of_odd {n : ℕ} (f : SignCube n → ℝ)
    (h : ∀ x, f (cubeNeg x) = -f x) : fmean f = 0 := by
  have he := cubeMean_negCube f
  rw [fmean_congr h, fmean_neg] at he
  linarith

theorem cubeNeg_cons {n : ℕ} (b : Bool) (x : SignCube n) :
    cubeNeg (Fin.cons b x) = Fin.cons (!b) (cubeNeg x) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [cubeNeg]

theorem cubeFlip_zero {n : ℕ} (b : Bool) (x : SignCube n) :
    cubeFlip 0 (Fin.cons b x) = Fin.cons (!b) x := by
  simp only [cubeFlip, Fin.cons_zero, Fin.update_cons_zero]

theorem cubeFlip_succ {n : ℕ} (i : Fin n) (b : Bool) (x : SignCube n) :
    cubeFlip i.succ (Fin.cons b x) = Fin.cons b (cubeFlip i x) := by
  simp only [cubeFlip, Fin.cons_succ, Fin.cons_update]

noncomputable def cubeEvenPart {n : ℕ} (f : SignCube (n+1) → ℝ) (x : SignCube n) : ℝ :=
  (f (Fin.cons false x) + f (Fin.cons true x)) / 2
noncomputable def cubeOddPart {n : ℕ} (f : SignCube (n+1) → ℝ) (x : SignCube n) : ℝ :=
  (f (Fin.cons false x) - f (Fin.cons true x)) / 2

theorem cube_cons_false {n : ℕ} (f : SignCube (n+1) → ℝ) (x : SignCube n) :
    f (Fin.cons false x) = cubeEvenPart f x + cubeOddPart f x := by
  dsimp [cubeEvenPart, cubeOddPart]; ring

theorem cube_cons_true {n : ℕ} (f : SignCube (n+1) → ℝ) (x : SignCube n) :
    f (Fin.cons true x) = cubeEvenPart f x - cubeOddPart f x := by
  dsimp [cubeEvenPart, cubeOddPart]; ring

theorem cube_parts_parity {n : ℕ} (f : SignCube (n+1) → ℝ)
    (h : ∀ x, f (cubeNeg x) = f x) :
    (∀ x, cubeEvenPart f (cubeNeg x) = cubeEvenPart f x) ∧
    (∀ x, cubeOddPart f (cubeNeg x) = -cubeOddPart f x) := by
  have hf (x : SignCube n) : f (Fin.cons false (cubeNeg x)) = f (Fin.cons true x) := by
    simpa only [cubeNeg_cons, Bool.not_true] using h (Fin.cons true x)
  have ht (x : SignCube n) : f (Fin.cons true (cubeNeg x)) = f (Fin.cons false x) := by
    simpa only [cubeNeg_cons, Bool.not_false] using h (Fin.cons false x)
  constructor
  · intro x
    dsimp [cubeEvenPart]
    rw [hf, ht]
    ring
  · intro x
    dsimp [cubeOddPart]
    rw [hf, ht]
    ring

end SPOBounds.Margin.Proof

end
-- END MODULE CubeGeometry

-- BEGIN MODULE CubeEnergy
section

namespace SPOBounds.Margin.Proof

open scoped BigOperators

noncomputable def cubeGrad {n : ℕ} (f : SignCube n → ℝ) (i : Fin n) (x : SignCube n) : ℝ :=
  (f x - f (cubeFlip i x)) / 2
noncomputable def cubeEnergy {n : ℕ} (f : SignCube n → ℝ) : ℝ :=
  ∑ i, fmean (fun x => (cubeGrad f i x)^2)
noncomputable def cubeVariance {n : ℕ} (f : SignCube n → ℝ) : ℝ :=
  fmean (fun x => (f x)^2) - (fmean f)^2

theorem cubeEnergy_nonneg {n : ℕ} (f : SignCube n → ℝ) : 0 ≤ cubeEnergy f :=
  Finset.sum_nonneg fun i _ => fmean_nonneg (fun x => sq_nonneg (cubeGrad f i x))

theorem cubeMean_evenPart {n : ℕ} (f : SignCube (n+1) → ℝ) :
    fmean (cubeEvenPart f) = fmean f := by
  rw [cubeMean_cons f]
  exact (fmean_div _ 2).trans (congrArg (fun z : ℝ => z/2) (fmean_add _ _))

theorem cubeMean_pair_square {n : ℕ} (f g : SignCube n → ℝ) :
    (fmean (fun x => (f x + g x)^2) + fmean (fun x => (f x - g x)^2))/2 =
      fmean (fun x => (f x)^2) + fmean (fun x => (g x)^2) := by
  have he : fmean (fun x => (f x + g x)^2) + fmean (fun x => (f x - g x)^2) =
      2 * (fmean (fun x => (f x)^2) + fmean (fun x => (g x)^2)) := by
    rw [← fmean_add (fun x => (f x)^2) (fun x => (g x)^2), ← fmean_mul, ← fmean_add]
    apply fmean_congr
    intro x
    ring
  linarith

theorem cubeMean_square_cons {n : ℕ} (f : SignCube (n+1) → ℝ) :
    fmean (fun x => (f x)^2) =
      fmean (fun x => (cubeEvenPart f x)^2) + fmean (fun x => (cubeOddPart f x)^2) := by
  rw [cubeMean_cons]
  simp_rw [cube_cons_false, cube_cons_true]
  exact cubeMean_pair_square _ _

theorem cubeVariance_cons {n : ℕ} (f : SignCube (n+1) → ℝ) :
    cubeVariance f = cubeVariance (cubeEvenPart f) + fmean (fun x => (cubeOddPart f x)^2) := by
  unfold cubeVariance
  rw [cubeMean_square_cons, cubeMean_evenPart]
  ring

theorem cubeGrad_zero_sq {n : ℕ} (f : SignCube (n+1) → ℝ) (b : Bool) (x : SignCube n) :
    (cubeGrad f 0 (Fin.cons b x))^2 = (cubeOddPart f x)^2 := by
  cases b <;> simp only [cubeGrad, cubeFlip_zero, Bool.not_false, Bool.not_true, cubeOddPart]; ring

theorem cubeGrad_succ_false {n : ℕ} (f : SignCube (n+1) → ℝ) (i : Fin n) (x : SignCube n) :
    cubeGrad f i.succ (Fin.cons false x) =
      cubeGrad (cubeEvenPart f) i x + cubeGrad (cubeOddPart f) i x := by
  simp only [cubeGrad, cubeFlip_succ]
  rw [cube_cons_false f x, cube_cons_false f (cubeFlip i x)]
  ring

theorem cubeGrad_succ_true {n : ℕ} (f : SignCube (n+1) → ℝ) (i : Fin n) (x : SignCube n) :
    cubeGrad f i.succ (Fin.cons true x) =
      cubeGrad (cubeEvenPart f) i x - cubeGrad (cubeOddPart f) i x := by
  simp only [cubeGrad, cubeFlip_succ]
  rw [cube_cons_true f x, cube_cons_true f (cubeFlip i x)]
  ring

theorem cubeEnergy_cons {n : ℕ} (f : SignCube (n+1) → ℝ) :
    cubeEnergy f = cubeEnergy (cubeEvenPart f) + cubeEnergy (cubeOddPart f) +
      fmean (fun x => (cubeOddPart f x)^2) := by
  have hz : fmean (fun x => (cubeGrad f 0 x)^2) =
      fmean (fun x => (cubeOddPart f x)^2) := by
    rw [cubeMean_cons]
    simp_rw [cubeGrad_zero_sq]
    ring
  have hs (i : Fin n) : fmean (fun x => (cubeGrad f i.succ x)^2) =
      fmean (fun x => (cubeGrad (cubeEvenPart f) i x)^2) +
      fmean (fun x => (cubeGrad (cubeOddPart f) i x)^2) := by
    rw [cubeMean_cons]
    simp_rw [cubeGrad_succ_false, cubeGrad_succ_true]
    exact cubeMean_pair_square _ _
  unfold cubeEnergy
  rw [Fin.sum_univ_succ, hz]
  simp_rw [hs]
  rw [Finset.sum_add_distrib]
  ring

theorem cubeVariance_zero (f : SignCube 0 → ℝ) : cubeVariance f = 0 := by
  simp only [cubeVariance, cubeMean_zero, sub_self]

theorem cube_poincare (n : ℕ) (f : SignCube n → ℝ) : cubeVariance f ≤ cubeEnergy f := by
  induction n with
  | zero => simp only [cubeVariance_zero, cubeEnergy, Fin.sum_univ_zero, le_refl]
  | succ n ih =>
    rw [cubeVariance_cons, cubeEnergy_cons]
    have h := ih (cubeEvenPart f)
    have h0 := cubeEnergy_nonneg (cubeOddPart f)
    linarith

theorem cube_even_poincare (n : ℕ) (f : SignCube n → ℝ)
    (he : ∀ x, f (cubeNeg x) = f x) : cubeVariance f ≤ cubeEnergy f / 2 := by
  induction n with
  | zero => simp only [cubeVariance_zero, cubeEnergy, Fin.sum_univ_zero, zero_div, le_refl]
  | succ n ih =>
    obtain ⟨hu, hv⟩ := cube_parts_parity f he
    have h1 := ih (cubeEvenPart f) hu
    have h2 := cube_poincare n (cubeOddPart f)
    have hm := cubeMean_of_odd (cubeOddPart f) hv
    simp only [cubeVariance, hm, zero_pow (by decide : 2 ≠ 0), sub_zero] at h2
    rw [cubeVariance_cons, cubeEnergy_cons]
    linarith

end SPOBounds.Margin.Proof

end
-- END MODULE CubeEnergy

-- BEGIN MODULE SharpKhintchine
section

namespace SPOBounds.Margin.Proof

open scoped BigOperators

def cubeSign (b : Bool) : ℝ := if b then 1 else -1
@[simp] theorem cubeSign_not (b : Bool) : cubeSign (!b) = -cubeSign b := by cases b <;> norm_num [cubeSign]
@[simp] theorem abs_cubeSign (b : Bool) : |cubeSign b| = 1 := by cases b <;> norm_num [cubeSign]
noncomputable def signSum {n : ℕ} (a : Fin n → ℝ) (x : SignCube n) : ℝ :=
  ∑ i, a i * cubeSign (x i)

theorem signSum_negCube {n : ℕ} (a : Fin n → ℝ) (x : SignCube n) :
    signSum a (cubeNeg x) = -signSum a x := by
  simp [signSum, cubeNeg, Finset.sum_neg_distrib]

theorem signSum_cons {n : ℕ} (a : Fin (n+1) → ℝ) (b : Bool) (x : SignCube n) :
    signSum a (Fin.cons b x) = a 0 * cubeSign b + signSum (fun i => a i.succ) x := by
  simp [signSum, Fin.sum_univ_succ]

theorem signSum_evenPart {n : ℕ} (a : Fin (n+1) → ℝ) :
    cubeEvenPart (signSum a) = signSum (fun i => a i.succ) := by
  funext x
  simp only [cubeEvenPart, signSum_cons]
  norm_num [cubeSign]
  ring

theorem signSum_oddPart {n : ℕ} (a : Fin (n+1) → ℝ) :
    cubeOddPart (signSum a) = fun _ => -a 0 := by
  funext x
  simp only [cubeOddPart, signSum_cons]
  norm_num [cubeSign]
  ring

theorem signSum_second_moment (n : ℕ) (a : Fin n → ℝ) :
    fmean (fun x => (signSum a x)^2) = ∑ i, (a i)^2 := by
  induction n with
  | zero => simp [signSum, fmean_const]
  | succ n ih =>
    rw [cubeMean_square_cons, signSum_evenPart, signSum_oddPart]
    simp only [neg_sq, fmean_const, ih, Fin.sum_univ_succ]
    ring

theorem signSum_flip {n : ℕ} (a : Fin n → ℝ) (i : Fin n) (x : SignCube n) :
    signSum a x - signSum a (cubeFlip i x) = 2 * a i * cubeSign (x i) := by
  unfold signSum
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
  · simp only [cubeFlip, Function.update_self, cubeSign_not]
    ring
  · intro j _ hji
    simp [cubeFlip, hji]
  · simp

theorem cubeGrad_abs_bound {n : ℕ} (a : Fin n → ℝ) (i : Fin n) (x : SignCube n) :
    |cubeGrad (fun y => |signSum a y|) i x| ≤ |a i| := by
  change |(|signSum a x| - |signSum a (cubeFlip i x)|) / 2| ≤ |a i|
  rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
  calc
    |(|signSum a x| - |signSum a (cubeFlip i x)|)| / 2 ≤
        |signSum a x - signSum a (cubeFlip i x)| / 2 :=
      div_le_div_of_nonneg_right (abs_abs_sub_abs_le_abs_sub _ _) (by norm_num)
    _ = |a i| := by rw [signSum_flip]; simp [abs_mul]

theorem signSum_abs_energy {n : ℕ} (a : Fin n → ℝ) :
    cubeEnergy (fun x => |signSum a x|) ≤ ∑ i, (a i)^2 := by
  apply Finset.sum_le_sum
  intro i _
  calc
    fmean (fun x => (cubeGrad (fun y => |signSum a y|) i x)^2) ≤
        fmean (fun _ : SignCube n => (a i)^2) := by
      apply fmean_mono
      intro x
      have h := pow_le_pow_left₀ (abs_nonneg _) (cubeGrad_abs_bound a i x) 2
      simpa only [sq_abs] using h
    _ = (a i)^2 := fmean_const _

theorem sharp_khintchine_sq (n : ℕ) (a : Fin n → ℝ) :
    (∑ i, (a i)^2) ≤ 2 * (fmean (fun x => |signSum a x|))^2 := by
  have he : ∀ x, |signSum a (cubeNeg x)| = |signSum a x| := by
    intro x
    rw [signSum_negCube, abs_neg]
  have hp := cube_even_poincare n (fun x => |signSum a x|) he
  have hb := signSum_abs_energy a
  simp only [cubeVariance, sq_abs, signSum_second_moment] at hp
  linarith

theorem sharp_khintchine (n : ℕ) (a : Fin n → ℝ) :
    Real.sqrt (∑ i, (a i)^2) ≤ Real.sqrt 2 * fmean (fun x => |signSum a x|) := by
  have hm : 0 ≤ fmean (fun x => |signSum a x|) := fmean_nonneg (fun _ => abs_nonneg _)
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hm)).mp
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), mul_pow,
    Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  exact sharp_khintchine_sq n a

end SPOBounds.Margin.Proof

end
-- END MODULE SharpKhintchine

-- BEGIN MODULE VectorRowContraction
section

namespace SPOBounds.Margin.Proof

open scoped BigOperators

theorem signSum_sub {d : ℕ} (a b : Fin d → ℝ) (x : SignCube d) :
    signSum (fun j => a j - b j) x = signSum a x - signSum b x := by
  simp [signSum, sub_mul, Finset.sum_sub_distrib]

theorem finite_sup_le {ι : Type*} [Finite ι] (f : ι → ℝ) (i : ι) : f i ≤ ⨆ j, f j :=
  le_ciSup (Set.finite_range f).bddAbove i

theorem vector_row_contraction {ι : Type*} [Fintype ι] [Nonempty ι] {d : ℕ}
    (a ψ : ι → ℝ) (v : ι → Fin d → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hψ : ∀ s t, |ψ s - ψ t| ≤ L * Real.sqrt (∑ j, (v s j - v t j)^2)) :
    fmean (fun b : Bool => ⨆ s, a s + cubeSign b * ψ s) ≤
      fmean (fun x : SignCube d => ⨆ s, a s + (Real.sqrt 2 * L) * signSum (v s) x) := by
  classical
  obtain ⟨p, hp⟩ := exists_eq_ciSup_of_finite (f := fun s => a s + ψ s)
  obtain ⟨q, hq⟩ := exists_eq_ciSup_of_finite (f := fun s => a s - ψ s)
  let K := Real.sqrt 2 * L
  let P : SignCube d → ℝ := fun x => ⨆ s, a s + K * signSum (v s) x
  let Q : SignCube d → ℝ := fun x => ⨆ s, a s - K * signSum (v s) x
  have hscalar : 2 * fmean (fun b : Bool => ⨆ s, a s + cubeSign b * ψ s) =
      a p + a q + ψ p - ψ q := by
    rw [fmean_bool]
    norm_num only [cubeSign, Bool.false_eq_true, ↓reduceIte, if_false, if_true, neg_one_mul, one_mul,
      ← sub_eq_add_neg, ← hp, ← hq]
    ring
  have hQ : fmean Q = fmean P := by
    calc
      fmean Q = fmean (fun x => P (cubeNeg x)) := by
        apply fmean_congr
        intro x
        dsimp [P, Q]
        congr 1
        funext s
        rw [signSum_negCube]
        ring
      _ = fmean P := cubeMean_negCube P
  have hpoint (x : SignCube d) : a p + a q + K * |signSum (fun j => v p j - v q j) x| ≤ P x + Q x := by
    have hpp : a p + K * signSum (v p) x ≤ P x := finite_sup_le (fun s => a s + K * signSum (v s) x) p
    have hpq : a q + K * signSum (v q) x ≤ P x := finite_sup_le (fun s => a s + K * signSum (v s) x) q
    have hqp : a p - K * signSum (v p) x ≤ Q x := finite_sup_le (fun s => a s - K * signSum (v s) x) p
    have hqq : a q - K * signSum (v q) x ≤ Q x := finite_sup_le (fun s => a s - K * signSum (v s) x) q
    rw [signSum_sub]
    by_cases h : 0 ≤ signSum (v p) x - signSum (v q) x
    · rw [abs_of_nonneg h]
      linarith
    · rw [abs_of_neg (lt_of_not_ge h)]
      linarith
  have havg := fmean_mono hpoint
  simp only [fmean_add, fmean_const, fmean_mul, hQ] at havg
  have hsize : L * Real.sqrt (∑ j, (v p j - v q j)^2) ≤
      K * fmean (fun x => |signSum (fun j => v p j - v q j) x|) := by
    have h := mul_le_mul_of_nonneg_left (sharp_khintchine d (fun j => v p j - v q j)) hL
    dsimp [K]
    nlinarith [h]
  have hdiff : ψ p - ψ q ≤ L * Real.sqrt (∑ j, (v p j - v q j)^2) :=
    (le_abs_self _).trans (hψ p q)
  change _ ≤ fmean P
  linarith

end SPOBounds.Margin.Proof

end
-- END MODULE VectorRowContraction

-- BEGIN MODULE FiniteProductMean
section

namespace SPOBounds.Margin.Proof

theorem fmean_comm {ι κ : Type*} [Fintype ι] [Fintype κ] (f : ι → κ → ℝ) :
    fmean (fun i => fmean (fun j => f i j)) = fmean (fun j => fmean (fun i => f i j)) :=
  Finset.expect_comm _ _ _

theorem fmean_pi_cons {α : Type*} [Fintype α] {n : ℕ} (f : (Fin (n+1) → α) → ℝ) :
    fmean f = fmean (fun b : α => fmean (fun x : Fin n → α => f (Fin.cons b x))) := by
  have h := fmean_equiv (Fin.consEquiv (fun _ : Fin (n+1) => α)) f
  rw [fmean_prod] at h
  exact h.symm

theorem fmean_pi_zero {α : Type*} (f : (Fin 0 → α) → ℝ) :
    fmean f = f Fin.elim0 := by
  have he : f = fun _ => f Fin.elim0 := funext fun x => congrArg f (Subsingleton.elim x Fin.elim0)
  rw [he, fmean_const]

end SPOBounds.Margin.Proof

end
-- END MODULE FiniteProductMean

-- BEGIN MODULE FiniteVectorContraction
section

namespace SPOBounds.Margin.Proof

open scoped BigOperators

theorem finite_vector_contraction {ι : Type*} [Fintype ι] [Nonempty ι]
    (n d : ℕ) (a : ι → ℝ) (ψ : Fin n → ι → ℝ) (v : Fin n → ι → Fin d → ℝ)
    (L : ℝ) (hL : 0 ≤ L)
    (hψ : ∀ i s t, |ψ i s - ψ i t| ≤ L * Real.sqrt (∑ j, (v i s j - v i t j)^2)) :
    fmean (fun ε : SignCube n => ⨆ s, a s + ∑ i, cubeSign (ε i) * ψ i s) ≤
      fmean (fun ξ : Fin n → SignCube d =>
        ⨆ s, a s + (Real.sqrt 2 * L) * ∑ i, signSum (v i s) (ξ i)) := by
  induction n generalizing a with
  | zero =>
    simp only [Fin.sum_univ_zero, mul_zero, add_zero, fmean_const, le_refl]
  | succ n ih =>
    let K := Real.sqrt 2 * L
    let Ψ : Fin n → ι → ℝ := fun i => ψ i.succ
    let V : Fin n → ι → Fin d → ℝ := fun i => v i.succ
    have htail : ∀ i s t, |Ψ i s - Ψ i t| ≤ L * Real.sqrt (∑ j, (V i s j - V i t j)^2) :=
      fun i s t => hψ i.succ s t
    have hl : fmean (fun ε : SignCube (n+1) => ⨆ s, a s + ∑ i, cubeSign (ε i) * ψ i s) =
        fmean (fun ε : SignCube n => fmean (fun b : Bool =>
          ⨆ s, (a s + ∑ i, cubeSign (ε i) * Ψ i s) + cubeSign b * ψ 0 s)) := by
      rw [fmean_pi_cons, fmean_comm]
      apply fmean_congr
      intro ε
      apply fmean_congr
      intro b
      congr 1
      funext s
      simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Ψ]
      ring
    rw [hl]
    calc
      _ ≤ fmean (fun ε : SignCube n => fmean (fun x : SignCube d =>
          ⨆ s, (a s + ∑ i, cubeSign (ε i) * Ψ i s) + K * signSum (v 0 s) x)) := by
        apply fmean_mono
        intro ε
        exact vector_row_contraction _ (ψ 0) (v 0) L hL (hψ 0)
      _ = fmean (fun x : SignCube d => fmean (fun ε : SignCube n =>
          ⨆ s, (a s + K * signSum (v 0 s) x) + ∑ i, cubeSign (ε i) * Ψ i s)) := by
        rw [fmean_comm]
        apply fmean_congr
        intro x
        apply fmean_congr
        intro ε
        congr 1
        funext s
        ring
      _ ≤ fmean (fun x : SignCube d => fmean (fun ξ : Fin n → SignCube d =>
          ⨆ s, (a s + K * signSum (v 0 s) x) + K * ∑ i, signSum (V i s) (ξ i))) := by
        apply fmean_mono
        intro x
        exact ih (fun s => a s + K * signSum (v 0 s) x) Ψ V htail
      _ = fmean (fun ξ : Fin (n+1) → SignCube d =>
          ⨆ s, a s + (Real.sqrt 2 * L) * ∑ i, signSum (v i s) (ξ i)) := by
        rw [fmean_pi_cons]
        apply fmean_congr
        intro x
        apply fmean_congr
        intro ξ
        congr 1
        funext s
        simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, V, K]
        ring

end SPOBounds.Margin.Proof

end
-- END MODULE FiniteVectorContraction

-- BEGIN MODULE ClassVectorContraction
section

namespace SPOBounds.Margin.Proof

open scoped BigOperators

theorem class_vector_contraction {ι : Type*} [Nonempty ι] (n d : ℕ)
    (ψ : Fin n → ι → ℝ) (v : Fin n → ι → Fin d → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hψ : ∀ i s t, |ψ i s - ψ i t| ≤ L * Real.sqrt (∑ j, (v i s j - v i t j)^2))
    (hB : ∀ ξ : Fin n → SignCube d, BddAbove (Set.range fun s : ι => ∑ i, signSum (v i s) (ξ i))) :
    fmean (fun ε : SignCube n => ⨆ s, ∑ i, cubeSign (ε i) * ψ i s) ≤
      Real.sqrt 2 * L * fmean (fun ξ : Fin n → SignCube d => ⨆ s, ∑ i, signSum (v i s) (ξ i)) := by
  classical
  let S : SignCube n → ℝ := fun ε => ⨆ s, ∑ i, cubeSign (ε i) * ψ i s
  let T : (Fin n → SignCube d) → ℝ := fun ξ => ⨆ s, ∑ i, signSum (v i s) (ξ i)
  let K := Real.sqrt 2 * L
  have hK : 0 ≤ K := mul_nonneg (Real.sqrt_nonneg _) hL
  change fmean S ≤ K * fmean T
  by_contra hnot
  let δ := (fmean S - K * fmean T) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have happ (ε : SignCube n) : ∃ s : ι, S ε - δ < ∑ i, cubeSign (ε i) * ψ i s := by
    apply exists_lt_of_lt_ciSup
    change S ε - δ < S ε
    linarith
  choose q hq using happ
  have hfinite := finite_vector_contraction n d (fun _ : SignCube n => (0 : ℝ))
    (fun i ε => ψ i (q ε)) (fun i ε => v i (q ε)) L hL (fun i ε η => hψ i (q ε) (q η))
  simp only [zero_add] at hfinite
  have hleft : fmean S ≤
      fmean (fun ε : SignCube n => ⨆ η : SignCube n, ∑ i, cubeSign (ε i) * ψ i (q η)) + δ := by
    calc
      fmean S ≤ fmean (fun ε : SignCube n =>
          (⨆ η : SignCube n, ∑ i, cubeSign (ε i) * ψ i (q η)) + δ) := by
        apply fmean_mono
        intro ε
        have hh := finite_sup_le (fun η : SignCube n => ∑ i, cubeSign (ε i) * ψ i (q η)) ε
        have h := hq ε
        linarith
      _ = _ := by rw [fmean_add, fmean_const]
  have hright : fmean (fun ξ : Fin n → SignCube d =>
      ⨆ η : SignCube n, K * ∑ i, signSum (v i (q η)) (ξ i)) ≤ K * fmean T := by
    calc
      _ ≤ fmean (fun ξ : Fin n → SignCube d => K * T ξ) := by
        apply fmean_mono
        intro ξ
        apply ciSup_le
        intro η
        exact mul_le_mul_of_nonneg_left (le_ciSup (hB ξ) (q η)) hK
      _ = _ := fmean_mul _ _
  change _ ≤ fmean (fun ξ : Fin n → SignCube d =>
    ⨆ η : SignCube n, K * ∑ i, signSum (v i (q η)) (ξ i)) at hfinite
  dsimp [δ] at hleft
  linarith

end SPOBounds.Margin.Proof

end
-- END MODULE ClassVectorContraction

-- BEGIN MODULE DualCoordinates
section

namespace SPOBounds.Margin.Proof

open scoped BigOperators InnerProductSpace

noncomputable def dualCoords {d : ℕ} (f : StrongDual ℝ (EuclideanSpace ℝ (Fin d))) : Fin d → ℝ :=
  fun j => (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm f j

theorem dualCoords_norm_sub {d : ℕ} (f g : StrongDual ℝ (EuclideanSpace ℝ (Fin d))) :
    ‖f-g‖ = Real.sqrt (∑ j, (dualCoords f j - dualCoords g j)^2) := by
  rw [← (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm.norm_map (f-g),
    map_sub, EuclideanSpace.norm_eq]
  simp only [PiLp.sub_apply, Real.norm_eq_abs, sq_abs, dualCoords]

theorem dualCoords_signSum {d : ℕ} (f : StrongDual ℝ (EuclideanSpace ℝ (Fin d))) (x : SignCube d) :
    signSum (dualCoords f) x = f (signVec x) := by
  rw [← InnerProductSpace.toDual_symm_apply]
  simp only [PiLp.inner_apply, Real.inner_apply, signSum, dualCoords, signVec, cubeSign]

end SPOBounds.Margin.Proof

end
-- END MODULE DualCoordinates

-- BEGIN MODULE VectorContraction
section

namespace SPOBounds.Margin.Proof

open scoped BigOperators

theorem maurer_vector_contraction_bounded {d n : ℕ} {X : Type*}
    (H : Set (X → StrongDual ℝ (EuclideanSpace ℝ (Fin d)))) (hH : H.Nonempty)
    (x : Fin n → X) (Φ : Fin n → StrongDual ℝ (EuclideanSpace ℝ (Fin d)) → ℝ)
    (L : ℝ) (hL : 0 ≤ L)
    (hΦ : ∀ i u v, |Φ i u - Φ i v| ≤ L * ‖u-v‖)
    (hB : ∀ σ : Fin n → Fin d → Bool,
      BddAbove (Set.range fun f : H => (1/n : ℝ) * ∑ i, (f : X → StrongDual ℝ (EuclideanSpace ℝ (Fin d))) (x i) (signVec (σ i)))) :
    (1/2^n : ℝ) * ∑ τ : Fin n → Bool,
      ⨆ f : H, (1/n : ℝ) * ∑ i,
        (if τ i then (1:ℝ) else -1) * Φ i ((f : X → StrongDual ℝ (EuclideanSpace ℝ (Fin d))) (x i))
      ≤ Real.sqrt 2 * L * empRademacherMulti H x := by
  classical
  let : Nonempty H := ⟨⟨hH.choose, hH.choose_spec⟩⟩
  let k : ℝ := 1/n
  have hk : 0 ≤ k := by dsimp [k]; positivity
  let ψ : Fin n → H → ℝ := fun i f => k * Φ i (f.val (x i))
  let v : Fin n → H → Fin d → ℝ := fun i f => dualCoords (k • f.val (x i))
  have hψ : ∀ i f g, |ψ i f - ψ i g| ≤ L * Real.sqrt (∑ j, (v i f j - v i g j)^2) := by
    intro i f g
    dsimp only [ψ, v]
    rw [← dualCoords_norm_sub, ← smul_sub k (f.val (x i)) (g.val (x i)), norm_smul, Real.norm_eq_abs, abs_of_nonneg hk,
      ← mul_sub, abs_mul, abs_of_nonneg hk]
    have h := mul_le_mul_of_nonneg_left (hΦ i (f.val (x i)) (g.val (x i))) hk
    nlinarith [h]
  have hv (σ : Fin n → SignCube d) (f : H) : ∑ i, signSum (v i f) (σ i) =
      k * ∑ i, f.val (x i) (signVec (σ i)) := by
    simp only [v, dualCoords_signSum, smul_apply, smul_eq_mul, Finset.mul_sum]
  have hs (τ : SignCube n) (f : H) : ∑ i, cubeSign (τ i) * ψ i f =
      k * ∑ i, cubeSign (τ i) * Φ i (f.val (x i)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [ψ]
    ring
  have hb : ∀ σ : Fin n → SignCube d,
      BddAbove (Set.range fun f : H => ∑ i, signSum (v i f) (σ i)) := by
    intro σ
    simp_rw [hv]
    exact hB σ
  have hc := class_vector_contraction n d ψ v L hL hψ hb
  simp_rw [hv, hs] at hc
  have hcard : (Fintype.card (Fin n → SignCube d) : ℝ) = 2^(n*d) := by
    simp [SignCube, pow_mul, Nat.mul_comm]
  have hmean : fmean (multiSignedSup H x) = empRademacherMulti H x := by
    rw [fmean_eq, hcard]
    unfold empRademacherMulti
    rw [div_eq_mul_inv, one_div, mul_comm]
  change fmean (fun τ : SignCube n => ⨆ f : H, k * ∑ i, cubeSign (τ i) * Φ i (f.val (x i))) ≤
    Real.sqrt 2 * L * fmean (multiSignedSup H x) at hc
  rw [cubeMean_eq, hmean] at hc
  simpa only [cubeSign] using hc

end SPOBounds.Margin.Proof

end
-- END MODULE VectorContraction

-- BEGIN MODULE MarginComplexity
section

set_option autoImplicit false

open MeasureTheory

namespace SPOBounds.Margin.Proof

theorem margin_empirical_le {d n : ℕ} {X : Type*}
    (S : Set (EuclideanSpace ℝ (Fin d))) (hS : S.Nonempty) (hSc : IsCompact S)
    (hSv : Convex ℝ S) (hSnt : S.Nontrivial)
    (w : StrongDual ℝ (EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d)) (hw : IsOracle S w)
    (μ : ℝ) (hμ : 0 < μ) (hstr : StrengthProperty S μ w) (γ : ℝ) (hγ : 0 < γ)
    (C : Set (StrongDual ℝ (EuclideanSpace ℝ (Fin d)))) (hC : C.Nonempty)
    (hCb : Bornology.IsBounded C)
    (H : Set (X → StrongDual ℝ (EuclideanSpace ℝ (Fin d)))) (hH : H.Nonempty)
    (s : Fin n → X × StrongDual ℝ (EuclideanSpace ℝ (Fin d))) (hs : ∀ i, (s i).2 ∈ C)
    (hB : ∀ σ : Fin n → Fin d → Bool,
      BddAbove (Set.range fun f : H => (1 / n : ℝ) *
        ∑ i, f.val (s i).1 (signVec (σ i)))) :
    empRademacherMargin S w γ H s ≤
      Real.sqrt 2 * ((rhoSet C + μ * omegaSet S C) / (γ * μ)) *
        empRademacherMulti H (fun i => (s i).1) := by
  have hb := costSet_bounds S hSc.isBounded w hw C hC hCb
  let L := (rhoSet C + μ * omegaSet S C) / (γ * μ)
  have hL : 0 ≤ L := div_nonneg (add_nonneg hb.2.1 (mul_nonneg hμ.le hb.1)) (mul_pos hγ hμ).le
  have hΦ : ∀ i u v, |marginLoss S w γ u (s i).2 - marginLoss S w γ v (s i).2| ≤
      L * ‖u - v‖ := by
    intro i u v
    have h := checked_margin_loss_lipschitz S hS hSc hSv hSnt w hw μ hμ hstr γ hγ (s i).2 u v
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    apply div_le_div_of_nonneg_right _ (mul_pos hγ hμ).le
    exact add_le_add (hb.2.2.2 _ (hs i)) (mul_le_mul_of_nonneg_left (hb.2.2.1 _ (hs i)) hμ.le)
  exact maurer_vector_contraction_bounded H hH (fun i => (s i).1)
    (fun i u => marginLoss S w γ u (s i).2) L hL hΦ hB

theorem expected_margin_complexity_le {d : ℕ} {X : Type*} [MeasurableSpace X]
    [MeasurableSpace (StrongDual ℝ (EuclideanSpace ℝ (Fin d)))]
    (S : Set (EuclideanSpace ℝ (Fin d))) (hS : S.Nonempty) (hSc : IsCompact S)
    (hSv : Convex ℝ S) (hSnt : S.Nontrivial)
    (w : StrongDual ℝ (EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d)) (hw : IsOracle S w)
    (μ : ℝ) (hμ : 0 < μ) (hstr : StrengthProperty S μ w) (γ : ℝ) (hγ : 0 < γ)
    (C : Set (StrongDual ℝ (EuclideanSpace ℝ (Fin d)))) (hC : C.Nonempty)
    (hCb : Bornology.IsBounded C)
    (D : Measure (X × StrongDual ℝ (EuclideanSpace ℝ (Fin d)))) [IsProbabilityMeasure D]
    (hDC : ∀ᵐ z ∂D, z.2 ∈ C)
    (H : Set (X → StrongDual ℝ (EuclideanSpace ℝ (Fin d)))) (hH : H.Nonempty)
    (n : ℕ)
    (hB : ∀ᵐ s ∂sampleLaw D n, ∀ σ : Fin n → Fin d → Bool,
      BddAbove (Set.range fun f : H => (1 / n : ℝ) * ∑ i, f.val (s i).1 (signVec (σ i))))
    (hI : Integrable (fun s => empRademacherMargin S w γ H s) (sampleLaw D n))
    (hV : Integrable (fun s : Fin n → X × StrongDual ℝ (EuclideanSpace ℝ (Fin d)) =>
      empRademacherMulti H (fun i => (s i).1)) (sampleLaw D n)) :
    (∫ s, empRademacherMargin S w γ H s ∂sampleLaw D n) ≤
      Real.sqrt 2 * ((rhoSet C + μ * omegaSet S C) / (γ * μ)) * expRademacherMulti D H n := by
  have hs : ∀ᵐ s ∂sampleLaw D n, ∀ i, (s i).2 ∈ C :=
    ae_all_iff.mpr (fun i => (measurePreserving_eval (fun _ : Fin n => D) i).quasiMeasurePreserving.ae hDC)
  have hle : ∀ᵐ s ∂sampleLaw D n, empRademacherMargin S w γ H s ≤
      (Real.sqrt 2 * ((rhoSet C + μ * omegaSet S C) / (γ * μ))) *
        empRademacherMulti H (fun i => (s i).1) := by
    filter_upwards [hs, hB] with s hs hB
    exact margin_empirical_le S hS hSc hSv hSnt w hw μ hμ hstr γ hγ C hC hCb H hH s hs hB
  have hi := integral_mono_ae hI (hV.const_mul _) hle
  rw [integral_const_mul] at hi
  exact hi

end SPOBounds.Margin.Proof

end
-- END MODULE MarginComplexity

-- BEGIN MODULE MarginGeneralization
section

set_option autoImplicit false
open MeasureTheory

namespace SPOBounds.Margin

/-- **Theorem 4, second display** (arXiv:1905.11488v3, pp. 19–20). ℓ₂ set-up: `E = ℝ^d` with the
Euclidean norm, costs and predictions in its dual (operator norm = Euclidean norm), with the Borel
σ-algebra. Let `S` be nonempty, compact, convex and not a singleton, `w` any oracle, and suppose
`S` satisfies the strength property with parameter `μ > 0`. Fix `γ > 0`, a nonempty bounded set
`C` containing the cost vector almost surely, and any `δ > 0`. Then with probability at least
`1 − δ` over an i.i.d. sample of size `n` from `D`, every `f ∈ H` satisfies
`R_SPO(f) ≤ R̂^γ_SPO(f) + ((2√2 ρ₂(C) + 2√2 μ ω_S(C)) / (γ μ)) ℜⁿ(H) + ω_S(C) √(log(1/δ) / (2n))`.
Stated as: the (outer) `Dⁿ`-measure of the samples on which some `f ∈ H` violates the bound is at
most `δ`. Added hypotheses (the paper is silent): measurability of each `f ∈ H` and of its SPO
loss (`hf`, `hℓ`), of the uniform deviation and of the margin Rademacher sups (`hΦ`, `hA`); and
almost-sure boundedness plus integrability of the multivariate empirical Rademacher complexity
(`hBdd`, `hInt`), without which `ℜⁿ(H)` is not the paper's quantity. -/
theorem margin_generalization_bound {d : ℕ} {X : Type*} [MeasurableSpace X]
    [MeasurableSpace (StrongDual ℝ (EuclideanSpace ℝ (Fin d)))]
    [BorelSpace (StrongDual ℝ (EuclideanSpace ℝ (Fin d)))]
    (S : Set (EuclideanSpace ℝ (Fin d))) (hS : S.Nonempty) (hSc : IsCompact S)
    (hSv : Convex ℝ S) (hSnt : S.Nontrivial)
    (w : StrongDual ℝ (EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d)) (hw : IsOracle S w)
    (μ : ℝ) (hμ : 0 < μ) (hstr : StrengthProperty S μ w)
    (γ : ℝ) (hγ : 0 < γ)
    (C : Set (StrongDual ℝ (EuclideanSpace ℝ (Fin d)))) (hC : C.Nonempty)
    (hCb : Bornology.IsBounded C)
    (D : Measure (X × StrongDual ℝ (EuclideanSpace ℝ (Fin d)))) [IsProbabilityMeasure D]
    (hDC : ∀ᵐ z ∂D, z.2 ∈ C)
    (H : Set (X → StrongDual ℝ (EuclideanSpace ℝ (Fin d))))
    (hf : ∀ f ∈ H, Measurable f)
    (hℓ : ∀ f ∈ H,
      Measurable (fun z : X × StrongDual ℝ (EuclideanSpace ℝ (Fin d)) => spoLoss w (f z.1) z.2))
    (n : ℕ) (hn : 0 < n)
    (hΦ : AEMeasurable
      (fun s : Fin n → X × StrongDual ℝ (EuclideanSpace ℝ (Fin d)) =>
        marginSupDeviation S w γ D H s)
      (Measure.pi fun _ : Fin n => D))
    (hA : ∀ σ : Fin n → Bool,
      AEMeasurable
        (fun s : Fin n → X × StrongDual ℝ (EuclideanSpace ℝ (Fin d)) =>
          marginSignedSup S w γ H σ s)
        (Measure.pi fun _ : Fin n => D))
    (hBdd : ∀ᵐ s ∂(Measure.pi fun _ : Fin n => D), ∀ σ : Fin n → Fin d → Bool,
      BddAbove (Set.range fun f : H => (1 / n : ℝ) *
        ∑ i, (f : X → StrongDual ℝ (EuclideanSpace ℝ (Fin d))) (s i).1 (signVec (σ i))))
    (hInt : Integrable
      (fun s : Fin n → X × StrongDual ℝ (EuclideanSpace ℝ (Fin d)) =>
        empRademacherMulti H (fun i => (s i).1))
      (Measure.pi fun _ : Fin n => D))
    (δ : ℝ) (hδ : 0 < δ) :
    Measure.pi (fun _ : Fin n => D)
        {s | ∃ f ∈ H, ¬ (spoRisk D w f ≤ empMarginRisk S w γ f s +
          (2 * Real.sqrt 2 * rhoSet C + 2 * Real.sqrt 2 * μ * omegaSet S C) / (γ * μ) *
            expRademacherMulti D H n +
          omegaSet S C * Real.sqrt (Real.log (1 / δ) / (2 * n)))} ≤ ENNReal.ofReal δ := by
  classical
  by_cases hH : H.Nonempty
  swap
  · have he : H = ∅ := Set.not_nonempty_iff_eq_empty.mp hH
    simp [he]
  let : Nonempty H := hH.to_subtype
  let loss := Proof.clippedMargin S w γ C H
  have hb0 := (Proof.costSet_bounds S hSc.isBounded w hw C hC hCb).1
  have hb := Proof.clippedMargin_bounds S w γ C H hb0
  have hm := Proof.clippedMargin_measurable S hSc w hw γ C H hf hℓ
  have heΦ := Proof.clippedMargin_deviation_ae S hSc w hw γ hγ C hC hCb H D hDC n
  have heA := Proof.clippedMargin_signed_ae S hSc w hw γ hγ C hC hCb H D hDC n
  have hΦ' : AEMeasurable (fun s : Fin n → X × StrongDual ℝ (EuclideanSpace ℝ (Fin d)) =>
      Proof.lossDeviation D loss s) (Proof.sampleLaw D n) := hΦ.congr heΦ.symm
  have hA' : ∀ σ : Fin n → Bool,
      AEMeasurable (Proof.lossSignedSup loss σ) (Proof.sampleLaw D n) :=
    fun σ => (hA σ).congr (heA σ).symm
  have hIR := Proof.lossRademacher_integrable D loss (omegaSet S C) hb hn hA'
  have heR := Proof.clippedMargin_rademacher_ae S hSc w hw γ hγ C hC hCb H D hDC n
  have hIM : Integrable (fun s => empRademacherMargin S w γ H s) (Proof.sampleLaw D n) :=
    hIR.congr heR
  have hCplx := Proof.expected_margin_complexity_le S hS hSc hSv hSnt w hw μ hμ hstr
    γ hγ C hC hCb D hDC H hH n hBdd hIM hInt
  have hC' : (∫ s, Proof.lossRademacher loss s ∂Proof.sampleLaw D n) ≤
      Real.sqrt 2 * ((rhoSet C + μ * omegaSet S C) / (γ * μ)) * expRademacherMulti D H n := by
    rw [integral_congr_ae heR]
    exact hCplx
  have ht := Proof.bounded_loss_generalization D loss hm (omegaSet S C) hb0 hb n hn
    hΦ' hA' _ hC' δ hδ
  have hc : 2 * (Real.sqrt 2 * ((rhoSet C + μ * omegaSet S C) / (γ * μ)) *
      expRademacherMulti D H n) =
      (2 * Real.sqrt 2 * rhoSet C + 2 * Real.sqrt 2 * μ * omegaSet S C) / (γ * μ) *
        expRademacherMulti D H n := by ring
  rw [hc] at ht
  refine (measure_mono_ae ?_).trans ht
  filter_upwards [Proof.clippedMargin_mean_ae S hSc w hw γ hγ C hC hCb H D hDC n] with s hs
  rintro ⟨f, hfH, hbad⟩
  refine ⟨⟨f, hfH⟩, ?_⟩
  intro hgood
  apply hbad
  have hr := Proof.spoRisk_le_clippedMargin_risk S hSc w hw γ hγ C hC hCb H D hDC hf hℓ ⟨f, hfH⟩
  rw [hs ⟨f, hfH⟩] at hgood
  exact hr.trans hgood


end SPOBounds.Margin

end
-- END MODULE MarginGeneralization

-- BEGIN MODULE PublicSolution
section

open MeasureTheory SPOBounds.Margin

/-- **Theorem 4, second display** (arXiv:1905.11488v3, pp. 19–20). ℓ₂ set-up: `E = ℝ^d` with the
Euclidean norm, costs and predictions in its dual (operator norm = Euclidean norm), with the Borel
σ-algebra. Let `S` be nonempty, compact, convex and not a singleton, `w` any oracle, and suppose
`S` satisfies the strength property with parameter `μ > 0`. Fix `γ > 0`, a nonempty bounded set
`C` containing the cost vector almost surely, and any `δ > 0`. Then with probability at least
`1 − δ` over an i.i.d. sample of size `n` from `D`, every `f ∈ H` satisfies
`R_SPO(f) ≤ R̂^γ_SPO(f) + ((2√2 ρ₂(C) + 2√2 μ ω_S(C)) / (γ μ)) ℜⁿ(H) + ω_S(C) √(log(1/δ) / (2n))`.
Stated as: the (outer) `Dⁿ`-measure of the samples on which some `f ∈ H` violates the bound is at
most `δ`. Added hypotheses (the paper is silent): measurability of each `f ∈ H` and of its SPO
loss (`hf`, `hℓ`), of the uniform deviation and of the margin Rademacher sups (`hΦ`, `hA`); and
almost-sure boundedness plus integrability of the multivariate empirical Rademacher complexity
(`hBdd`, `hInt`), without which `ℜⁿ(H)` is not the paper's quantity. -/
theorem solution {d : ℕ} {X : Type*} [MeasurableSpace X]
    [MeasurableSpace (StrongDual ℝ (EuclideanSpace ℝ (Fin d)))]
    [BorelSpace (StrongDual ℝ (EuclideanSpace ℝ (Fin d)))]
    (S : Set (EuclideanSpace ℝ (Fin d))) (hS : S.Nonempty) (hSc : IsCompact S)
    (hSv : Convex ℝ S) (hSnt : S.Nontrivial)
    (w : StrongDual ℝ (EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d)) (hw : IsOracle S w)
    (μ : ℝ) (hμ : 0 < μ) (hstr : StrengthProperty S μ w)
    (γ : ℝ) (hγ : 0 < γ)
    (C : Set (StrongDual ℝ (EuclideanSpace ℝ (Fin d)))) (hC : C.Nonempty)
    (hCb : Bornology.IsBounded C)
    (D : Measure (X × StrongDual ℝ (EuclideanSpace ℝ (Fin d)))) [IsProbabilityMeasure D]
    (hDC : ∀ᵐ z ∂D, z.2 ∈ C)
    (H : Set (X → StrongDual ℝ (EuclideanSpace ℝ (Fin d))))
    (hf : ∀ f ∈ H, Measurable f)
    (hℓ : ∀ f ∈ H,
      Measurable (fun z : X × StrongDual ℝ (EuclideanSpace ℝ (Fin d)) => spoLoss w (f z.1) z.2))
    (n : ℕ) (hn : 0 < n)
    (hΦ : AEMeasurable
      (fun s : Fin n → X × StrongDual ℝ (EuclideanSpace ℝ (Fin d)) =>
        marginSupDeviation S w γ D H s)
      (Measure.pi fun _ : Fin n => D))
    (hA : ∀ σ : Fin n → Bool,
      AEMeasurable
        (fun s : Fin n → X × StrongDual ℝ (EuclideanSpace ℝ (Fin d)) =>
          marginSignedSup S w γ H σ s)
        (Measure.pi fun _ : Fin n => D))
    (hBdd : ∀ᵐ s ∂(Measure.pi fun _ : Fin n => D), ∀ σ : Fin n → Fin d → Bool,
      BddAbove (Set.range fun f : H => (1 / n : ℝ) *
        ∑ i, (f : X → StrongDual ℝ (EuclideanSpace ℝ (Fin d))) (s i).1 (signVec (σ i))))
    (hInt : Integrable
      (fun s : Fin n → X × StrongDual ℝ (EuclideanSpace ℝ (Fin d)) =>
        empRademacherMulti H (fun i => (s i).1))
      (Measure.pi fun _ : Fin n => D))
    (δ : ℝ) (hδ : 0 < δ) :
    Measure.pi (fun _ : Fin n => D)
        {s | ∃ f ∈ H, ¬ (spoRisk D w f ≤ empMarginRisk S w γ f s +
          (2 * Real.sqrt 2 * rhoSet C + 2 * Real.sqrt 2 * μ * omegaSet S C) / (γ * μ) *
            expRademacherMulti D H n +
          omegaSet S C * Real.sqrt (Real.log (1 / δ) / (2 * n)))} ≤ ENNReal.ofReal δ := by
  exact SPOBounds.Margin.margin_generalization_bound S hS hSc hSv hSnt w hw μ hμ hstr γ hγ C hC hCb D hDC H hf hℓ n hn hΦ hA hBdd hInt δ hδ



end
-- END MODULE PublicSolution

#print axioms SPOBounds.Margin.margin_generalization_bound
#print axioms solution
