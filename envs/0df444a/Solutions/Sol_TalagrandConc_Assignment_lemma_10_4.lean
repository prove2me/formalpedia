-- Prove2me | solution 1 for TalagrandConc.Assignment.lemma_10_4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-07T06:31:22.237176+00:00
-- url     : https://prove2.me/submissions/8f9e5936-1d95-4ac1-92d2-18ea20c99c27

import Mathlib

open MeasureTheory ProbabilityTheory

namespace TalagrandConc.Assignment

theorem exp_neg_le_quad (s : ℝ) (hs : 0 ≤ s) : Real.exp (-s) ≤ 1 - s + s ^ 2 / 2 := by
  have hmono : MonotoneOn (fun x : ℝ => 1 - x + x ^ 2 / 2 - Real.exp (-x)) (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · fun_prop
    · fun_prop
    · intro x hx
      have hx0 : 0 < x := by simpa using hx
      have a : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by simpa using (hasDerivAt_id x).const_sub 1
      have b : HasDerivAt (fun x : ℝ => x ^ 2 / 2) x x := by
        simpa using ((hasDerivAt_pow 2 x).div_const 2)
      have c : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-x)) x := by
        exact (hasDerivAt_neg x).exp.congr_deriv (by ring)
      have d : HasDerivAt (fun x : ℝ => 1 - x + x ^ 2 / 2 - Real.exp (-x)) (-1 + x + Real.exp (-x)) x :=
        ((a.add b).sub c).congr_deriv (by ring)
      rw [d.deriv]
      have := Real.one_sub_le_exp_neg x
      linarith
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hs) hs
  simp at this
  linarith

theorem mgf_indicator {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (hA : MeasurableSet A) (t : ℝ) :
    mgf (A.indicator (fun _ => (1 : ℝ))) P t = 1 + (Real.exp t - 1) * P.real A := by
  unfold mgf
  have h : ∀ ω, Real.exp (t * A.indicator (fun _ => (1 : ℝ)) ω) =
      1 + (Real.exp t - 1) * A.indicator (fun _ => (1 : ℝ)) ω := by
    intro ω
    by_cases hω : ω ∈ A <;> simp [hω]
  simp_rw [h]
  rw [integral_add (integrable_const _), integral_const_mul, integral_indicator_const _ hA]
  · simp
  · exact (integrable_indicator_iff hA).2 (integrable_const _ |>.integrableOn) |>.const_mul _

theorem lemma_10_4_aux :
    ∀ δ : ℝ, δ < 1 → ∃ K : ℝ, 0 < K ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (N : ℕ) (A : Fin N → Set Ω) (p : ℝ),
        (∀ i, MeasurableSet (A i)) → iIndepSet A P → (∀ i, P.real (A i) = p) →
        P {ω | (({i : Fin N | ω ∈ A i}.ncard : ℕ) : ℝ) < δ * p * N} ≤
          ENNReal.ofReal (Real.exp (-((N : ℝ) * p) / K)) := by
  intro δ hδ
  have hs : 0 < 1 - δ := by linarith
  refine ⟨2 / (1 - δ) ^ 2, by positivity, ?_⟩
  intro Ω _ P _ N A p hA hind hp
  classical
  set s : ℝ := 1 - δ with hs_def
  have hNp : 0 ≤ (N : ℝ) * p := by
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · subst h0; simp
    · have : p = P.real (A ⟨0, hpos⟩) := (hp _).symm
      rw [this]; positivity
  set X : Fin N → Ω → ℝ := fun i => (A i).indicator (fun _ => (1 : ℝ)) with hX_def
  have hX : iIndepFun X P := hind.iIndepFun_indicator
  have hXm : ∀ i, Measurable (X i) := fun i => measurable_const.indicator (hA i)
  have hcount : ∀ ω, (({i : Fin N | ω ∈ A i}.ncard : ℕ) : ℝ) = (∑ i ∈ Finset.univ, X i) ω := by
    intro ω
    simp only [Finset.sum_apply, hX_def, Set.indicator_apply, Finset.sum_boole]
    rw [Set.ncard_eq_toFinset_card']
    simp
  have hsub : {ω | (({i : Fin N | ω ∈ A i}.ncard : ℕ) : ℝ) < δ * p * N} ⊆
      {ω | (∑ i ∈ Finset.univ, X i) ω ≤ δ * p * N} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [← hcount]; exact hω.le
  have hSm : Measurable (∑ i ∈ Finset.univ, X i) := by
    have := Finset.measurable_fun_sum Finset.univ (fun i _ => hXm i)
    convert this using 1
    ext ω
    simp [Finset.sum_apply]
  have hint : Integrable (fun ω => Real.exp (-s * (∑ i ∈ Finset.univ, X i) ω)) P := by
    refine Integrable.of_bound (C := 1) ?_ ?_
    · exact (hSm.const_mul _).exp.aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun ω => ?_)
      have h0 : 0 ≤ (∑ i ∈ Finset.univ, X i) ω := by
        simp only [Finset.sum_apply, hX_def]
        exact Finset.sum_nonneg (fun i _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _)
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_one_iff.2
      nlinarith
  have hchernoff := measure_le_le_exp_mul_mgf (μ := P) (X := ∑ i ∈ Finset.univ, X i)
    (δ * p * N) (t := -s) (by linarith) hint
  have hmgf : mgf (∑ i ∈ Finset.univ, X i) P (-s) ≤ Real.exp (N * p * (Real.exp (-s) - 1)) := by
    rw [hX.mgf_sum hXm Finset.univ]
    have hfac : ∀ i : Fin N, mgf (X i) P (-s) ≤ Real.exp (p * (Real.exp (-s) - 1)) := by
      intro i
      rw [hX_def]
      simp only
      rw [mgf_indicator P (A i) (hA i), hp i]
      have := Real.add_one_le_exp (p * (Real.exp (-s) - 1))
      nlinarith
    calc ∏ i : Fin N, mgf (X i) P (-s) ≤ ∏ i : Fin N, Real.exp (p * (Real.exp (-s) - 1)) :=
          Finset.prod_le_prod (fun i _ => mgf_nonneg) (fun i _ => hfac i)
      _ = Real.exp (N * p * (Real.exp (-s) - 1)) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]
          congr 1; ring
  have hq := exp_neg_le_quad s hs.le
  have hexp : Real.exp (-(-s) * (δ * p * N)) * Real.exp (N * p * (Real.exp (-s) - 1)) ≤
      Real.exp (-((N : ℝ) * p) / (2 / s ^ 2)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have h2 : δ = 1 - s := by rw [hs_def]; ring
    have hmain : (N : ℝ) * p * (Real.exp (-s) - 1) ≤ (N : ℝ) * p * (-s + s ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hNp
    have : -((N : ℝ) * p) / (2 / s ^ 2) = -((N : ℝ) * p) * s ^ 2 / 2 := by
      field_simp
    rw [this]
    have hh : -(-s) * (δ * p * N) = (N : ℝ) * p * (s * δ) := by ring
    rw [hh]
    have : (N : ℝ) * p * (s * δ) + (N : ℝ) * p * (-s + s ^ 2 / 2) = -((N : ℝ) * p) * s ^ 2 / 2 := by
      rw [h2]; ring
    linarith
  have hreal : P.real {ω | (({i : Fin N | ω ∈ A i}.ncard : ℕ) : ℝ) < δ * p * N} ≤
      Real.exp (-((N : ℝ) * p) / (2 / s ^ 2)) := by
    calc P.real {ω | (({i : Fin N | ω ∈ A i}.ncard : ℕ) : ℝ) < δ * p * N}
        ≤ P.real {ω | (∑ i ∈ Finset.univ, X i) ω ≤ δ * p * N} := measureReal_mono hsub
      _ ≤ Real.exp (-(-s) * (δ * p * N)) * mgf (∑ i ∈ Finset.univ, X i) P (-s) := hchernoff
      _ ≤ Real.exp (-(-s) * (δ * p * N)) * Real.exp (N * p * (Real.exp (-s) - 1)) :=
          mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
      _ ≤ _ := hexp
  rw [← ENNReal.ofReal_toReal (measure_ne_top P _)]
  exact ENNReal.ofReal_le_ofReal hreal

end TalagrandConc.Assignment

open MeasureTheory ProbabilityTheory in
theorem solution :
    ∀ δ : ℝ, δ < 1 → ∃ K : ℝ, 0 < K ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (N : ℕ) (A : Fin N → Set Ω) (p : ℝ),
        (∀ i, MeasurableSet (A i)) → iIndepSet A P → (∀ i, P.real (A i) = p) →
        P {ω | (({i : Fin N | ω ∈ A i}.ncard : ℕ) : ℝ) < δ * p * N} ≤
          ENNReal.ofReal (Real.exp (-((N : ℝ) * p) / K)) :=
  TalagrandConc.Assignment.lemma_10_4_aux
