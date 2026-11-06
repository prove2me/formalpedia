-- Prove2me | solution 1 for SAARate.Polyhedral.theorem_3_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T22:01:28.719181+00:00
-- url     : https://prove2.me/submissions/a0647162-cda9-4d63-82c8-201bacbb9e67

import Mathlib
import Definitions.Def_SAARate_Polyhedral_Setting
import Theorems.Thm_SAARate_Polyhedral_lemma_2_4_c
import Theorems.Thm_SAARate_Polyhedral_union_bound_p13
import Theorems.Thm_SAARate_Polyhedral_pointwise_exponential_bounds

open MeasureTheory ProbabilityTheory Filter

namespace SAA3Aux

open SAARate.Polyhedral SAARate.Sharp

/-- Combining finitely many exponential bounds into one. -/
lemma sum_exp_bound {q : ℕ} (β : ℝ) (δ : ℝ) (hδ : 0 < δ) (N : ℕ)
    (hN : (2 * q : ℝ) ≤ Real.exp (δ / 2 * N))
    (s1 s2 : Finset (Fin q)) (t u : Fin q → ENNReal)
    (ht : ∀ i, t i ≤ ENNReal.ofReal (Real.exp (-(β - δ / 2) * N)))
    (hu : ∀ i, u i ≤ ENNReal.ofReal (Real.exp (-(β - δ / 2) * N))) :
    (∑ i ∈ s1, t i) + (∑ j ∈ s2, u j) ≤ ENNReal.ofReal (Real.exp (-(β - δ) * N)) := by
  set a := ENNReal.ofReal (Real.exp (-(β - δ / 2) * N))
  have h1 : (∑ i ∈ s1, t i) ≤ q • a := by
    calc (∑ i ∈ s1, t i) ≤ s1.card • a := Finset.sum_le_card_nsmul _ _ _ (fun i _ => ht i)
      _ ≤ q • a := by
        apply nsmul_le_nsmul_left (by simp)
        simpa using Finset.card_le_univ s1
  have h2 : (∑ j ∈ s2, u j) ≤ q • a := by
    calc (∑ j ∈ s2, u j) ≤ s2.card • a := Finset.sum_le_card_nsmul _ _ _ (fun i _ => hu i)
      _ ≤ q • a := by
        apply nsmul_le_nsmul_left (by simp)
        simpa using Finset.card_le_univ s2
  calc _ ≤ q • a + q • a := add_le_add h1 h2
    _ = ENNReal.ofReal ((2 * q : ℝ) * Real.exp (-(β - δ / 2) * N)) := by
        rw [ENNReal.ofReal_mul (by positivity), ← two_nsmul, smul_smul, nsmul_eq_mul]
        congr 1
        rw [ENNReal.ofReal_mul (by norm_num)]
        simp
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        calc (2 * q : ℝ) * Real.exp (-(β - δ / 2) * N)
            ≤ Real.exp (δ / 2 * N) * Real.exp (-(β - δ / 2) * N) :=
              mul_le_mul_of_nonneg_right hN (Real.exp_pos _).le
          _ = Real.exp (-(β - δ) * N) := by rw [← Real.exp_add]; ring_nf

/-- Theorem 3.2 under the extra pin that every scenario has positive mass. -/
theorem pos_case {m : ℕ} {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : ∀ ω, P {ω} ≠ 0)
    (h : SAARate.Sharp.E m → Ω → ℝ) (hpl : ∀ ω, IsPLConvex (fun x => h x ω))
    (Θ : Set (SAARate.Sharp.E m)) (hΘc : IsClosed Θ) (hΘv : Convex ℝ Θ) (hΘp : IsPolyhedral Θ)
    (hA : (SAARate.Sharp.argminOn (SAARate.Sharp.expectedObj P h) Θ).Nonempty ∧
      Bornology.IsBounded (SAARate.Sharp.argminOn (SAARate.Sharp.expectedObj P h) Θ))
    {S : Type*} [MeasurableSpace S] (Q : Measure S) [IsProbabilityMeasure Q]
    (ω : ℕ → S → Ω) (hω : SAARate.SharpLD.IsIIDSample Q P ω) :
    ∃ β > 0, ∀ δ > 0, ∀ᶠ N : ℕ in atTop,
      Q {s | ¬ ((SAARate.Sharp.argminOn (SAARate.Sharp.saaObj h (fun j => ω j s) N) Θ).Nonempty ∧
          IsFace (SAARate.Sharp.argminOn (SAARate.Sharp.expectedObj P h) Θ) (SAARate.Sharp.argminOn (SAARate.Sharp.saaObj h (fun j => ω j s) N) Θ))} ≤
        ENNReal.ofReal (Real.exp (-(β - δ) * (N : ℝ))) := by
  obtain ⟨q, ℓ, -, x, -, hgap, hc⟩ :=
    lemma_2_4_c P hP h hpl Θ hΘc hΘv hΘp hA
  obtain ⟨ε, hε, hub⟩ := union_bound_p13 P h Θ Q ω q ℓ x hc hgap
  have hpw := fun i : Fin q => pointwise_exponential_bounds P h Q ω hω (x i) ε hε
  choose β1 hβ1 H1 using fun i => (hpw i).1
  choose β2 hβ2 H2 using fun i => (hpw i).2
  obtain ⟨β, hβ, hβle⟩ : ∃ β > 0, ∀ i, β ≤ β1 i ∧ β ≤ β2 i := by
    rcases isEmpty_or_nonempty (Fin q) with hq | hq
    · exact ⟨1, one_pos, fun i => (IsEmpty.false i).elim⟩
    · obtain ⟨i0, hi0⟩ := Finite.exists_min (fun i => min (β1 i) (β2 i))
      refine ⟨min (β1 i0) (β2 i0), lt_min (hβ1 i0) (hβ2 i0), fun i => ?_⟩
      exact ⟨(hi0 i).trans (min_le_left _ _), (hi0 i).trans (min_le_right _ _)⟩
  refine ⟨β, hβ, fun δ hδ => ?_⟩
  have e1 : ∀ᶠ N : ℕ in atTop, ∀ i, Q {s | SAARate.Sharp.expectedObj P h (x i) + ε ≤
      SAARate.Sharp.saaObj h (fun j => ω j s) N (x i)} ≤
      ENNReal.ofReal (Real.exp (-(β - δ / 2) * (N : ℝ))) := by
    rw [Filter.eventually_all]
    intro i
    filter_upwards [H1 i (δ / 2) (by linarith)] with N hN
    refine hN.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
    have := (hβle i).1
    have : (0 : ℝ) ≤ N := N.cast_nonneg
    nlinarith
  have e2 : ∀ᶠ N : ℕ in atTop, ∀ i, Q {s | SAARate.Sharp.saaObj h (fun j => ω j s) N (x i) ≤
      SAARate.Sharp.expectedObj P h (x i) - ε} ≤
      ENNReal.ofReal (Real.exp (-(β - δ / 2) * (N : ℝ))) := by
    rw [Filter.eventually_all]
    intro i
    filter_upwards [H2 i (δ / 2) (by linarith)] with N hN
    refine hN.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
    have := (hβle i).2
    have : (0 : ℝ) ≤ N := N.cast_nonneg
    nlinarith
  have e3 : ∀ᶠ N : ℕ in atTop, (2 * q : ℝ) ≤ Real.exp (δ / 2 * N) := by
    filter_upwards [eventually_ge_atTop ⌈(4 * q : ℝ) / δ⌉₊] with N hN
    have h1 : (4 * q : ℝ) / δ ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hN)
    have h2 : (4 * q : ℝ) ≤ δ * N := by rw [div_le_iff₀ hδ] at h1; linarith
    have h3 := Real.add_one_le_exp (δ / 2 * N)
    have : (0 : ℝ) ≤ q := q.cast_nonneg
    nlinarith
  filter_upwards [e1, e2, e3] with N h1 h2 h3
  exact (hub N).trans (sum_exp_bound β δ hδ N h3 _ _ _ _ h1 h2)

end SAA3Aux

open SAARate.Polyhedral in
theorem solution {m : ℕ} {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : SAARate.Sharp.E m → Ω → ℝ) (hpl : ∀ ω, IsPLConvex (fun x => h x ω))
    (Θ : Set (SAARate.Sharp.E m)) (hΘc : IsClosed Θ) (hΘv : Convex ℝ Θ) (hΘp : IsPolyhedral Θ)
    (hA : (SAARate.Sharp.argminOn (SAARate.Sharp.expectedObj P h) Θ).Nonempty ∧
      Bornology.IsBounded (SAARate.Sharp.argminOn (SAARate.Sharp.expectedObj P h) Θ))
    {S : Type*} [MeasurableSpace S] (Q : Measure S) [IsProbabilityMeasure Q]
    (ω : ℕ → S → Ω) (hω : SAARate.SharpLD.IsIIDSample Q P ω) :
    ∃ β > 0, ∀ δ > 0, ∀ᶠ N : ℕ in atTop,
      Q {s | ¬ ((SAARate.Sharp.argminOn (SAARate.Sharp.saaObj h (fun j => ω j s) N) Θ).Nonempty ∧
          IsFace (SAARate.Sharp.argminOn (SAARate.Sharp.expectedObj P h) Θ) (SAARate.Sharp.argminOn (SAARate.Sharp.saaObj h (fun j => ω j s) N) Θ))} ≤
        ENNReal.ofReal (Real.exp (-(β - δ) * (N : ℝ))) := by
  classical
  -- the support of `P`
  obtain ⟨w0, hw0⟩ : ∃ w, P {w} ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have : P (⋃ w ∈ (Set.univ : Set Ω), {w}) = 0 :=
      (measure_biUnion_null_iff (Set.to_countable _)).2 (fun w _ => hcon w)
    have h1 : (⋃ w ∈ (Set.univ : Set Ω), ({w} : Set Ω)) = Set.univ := by ext; simp
    rw [h1, measure_univ] at this
    exact one_ne_zero this
  let Ω' := {w : Ω // P {w} ≠ 0}
  let g : Ω → Ω' := fun w => if hw : P {w} ≠ 0 then ⟨w, hw⟩ else ⟨w0, hw0⟩
  have hg : Measurable g := Measurable.of_discrete
  let P' : Measure Ω' := P.map g
  have : IsProbabilityMeasure P' := Measure.isProbabilityMeasure_map hg.aemeasurable
  let h' : SAARate.Sharp.E m → Ω' → ℝ := fun x w => h x w.val
  -- the null set of scenarios outside the support
  set Z : Set Ω := {w | P {w} = 0} with hZdef
  have hZ : P Z = 0 := by
    have : Z = ⋃ w ∈ Z, {w} := by simp
    rw [this]
    exact (measure_biUnion_null_iff (Set.to_countable _)).2 (fun w hw => hw)
  have hgv : ∀ w, w ∉ Z → (g w).val = w := by
    intro w hw
    simp only [hZdef, Set.mem_ofPred_eq] at hw
    simp [g, hw]
  have hE : SAARate.Sharp.expectedObj P' h' = SAARate.Sharp.expectedObj P h := by
    funext x
    simp only [SAARate.Sharp.expectedObj, P', h']
    rw [integral_map hg.aemeasurable (Measurable.of_discrete.aestronglyMeasurable)]
    apply integral_congr_ae
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null (fun w hw => ?_) hZ
    by_contra hwZ
    exact hw (by rw [hgv w hwZ])
  have hP' : ∀ w : Ω', P' {w} ≠ 0 := by
    intro w
    rw [Measure.map_apply hg (measurableSet_singleton _)]
    intro h0
    apply w.2
    refine measure_mono_null (fun v hv => ?_) h0
    rw [Set.mem_singleton_iff] at hv
    subst hv
    simp only [Set.mem_preimage, Set.mem_singleton_iff, g, dif_pos w.2]
    rfl
  have hpl' : ∀ w : Ω', IsPLConvex (fun x => h' x w) := fun w => hpl w.val
  let ω' : ℕ → S → Ω' := fun j s => g (ω j s)
  have hω' : SAARate.SharpLD.IsIIDSample Q P' ω' := by
    obtain ⟨hm, hind, hlaw⟩ := hω
    refine ⟨fun j => hg.comp (hm j), hind.comp (fun _ => g) (fun _ => hg), fun j => ?_⟩
    show Q.map (g ∘ ω j) = P.map g
    rw [← Measure.map_map hg (hm j), hlaw j]
  have hA' : (SAARate.Sharp.argminOn (SAARate.Sharp.expectedObj P' h') Θ).Nonempty ∧
      Bornology.IsBounded (SAARate.Sharp.argminOn (SAARate.Sharp.expectedObj P' h') Θ) := by
    rw [hE]; exact hA
  obtain ⟨β, hβ, H⟩ := SAA3Aux.pos_case P' hP' h' hpl' Θ hΘc hΘv hΘp hA' Q ω' hω'
  -- the bad sample set
  set Bad : Set S := ⋃ j, ω j ⁻¹' Z with hBad
  have hBad0 : Q Bad = 0 := by
    apply measure_iUnion_null
    intro j
    have : Q (ω j ⁻¹' Z) = (Q.map (ω j)) Z :=
      (Measure.map_apply (hω.1 j) (Set.toFinite Z).measurableSet).symm
    rw [this, hω.2.2 j]; exact hZ
  refine ⟨β, hβ, fun δ hδ => ?_⟩
  filter_upwards [H δ hδ] with N hN
  refine le_trans ?_ hN
  rw [hE]
  calc _ ≤ Q ({s | ¬ ((SAARate.Sharp.argminOn (SAARate.Sharp.saaObj h' (fun j => ω' j s) N) Θ).Nonempty ∧
          IsFace (SAARate.Sharp.argminOn (SAARate.Sharp.expectedObj P h) Θ)
            (SAARate.Sharp.argminOn (SAARate.Sharp.saaObj h' (fun j => ω' j s) N) Θ))} ∪ Bad) := by
        apply measure_mono
        intro s hs
        by_cases hsB : s ∈ Bad
        · exact Or.inr hsB
        · left
          have hsaa : SAARate.Sharp.saaObj h' (fun j => ω' j s) N = SAARate.Sharp.saaObj h (fun j => ω j s) N := by
            funext x
            simp only [SAARate.Sharp.saaObj, h', ω']
            congr 1
            apply Finset.sum_congr rfl
            intro j _
            rw [hgv]
            intro hj
            exact hsB (Set.mem_iUnion.2 ⟨j, hj⟩)
          simpa only [Set.mem_ofPred_eq, hsaa] using hs
    _ ≤ _ + Q Bad := measure_union_le _ _
    _ = _ := by rw [hBad0, add_zero]
