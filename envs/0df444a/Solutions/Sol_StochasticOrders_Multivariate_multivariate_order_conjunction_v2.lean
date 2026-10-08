-- Prove2me | solution 1 for StochasticOrders.Multivariate.multivariate_order_conjunction_v2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T19:11:54.234692+00:00
-- url     : https://prove2.me/submissions/c627207f-643c-4037-b656-8f9d8f4b50e5

import Mathlib
import Definitions.Def_StochasticOrders_Multivariate_MultivariateOrder_v2



namespace StochasticOrders.Multivariate

open MeasureTheory ProbabilityTheory

universe u

lemma pi_mono_core : ∀ (m : ℕ) (E : Fin m → Type u) [∀ i, MeasurableSpace (E i)]
    [∀ i, Preorder (E i)] (P Q : ∀ i, Measure (E i))
    [∀ i, IsProbabilityMeasure (P i)] [∀ i, IsProbabilityMeasure (Q i)],
    (∀ i, ∀ φ : E i → ℝ, Measurable φ → Monotone φ → (∃ C, ∀ x, |φ x| ≤ C) →
      ∫ x, φ x ∂(P i) ≤ ∫ x, φ x ∂(Q i)) →
    ∀ f : (∀ i, E i) → ℝ, Measurable f → Monotone f → (∃ C, ∀ x, |f x| ≤ C) →
      ∫ x, f x ∂(Measure.pi P) ≤ ∫ x, f x ∂(Measure.pi Q) := by
  intro m
  induction m with
  | zero =>
    intro E _ _ P Q _ _ h f hf hm hb
    have h1 : ∀ μ : Measure (∀ i, E i), IsProbabilityMeasure μ → ∫ x, f x ∂μ = f default := by
      intro μ hμ
      have : ∀ x, f x = f default := fun x => by rw [Subsingleton.elim x default]
      simp_rw [this]
      simp
    have : IsProbabilityMeasure (Measure.pi P) := inferInstance
    rw [h1 _ inferInstance, h1 _ inferInstance]
  | succ m ih =>
    intro E _ _ P Q _ _ h f hf hm hb
    obtain ⟨C, hC⟩ := hb
    let e := MeasurableEquiv.piFinSuccAbove E 0
    let F : E 0 × (∀ j, E (Fin.succAbove 0 j)) → ℝ := fun p => f (e.symm p)
    have hFm : Measurable F := hf.comp e.symm.measurable
    have hFb : ∀ p, |F p| ≤ C := fun p => hC _
    have hFmono : Monotone F := by
      intro p q hpq
      apply hm
      intro j
      change Fin.insertNth 0 p.1 p.2 j ≤ Fin.insertNth 0 q.1 q.2 j
      induction j using Fin.succAboveCases 0 with
      | x => simpa using hpq.1
      | p j =>
        rw [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove]
        exact hpq.2 j
    have key : ∀ μ : ∀ i, Measure (E i), (∀ i, IsProbabilityMeasure (μ i)) →
        ∫ x, f x ∂(Measure.pi μ) = ∫ p, F p ∂((μ 0).prod (Measure.pi fun j => μ (Fin.succAbove 0 j))) := by
      intro μ hμ
      have := (measurePreserving_piFinSuccAbove μ 0).integral_comp' (g := F)
      rw [← this]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show f x = f ((MeasurableEquiv.piFinSuccAbove E 0).symm ((MeasurableEquiv.piFinSuccAbove E 0) x))
      rw [MeasurableEquiv.symm_apply_apply]
    rw [key P inferInstance, key Q inferInstance]
    have hint : ∀ (μ : Measure (E 0)) (ν : Measure (∀ j, E (Fin.succAbove 0 j)))
        [IsProbabilityMeasure μ] [IsProbabilityMeasure ν], Integrable F (μ.prod ν) := by
      intro μ ν _ _
      refine Integrable.of_bound (C := C) hFm.aestronglyMeasurable (Filter.Eventually.of_forall ?_)
      intro p; simpa using hFb p
    rw [integral_prod _ (hint _ _), integral_prod _ (hint _ _)]
    set P' := Measure.pi fun j => P (Fin.succAbove 0 j)
    set Q' := Measure.pi fun j => Q (Fin.succAbove 0 j)
    -- step 1
    have s1 : ∫ x, ∫ r, F (x, r) ∂P' ∂(P 0) ≤ ∫ x, ∫ r, F (x, r) ∂Q' ∂(P 0) := by
      refine integral_mono ?_ ?_ ?_
      · exact (hint (P 0) P').integral_prod_left
      · exact (hint (P 0) Q').integral_prod_left
      · intro x
        exact ih (fun j => E (Fin.succAbove 0 j)) (fun j => P (Fin.succAbove 0 j))
          (fun j => Q (Fin.succAbove 0 j))
          (fun j => h _) (fun r => F (x, r)) (hFm.comp measurable_prodMk_left)
          (fun a b hab => hFmono ⟨le_rfl, hab⟩) ⟨C, fun r => hFb _⟩
    have swap : ∫ x, ∫ r, F (x, r) ∂Q' ∂(P 0) = ∫ r, ∫ x, F (x, r) ∂(P 0) ∂Q' :=
      integral_integral_swap (hint (P 0) Q')
    have swap2 : ∫ x, ∫ r, F (x, r) ∂Q' ∂(Q 0) = ∫ r, ∫ x, F (x, r) ∂(Q 0) ∂Q' :=
      integral_integral_swap (hint (Q 0) Q')
    have s2 : ∫ r, ∫ x, F (x, r) ∂(P 0) ∂Q' ≤ ∫ r, ∫ x, F (x, r) ∂(Q 0) ∂Q' := by
      refine integral_mono ?_ ?_ ?_
      · exact (hint (P 0) Q').integral_prod_right
      · exact (hint (Q 0) Q').integral_prod_right
      · intro r
        exact h 0 (fun x => F (x, r)) (hFm.comp measurable_prodMk_right)
          (fun a b hab => hFmono ⟨hab, le_rfl⟩) ⟨C, fun x => hFb _⟩
    linarith


theorem conj_core {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {m : ℕ} (k : Fin m → ℕ) (X : (i : Fin m) → Ω → Fin (k i) → ℝ)
    (Y : (i : Fin m) → Ω' → Fin (k i) → ℝ)
    (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    (hXindep : iIndepFun X μ) (hYindep : iIndepFun Y ν)
    (hord : ∀ i, MultivariateOrder μ ν (X i) (Y i))
    (ψ : ((i : Fin m) → Fin (k i) → ℝ) → ℝ) (hψmeas : Measurable ψ) (hψ : Monotone ψ) :
    ∀ x : ℝ, μ {ω | x < ψ (fun i => X i ω)} ≤ ν {ω | x < ψ (fun i => Y i ω)} := by
  intro x
  have hXm : Measurable (fun ω i => X i ω) := measurable_pi_iff.2 hX
  have hYm : Measurable (fun ω i => Y i ω) := measurable_pi_iff.2 hY
  have eX := (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hX i).aemeasurable)).1 hXindep
  have eY := (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hY i).aemeasurable)).1 hYindep
  have pX : ∀ i, IsProbabilityMeasure (μ.map (X i)) := fun i =>
    Measure.isProbabilityMeasure_map (hX i).aemeasurable
  have pY : ∀ i, IsProbabilityMeasure (ν.map (Y i)) := fun i =>
    Measure.isProbabilityMeasure_map (hY i).aemeasurable
  let S : Set ((i : Fin m) → Fin (k i) → ℝ) := {p | x < ψ p}
  have hS : MeasurableSet S := measurableSet_lt measurable_const hψmeas
  let f : ((i : Fin m) → Fin (k i) → ℝ) → ℝ := S.indicator (fun _ => 1)
  have hfm : Measurable f := measurable_const.indicator hS
  have hfmono : Monotone f := by
    intro a b hab
    by_cases ha : a ∈ S
    · have hb : b ∈ S := lt_of_lt_of_le ha (hψ hab)
      simp [f, ha, hb]
    · simp only [f, Set.indicator_of_notMem ha]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) b
  have hfb : ∃ C, ∀ p, |f p| ≤ C := ⟨1, fun p => by
    by_cases hp : p ∈ S <;> simp [f, hp]⟩
  have main := pi_mono_core m (fun i => Fin (k i) → ℝ) (fun i => μ.map (X i))
    (fun i => ν.map (Y i)) (by
      intro i φ hφm hφmono hφb
      obtain ⟨C, hC⟩ := hφb
      have i1 : Integrable (φ ∘ X i) μ :=
        Integrable.of_bound (C := C) (hφm.comp (hX i)).aestronglyMeasurable
          (Filter.Eventually.of_forall fun ω => by simpa using hC (X i ω))
      have i2 : Integrable (φ ∘ Y i) ν :=
        Integrable.of_bound (C := C) (hφm.comp (hY i)).aestronglyMeasurable
          (Filter.Eventually.of_forall fun ω => by simpa using hC (Y i ω))
      have := hord i φ hφm hφmono i1 i2
      rwa [integral_map (hX i).aemeasurable hφm.aestronglyMeasurable,
        integral_map (hY i).aemeasurable hφm.aestronglyMeasurable])
    f hfm hfmono hfb
  rw [← eX, ← eY, integral_map hXm.aemeasurable hfm.aestronglyMeasurable,
    integral_map hYm.aemeasurable hfm.aestronglyMeasurable] at main
  have e1 : ∫ ω, f (fun i => X i ω) ∂μ = (μ {ω | x < ψ (fun i => X i ω)}).toReal := by
    have : (fun ω => f (fun i => X i ω)) =
        {ω | x < ψ (fun i => X i ω)}.indicator (fun _ => (1:ℝ)) := by
      ext ω; simp [f, S, Set.indicator]
    rw [this]
    have := integral_indicator_const (μ := μ) (1:ℝ) (hS.preimage hXm)
    simpa [Measure.real, S] using this
  have e2 : ∫ ω, f (fun i => Y i ω) ∂ν = (ν {ω | x < ψ (fun i => Y i ω)}).toReal := by
    have : (fun ω => f (fun i => Y i ω)) =
        {ω | x < ψ (fun i => Y i ω)}.indicator (fun _ => (1:ℝ)) := by
      ext ω; simp [f, S, Set.indicator]
    rw [this]
    have := integral_indicator_const (μ := ν) (1:ℝ) (hS.preimage hYm)
    simpa [Measure.real, S] using this
  rw [e1, e2] at main
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).1 main

end StochasticOrders.Multivariate

open StochasticOrders.Multivariate
open MeasureTheory ProbabilityTheory

theorem solution {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {m : ℕ} (k : Fin m → ℕ) (X : (i : Fin m) → Ω → Fin (k i) → ℝ)
    (Y : (i : Fin m) → Ω' → Fin (k i) → ℝ)
    (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    (hXindep : iIndepFun X μ) (hYindep : iIndepFun Y ν)
    (hord : ∀ i, MultivariateOrder μ ν (X i) (Y i))
    (ψ : ((i : Fin m) → Fin (k i) → ℝ) → ℝ) (hψmeas : Measurable ψ) (hψ : Monotone ψ) :
    ∀ x : ℝ, μ {ω | x < ψ (fun i => X i ω)} ≤ ν {ω | x < ψ (fun i => Y i ω)} := by
  exact conj_core μ ν k X Y hX hY hXindep hYindep hord ψ hψmeas hψ
