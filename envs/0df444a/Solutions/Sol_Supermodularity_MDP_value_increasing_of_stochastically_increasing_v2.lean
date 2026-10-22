-- Prove2me | solution 1 for Supermodularity.MDP.value_increasing_of_stochastically_increasing_v2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T02:19:49.383855+00:00
-- url     : https://prove2.me/submissions/24b895f9-e8f1-4259-b539-ca6d0a2fc3f7

import Mathlib
import Definitions.Def_Supermodularity_MDP_StochasticallyIncreasingOn

open MeasureTheory


namespace Supermodularity.MDP

theorem vi_meas_le {m : ℕ} (T : Set (Fin m → ℝ)) (f : (Fin m → ℝ) → ℝ) (hf : MonotoneOn f T)
    (P : ℝ → Prop) (hP : ∀ a b, a ≤ b → P a → P b)
    (ν ν' : Measure (Fin m → ℝ)) (hν : ν Tᶜ = 0) (hν' : ν' Tᶜ = 0)
    (hdom : ∀ U : Set (Fin m → ℝ), IsUpperSet U → ν U ≤ ν' U) :
    ν {w | P (f w)} ≤ ν' {w | P (f w)} := by
  set U : Set (Fin m → ℝ) := {w | ∃ v ∈ T, v ≤ w ∧ P (f v)} with hU
  have hUup : IsUpperSet U := by
    intro a b hab ha
    obtain ⟨v, hv, hva, hPv⟩ := ha
    exact ⟨v, hv, hva.trans hab, hPv⟩
  have key : ∀ ρ : Measure (Fin m → ℝ), ρ Tᶜ = 0 → ρ {w | P (f w)} = ρ U := by
    intro ρ hρ
    apply measure_congr
    have hT : T ∈ MeasureTheory.ae ρ := by
      rw [MeasureTheory.mem_ae_iff]; exact hρ
    rw [Filter.eventuallyEq_set]
    filter_upwards [hT] with w hw
    constructor
    · intro h
      exact ⟨w, hw, le_rfl, h⟩
    · rintro ⟨v, hv, hvw, hPv⟩
      exact hP _ _ (hf hv hw hvw) hPv
  rw [key ν hν, key ν' hν']
  exact hdom U hUup

theorem vi_integral_mono {m : ℕ} (T : Set (Fin m → ℝ)) (f : (Fin m → ℝ) → ℝ)
    (hf : MonotoneOn f T)
    (ν ν' : Measure (Fin m → ℝ)) [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    (hν : ν Tᶜ = 0) (hν' : ν' Tᶜ = 0)
    (hi : Integrable f ν) (hi' : Integrable f ν')
    (hdom : ∀ U : Set (Fin m → ℝ), IsUpperSet U → (ν U).toReal ≤ (ν' U).toReal) :
    ∫ w, f w ∂ν ≤ ∫ w, f w ∂ν' := by
  have hdom' : ∀ U : Set (Fin m → ℝ), IsUpperSet U → ν U ≤ ν' U := fun U hU =>
    (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).1 (hdom U hU)
  have hpos : ∀ ρ : Measure (Fin m → ℝ), ∫⁻ a, ENNReal.ofReal (f a) ∂ρ
      = ∫⁻ a, ENNReal.ofReal (max (f a) 0) ∂ρ := by
    intro ρ
    apply lintegral_congr
    intro a
    rcases le_total (f a) 0 with h | h
    · simp [h, max_eq_right]
    · simp [h]
  have hneg : ∀ ρ : Measure (Fin m → ℝ), ∫⁻ a, ENNReal.ofReal (-f a) ∂ρ
      = ∫⁻ a, ENNReal.ofReal (max (-f a) 0) ∂ρ := by
    intro ρ
    apply lintegral_congr
    intro a
    rcases le_total (-f a) 0 with h | h
    · simp [h, max_eq_right]
    · simp [h]
  have mpos : ∀ ρ : Measure (Fin m → ℝ), Integrable f ρ →
      ∫⁻ a, ENNReal.ofReal (max (f a) 0) ∂ρ = ∫⁻ t in Set.Ioi (0:ℝ), ρ {a | t < max (f a) 0} := by
    intro ρ h
    apply lintegral_eq_lintegral_meas_lt
    · exact Filter.Eventually.of_forall (fun a => le_max_right _ _)
    · exact (h.1.aemeasurable.max aemeasurable_const)
  have mneg : ∀ ρ : Measure (Fin m → ℝ), Integrable f ρ →
      ∫⁻ a, ENNReal.ofReal (max (-f a) 0) ∂ρ
        = ∫⁻ t in Set.Ioi (0:ℝ), ρ {a | t < max (-f a) 0} := by
    intro ρ h
    apply lintegral_eq_lintegral_meas_lt
    · exact Filter.Eventually.of_forall (fun a => le_max_right _ _)
    · exact (h.1.aemeasurable.neg.max aemeasurable_const)
  have hP1 : ∫⁻ t in Set.Ioi (0:ℝ), ν {a | t < max (f a) 0}
      ≤ ∫⁻ t in Set.Ioi (0:ℝ), ν' {a | t < max (f a) 0} := by
    apply setLIntegral_mono' measurableSet_Ioi
    intro t ht
    have ht : (0:ℝ) < t := ht
    have e : ∀ a, (t < max (f a) 0) ↔ (t < f a) := by
      intro a
      rw [lt_max_iff]; constructor
      · rintro (h | h)
        · exact h
        · exact absurd h (not_lt.2 ht.le)
      · exact Or.inl
    simp only [e]
    exact vi_meas_le T f hf (fun a => t < a) (fun a b hab h => lt_of_lt_of_le h hab) ν ν' hν hν' hdom'
  have hP2 : ∫⁻ t in Set.Ioi (0:ℝ), ν' {a | t < max (-f a) 0}
      ≤ ∫⁻ t in Set.Ioi (0:ℝ), ν {a | t < max (-f a) 0} := by
    apply setLIntegral_mono' measurableSet_Ioi
    intro t ht
    have ht : (0:ℝ) < t := ht
    have e : {a | t < max (-f a) 0} = {a | -t ≤ f a}ᶜ := by
      ext a
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le, lt_max_iff]
      constructor
      · rintro (h | h)
        · linarith
        · exact absurd h (not_lt.2 ht.le)
      · intro h; exact Or.inl (by linarith)
    rw [e]
    have n1 : NullMeasurableSet {a | -t ≤ f a} ν :=
      aestronglyMeasurable_const.nullMeasurableSet_le hi.1
    have n2 : NullMeasurableSet {a | -t ≤ f a} ν' :=
      aestronglyMeasurable_const.nullMeasurableSet_le hi'.1
    rw [prob_compl_eq_one_sub₀ n1, prob_compl_eq_one_sub₀ n2]
    apply tsub_le_tsub_left
    exact vi_meas_le T f hf (fun a => -t ≤ a) (fun a b hab h => le_trans h hab) ν ν' hν hν' hdom'
  have f1 := hi.lintegral_lt_top
  have f2 := hi'.lintegral_lt_top
  have f3 : ∫⁻ a, ENNReal.ofReal (-f a) ∂ν < ⊤ := hi.neg.lintegral_lt_top
  have f4 : ∫⁻ a, ENNReal.ofReal (-f a) ∂ν' < ⊤ := hi'.neg.lintegral_lt_top
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi']
  have e1 := (hpos ν).trans (mpos ν hi)
  have e2 := (hpos ν').trans (mpos ν' hi')
  have e3 := (hneg ν).trans (mneg ν hi)
  have e4 := (hneg ν').trans (mneg ν' hi')
  have a1 : ∫⁻ a, ENNReal.ofReal (f a) ∂ν ≤ ∫⁻ a, ENNReal.ofReal (f a) ∂ν' := by
    rw [e1, e2]; exact hP1
  have a2 : ∫⁻ a, ENNReal.ofReal (-f a) ∂ν' ≤ ∫⁻ a, ENNReal.ofReal (-f a) ∂ν := by
    rw [e3, e4]; exact hP2
  have b1 := (ENNReal.toReal_le_toReal f1.ne f2.ne).2 a1
  have b2 := (ENNReal.toReal_le_toReal f4.ne f3.ne).2 a2
  linarith


theorem vi_core {n m : ℕ} (k : ℕ)
    (T : ℕ → Set (Fin m → ℝ)) (X : ℕ → (Fin m → ℝ) → Finset (Fin n → ℝ))
    (S : ℕ → Set ((Fin n → ℝ) × (Fin m → ℝ)))
    (hS : ∀ i, S i = {p : (Fin n → ℝ) × (Fin m → ℝ) | p.2 ∈ T i ∧ p.1 ∈ X i p.2})
    (r : ℕ → (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (μ : ℕ → (Fin n → ℝ) → (Fin m → ℝ) → Measure (Fin m → ℝ))
    (hμprob : ∀ i x t, IsProbabilityMeasure (μ i x t))
    (hμsupp : ∀ i, 1 ≤ i → i < k → ∀ x t, (x, t) ∈ S i → μ i x t (T (i + 1))ᶜ = 0)
    (f : ℕ → (Fin m → ℝ) → ℝ) (g : ℕ → (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (hgk : ∀ x t, g k x t = r k x t)
    (hg : ∀ i, 1 ≤ i → i < k → ∀ x t, (x, t) ∈ S i →
      g i x t = r i x t + (1 / (1 + β)) * ∫ w, f (i + 1) w ∂ (μ i x t))
    (hfint : ∀ i, 1 ≤ i → i < k → ∀ x t, (x, t) ∈ S i → Integrable (f (i + 1)) (μ i x t))
    (hf : ∀ i, 1 ≤ i → i ≤ k → ∀ t ∈ T i,
      IsGreatest ((fun x => g i x t) '' (X i t : Set (Fin n → ℝ))) (f i t))
    (hXne : ∀ i, 1 ≤ i → i ≤ k → ∀ t ∈ T i, (X i t).Nonempty)
    (hXsub : ∀ i, 1 ≤ i → i ≤ k → ∀ ⦃t' t'' : Fin m → ℝ⦄, t' ∈ T i → t'' ∈ T i → t' ≤ t'' →
      X i t' ⊆ X i t'')
    (hrmono : ∀ i, 1 ≤ i → i ≤ k → ∀ x, MonotoneOn (fun t => r i x t) {t | (x, t) ∈ S i})
    (hFmono : ∀ i, 1 ≤ i → i ≤ k → ∀ x,
      Supermodularity.MDP.StochasticallyIncreasingOn {t | (x, t) ∈ S i} (μ i x)) :
    ∀ i, 1 ≤ i → i ≤ k → MonotoneOn (f i) (T i) := by
  -- step: monotone g gives monotone f
  have step : ∀ i, 1 ≤ i → i ≤ k →
      (∀ x, MonotoneOn (fun t => g i x t) {t | (x, t) ∈ S i}) → MonotoneOn (f i) (T i) := by
    intro i hi1 hik hgm t' ht' t'' ht'' hle
    obtain ⟨⟨x', hx', hxe⟩, _⟩ := hf i hi1 hik t' ht'
    have hx'' : x' ∈ X i t'' := hXsub i hi1 hik ht' ht'' hle hx'
    have m1 : (x', t') ∈ S i := by rw [hS]; exact ⟨ht', hx'⟩
    have m2 : (x', t'') ∈ S i := by rw [hS]; exact ⟨ht'', hx''⟩
    have h1 : g i x' t' ≤ g i x' t'' := hgm x' m1 m2 hle
    have h2 : g i x' t'' ≤ f i t'' := (hf i hi1 hik t'' ht'').2 ⟨x', hx'', rfl⟩
    show f i t' ≤ f i t''
    have : f i t' = g i x' t' := hxe.symm
    linarith
  have main : ∀ d i, i + d = k → 1 ≤ i → MonotoneOn (f i) (T i) := by
    intro d
    induction d with
    | zero =>
      intro i hik hi1
      have hik' : i = k := by omega
      subst hik'
      apply step i hi1 le_rfl
      intro x a ha b hb hab
      simp only [hgk]
      exact hrmono i hi1 le_rfl x ha hb hab
    | succ d ih =>
      intro i hik hi1
      have hlt : i < k := by omega
      have ih' := ih (i + 1) (by omega) (by omega)
      apply step i hi1 hlt.le
      intro x a ha b hb hab
      have ha' : (x, a) ∈ S i := ha
      have hb' : (x, b) ∈ S i := hb
      simp only [hg i hi1 hlt x a ha', hg i hi1 hlt x b hb']
      have hγ : (0:ℝ) ≤ 1 / (1 + β) := by positivity
      have hr := hrmono i hi1 hlt.le x ha hb hab
      have := hμprob i x a
      have := hμprob i x b
      have hI := vi_integral_mono (T (i + 1)) (f (i + 1)) ih' (μ i x a) (μ i x b)
        (hμsupp i hi1 hlt x a ha') (hμsupp i hi1 hlt x b hb')
        (hfint i hi1 hlt x a ha') (hfint i hi1 hlt x b hb')
        (fun U hU => hFmono i hi1 hlt.le x hU ha hb hab)
      have := mul_le_mul_of_nonneg_left hI hγ
      show r i x a + _ ≤ r i x b + _
      have hr' : r i x a ≤ r i x b := hr
      linarith
  intro i hi1 hik
  exact main (k - i) i (by omega) hi1

end Supermodularity.MDP

open Supermodularity.MDP


theorem solution {n m : ℕ} (k : ℕ)
    (T : ℕ → Set (Fin m → ℝ)) (X : ℕ → (Fin m → ℝ) → Finset (Fin n → ℝ))
    (S : ℕ → Set ((Fin n → ℝ) × (Fin m → ℝ)))
    (hS : ∀ i, S i = {p : (Fin n → ℝ) × (Fin m → ℝ) | p.2 ∈ T i ∧ p.1 ∈ X i p.2})
    (r : ℕ → (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (μ : ℕ → (Fin n → ℝ) → (Fin m → ℝ) → Measure (Fin m → ℝ))
    (hμprob : ∀ i x t, IsProbabilityMeasure (μ i x t))
    (hμsupp : ∀ i, 1 ≤ i → i < k → ∀ x t, (x, t) ∈ S i → μ i x t (T (i + 1))ᶜ = 0)
    (f : ℕ → (Fin m → ℝ) → ℝ) (g : ℕ → (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (hgk : ∀ x t, g k x t = r k x t)
    (hg : ∀ i, 1 ≤ i → i < k → ∀ x t, (x, t) ∈ S i →
      g i x t = r i x t + (1 / (1 + β)) * ∫ w, f (i + 1) w ∂ (μ i x t))
    (hfint : ∀ i, 1 ≤ i → i < k → ∀ x t, (x, t) ∈ S i → Integrable (f (i + 1)) (μ i x t))
    (hf : ∀ i, 1 ≤ i → i ≤ k → ∀ t ∈ T i,
      IsGreatest ((fun x => g i x t) '' (X i t : Set (Fin n → ℝ))) (f i t))
    (hXne : ∀ i, 1 ≤ i → i ≤ k → ∀ t ∈ T i, (X i t).Nonempty)
    (hXsub : ∀ i, 1 ≤ i → i ≤ k → ∀ ⦃t' t'' : Fin m → ℝ⦄, t' ∈ T i → t'' ∈ T i → t' ≤ t'' →
      X i t' ⊆ X i t'')
    (hrmono : ∀ i, 1 ≤ i → i ≤ k → ∀ x, MonotoneOn (fun t => r i x t) {t | (x, t) ∈ S i})
    (hFmono : ∀ i, 1 ≤ i → i ≤ k → ∀ x,
      Supermodularity.MDP.StochasticallyIncreasingOn {t | (x, t) ∈ S i} (μ i x)) :
    ∀ i, 1 ≤ i → i ≤ k → MonotoneOn (f i) (T i) := by
  exact vi_core k T X S hS r β hβ0 hβ1 μ hμprob hμsupp f g hgk hg hfint hf hXne hXsub hrmono hFmono
