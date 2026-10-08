-- Prove2me | solution 1 for WeightedMajority.Randomized.expected_mistakes_eq
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T18:45:46.406174+00:00
-- url     : https://prove2.me/submissions/e6ced3f4-6265-4956-88fc-b63df59d422a

import Mathlib
import Definitions.Def_WeightedMajority_Randomized_WMRModel

open MeasureTheory


namespace WeightedMajority.Randomized

lemma wmr_weight_nonneg {Ω : Type*} [MeasurableSpace Ω] {n t : ℕ} {β : ℝ} {w1 : Fin n → ℝ}
    {F : ℕ → Fin n → ℝ → ℝ → ℝ} {x : ℕ → Fin n → Ω → ℝ} {ρ lam : ℕ → Ω → ℝ}
    (hM : IsWMRModel t β w1 F x ρ lam) :
    ∀ j ≤ t, ∀ i ω, 0 ≤ weight w1 F x ρ j i ω := by
  obtain ⟨hb0, hb1, hw, -, -, -, -, -, -, -, hF⟩ := hM
  intro j
  induction j with
  | zero => intro _ i ω; simp [weight]; exact (hw i).le
  | succ j ih =>
    intro hj i ω
    simp only [weight]
    have h1 := (hF j (by omega) i ω).1
    have h2 : 0 ≤ β ^ |x j i ω - ρ j ω| := Real.rpow_nonneg hb0 _
    exact mul_nonneg (h2.trans h1) (ih (by omega) i ω)

lemma wmr_gamma_mem {Ω : Type*} [MeasurableSpace Ω] {n t : ℕ} {β : ℝ} {w1 : Fin n → ℝ}
    {F : ℕ → Fin n → ℝ → ℝ → ℝ} {x : ℕ → Fin n → Ω → ℝ} {ρ lam : ℕ → Ω → ℝ}
    (hM : IsWMRModel t β w1 F x ρ lam) {j : ℕ} (hj : j < t) (ω : Ω) :
    0 ≤ gamma w1 F x ρ j ω ∧ gamma w1 F x ρ j ω ≤ 1 := by
  have hw := wmr_weight_nonneg hM j hj.le
  have hx := hM.2.2.2.2.2.1
  have hs : 0 ≤ totalWeight w1 F x ρ j ω := Finset.sum_nonneg (fun i _ => hw i ω)
  unfold gamma
  rcases hs.eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  · constructor
    · apply div_nonneg _ hs
      exact Finset.sum_nonneg (fun i _ => mul_nonneg (hw i ω) (hx j hj i ω).1)
    · rw [div_le_one hpos]
      unfold totalWeight
      exact Finset.sum_le_sum (fun i _ => by
        have := (hx j hj i ω).2
        nlinarith [hw i ω])

lemma wmr_history_le {Ω : Type*} [m0 : MeasurableSpace Ω] {n t : ℕ} {β : ℝ} {w1 : Fin n → ℝ}
    {F : ℕ → Fin n → ℝ → ℝ → ℝ} {x : ℕ → Fin n → Ω → ℝ} {ρ lam : ℕ → Ω → ℝ}
    (hM : IsWMRModel t β w1 F x ρ lam) {j : ℕ} (hj : j < t) :
    history x ρ j ≤ m0 := by
  obtain ⟨-, -, -, -, hx, -, hρ, -⟩ := hM
  refine iSup₂_le (fun k hk => ?_)
  apply Measurable.comap_le
  refine Measurable.prodMk ?_ (hρ k (by omega))
  exact measurable_pi_lambda _ (fun i => hx k (by omega) i)

lemma wmr_rho_meas {Ω : Type*} [m0 : MeasurableSpace Ω] {n : ℕ} (x : ℕ → Fin n → Ω → ℝ)
    (ρ : ℕ → Ω → ℝ) (j : ℕ) : Measurable[history x ρ j] (ρ j) := by
  have h : Measurable[MeasurableSpace.comap (fun ω => ((fun i => x j i ω), ρ j ω)) inferInstance]
      (ρ j) := by
    exact measurable_snd.comp (comap_measurable (fun ω => ((fun i => x j i ω), ρ j ω)))
  have hle : MeasurableSpace.comap (fun ω => ((fun i => x j i ω), ρ j ω)) inferInstance
      ≤ history x ρ j := le_iSup₂ (f := fun (k : ℕ) (_ : k ≤ j) =>
        MeasurableSpace.comap (fun ω => ((fun i => x k i ω), ρ k ω)) inferInstance) j le_rfl
  exact h.mono hle le_rfl

theorem em_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n t : ℕ} (β : ℝ) (w1 : Fin n → ℝ)
    (F : ℕ → Fin n → ℝ → ℝ → ℝ) (x : ℕ → Fin n → Ω → ℝ) (ρ lam : ℕ → Ω → ℝ)
    (hM : IsWMRModel t β w1 F x ρ lam)
    (hweak : WeakIndependence P t w1 F x ρ lam) :
    (∀ j < t, P[fun ω => |lam j ω - ρ j ω| | history x ρ j]
        =ᵐ[P] fun ω => |gamma w1 F x ρ j ω - ρ j ω|) ∧
    ∫ ω, mistakes t lam ρ ω ∂P
      = ∫ ω, ∑ j ∈ Finset.range t, |gamma w1 F x ρ j ω - ρ j ω| ∂P := by
  obtain ⟨-, -, -, -, -, -, hρm, hρ01, hlm, hl01, -⟩ := id hM
  have key : ∀ j < t, (P[fun ω => |lam j ω - ρ j ω| | history x ρ j]
        =ᵐ[P] fun ω => |gamma w1 F x ρ j ω - ρ j ω|) ∧
        Integrable (fun ω => |lam j ω - ρ j ω|) P := by
    intro j hj
    have hle := wmr_history_le hM hj
    have hρmeas : Measurable (ρ j) := hρm j hj
    have hlmeas : Measurable (lam j) := hlm j hj
    have hρi : Integrable (ρ j) P := by
      refine Integrable.of_bound hρmeas.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun ω => ?_)
      rcases hρ01 j hj ω with h | h <;> simp [h]
    have hli : Integrable (lam j) P := by
      refine Integrable.of_bound hlmeas.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun ω => ?_)
      rcases hl01 j hj ω with h | h <;> simp [h]
    have hcm : Measurable (fun ω => 1 - 2 * ρ j ω) := by fun_prop
    have hci : Integrable (fun ω => 1 - 2 * ρ j ω) P := by
      refine Integrable.of_bound hcm.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun ω => ?_)
      rcases hρ01 j hj ω with h | h <;> simp [h] <;> norm_num
    have hprod : Integrable ((fun ω => 1 - 2 * ρ j ω) * lam j) P := by
      refine Integrable.of_bound (hcm.mul hlmeas).aestronglyMeasurable 1 (Filter.Eventually.of_forall fun ω => ?_)
      rcases hρ01 j hj ω with h | h <;> rcases hl01 j hj ω with h' | h' <;> simp [h, h'] <;> norm_num
    have hfeq : (fun ω => |lam j ω - ρ j ω|) = ρ j + (fun ω => 1 - 2 * ρ j ω) * lam j := by
      funext ω
      rcases hρ01 j hj ω with h | h <;> rcases hl01 j hj ω with h' | h' <;> simp [h, h'] <;> norm_num
    have hint : Integrable (fun ω => |lam j ω - ρ j ω|) P := by
      rw [hfeq]; exact hρi.add hprod
    refine ⟨?_, hint⟩
    have hρs : StronglyMeasurable[history x ρ j] (ρ j) := (wmr_rho_meas x ρ j).stronglyMeasurable
    have hcs : StronglyMeasurable[history x ρ j] (fun ω => 1 - 2 * ρ j ω) := by
      have : Measurable[history x ρ j] (fun ω => 1 - 2 * ρ j ω) := by
        have := wmr_rho_meas x ρ j
        fun_prop
      exact this.stronglyMeasurable
    rw [hfeq]
    have h1 := condExp_add hρi hprod (history x ρ j) (μ := P)
    have h2 := condExp_mul_of_stronglyMeasurable_left hcs hprod hli (μ := P)
    have h3 : P[ρ j | history x ρ j] = ρ j := condExp_of_stronglyMeasurable hle hρs hρi
    have h4 := hweak j hj
    filter_upwards [h1, h2, h4] with ω a b c
    rw [a]
    simp only [Pi.add_apply, h3]
    rw [b]
    simp only [Pi.mul_apply, c]
    obtain ⟨g0, g1⟩ := wmr_gamma_mem hM hj ω
    rcases hρ01 j hj ω with h | h <;> simp [h] <;> [rw [abs_of_nonneg g0]; rw [abs_of_nonpos (by linarith)]] <;> ring
  refine ⟨fun j hj => (key j hj).1, ?_⟩
  unfold mistakes
  rw [integral_finset_sum _ (fun j hj => (key j (Finset.mem_range.1 hj)).2)]
  have hle := fun j (hj : j < t) => wmr_history_le hM hj
  have e : ∀ j ∈ Finset.range t, ∫ ω, |lam j ω - ρ j ω| ∂P = ∫ ω, |gamma w1 F x ρ j ω - ρ j ω| ∂P := by
    intro j hj
    have hj' := Finset.mem_range.1 hj
    rw [← integral_condExp (hle j hj') (μ := P) (f := fun ω => |lam j ω - ρ j ω|)]
    exact integral_congr_ae (key j hj').1
  rw [Finset.sum_congr rfl e, integral_finset_sum]
  intro j hj
  have hj' := Finset.mem_range.1 hj
  exact (integrable_condExp (μ := P) (m := history x ρ j) (f := fun ω => |lam j ω - ρ j ω|)).congr (key j hj').1

end WeightedMajority.Randomized

open WeightedMajority.Randomized


theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n t : ℕ} (β : ℝ) (w1 : Fin n → ℝ)
    (F : ℕ → Fin n → ℝ → ℝ → ℝ) (x : ℕ → Fin n → Ω → ℝ) (ρ lam : ℕ → Ω → ℝ)
    (hM : IsWMRModel t β w1 F x ρ lam)
    (hweak : WeakIndependence P t w1 F x ρ lam) :
    (∀ j < t, P[fun ω => |lam j ω - ρ j ω| | history x ρ j]
        =ᵐ[P] fun ω => |gamma w1 F x ρ j ω - ρ j ω|) ∧
    ∫ ω, mistakes t lam ρ ω ∂P
      = ∫ ω, ∑ j ∈ Finset.range t, |gamma w1 F x ρ j ω - ρ j ω| ∂P := by
  exact em_core P β w1 F x ρ lam hM hweak
