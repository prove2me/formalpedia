-- Prove2me | solution 1 for VectorPayoffs.Convex.not_approachable_and_excludable
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:30:25.080626+00:00
-- url     : https://prove2.me/submissions/337a9f4a-3955-4113-a2c9-ab501e732439

import Mathlib
import Definitions.Def_VectorPayoffs_Convex_Game

open MeasureTheory

namespace VectorPayoffs.Convex

open ProbabilityTheory Finset Preorder

/-- The history `(z₁, …, zₙ)` extracted from a finite trajectory `(z₀, …, zₙ)`. -/
def aux_nae_h {N : ℕ} (n : ℕ) (z : (i : Iic n) → E N) : Fin n → E N :=
  fun k => z ⟨k.val + 1, by simp only [Finset.mem_Iic]; omega⟩

lemma aux_nae_h_meas {N : ℕ} (n : ℕ) : Measurable (aux_nae_h (N := N) n) := by
  unfold aux_nae_h
  fun_prop

/-- The one-step law of the next outcome given a history. -/
noncomputable def aux_nae_meas {N r s : ℕ} (G : Game N r s) (f : Strategy N r)
    (g : Strategy N s) (n : ℕ) (h : Fin n → E N) : Measure (E N) :=
  ∑ i, ∑ j, ENNReal.ofReal (f.toFun n h i * g.toFun n h j) • G.m i j

lemma aux_nae_meas_apply {N r s : ℕ} (G : Game N r s) (f : Strategy N r)
    (g : Strategy N s) (n : ℕ) (h : Fin n → E N) (B : Set (E N)) :
    aux_nae_meas G f g n h B =
      ∑ i, ∑ j, ENNReal.ofReal (f.toFun n h i * g.toFun n h j) * G.m i j B := by
  simp [aux_nae_meas, Finset.sum_apply]

noncomputable def aux_nae_kernel {N r s : ℕ} (G : Game N r s) (f : Strategy N r)
    (g : Strategy N s) (n : ℕ) : Kernel ((i : Iic n) → E N) (E N) where
  toFun z := aux_nae_meas G f g n (aux_nae_h n z)
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ (fun B _ => ?_)
    simp_rw [aux_nae_meas_apply]
    refine Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _ (fun j _ => ?_))
    refine Measurable.mul_const ?_ _
    refine ENNReal.measurable_ofReal.comp ?_
    refine Measurable.mul ?_ ?_
    · exact (measurable_pi_apply i).comp ((f.meas n).comp (aux_nae_h_meas n))
    · exact (measurable_pi_apply j).comp ((g.meas n).comp (aux_nae_h_meas n))

lemma aux_nae_kernel_apply {N r s : ℕ} (G : Game N r s) (f : Strategy N r)
    (g : Strategy N s) (n : ℕ) (z : (i : Iic n) → E N) :
    aux_nae_kernel G f g n z = aux_nae_meas G f g n (aux_nae_h n z) := rfl

instance aux_nae_kernel_markov {N r s : ℕ} (G : Game N r s) (f : Strategy N r)
    (g : Strategy N s) (n : ℕ) : IsMarkovKernel (aux_nae_kernel G f g n) := by
  refine ⟨fun z => ⟨?_⟩⟩
  rw [aux_nae_kernel_apply, aux_nae_meas_apply]
  set h := aux_nae_h n z
  have hf := f.mem n h
  have hg := g.mem n h
  have e1 : ∀ i j, G.m i j Set.univ = 1 := fun i j => by
    have := G.isProb i j
    exact measure_univ
  simp only [e1, mul_one]
  rw [← ENNReal.ofReal_one]
  have hsum : ∑ i, ∑ j, f.toFun n h i * g.toFun n h j = 1 := by
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul, hf.2, hg.2, one_mul]
  rw [← hsum, ENNReal.ofReal_sum_of_nonneg]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [ENNReal.ofReal_sum_of_nonneg]
    intro j _
    exact mul_nonneg (hf.1 i) (hg.1 j)
  · intro i _
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (hf.1 i) (hg.1 j))

lemma aux_nae_toReal {N r s : ℕ} (G : Game N r s) (f : Strategy N r)
    (g : Strategy N s) (n : ℕ) (h : Fin n → E N) (B : Set (E N)) :
    (aux_nae_meas G f g n h B).toReal =
      ∑ i, ∑ j, f.toFun n h i * g.toFun n h j * (G.m i j B).toReal := by
  have hf := f.mem n h
  have hg := g.mem n h
  have hne : ∀ i j, G.m i j B ≠ ⊤ := fun i j => by
    have := G.isProb i j
    exact measure_ne_top _ _
  rw [aux_nae_meas_apply, ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [ENNReal.toReal_sum]
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg (hf.1 i) (hg.1 j))]
    · intro j _
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hne i j)
  · intro i _
    exact ENNReal.sum_ne_top.2 (fun j _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hne i j))

/-- The canonical play built by the Ionescu-Tulcea theorem. -/
noncomputable def aux_nae_mu {N r s : ℕ} (G : Game N r s) (f : Strategy N r)
    (g : Strategy N s) : Measure (ℕ → E N) :=
  Kernel.traj (aux_nae_kernel G f g) 0 (fun _ => 0)

instance aux_nae_mu_prob {N r s : ℕ} (G : Game N r s) (f : Strategy N r)
    (g : Strategy N s) : IsProbabilityMeasure (aux_nae_mu G f g) := by
  unfold aux_nae_mu
  infer_instance

lemma aux_nae_isPlay {N r s : ℕ} (G : Game N r s) (f : Strategy N r)
    (g : Strategy N s) : G.IsPlay f g (aux_nae_mu G f g) (fun n ω => ω n) := by
  refine ⟨fun n => measurable_pi_apply (n + 1), fun n B hB => ?_⟩
  set κ := aux_nae_kernel G f g
  set μ := aux_nae_mu G f g
  set x : ℕ → (ℕ → E N) → E N := fun n ω => ω n
  set F : (ℕ → E N) → ℝ := (x (n + 1) ⁻¹' B).indicator (fun _ => (1 : ℝ))
  have hxm : Measurable (x (n + 1)) := measurable_pi_apply (n + 1)
  have hFi : Integrable F μ := (integrable_const (1 : ℝ)).indicator (hxm hB)
  -- the explicit conditional probability as a function of the trajectory
  set Φ : (ℕ → E N) → ℝ := fun ω => (κ n (frestrictLe n ω) B).toReal
  have hhist : ∀ ω, hist x n ω = aux_nae_h n (frestrictLe n ω) := fun ω => rfl
  have hΦ : ∀ ω, Φ ω = ∑ i, ∑ j,
      f.toFun n (hist x n ω) i * g.toFun n (hist x n ω) j * (G.m i j B).toReal := by
    intro ω
    simp only [Φ, κ, aux_nae_kernel_apply, hhist]
    exact aux_nae_toReal G f g n _ B
  -- step 1: conditional expectation w.r.t. the full past
  have h1 : μ[F | Filtration.piLE n] =ᵐ[μ] Φ := by
    refine (Kernel.condExp_traj (Nat.zero_le n) hFi).trans (Filter.Eventually.of_forall ?_)
    intro ω
    simp only [Φ]
    rw [show F = Set.indicator ((fun y : ℕ → E N => y (n + 1)) ⁻¹' B) 1 from rfl,
      integral_indicator_one (hxm hB), Measure.real_def,
      ← Measure.map_apply hxm hB, ← Kernel.map_apply _ hxm, Kernel.map_traj_succ_self]
  -- the σ-algebra generated by the history
  have hmle : MeasurableSpace.comap (hist x n) inferInstance ≤ Filtration.piLE n := by
    rw [Filtration.piLE_eq_comap_frestrictLe]
    have : hist x n = aux_nae_h n ∘ frestrictLe n := funext hhist
    rw [this, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (aux_nae_h_meas n).comap_le
  have hpile : (Filtration.piLE n : MeasurableSpace (ℕ → E N)) ≤ MeasurableSpace.pi :=
    Filtration.le _ n
  -- Φ is measurable w.r.t. the history σ-algebra
  have hΦm : StronglyMeasurable[MeasurableSpace.comap (hist x n) inferInstance] Φ := by
    have : Φ = (fun h => (aux_nae_meas G f g n h B).toReal) ∘ hist x n := by
      funext ω
      simp only [Φ, κ, aux_nae_kernel_apply, Function.comp_apply, hhist]
    rw [this]
    refine Measurable.stronglyMeasurable ?_
    refine Measurable.comp ?_ (comap_measurable (hist x n))
    refine Measurable.ennreal_toReal ?_
    simp_rw [aux_nae_meas_apply]
    refine Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _ (fun j _ => ?_))
    refine Measurable.mul_const ?_ _
    refine ENNReal.measurable_ofReal.comp ?_
    refine Measurable.mul ?_ ?_
    · exact (measurable_pi_apply i).comp (f.meas n)
    · exact (measurable_pi_apply j).comp (g.meas n)
  have hΦi : Integrable Φ μ := by
    refine Integrable.of_bound (hΦm.mono (hmle.trans hpile)).aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun ω => ?_))
    simp only [Φ, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
  have h2 : μ[F | MeasurableSpace.comap (hist x n) inferInstance] =ᵐ[μ] Φ := by
    refine (condExp_condExp_of_le hmle hpile).symm.trans ?_
    refine (condExp_congr_ae h1).trans ?_
    rw [condExp_of_stronglyMeasurable (hmle.trans hpile) hΦm hΦi]
  refine h2.trans (Filter.Eventually.of_forall (fun ω => hΦ ω))

end VectorPayoffs.Convex

open VectorPayoffs.Convex

open MeasureTheory

theorem solution {N r s : ℕ} (G : Game N r s) (hr : 1 ≤ r)
    (hs : 1 ≤ s) (S : Set (E N)) : ¬ (G.ApproachableIn S ∧ G.ExcludableIn S) := by
  rintro ⟨⟨f, hf⟩, ⟨g, d, hd, hg⟩⟩
  set ε : ℝ := min d (1 / 2) with hεdef
  have hε : 0 < ε := lt_min hd (by norm_num)
  have hεd : ε ≤ d := min_le_left _ _
  have hε2 : ε ≤ 1 / 2 := min_le_right _ _
  obtain ⟨N₀, hN₀⟩ := hf ε hε
  obtain ⟨N₁, hN₁⟩ := hg ε hε
  have hplay := aux_nae_isPlay G f g
  have h1 := hN₀ g (ℕ → E N) (aux_nae_mu G f g) (fun n ω => ω n) hplay
  have h2 := hN₁ f (ℕ → E N) (aux_nae_mu G f g) (fun n ω => ω n) hplay
  have hsub : {ω : ℕ → E N | ∀ n, N₁ ≤ n → 1 ≤ n →
      ENNReal.ofReal d ≤ Metric.infEDist (avg (fun n ω => ω n) n ω) S} ⊆
      {ω | ∃ n, N₀ ≤ n ∧ 1 ≤ n ∧
        ENNReal.ofReal ε ≤ Metric.infEDist (avg (fun n ω => ω n) n ω) S} := by
    intro ω hω
    refine ⟨max N₀ (max N₁ 1), le_max_left _ _, ?_, ?_⟩
    · exact le_trans (le_max_right _ _) (le_max_right _ _)
    · refine le_trans (ENNReal.ofReal_le_ofReal hεd) (hω _ ?_ ?_)
      · exact le_trans (le_max_left _ _) (le_max_right _ _)
      · exact le_trans (le_max_right _ _) (le_max_right _ _)
  have h3 := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (μ := aux_nae_mu G f g) hsub)
  linarith
