-- Prove2me | solution 1 for TeschlQM.OneParticle.hydrogen_spectrum
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-07T15:11:56.380614+00:00
-- url     : https://prove2.me/submissions/6e88446c-4c4e-41ac-aa32-834866041a26
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_TeschlQM_Shared_resolventSet
import Definitions.Def_TeschlQM_OneParticle_essentialSpectrum
import Definitions.Def_TeschlQM_OneParticle_hydrogenHamiltonian
import Theorems.Thm_TeschlQM_OneParticle_hydrogen_eigenvalues
import Theorems.Thm_TeschlQM_OneParticle_schroedinger_selfAdjoint

open MeasureTheory Filter Topology TeschlQM.OneParticle

namespace HydSpecAux

/-- The Coulomb potential `-γ/|x|` on `ℝ³`. -/
noncomputable def coul (γ : ℝ) (x : EuclideanSpace ℝ (Fin 3)) : ℝ := -γ / ‖x‖

lemma coul_measurable (γ : ℝ) : Measurable (coul γ) := by
  unfold coul; fun_prop

/-- The far part of the Coulomb potential is bounded and vanishes at infinity. -/
lemma far_bvi (γ : ℝ) :
    IsBoundedVanishingAtInfinity ((Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1)ᶜ.indicator
      (coul γ)) := by
  refine ⟨(coul_measurable γ).indicator Metric.isOpen_ball.measurableSet.compl, ⟨|γ|, ?_⟩, ?_⟩
  · intro x
    by_cases hx : x ∈ (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1)ᶜ
    · rw [Set.indicator_of_mem hx]
      have h1 : 1 ≤ ‖x‖ := by simpa using hx
      unfold coul
      rw [abs_div, abs_neg, abs_norm]
      rw [div_le_iff₀ (by linarith)]
      nlinarith [abs_nonneg γ]
    · rw [Set.indicator_of_notMem hx]; simp
  · have hn : Tendsto (fun x : EuclideanSpace ℝ (Fin 3) => ‖x‖) (cocompact _) atTop :=
      tendsto_norm_cocompact_atTop
    have h0 : Tendsto (fun x : EuclideanSpace ℝ (Fin 3) => coul γ x) (cocompact _) (𝓝 0) := by
      unfold coul
      exact tendsto_const_nhds.div_atTop hn
    refine h0.congr' ?_
    filter_upwards [hn.eventually_ge_atTop 1] with x hx
    rw [Set.indicator_of_mem]
    simpa using hx

/-- The near part of the Coulomb potential is square integrable on `ℝ³`. -/
lemma near_memLp (γ : ℝ) :
    MemLp ((Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1).indicator (coul γ)) 2 volume := by
  have hmeas : AEStronglyMeasurable
      ((Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1).indicator (coul γ)) volume :=
    ((coul_measurable γ).indicator Metric.isOpen_ball.measurableSet).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hmeas]
  have hsq : (fun x => (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1).indicator (coul γ) x ^ 2) =
      (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1).indicator (fun x => coul γ x ^ 2) := by
    ext x
    by_cases hx : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  rw [hsq, integrable_indicator_iff Metric.isOpen_ball.measurableSet]
  refine integrableOn_ball_of_norm_le_rpow (C := γ ^ 2) (α := 2) (by simp) (by simp; norm_num)
    (Eventually.of_forall fun x => ?_) ((coul_measurable γ).pow_const 2).aestronglyMeasurable
  unfold coul
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), div_pow, neg_sq, Real.rpow_neg (norm_nonneg _),
    div_eq_mul_inv]
  norm_cast

end HydSpecAux

open HydSpecAux in
theorem solution (γ : ℝ) (hγ : 0 < γ) :
    ∃ E : ℕ → ℝ, StrictMono E ∧ (∀ j, E j < 0) ∧ Tendsto E atTop (𝓝 0) ∧
      pointSpectrum (hydrogenHamiltonian γ) = Set.range (fun j => (E j : ℂ)) ∧
      discreteSpectrum (hydrogenHamiltonian γ) = Set.range (fun j => (E j : ℂ)) := by
  set E : ℕ → ℝ := fun k => -((γ / (2 * ((k : ℝ) + 1))) ^ 2) with hE
  have hpt : pointSpectrum (hydrogenHamiltonian γ) = Set.range (fun j => (E j : ℂ)) :=
    hydrogen_eigenvalues γ hγ
  -- essential spectrum from Theorem 10.2
  have hess : essentialSpectrum (hydrogenHamiltonian γ) = (fun t : ℝ => (t : ℂ)) '' Set.Ici 0 := by
    have h := schroedinger_selfAdjoint 3 (by norm_num) (coul γ) (fun h => absurd h (lt_irrefl 3))
      (fun _ => ⟨_, _, far_bvi γ, near_memLp γ, (Set.indicator_compl_add_self _ _).symm⟩)
    exact h.2.2.2.2.1
  have hEneg : ∀ j, E j < 0 := by
    intro j
    simp only [hE, neg_lt_zero]
    have : 0 < 2 * ((j : ℝ) + 1) := by positivity
    positivity
  refine ⟨E, ?_, hEneg, ?_, hpt, ?_⟩
  · intro i j hij
    simp only [hE, neg_lt_neg_iff]
    have hi : (0 : ℝ) < 2 * ((i : ℝ) + 1) := by positivity
    have hj : 2 * ((i : ℝ) + 1) < 2 * ((j : ℝ) + 1) := by
      have : (i : ℝ) < j := by exact_mod_cast hij
      linarith
    have h1 : γ / (2 * ((j : ℝ) + 1)) < γ / (2 * ((i : ℝ) + 1)) :=
      div_lt_div_of_pos_left hγ hi hj
    have h2 : 0 ≤ γ / (2 * ((j : ℝ) + 1)) := by positivity
    exact pow_lt_pow_left₀ h1 h2 (by norm_num)
  · have h1 : Tendsto (fun k : ℕ => 2 * ((k : ℝ) + 1)) atTop atTop := by
      apply Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
      exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun k : ℕ => γ / (2 * ((k : ℝ) + 1))) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop h1
    have h3 := (h2.pow 2).neg
    simpa [hE] using h3
  · apply Set.Subset.antisymm
    · intro z hz
      rw [← hpt]
      exact hz.2.1
    · intro z hz
      have hzp : z ∈ pointSpectrum (hydrogenHamiltonian γ) := hpt ▸ hz
      obtain ⟨j, rfl⟩ := hz
      -- eigenvalues lie in the spectrum
      have hspec : ((E j : ℝ) : ℂ) ∈ TeschlQM.Shared.spectrum (hydrogenHamiltonian γ) := by
        intro hres
        obtain ⟨R, -, hR⟩ := hres
        apply hzp
        rw [eq_bot_iff]
        rintro _ ⟨ψ, hψ, rfl⟩
        have hk : (hydrogenHamiltonian γ).toFun ψ - ((E j : ℝ) : ℂ) • (ψ : L2 3) = 0 := by
          exact LinearMap.mem_ker.mp hψ
        have := hR ψ
        change R ((hydrogenHamiltonian γ).toFun ψ - ((E j : ℝ) : ℂ) • (ψ : L2 3)) = ψ at this
        rw [hk, map_zero] at this
        simp [← this]
      by_contra hnd
      have hmem : ((E j : ℝ) : ℂ) ∈ essentialSpectrum (hydrogenHamiltonian γ) := ⟨hspec, hnd⟩
      rw [hess] at hmem
      obtain ⟨t, ht, hteq⟩ := hmem
      have : t = E j := by simpa using hteq
      have := hEneg j
      simp only [Set.mem_Ici] at ht
      linarith
