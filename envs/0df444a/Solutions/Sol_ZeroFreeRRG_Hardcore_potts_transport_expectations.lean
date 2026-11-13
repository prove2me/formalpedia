-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.potts_transport_expectations
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T05:49:06.528309+00:00
-- url     : https://prove2.me/submissions/2bd34691-b23a-4e60-835e-589eabfaa63d

import Theorems.Thm_ZeroFreeRRG_Hardcore_potts_affine_factors
import Mathlib
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open scoped Classical BigOperators
open MeasureTheory Set ZeroFreeRRG.Hardcore

private noncomputable def affine (q : ℕ) (c : ℝ) (μ : Fin q → ℝ) : Fin q → ℝ :=
  fun i => (1-c)*(q:ℝ)⁻¹+c*μ i

private theorem affine_cont (q : ℕ) (c : ℝ) : Continuous (affine q c) := by
  apply continuous_pi
  intro i
  exact continuous_const.add (continuous_const.mul (continuous_apply i))

private theorem vertex_cont (q d : ℕ) (β : ℝ) :
    Continuous (fun μs : Fin d → Fin q → ℝ => vertexFactor (.potts q) β d μs) := by
  unfold vertexFactor Mmul
  fun_prop

private theorem edge_cont (q : ℕ) (β : ℝ) :
    Continuous (fun p : (Fin q → ℝ) × (Fin q → ℝ) => edgeFactor (.potts q) β p.1 p.2) := by
  unfold edgeFactor
  fun_prop

private theorem vertex_entropy_cont (q d : ℕ) (β : ℝ) :
    Continuous (fun μs : Fin d → Fin q → ℝ => xlogx (vertexFactor (.potts q) β d μs)) :=
  Real.continuous_mul_log.comp (vertex_cont q d β)

private theorem edge_entropy_cont (q : ℕ) (β : ℝ) :
    Continuous (fun p : (Fin q → ℝ) × (Fin q → ℝ) => xlogx (edgeFactor (.potts q) β p.1 p.2)) :=
  Real.continuous_mul_log.comp (edge_cont q β)

private theorem simplex_ae (q : ℕ) (β : ℝ) (ν : ProbabilityMeasure (Fin q → ℝ))
    (hν : ν ∈ cavityLaws (.potts q) β) :
    ∀ᵐ μ ∂(ν : Measure (Fin q → ℝ)), μ ∈ stdSimplex ℝ (Fin q) := by
  exact ae_iff.mpr hν.1

private theorem simplex_pi_ae (q d : ℕ) (β : ℝ) (ν : ProbabilityMeasure (Fin q → ℝ))
    (hν : ν ∈ cavityLaws (.potts q) β) :
    ∀ᵐ xs ∂(Measure.pi fun _ : Fin d => (ν : Measure (Fin q → ℝ))),
      ∀ i, xs i ∈ stdSimplex ℝ (Fin q) := by
  apply Measure.ae_pi_le_pi
  apply Filter.eventually_pi
  intro i
  exact simplex_ae q β ν hν

private theorem simplex_pair_ae (q : ℕ) (β : ℝ) (ν : ProbabilityMeasure (Fin q → ℝ))
    (hν : ν ∈ cavityLaws (.potts q) β) :
    ∀ᵐ p ∂((ν : Measure (Fin q → ℝ)).prod (ν : Measure (Fin q → ℝ))),
      p.1 ∈ stdSimplex ℝ (Fin q) ∧ p.2 ∈ stdSimplex ℝ (Fin q) := by
  have hs : MeasurableSet (stdSimplex ℝ (Fin q)) := (isClosed_stdSimplex ℝ (Fin q)).measurableSet
  apply (Measure.ae_prod_iff_ae_ae (hs.prod hs)).2
  filter_upwards [simplex_ae q β ν hν] with x hx
  filter_upwards [simplex_ae q β ν hν] with y hy
  exact ⟨hx,hy⟩

/-- Product expectations transform coordinatewise under a continuous message map. -/
private theorem pi_pushforward_expectation (q d : ℕ) (ν : ProbabilityMeasure (Fin q → ℝ))
    (f : (Fin q → ℝ) → (Fin q → ℝ)) (hf : Continuous f)
    (H : (Fin d → Fin q → ℝ) → ℝ) (hH : Continuous H) :
    (∫ ys, H ys ∂(Measure.pi fun _ : Fin d => ((ν.map hf.measurable.aemeasurable : ProbabilityMeasure (Fin q → ℝ)) : Measure (Fin q → ℝ)))) =
      ∫ xs, H (fun i => f (xs i)) ∂(Measure.pi fun _ : Fin d => (ν : Measure (Fin q → ℝ))) := by
  have hmap : (Measure.pi fun _ : Fin d => ((ν.map hf.measurable.aemeasurable : ProbabilityMeasure (Fin q → ℝ)) : Measure (Fin q → ℝ))) =
      (Measure.pi fun _ : Fin d => (ν : Measure (Fin q → ℝ))).map (fun xs i => f (xs i)) := by
    symm
    apply Measure.pi_map_pi
    intro i
    exact hf.measurable.aemeasurable
  rw [hmap]
  apply integral_map _ hH.aestronglyMeasurable
  apply (continuous_pi fun i => hf.comp (continuous_apply i)).measurable.aemeasurable

/-- Pair expectations transform under the same continuous message map. -/
private theorem pair_pushforward_expectation (q : ℕ) (ν : ProbabilityMeasure (Fin q → ℝ))
    (f : (Fin q → ℝ) → (Fin q → ℝ)) (hf : Continuous f)
    (H : ((Fin q → ℝ) × (Fin q → ℝ)) → ℝ) (hH : Continuous H) :
    (∫ ys, H ys ∂(((ν.map hf.measurable.aemeasurable : ProbabilityMeasure (Fin q → ℝ)) : Measure (Fin q → ℝ))).prod
      (((ν.map hf.measurable.aemeasurable : ProbabilityMeasure (Fin q → ℝ)) : Measure (Fin q → ℝ)))) =
      ∫ xs, H (f xs.1, f xs.2) ∂((ν : Measure (Fin q → ℝ)).prod (ν : Measure (Fin q → ℝ))) := by
  change (∫ ys, H ys ∂((Measure.map f (ν : Measure (Fin q → ℝ))).prod
      (Measure.map f (ν : Measure (Fin q → ℝ))))) = _
  rw [Measure.map_prod_map _ _ hf.measurable hf.measurable]
  exact integral_map (hf.measurable.prodMap hf.measurable).aemeasurable hH.aestronglyMeasurable


/-- The vertex expectation is invariant under the Potts message contraction. -/
theorem vertex_transport (q d : ℕ) (hq : 2 ≤ q) (β β' c : ℝ)
    (hb : 0 ≤ β) (hb' : 0 ≤ β')
    (hk : c*((β'-1)/((q:ℝ)-1+β')) = (β-1)/((q:ℝ)-1+β))
    (ν : ProbabilityMeasure (Fin q → ℝ)) (hν : ν ∈ cavityLaws (.potts q) β) :
    (∫ ys, xlogx (vertexFactor (.potts q) β' d ys)
      ∂(Measure.pi fun _ : Fin d => ((ν.map (affine_cont q c).measurable.aemeasurable : ProbabilityMeasure _) : Measure (Fin q → ℝ)))) =
    (∫ xs, xlogx (vertexFactor (.potts q) β d xs)
      ∂(Measure.pi fun _ : Fin d => (ν : Measure (Fin q → ℝ)))) := by
  have hq' : (2:ℝ) ≤ q := by exact_mod_cast hq
  have hqn : (q:ℝ) ≠ 0 := by linarith
  let u : Fin q → ℝ := fun _ => (q:ℝ)⁻¹
  have hu : (∑ i : Fin q, u i) = 1 := by dsimp [u]; simp [hqn]
  have hmap := pi_pushforward_expectation q d ν (affine q c) (affine_cont q c)
    (fun ys => xlogx (vertexFactor (.potts q) β' d ys)) (vertex_entropy_cont q d β')
  rw [hmap]
  apply integral_congr_ae
  filter_upwards [simplex_pi_ae q d β ν hν] with xs hxs
  have hsum : ∀ r, (∑ i, xs r i) = 1 := fun r => (hxs r).2
  have hfac := (potts_affine_factors q d hq β β' c hb hb' hk xs hsum u u hu hu).1
  change xlogx (vertexFactor (.potts q) β' d (fun i => affine q c (xs i))) = _
  exact congrArg xlogx hfac

/-- The transformed edge entropy is the entropy of an affine image of the original factor. -/
theorem edge_transport (q : ℕ) (hq : 2 ≤ q) (β β' c : ℝ)
    (hb : 0 ≤ β) (hb' : 0 ≤ β')
    (hk : c*((β'-1)/((q:ℝ)-1+β')) = (β-1)/((q:ℝ)-1+β))
    (ν : ProbabilityMeasure (Fin q → ℝ)) (hν : ν ∈ cavityLaws (.potts q) β) :
    (∫ ys, xlogx (edgeFactor (.potts q) β' ys.1 ys.2)
      ∂((ν.map (affine_cont q c).measurable.aemeasurable : ProbabilityMeasure (Fin q → ℝ)) : Measure (Fin q → ℝ)).prod
       ((ν.map (affine_cont q c).measurable.aemeasurable : ProbabilityMeasure (Fin q → ℝ)) : Measure (Fin q → ℝ))) =
    (∫ xs, xlogx (1-c+c*edgeFactor (.potts q) β xs.1 xs.2)
      ∂((ν : Measure (Fin q → ℝ)).prod (ν : Measure (Fin q → ℝ)))) := by
  have hmap := pair_pushforward_expectation q ν (affine q c) (affine_cont q c)
    (fun ys => xlogx (edgeFactor (.potts q) β' ys.1 ys.2)) (edge_entropy_cont q β')
  rw [hmap]
  apply integral_congr_ae
  filter_upwards [simplex_pair_ae q β ν hν] with p hp
  have hfac := (potts_affine_factors q 0 hq β β' c hb hb' hk
    (fun i => Fin.elim0 i) (by intro i; exact Fin.elim0 i) p.1 p.2 hp.1.2 hp.2.2).2
  change xlogx (edgeFactor (.potts q) β' (affine q c p.1) (affine q c p.2)) = _
  exact congrArg xlogx hfac

theorem solution (q d : ℕ) (hq : 2 ≤ q) (β β' c : ℝ)
    (hb : 0 ≤ β) (hb' : 0 ≤ β')
    (hk : c*((β'-1)/((q:ℝ)-1+β')) = (β-1)/((q:ℝ)-1+β))
    (ν ν' : ProbabilityMeasure (Fin q → ℝ)) (hν : ν ∈ cavityLaws (.potts q) β)
    (hmap : (ν' : Measure (Fin q → ℝ)) = Measure.map (fun μ : Fin q → ℝ => fun i => (1-c)*(q:ℝ)⁻¹+c*μ i) (ν : Measure (Fin q → ℝ))) :
    (∫ ys, xlogx (vertexFactor (.potts q) β' d ys)
      ∂(Measure.pi fun _ : Fin d => (ν' : Measure (Fin q → ℝ)))) =
    (∫ xs, xlogx (vertexFactor (.potts q) β d xs)
      ∂(Measure.pi fun _ : Fin d => (ν : Measure (Fin q → ℝ)))) ∧
    (∫ ys, xlogx (edgeFactor (.potts q) β' ys.1 ys.2)
      ∂((ν' : Measure (Fin q → ℝ)).prod (ν' : Measure (Fin q → ℝ)))) =
    (∫ xs, xlogx (1-c+c*edgeFactor (.potts q) β xs.1 xs.2)
      ∂((ν : Measure (Fin q → ℝ)).prod (ν : Measure (Fin q → ℝ)))) := by
  have heq : ν' = ν.map (affine_cont q c).measurable.aemeasurable := by
    apply ProbabilityMeasure.toMeasure_injective
    exact hmap
  subst ν'
  exact ⟨vertex_transport q d hq β β' c hb hb' hk ν hν,
    edge_transport q hq β β' c hb hb' hk ν hν⟩
