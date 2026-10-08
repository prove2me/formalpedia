-- Prove2me | solution 1 for PoissonDirichlet.Chain.eq_146
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T23:16:11.622857+00:00
-- url     : https://prove2.me/submissions/b9ff73c2-04d0-4374-be24-2123a0c488da

import Mathlib
import Definitions.Def_PoissonDirichlet_Chain_Setting
open MeasureTheory ProbabilityTheory Filter Topology
open PoissonDirichlet.Chain

private lemma y_meas : Measurable (fun r : ℕ → ℝ => YofR r 0) := by
  unfold YofR
  apply Measurable.inv
  apply Measurable.add measurable_const
  apply Measurable.tsum
  intro j
  exact Finset.measurable_prod _ (fun i hi => measurable_pi_apply (0 + i))

theorem solution (α θ : ℝ) (hα : 0 < α) (hα1 : α < 1) (hθ : -α < θ) (k : ℕ)
    (μ : Measure (ℕ → ℝ)) (hμ : IsStarLaw α θ μ)
    (μ' : Measure (ℕ → ℝ)) (hμ' : IsStarLaw α (θ + (k : ℝ) * α) μ') :
    ∀ s : Set ℝ, MeasurableSet s →
      μ ((fun r => YofR r k) ⁻¹' s) = μ' ((fun r => YofR r 0) ⁻¹' s) := by
  haveI := hμ.1
  haveI := hμ'.1
  let shift : (ℕ → ℝ) → ℕ → ℝ := fun r i => r (k + i)
  have hm : Measurable shift := by fun_prop
  have hind : iIndepFun (fun i (r : ℕ → ℝ) => r (k + i)) μ :=
    hμ.2.1.precomp (by intro i j h; omega)
  have heq : μ.map shift = μ' := by
    have ha := hind.map_fun_eq_infinitePi_map (by intro i; fun_prop)
    have hb := hμ'.2.1.map_fun_eq_infinitePi_map (by intro i; fun_prop)
    have hc : ∀ i, μ.map (fun r : ℕ → ℝ => r (k+i)) = μ'.map (fun r => r i) := by
      intro i
      rw [(hμ.2.2 (k+i)).map_eq, (hμ'.2.2 i).map_eq]
      congr 1
      push_cast
      ring
    simp only [hc] at ha
    change μ'.map id = _ at hb
    rw [Measure.map_id] at hb
    simpa only [shift, Measure.map_id] using ha.trans hb.symm
  intro s hs
  have hpre : shift ⁻¹' ((fun r => YofR r 0) ⁻¹' s) = (fun r => YofR r k) ⁻¹' s := by
    ext r
    simp [shift, YofR]
  rw [← heq, Measure.map_apply hm (y_meas hs), hpre]
#print axioms solution
