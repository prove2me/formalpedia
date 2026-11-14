-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.overlap_likelihood_model_reduction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:55:04.167392+00:00
-- url     : https://prove2.me/submissions/6581e127-f8c5-4fe5-ae5e-a7d899945428
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
import Definitions.Def_ZeroFreeRRG_Hardcore_Moments
import Theorems.Thm_ZeroFreeRRG_Hardcore_model_pi_positive_simplex
import Theorems.Thm_ZeroFreeRRG_Hardcore_cavity_dirac_membership
import Theorems.Thm_ZeroFreeRRG_Hardcore_cavity_perturbation_dirac_zero
import Theorems.Thm_ZeroFreeRRG_Hardcore_bethe_dirac_zero_general
import Theorems.Thm_ZeroFreeRRG_Hardcore_overlap_likelihood_model_bridge
import Mathlib
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (m : Model) (hm : m.Valid) (d : ℕ) (hd : 3 ≤ d) (t : ℝ) (ht : m.PosParam t)
    (hC1 : Condition1 m d t)
    (hcompact : IsCompact (cavityLaws m t))
    (hbethe : ContinuousOn (betheK m t d) (cavityLaws m t))
    (hpert : ContinuousOn (fun ν : ProbabilityMeasure (m.Spin → ℝ) =>
      (d:ℝ) * ∫ μ, (∑ a, m.pi t a * (Mmul m t μ a - 1)^2)
        ∂(ν : Measure (m.Spin → ℝ))) (cavityLaws m t)) :
    ∀ ε : ℝ, 0 < ε → ∃ s : ℝ, 0 < s ∧ s < 1 ∧ ∃ N : ℕ,
      ∀ n ≥ N, Even (n*d) →
        (1:ℝ)/n * plantedPinnedE m t s d n (fun M σ U => pinnedLL m t M σ U) ≤ ε*s := by
  classical
  obtain ⟨hpos,hπ⟩ := model_pi_positive_simplex m hm t ht
  have hnz (a : m.Spin) : m.pi t a ≠ 0 := ne_of_gt (hpos a)
  have hsum : (∑ a, m.pi t a) = 1 := hπ.2
  have hbase := bethe_dirac_zero_general m t d hnz hsum
  have hpertzero := (cavity_perturbation_dirac_zero m t d hnz).2
  exact overlap_likelihood_model_bridge m hm d hd t ht hC1 hcompact
    (cavity_dirac_membership m t hπ) hbethe hbase hpert hpertzero
