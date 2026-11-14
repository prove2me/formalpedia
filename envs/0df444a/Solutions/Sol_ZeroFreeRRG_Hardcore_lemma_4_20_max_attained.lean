-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.lemma_4_20_max_attained
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T11:10:53.651653+00:00
-- url     : https://prove2.me/submissions/5958a6b5-3e72-44ea-a351-1f950344deab

import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
import Definitions.Def_ZeroFreeRRG_Hardcore_Moments
import Theorems.Thm_ZeroFreeRRG_Hardcore_model_pi_positive_simplex
import Theorems.Thm_ZeroFreeRRG_Hardcore_cavity_dirac_membership
import Theorems.Thm_ZeroFreeRRG_Hardcore_cavity_laws_compact
import Theorems.Thm_ZeroFreeRRG_Hardcore_cavity_bethe_continuous
import Theorems.Thm_ZeroFreeRRG_Hardcore_cavity_perturbation_continuous
import Mathlib
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (m : Model) (hm : m.Valid) (d : ℕ) (t : ℝ) (ht : m.PosParam t) (s : ℝ) :
    ∃ ν₀ ∈ cavityLaws m t, ∀ ν ∈ cavityLaws m t,
      betheK m t d ν + d * s * ∫ μ, (∑ a, m.pi t a * (Mmul m t μ a - 1) ^ 2)
          ∂(ν : Measure (m.Spin → ℝ)) ≤
      betheK m t d ν₀ + d * s * ∫ μ, (∑ a, m.pi t a * (Mmul m t μ a - 1) ^ 2)
          ∂(ν₀ : Measure (m.Spin → ℝ)) := by
  classical
  have hπ := (model_pi_positive_simplex m hm t ht).2
  have hbase := cavity_dirac_membership m t hπ
  have hf := cavity_bethe_continuous m t d
  have hg := cavity_perturbation_continuous m t d
  have hcont : ContinuousOn (fun ν : ProbabilityMeasure (m.Spin → ℝ) =>
      betheK m t d ν + d * s * ∫ μ, (∑ a, m.pi t a * (Mmul m t μ a - 1)^2)
        ∂(ν : Measure (m.Spin → ℝ))) (cavityLaws m t) := by
    have h := hf.add (hg.const_mul s)
    change ContinuousOn (fun ν : ProbabilityMeasure (m.Spin → ℝ) =>
      betheK m t d ν + s*((d:ℝ) * ∫ μ, (∑ a, m.pi t a * (Mmul m t μ a - 1)^2)
        ∂(ν : Measure (m.Spin → ℝ)))) (cavityLaws m t) at h
    convert h using 1
    funext ν
    ring
  exact (cavity_laws_compact m t).exists_isMaxOn ⟨diracPi m t,hbase⟩ hcont
