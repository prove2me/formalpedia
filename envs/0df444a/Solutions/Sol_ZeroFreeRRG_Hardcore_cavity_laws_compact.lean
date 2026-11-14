-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.cavity_laws_compact
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:55:04.060655+00:00
-- url     : https://prove2.me/submissions/ce5bed38-48da-4707-adff-2f2a443dd2dc

import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (m : Model) (t : ℝ) : IsCompact (cavityLaws m t) := by
  classical
  let X := m.Spin → ℝ
  let S : Set X := stdSimplex ℝ m.Spin
  let support : Set (ProbabilityMeasure X) := {ν | (ν : Measure X) Sᶜ = 0}
  have hsupp : IsCompact support := by
    have hh := isCompact_setOfPred_probabilityMeasure_mass_eq_compl_isCompact_le
      (u := fun _ : ℕ => (0 : NNReal)) (K := fun _ : ℕ => S)
      tendsto_const_nhds (fun _ => isCompact_stdSimplex ℝ m.Spin) (Or.inr (monotone_const))
    simpa [support] using hh
  let clip (a : m.Spin) : BoundedContinuousFunction X ℝ :=
    BoundedContinuousFunction.mkOfBound
      ⟨fun x => max 0 (min (x a) 1), continuous_const.max ((continuous_apply a).min continuous_const)⟩
      1 (by
        intro x y
        change dist (max 0 (min (x a) 1)) (max 0 (min (y a) 1)) ≤ 1
        rw [Real.dist_eq, abs_le]
        have hx0 : 0 ≤ max 0 (min (x a) 1) := le_max_left _ _
        have hx1 : max 0 (min (x a) 1) ≤ 1 := max_le (by norm_num) (min_le_right _ _)
        have hy0 : 0 ≤ max 0 (min (y a) 1) := le_max_left _ _
        have hy1 : max 0 (min (y a) 1) ≤ 1 := max_le (by norm_num) (min_le_right _ _)
        constructor <;> linarith)
  let moments : Set (ProbabilityMeasure X) := {ν | ∀ a, ∫ x, clip a x ∂(ν : Measure X) = m.pi t a}
  have hmoments : IsClosed moments := by
    dsimp [moments]
    have hc : IsClosed (⋂ a : m.Spin, {ν : ProbabilityMeasure X |
        ∫ x, clip a x ∂(ν : Measure X) = m.pi t a}) :=
      isClosed_iInter (fun a => isClosed_eq
        (ProbabilityMeasure.continuous_integral_boundedContinuousFunction (clip a)) continuous_const)
    convert hc using 1
    ext ν
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
  have hEq : cavityLaws m t = support ∩ moments := by
    ext ν
    constructor
    · intro hν
      refine ⟨hν.1,?_⟩
      intro a
      calc
        _ = ∫ x, x a ∂(ν : Measure X) := by
          apply integral_congr_ae
          have hae : ∀ᵐ x ∂(ν : Measure X), x ∈ S := ae_iff.mpr hν.1
          filter_upwards [hae] with x hx
          have hb : x a ∈ Icc (0:ℝ) 1 := mem_Icc_of_mem_stdSimplex hx a
          change max 0 (min (x a) 1) = x a
          rw [min_eq_left hb.2,max_eq_right hb.1]
        _ = m.pi t a := hν.2 a
    · rintro ⟨hs,hm⟩
      refine ⟨hs,?_⟩
      intro a
      calc
        _ = ∫ x, clip a x ∂(ν : Measure X) := by
          apply integral_congr_ae
          have hae : ∀ᵐ x ∂(ν : Measure X), x ∈ S := ae_iff.mpr hs
          filter_upwards [hae] with x hx
          have hb : x a ∈ Icc (0:ℝ) 1 := mem_Icc_of_mem_stdSimplex hx a
          change x a = max 0 (min (x a) 1)
          rw [min_eq_left hb.2,max_eq_right hb.1]
        _ = m.pi t a := hm a
  rw [hEq]
  exact hsupp.inter_right hmoments
