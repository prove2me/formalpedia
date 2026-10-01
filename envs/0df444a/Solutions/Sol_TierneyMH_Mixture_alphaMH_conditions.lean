-- Prove2me | solution 1 for TierneyMH.Mixture.alphaMH_conditions
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T12:00:30.637425+00:00
-- url     : https://prove2.me/submissions/45fdaf4d-e725-4dfe-bc49-4aa620b92db2

import Definitions.Def_TierneyMH_Mixture_alphaMH
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
open TierneyMH.Mixture

namespace TierneyProof
variable {E : Type*} [MeasurableSpace E] (π : Measure E) (Q : Kernel E E)

theorem density_measurable : Measurable (canonDensity π Q) :=
  Measure.measurable_rnDeriv _ _

theorem R_measurable : MeasurableSet (canonR π Q) :=
  (measurableSet_lt measurable_const (density_measurable π Q)).inter
    (measurableSet_lt measurable_const ((density_measurable π Q).comp measurable_swap))

theorem R_swap (p : E × E) : p.swap ∈ canonR π Q ↔ p ∈ canonR π Q := by
  simp [canonR,and_comm]

theorem ratio_pos (p : E × E) : 0 < canonRatio π Q p ∧ canonRatio π Q p ≠ ⊤ := by
  unfold canonRatio
  split_ifs with h
  · exact ⟨ENNReal.div_pos_iff.mpr ⟨ne_of_gt h.1.1,h.2.2⟩,
      ENNReal.div_ne_top h.2.1 (ne_of_gt h.1.2)⟩
  · simp

theorem ratio_inv (p : E × E) : canonRatio π Q p.swap = (canonRatio π Q p)⁻¹ := by
  classical
  have hs : (p.swap ∈ canonR π Q ∧ canonDensity π Q p.swap ≠ ⊤ ∧ canonDensity π Q p.swap.swap ≠ ⊤) ↔
      (p ∈ canonR π Q ∧ canonDensity π Q p ≠ ⊤ ∧ canonDensity π Q p.swap ≠ ⊤) := by
    simp [R_swap π Q,and_left_comm,and_comm,and_assoc]
  unfold canonRatio
  rw [if_congr hs rfl rfl]
  split_ifs with h
  · simpa using (ENNReal.inv_div (Or.inl h.2.2) (Or.inr (ne_of_gt h.1.1))).symm
  · simp

theorem alpha_identity (p : E × E) :
    alphaMH π Q p * canonRatio π Q p = alphaMH π Q p.swap := by
  by_cases hp : p ∈ canonR π Q
  · have hs := (R_swap π Q p).mpr hp
    simp only [alphaMH,Set.indicator_of_mem hp,Set.indicator_of_mem hs,Prod.swap_swap]
    rw [ratio_inv π Q p,min_mul,one_mul,
      ENNReal.inv_mul_cancel (ne_of_gt (ratio_pos π Q p).1) (ratio_pos π Q p).2,min_comm]
  · have hs : p.swap ∉ canonR π Q := fun h => hp ((R_swap π Q p).mp h)
    simp [alphaMH,hp,hs]
end TierneyProof

set_option autoImplicit false

theorem solution {E : Type*} [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (Q : Kernel E E) [IsMarkovKernel Q] :
    (∀ᵐ p ∂((π ⊗ₘ Q).restrict (canonR π Q)ᶜ), alphaMH π Q p = 0) ∧
      (∀ᵐ p ∂((π ⊗ₘ Q).restrict (canonR π Q)),
        alphaMH π Q p * canonRatio π Q p = alphaMH π Q p.swap) := by
  constructor
  · filter_upwards [self_mem_ae_restrict (TierneyProof.R_measurable π Q).compl] with p hp
    exact Set.indicator_of_notMem hp _
  · exact Eventually.of_forall (TierneyProof.alpha_identity π Q)
