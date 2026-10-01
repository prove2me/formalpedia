-- Prove2me | solution 1 for TierneyMH.Reversibility.mhKernel_reversible_iff_offDiagonal
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T12:22:38.547724+00:00
-- url     : https://prove2.me/submissions/274cc592-28f3-4fcb-95ae-c5675acb2152

import Definitions.Def_TierneyMH_Shared_mhKernel
import Mathlib.Tactic
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace CTierney
variable {E : Type*} [MeasurableSpace E]

theorem reversible_iff_swap (π : Measure E) [IsFiniteMeasure π]
    (K : Kernel E E) [IsFiniteKernel K] :
    Kernel.IsReversible K π ↔ (π ⊗ₘ K).map Prod.swap=π ⊗ₘ K := by
  constructor
  · intro h
    apply Measure.ext_prod
    intro A B hA hB
    rw [Measure.map_apply measurable_swap (hA.prod hB)]
    simp only [Set.preimage_swap_prod]
    rw [Measure.compProd_apply_prod hB hA,Measure.compProd_apply_prod hA hB]
    exact h hB hA
  · intro h A B hA hB
    have he := congrArg (fun μ : Measure (E × E) => μ (B ×ˢ A)) h
    rw [Measure.map_apply measurable_swap (hB.prod hA)] at he
    simp only [Set.preimage_swap_prod] at he
    simpa only [Measure.compProd_apply_prod hA hB,Measure.compProd_apply_prod hB hA] using he

theorem rejection_reversible (π : Measure E) (r : E → ℝ≥0∞) (hr : Measurable r) :
    Kernel.IsReversible (Kernel.id.withDensity (fun x (_ : E) => r x)) π := by
  have hval : ∀ (x : E) (S : Set E), MeasurableSet S →
      (Kernel.id.withDensity (fun x (_ : E) => r x)) x S=S.indicator r x := by
    intro x S hS
    rw [Kernel.withDensity_apply' Kernel.id (f := fun x (_ : E) => r x) (hr.comp measurable_fst),Kernel.id_apply]
    simp [lintegral_const,Measure.dirac_apply',hS,Set.indicator]
  intro A B hA hB
  simp_rw [hval _ B hB,hval _ A hA]
  rw [lintegral_indicator hB,lintegral_indicator hA,Measure.restrict_restrict hB,
    Measure.restrict_restrict hA,Set.inter_comm]

theorem mh_reversible_iff (π : Measure E) [IsProbabilityMeasure π]
    (Q : Kernel E E) [IsMarkovKernel Q] (α : E × E → ℝ≥0∞)
    (hα : Measurable α) (hα1 : ∀ p, α p ≤ 1) :
    Kernel.IsReversible (TierneyMH.Shared.mhKernel Q α) π ↔
      ((π ⊗ₘ Q).withDensity α).map Prod.swap=(π ⊗ₘ Q).withDensity α := by
  let K := Q.withDensity (fun x y => α (x,y))
  let r : E → ℝ≥0∞ := fun x => ∫⁻ u, (1-α (x,u)) ∂Q x
  let J : Kernel E E := Kernel.id.withDensity (fun x (_ : E) => r x)
  have hr : Measurable r := (measurable_const.sub hα).lintegral_kernel_prod_right' (κ := Q)
  have hr1 : ∀ x, r x ≤ 1 := by
    intro x
    calc
      r x ≤ ∫⁻ _u, 1 ∂Q x := lintegral_mono (fun _ => tsub_le_self)
      _ = 1 := by simp
  letI : IsFiniteKernel K := Kernel.isFiniteKernel_withDensity_of_bounded Q ENNReal.one_ne_top (fun x y => hα1 (x,y))
  letI : IsFiniteKernel J := Kernel.isFiniteKernel_withDensity_of_bounded Kernel.id ENNReal.one_ne_top (fun x _ => hr1 x)
  have hJ : (π ⊗ₘ J).map Prod.swap=π ⊗ₘ J :=
    (reversible_iff_swap π J).mp (rejection_reversible π r hr)
  change Kernel.IsReversible (K+J) π ↔ _
  rw [reversible_iff_swap,Measure.compProd_add_right,Measure.map_add _ _ measurable_swap,hJ,Measure.add_left_inj]
  have hK : π ⊗ₘ K=(π ⊗ₘ Q).withDensity α := Measure.compProd_withDensity hα
  rw [hK]
end CTierney

theorem solution {E : Type*} [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (Q : Kernel E E) [IsMarkovKernel Q]
    (α : E × E → ℝ≥0∞) (hα_meas : Measurable α) (hα_le : ∀ p, α p ≤ 1) :
    Kernel.IsReversible (TierneyMH.Shared.mhKernel Q α) π ↔
      ((π ⊗ₘ Q).withDensity α).map Prod.swap=(π ⊗ₘ Q).withDensity α :=
  CTierney.mh_reversible_iff π Q α hα_meas hα_le
