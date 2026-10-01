-- Prove2me | solution 1 for TierneyMH.Reversibility.theorem2_detailed_balance_iff
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T12:28:21.014929+00:00
-- url     : https://prove2.me/submissions/0919d027-8431-4b05-930b-458cbf8a6cb7

import Definitions.Def_TierneyMH_Shared_IsSymmetricSplit
import Definitions.Def_TierneyMH_Shared_IsRatioVersion
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

namespace CTierney
open TierneyMH.Shared
variable {E : Type*} [MeasurableSpace E]

theorem swap_withDensity (μ : Measure (E × E)) (α : E × E → ℝ≥0∞) (hα : Measurable α) :
    (μ.withDensity α).map Prod.swap=(μ.map Prod.swap).withDensity (fun p => α p.swap) := by
  have hαs : Measurable (fun p : E × E => α p.swap) := hα.comp measurable_swap
  ext S hS
  rw [Measure.map_apply measurable_swap hS,withDensity_apply _ (measurable_swap hS),
    withDensity_apply _ hS,setLIntegral_map hS hαs measurable_swap]
  rfl

theorem density_balance_iff (μ : Measure (E × E)) [IsFiniteMeasure μ]
    (α : E × E → ℝ≥0∞) (hα : Measurable α) (R : Set (E × E)) (r : E × E → ℝ≥0∞)
    (hR : IsSymmetricSplit μ R) (hr : IsRatioVersion μ R r) :
    (μ.withDensity α).map Prod.swap=μ.withDensity α ↔
      (α=ᵐ[μ.restrict Rᶜ] 0 ∧ (fun p => α p*r p)=ᵐ[μ.restrict R] fun p => α p.swap) := by
  let F := μ.withDensity α
  let G := (μ.map Prod.swap).withDensity (fun p => α p.swap)
  have hswap : F.map Prod.swap=G := swap_withDensity μ α hα
  have hαs : Measurable (fun p : E × E => α p.swap) := hα.comp measurable_swap
  have hRcommon : F.restrict R=G.restrict R ↔
      (fun p => α p*r p)=ᵐ[μ.restrict R] fun p => α p.swap := by
    dsimp [F,G]
    rw [restrict_withDensity hR.1,restrict_withDensity hR.1]
    conv_lhs => rw [hr.2.2.2,← withDensity_mul _ hr.1 hα]
    rw [withDensity_eq_iff_of_sigmaFinite (hr.1.mul hα).aemeasurable hαs.aemeasurable]
    constructor
    · intro h
      filter_upwards [Measure.AbsolutelyContinuous.ae_eq hR.2.2.1 h] with p hp
      simpa only [Pi.mul_apply,mul_comm] using hp
    · intro h
      filter_upwards [Measure.AbsolutelyContinuous.ae_eq hR.2.2.2.1 h] with p hp
      simpa only [Pi.mul_apply,mul_comm] using hp
  have hRc : Prod.swap ⁻¹' Rᶜ=Rᶜ := by rw [Set.preimage_compl,hR.2.1]
  have hzero : F.restrict Rᶜ=0 ↔ α=ᵐ[μ.restrict Rᶜ] 0 := by
    dsimp [F]
    rw [restrict_withDensity hR.1.compl]
    exact withDensity_eq_zero_iff hα.aemeasurable
  constructor
  · intro h
    have heq : F=G := h.symm.trans hswap
    have hs : F.restrict Rᶜ ⟂ₘ G.restrict Rᶜ := by
      dsimp [F,G]
      rw [restrict_withDensity hR.1.compl,restrict_withDensity hR.1.compl]
      exact hR.2.2.2.2.mono_ac (withDensity_absolutelyContinuous _ _) (withDensity_absolutelyContinuous _ _)
    have h0 : F.restrict Rᶜ=0 := by
      rw [← heq] at hs
      exact (Measure.MutuallySingular.self_iff _).mp hs
    exact ⟨hzero.mp h0,hRcommon.mp (congrArg (fun ν => ν.restrict R) heq)⟩
  · rintro ⟨hz,he⟩
    have hF0 : F.restrict Rᶜ=0 := hzero.mpr hz
    have hG0 : G.restrict Rᶜ=0 := by
      rw [← hswap,Measure.restrict_map measurable_swap hR.1.compl,hRc,hF0,Measure.map_zero]
    have heq : F=G := by
      rw [← Measure.restrict_add_restrict_compl (μ := F) hR.1,
        ← Measure.restrict_add_restrict_compl (μ := G) hR.1,hF0,hG0,add_zero,add_zero]
      exact hRcommon.mpr he
    exact hswap.trans heq.symm
end CTierney

open TierneyMH.Shared

theorem solution {E : Type*} [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (Q : Kernel E E) [IsMarkovKernel Q]
    (α : E × E → ℝ≥0∞) (hα_meas : Measurable α) (hα_le : ∀ p, α p ≤ 1)
    (R : Set (E × E)) (r : E × E → ℝ≥0∞)
    (hR : IsSymmetricSplit (π ⊗ₘ Q) R) (hr : IsRatioVersion (π ⊗ₘ Q) R r) :
    Kernel.IsReversible (mhKernel Q α) π ↔
      ((∀ᵐ p ∂((π ⊗ₘ Q).restrict Rᶜ), α p=0) ∧
        (∀ᵐ p ∂((π ⊗ₘ Q).restrict R), α p*r p=α p.swap)) := by
  rw [CTierney.mh_reversible_iff π Q α hα_meas hα_le]
  exact CTierney.density_balance_iff (π ⊗ₘ Q) α hα_meas R r hR hr
