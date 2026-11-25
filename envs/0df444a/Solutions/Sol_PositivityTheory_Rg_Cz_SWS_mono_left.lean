-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.SWS.mono_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:35:00.756437+00:00
-- url     : https://prove2.me/submissions/d1c6d4cf-649a-4406-8a0b-feaf21fbd000

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PSWStartB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PSWStart
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.lift_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_one



set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix MeasureTheory
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.SWS
variable {n : ℕ} {ι Γ : Type} [Fintype ι] [DecidableEq ι] [Group Γ] [TopologicalSpace Γ]
  {bar : ι → ι} {κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ}
variable [MeasurableSpace Γ] [BorelSpace Γ] [CompactSpace Γ] (μ : Measure Γ) [IsFiniteMeasure μ]
variable {M : Type} [AddCommGroup M] [Module ℂ M]
omit [MeasurableSpace Γ] [BorelSpace Γ] [CompactSpace Γ]
namespace PositivityTheory.Rg.Cz.SWS
theorem _root_.solution (hK : IsKD bar κ) {m : ℕ} (lab : Fin m → ι) (c : ι → ℤ) (I K : Fin m → Fin n) (γ k : Γ) :
    ∑ J : Fin m → Fin n, (∏ p, κ (lab p) γ (I p) (J p)) * mono κ lab c J K k =
      (∏ τ, (κ τ γ).det ^ (-c τ)) * mono κ lab c I K (γ * k) := by
  have hd : ∀ τ, (κ τ γ).det ≠ 0 := fun τ => det_ne hK τ γ
  have hc : (∏ τ, (κ τ γ).det ^ (-c τ)) * ∏ τ, (κ τ γ).det ^ (c τ) = 1 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro τ _
    rw [← zpow_add₀ (hd τ)]
    simp
  calc ∑ J : Fin m → Fin n, (∏ p, κ (lab p) γ (I p) (J p)) * mono κ lab c J K k
      = ∑ J : Fin m → Fin n, (∏ τ, (κ τ k).det ^ (c τ)) *
          ∏ p, (κ (lab p) γ (I p) (J p) * κ (lab p) k (J p) (K p)) := by
        apply Finset.sum_congr rfl
        intro J _
        simp only [mono, Finset.prod_mul_distrib]
        ring
    _ = (∏ τ, (κ τ k).det ^ (c τ)) *
          ∏ p, ∑ j, κ (lab p) γ (I p) j * κ (lab p) k j (K p) := by
        rw [Fintype.prod_sum, Finset.mul_sum]
    _ = (∏ τ, (κ τ γ).det ^ (-c τ)) * mono κ lab c I K (γ * k) := by
        simp only [mono, hK.mul, Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib, Matrix.mul_apply]
        rw [← mul_assoc, ← mul_assoc, hc, one_mul]
end PositivityTheory.Rg.Cz.SWS
