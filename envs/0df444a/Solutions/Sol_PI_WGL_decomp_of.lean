-- Prove2me | solution 1 for PI.WGL.decomp_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:47:29.571242+00:00
-- url     : https://prove2.me/submissions/56dc515c-0366-4d14-abfb-3a891f030ac0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDecomp
import Theorems.Thm_PI_WGL_dominant_weight_ext
import Theorems.Thm_P2M_PI_WGL_extremal_mem_nablaSq__339bb813a092
import Theorems.Thm_PI_WGL_weight_sum_eq_of_last_gap
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WGL
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
namespace PI.WGL
theorem _root_.solution (h4 : PI.GTBranch) (hL : EqvLast) : Decomp := by
  intro n N h lam sg hsg io0 hio hne f hf hfw
  classical
  let T : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ) := (nablaSq ℂ n sg).map io0 ⊔ OtherPart h lam sg
  have key : nablaSq ℂ N lam ≤ T.comap (weightedHomogeneousComponent (lastW N) (dLast lam sg)) := by
    rw [(h4 n N h lam).2]
    refine iSup_le fun mu => iSup_le fun hmu => iSup_le fun φ => iSup_le fun hφ => ?_
    rw [Submodule.map_le_iff_le_comap]
    intro s hs
    rw [Submodule.mem_comap, Submodule.mem_comap]
    have hφ' : IsEqv h mu lam φ := hφ
    have hhom := hL n N h lam mu hmu φ hφ' s hs
    by_cases hd : dLast lam mu = dLast lam sg
    · rw [hd] at hhom
      rw [hhom.weightedHomogeneousComponent_same]
      have hw : wsum mu = wsum sg := weight_sum_eq_of_last_gap h lam mu sg hmu hsg hd
      by_cases hmw : mu.w = sg.w
      · have hms : mu = sg := dominant_weight_ext mu sg hmw
        subst hms
        have hboth : ∀ ψ ∈ ({φ, io0} : Set (MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ)),
            (∀ s ∈ nablaSq ℂ n mu, ψ s ∈ nablaSq ℂ N lam) ∧
            ∀ (g : GL (Fin n) ℂ), ∀ s ∈ nablaSq ℂ n mu,
              ψ (sqAct ℂ n mu g s) = sqAct ℂ N lam (embGL ℂ n N h g) (ψ s) := by
          intro ψ hψ
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hψ
          rcases hψ with rfl | rfl
          · exact hφ'
          · exact hio
        obtain ⟨_, c, hc⟩ := (h4 n N h lam).1 mu φ io0 hboth ⟨extremal ℂ n mu, extremal_mem_nablaSq' n mu, hne⟩
        refine Submodule.mem_sup_left ?_
        rw [hc s hs, ← map_smul]
        exact Submodule.mem_map_of_mem (Submodule.smul_mem _ c hs)
      · refine Submodule.mem_sup_right ?_
        unfold OtherPart
        exact Submodule.mem_iSup_of_mem mu (Submodule.mem_iSup_of_mem hmu (Submodule.mem_iSup_of_mem hmw
          (Submodule.mem_iSup_of_mem hw (Submodule.mem_iSup_of_mem φ (Submodule.mem_iSup_of_mem hφ'
            (Submodule.mem_map_of_mem hs))))))
    · rw [hhom.weightedHomogeneousComponent_ne (dLast lam sg) (Ne.symm hd)]
      exact zero_mem _
  have hfT := key hf
  rw [Submodule.mem_comap, hfw.weightedHomogeneousComponent_same] at hfT
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hfT
  obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.1 hy
  refine ⟨u, hu, ?_⟩
  rw [← hyz, add_sub_cancel_left]
  exact hz
end PI.WGL
