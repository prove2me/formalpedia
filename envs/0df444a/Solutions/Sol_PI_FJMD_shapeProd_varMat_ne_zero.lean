-- Prove2me | solution 1 for PI.FJMD.shapeProd_varMat_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:42:35.51383+00:00
-- url     : https://prove2.me/submissions/d707b7ef-1b57-48af-9149-ba3957fb52d1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ShapeProdVarMatNeZero
import Theorems.Thm_PI_FJMD_det_vars_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action
open PI PI.FJMD
open PI.FJM
namespace PI.FJMD
theorem _root_.solution {p q r s m k : ℕ} (ρ : Fin m → Ix p q) (κ : Fin k → Ix r s)
    (hρ : Function.Injective ρ) (hκ : Function.Injective κ) (α : List ℕ)
    (hm : α.length ≤ m) (hk : α.length ≤ k) : shapeProd (varMat (r := r) (s := s) ρ κ) α ≠ 0 := by
  unfold PI.FJM.shapeProd
  rw [Finset.prod_ne_zero_iff]
  intro t ht
  have ht' : t < α.length := Finset.mem_range.mp ht
  apply pow_ne_zero
  have hc : t + 1 ≤ m ∧ t + 1 ≤ k := ⟨by omega, by omega⟩
  unfold PI.FJM.leadT
  rw [dif_pos hc]
  have hinj : Function.Injective
      (fun x : Fin (t + 1) × Fin (t + 1) => (ρ (Fin.castLE hc.1 x.1), κ (Fin.castLE hc.2 x.2))) := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ hxy
    simp only [Prod.mk.injEq] at hxy ⊢
    exact ⟨Fin.castLE_injective _ (hρ hxy.1), Fin.castLE_injective _ (hκ hxy.2)⟩
  exact det_vars_ne_zero
    (fun x : Fin (t + 1) × Fin (t + 1) => (ρ (Fin.castLE hc.1 x.1), κ (Fin.castLE hc.2 x.2))) hinj
end PI.FJMD
