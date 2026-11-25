-- Prove2me | solution 1 for PI.WeylForKWork.wt_common_eigvec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:15:31.20172+00:00
-- url     : https://prove2.me/submissions/b605c1fd-85fd-4151-90f7-1cde48ce964a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_FormulaStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_TrivKtype
import Definitions.Def_Lemmata_GeneralBFactLeftVariant_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_Weights
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WeylForKWork
open PI PI.UpqRep Matrix
open scoped InnerProductSpace
namespace PI.WeylForKWork
theorem _root_.solution {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ι : Type}
    (A : ι → (H →L[ℂ] H)) (W : Submodule ℂ H) [FiniteDimensional ℂ W] (hW : W ≠ ⊥)
    (hst : ∀ i, ∀ v ∈ W, A i v ∈ W) (hcomm : ∀ i j, ∀ v, A i (A j v) = A j (A i v)) :
    ∃ w ∈ W, w ≠ 0 ∧ ∀ i, ∃ c : ℂ, A i w = c • w := by
  classical
  have hex : ∃ n, ∃ W₀ : Submodule ℂ H, W₀ ≤ W ∧ W₀ ≠ ⊥ ∧ (∀ i, ∀ v ∈ W₀, A i v ∈ W₀) ∧
      Module.finrank ℂ W₀ = n := ⟨_, W, le_rfl, hW, hst, rfl⟩
  obtain ⟨W₀, hW₀W, hW₀, hW₀st, hW₀n⟩ := Nat.find_spec hex
  have hmin : ∀ W₁ : Submodule ℂ H, W₁ ≤ W → W₁ ≠ ⊥ → (∀ i, ∀ v ∈ W₁, A i v ∈ W₁) →
      Module.finrank ℂ W₀ ≤ Module.finrank ℂ W₁ := fun W₁ h1 h2 h3 => by
    rw [hW₀n]; exact Nat.find_min' hex ⟨W₁, h1, h2, h3, rfl⟩
  have : FiniteDimensional ℂ W₀ := Submodule.finiteDimensional_of_le hW₀W
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff W₀).mp hW₀
  refine ⟨w, hW₀W hw, hw0, fun i => ?_⟩
  let f : Module.End ℂ W₀ := (A i : H →ₗ[ℂ] H).restrict (fun x hx => hW₀st i x hx)
  have : Nontrivial W₀ := Submodule.nontrivial_iff_ne_bot.mpr hW₀
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue f
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  let E : Submodule ℂ H := W₀ ⊓ LinearMap.ker ((A i : H →ₗ[ℂ] H) - c • LinearMap.id)
  have hmemE : ∀ x, x ∈ E ↔ x ∈ W₀ ∧ A i x = c • x := by
    intro x; simp [E, sub_eq_zero]
  have hEst : ∀ j, ∀ x ∈ E, A j x ∈ E := by
    intro j x hx
    rw [hmemE] at hx ⊢
    exact ⟨hW₀st j x hx.1, by rw [hcomm i j, hx.2, map_smul]⟩
  have hvE : (v : H) ∈ E := by
    rw [hmemE]
    refine ⟨v.2, ?_⟩
    have h1 := Module.End.mem_eigenspace_iff.mp hv.1
    have h2 := congrArg Subtype.val h1
    simpa [f] using h2
  have hE0 : E ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    refine ⟨v, hvE, fun h => hv.2 ?_⟩
    exact Subtype.ext h
  have hEW : E ≤ W₀ := inf_le_left
  have hEeq : E = W₀ := Submodule.eq_of_le_of_finrank_le hEW (hmin E (hEW.trans hW₀W) hE0 hEst)
  have hwE : w ∈ E := hEeq ▸ hw
  exact ⟨c, ((hmemE w).mp hwE).2⟩
end PI.WeylForKWork
