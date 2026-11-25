-- Prove2me | solution 1 for PI.Dv.TIW.cut_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:46:47.348809+00:00
-- url     : https://prove2.me/submissions/59893665-2e10-48ad-a3f2-c445b4ad8dd7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_MatVTransvection
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsSmulMemTer
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_BlockHyp
import Theorems.Thm_PI_Dv_TIW_exists_smul_mem
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_UpperTheory_Reformulated_B_ExistsSmulMemTer_exists_smul_mem
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
open PI PI.Dv PI.Dv.TIW
open Formalism.BasicNotions NumberField IsDedekindDomain PI.Dv
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace PI.Dv.TIW
theorem _root_.solution (M : Submodule (𝓞 K) V) (hM : Submodule.span K (M : Set V) = ⊤) (X : Submodule K V) :
    Submodule.span K ((M ⊓ X.restrictScalars (𝓞 K) : Submodule (𝓞 K) V) : Set V) = X := by
  apply le_antisymm
  · rw [Submodule.span_le]; intro x hx; exact hx.2
  · intro x hx
    obtain ⟨a, ha, hax⟩ := exists_smul_mem M x (by rw [hM]; exact Submodule.mem_top)
    have haK : algebraMap (𝓞 K) K a ≠ 0 := by simpa using ha
    have hmem : a • x ∈ (M ⊓ X.restrictScalars (𝓞 K) : Submodule (𝓞 K) V) := by
      refine Submodule.mem_inf.mpr ⟨hax, ?_⟩
      rw [Submodule.restrictScalars_mem, ← algebraMap_smul K]
      exact X.smul_mem _ hx
    have : x = (algebraMap (𝓞 K) K a)⁻¹ • (a • x) := by
      rw [← algebraMap_smul K a x, smul_smul, inv_mul_cancel₀ haK, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
end PI.Dv.TIW
