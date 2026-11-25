-- Prove2me | solution 1 for PI.WeylForKWork.wt_perp_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:28:10.590803+00:00
-- url     : https://prove2.me/submissions/fc4ebfed-b9ce-46bc-9db0-bdd0b24dedf7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_FormulaStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_TrivKtype
import Definitions.Def_Lemmata_GeneralBFactLeftVariant_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_Weights
import Theorems.Thm_PI_WeylForKWork_wt_inner_iso
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
theorem _root_.solution {N : ℕ} (ε : Fin N → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (hσ : IsURepOn (Kset ε) σ) (X' X : Submodule ℂ H)
    (hX' : IsKStableOn ε σ X') (hX : IsKStableOn ε σ X) : IsKStableOn ε σ (X'ᗮ ⊓ X) := by
  intro g hg v hv
  refine ⟨?_, hX g hg v hv.2⟩
  show σ g v ∈ X'ᗮ
  rw [Submodule.mem_orthogonal]
  intro u hu
  have hg' : star g ∈ Kset ε := Kset_star ε hg
  have h1 : ⟪σ (star g) u, v⟫_ℂ = 0 := (Submodule.mem_orthogonal X' v).mp hv.1 _ (hX' _ hg' u hu)
  have h2 : σ g (σ (star g) u) = u := by
    have h3 := hσ.1.2 g hg (star g) hg'
    rw [Unitary.mul_star_self_of_mem hg.1, hσ.1.1] at h3
    have h4 := DFunLike.congr_fun h3 u
    simpa using h4.symm
  calc ⟪u, σ g v⟫_ℂ = ⟪σ g (σ (star g) u), σ g v⟫_ℂ := by rw [h2]
    _ = ⟪σ (star g) u, v⟫_ℂ := wt_inner_iso (σ g) (hσ.2.1 g hg) _ _
    _ = 0 := h1
end PI.WeylForKWork
