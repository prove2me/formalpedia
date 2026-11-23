-- Prove2me | solution 1 for PI.Dv.TIW.idx_smulSub_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:43.147708+00:00
-- url     : https://prove2.me/submissions/3ba0edda-a9d3-410a-8a55-dd05d5178e1a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_IdxNonnegOfLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_FinsumEqLogNorm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_IdxSmulSubMap
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_Dv_TIW_idx_map_inj
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
theorem _root_.solution (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) (d : K) (hd : d ≠ 0)
    (M N : Submodule (𝓞 K) V) (hM : M.FG) (hN : N.FG)
    (h1 : Submodule.span K (M : Set V) = Submodule.span K (N : Set V)) :
    idxAt w (smulSub d M) (smulSub d N) = idxAt w M N := by
  have hinj : ∀ P : Submodule (𝓞 K) V, ∀ x ∈ P, (d • LinearMap.id : V →ₗ[K] V) x = 0 → x = 0 := by
    intro P x _ hx
    simpa [hd] using hx
  exact (idx_map_inj hI w (d • LinearMap.id) M N hM hN h1 (hinj M) (hinj N)).symm
end PI.Dv.TIW
