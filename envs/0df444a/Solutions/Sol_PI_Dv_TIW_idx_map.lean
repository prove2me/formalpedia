-- Prove2me | solution 1 for PI.Dv.TIW.idx_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:23.901022+00:00
-- url     : https://prove2.me/submissions/5a53a317-9b96-4b65-83e4-5029b7c956ba

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_DvTransferIdxOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_IdxNonnegOfLe
import Theorems.Thm_PI_Dv_TIW_idx_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
open Formalism.BasicNotions NumberField IsDedekindDomain PI.Dv
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace PI.Dv.TIW
theorem _root_.solution (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {V' : Type} [AddCommGroup V'] [Module K V']
    [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (φ : V →ₗ[K] V') (M N : Submodule (𝓞 K) V) (hM : M.FG)
    (hN : N.FG) (h1 : Submodule.span K (M : Set V) = Submodule.span K (N : Set V))
    (hker : M ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K) = N ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K)) :
    idxAt w M N = idxAt w (M.map (φ.restrictScalars (𝓞 K))) (N.map (φ.restrictScalars (𝓞 K))) := by
  have := (hI K V w M N hM hN h1).2.2.1 V' φ
  rw [hker, idx_self, zero_add] at this
  exact this
end PI.Dv.TIW
