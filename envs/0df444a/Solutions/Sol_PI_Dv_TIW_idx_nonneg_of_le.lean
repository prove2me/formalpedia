-- Prove2me | solution 1 for PI.Dv.TIW.idx_nonneg_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:23:57.53274+00:00
-- url     : https://prove2.me/submissions/62adabff-d095-4af2-ac4b-2aef4920002f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_DvTransferIdxOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_IdxNonnegOfLe
import Theorems.Thm_PI_Dv_TIW_one_notMem_w
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
open PI PI.Dv PI.Dv.TIW
open Formalism.BasicNotions NumberField IsDedekindDomain PI.Dv
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace PI.Dv.TIW
theorem _root_.solution (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) (M N : Submodule (𝓞 K) V) (hM : M.FG)
    (hN : N.FG) (h1 : Submodule.span K (M : Set V) = Submodule.span K (N : Set V)) (hle : N ≤ M) :
    0 ≤ idxAt w M N := by
  have := (hI K V w M N hM hN h1).2.2.2.1 0 (fun x hx => ⟨1, one_notMem_w w, by
    rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul, one_smul]; exact hle hx⟩)
  simpa using this
end PI.Dv.TIW
