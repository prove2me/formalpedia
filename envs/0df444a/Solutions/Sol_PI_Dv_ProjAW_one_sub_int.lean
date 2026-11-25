-- Prove2me | solution 1 for PI.Dv.ProjAW.one_sub_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:35:44.098425+00:00
-- url     : https://prove2.me/submissions/eeb4a286-0ce2-4409-9c61-e656726a7734

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LengthIndex_LenAtEqZero
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
open PI PI.Dv PI.Dv.ProjAW
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable (A : HLat K)
namespace PI.Dv.ProjAW
theorem _root_.solution {f : Module.End K A.V} {n : ℕ}
    (hn : ∀ x ∈ A.L, ((n : ℕ) : 𝓞 K) • f x ∈ A.L) :
    ∀ x ∈ A.L, ((n : ℕ) : 𝓞 K) • (1 - f) x ∈ A.L := by
  intro x hx
  have h : ((n : ℕ) : 𝓞 K) • (1 - f) x = ((n : ℕ) : 𝓞 K) • x - ((n : ℕ) : 𝓞 K) • f x := by
    simp [smul_sub]
  rw [h]
  exact A.L.sub_mem (A.L.smul_mem _ hx) (hn x hx)
end PI.Dv.ProjAW
