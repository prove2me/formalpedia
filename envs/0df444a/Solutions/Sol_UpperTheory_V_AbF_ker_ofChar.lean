-- Prove2me | solution 1 for UpperTheory.V.AbF.ker_ofChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:06:45.050481+00:00
-- url     : https://prove2.me/submissions/f03fb291-f19f-44e3-9aa6-96016f7b2e32

import Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_ExistsPageN
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_StmtFields
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open NumberField Polynomial
open UpperTheory UpperTheory.V
open Formalism.HC UpperTheory.Top
namespace UpperTheory.V
namespace AbF
theorem _root_.solution (ψ : PChar) (a : ℕ) : (AbF.ofChar ψ).ker a ↔ ψ.val a = 1 := by
  show (∃ u ∈ ψ.χ.toUnitHom.ker, ((u : (ZMod ψ.N)ˣ) : ZMod ψ.N) = (a : ZMod ψ.N)) ↔
    ψ.χ (a : ZMod ψ.N) = 1
  constructor
  · rintro ⟨u, hu, hua⟩
    rw [← hua]
    have := congrArg (fun v : ℂˣ => (v : ℂ)) (MonoidHom.mem_ker.mp hu)
    simpa [MulChar.coe_toUnitHom] using this
  · intro h
    have hu : IsUnit (a : ZMod ψ.N) := by
      by_contra hn
      rw [MulChar.map_nonunit ψ.χ hn] at h
      exact zero_ne_one h
    refine ⟨hu.unit, ?_, hu.unit_spec⟩
    rw [MonoidHom.mem_ker]
    ext
    simpa [MulChar.coe_toUnitHom] using h
end AbF
end UpperTheory.V
