-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.checkDistinguishes_range_iff_exists_syndromeBit_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T18:43:13.772698+00:00
-- url     : https://prove2.me/submissions/4dfe4adb-cdde-4686-9030-dbb179018847

-- ID: 7e0be036-64bc-4b6e-a308-76ca954d12e4 | NAME: QEC.Coding.PauliSymplectic.checkDistinguishes_range_iff_exists_syndromeBit_eq_one | 未本地编译验证
import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open Classical
open scoped BigOperators
universe u w
open QEC.Coding.PauliSymplectic
variable {ι : Type u} [Fintype ι]
variable [DecidableEq ι]
omit [DecidableEq ι]

theorem solution {κ : Type w} [Fintype κ] (generators : κ → Binary ι) (E : Binary ι) :
    checkDistinguishes (Set.range generators) E ↔
      ∃ j, stabilizerSyndromeBit (generators j) E = 1 := by
  simp only [checkDistinguishes, Set.mem_range, Commutes, stabilizerSyndromeBit]
  constructor
  · rintro ⟨S, ⟨j, rfl⟩, h⟩
    exact ⟨j, zmod_two_eq_one_of_ne_zero h⟩
  · rintro ⟨j, hj⟩
    refine ⟨generators j, ⟨j, rfl⟩, ?_⟩
    simpa [hj] using (one_ne_zero : (1 : ZMod 2) ≠ 0)
