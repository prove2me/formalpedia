-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.scalar_action_on_code_of_detectableOn_of_inBinaryNormalizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:40:38.511202+00:00
-- url     : https://prove2.me/submissions/1c7014e8-2c3d-4f8f-bc71-f88ea7256214

import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Coding_Stabilizer_Symplectic
import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Definitions.Def_QEC_Coding_Stabilizer_Detectability
import Theorems.Thm_QEC_Coding_StabilizerCode_toQubitOperator_mem_code_of_inBinaryNormalizer

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
universe u
open QEC.Coding.StabilizerCode
open PauliSymplectic
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Coding.StabilizerCode
theorem _root_.solution
    (Q : SourceValidBinary ι) (E : Binary ι)
    (hN : Q.1.InBinaryNormalizer E)
    (hdet : Semantics.DetectableOn Q.1.code (toQubitOperator E)) :
    ∃ c : Complex, ∀ ψ, ψ ∈ Q.1.code.carrier →
      toQubitOperator E ψ = c • ψ := by
  rcases hdet with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro ψ hψ
  let d := toQubitOperator E ψ - c • ψ
  have hdmem : d ∈ Q.1.code.carrier := by
    exact Q.1.code.carrier.sub_mem
      (toQubitOperator_mem_code_of_inBinaryNormalizer Q hN hψ)
      (Q.1.code.carrier.smul_mem c hψ)
  have hinner : inner Complex d d = 0 := by
    change inner Complex d (toQubitOperator E ψ - c • ψ) = 0
    rw [inner_sub_right, hc d hdmem ψ hψ]
    rw [inner_smul_right]
    ring
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hinner)
end QEC.Coding.StabilizerCode
