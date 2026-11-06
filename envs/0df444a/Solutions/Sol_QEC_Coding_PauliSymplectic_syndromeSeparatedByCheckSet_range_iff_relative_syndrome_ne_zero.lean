-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.syndromeSeparatedByCheckSet_range_iff_relative_syndrome_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T18:42:03.510214+00:00
-- url     : https://prove2.me/submissions/29e63723-7992-45b5-bf95-e5ce5a17d955

-- ID: 893f2096-ef6a-4dd9-a4b7-7c936e64148a | NAME: QEC.Coding.PauliSymplectic.syndromeSeparatedByCheckSet_range_iff_relative_syndrome_ne_zero | 未本地编译验证
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

theorem solution {κ : Type w} [Fintype κ] (generators : κ → Binary ι) (E F : Binary ι) :
    syndromeSeparatedByCheckSet (Set.range generators) E F ↔
      stabilizerSyndrome generators (binaryMul (binaryDagger E) F) ≠ 0 := by
  classical
  simp only [QEC.Coding.PauliSymplectic.syndromeSeparatedByCheckSet,
    QEC.Coding.PauliSymplectic.checkDistinguishes, Set.mem_range]
  constructor
  · rintro ⟨S, ⟨j, rfl⟩, hS⟩
    intro hzero
    apply hS
    simpa [QEC.Coding.PauliSymplectic.Commutes,
      QEC.Coding.PauliSymplectic.stabilizerSyndrome,
      QEC.Coding.PauliSymplectic.stabilizerSyndromeBit] using congrFun hzero j
  · intro hne
    have hex : ∃ j, stabilizerSyndrome generators
        (binaryMul (binaryDagger E) F) j ≠ 0 := by
      by_contra h
      apply hne
      funext j
      by_contra hj
      exact h ⟨j, by simpa using hj⟩
    rcases hex with ⟨j, hj⟩
    refine ⟨generators j, ⟨j, rfl⟩, ?_⟩
    simpa [QEC.Coding.PauliSymplectic.Commutes,
      QEC.Coding.PauliSymplectic.stabilizerSyndrome,
      QEC.Coding.PauliSymplectic.stabilizerSyndromeBit] using hj
