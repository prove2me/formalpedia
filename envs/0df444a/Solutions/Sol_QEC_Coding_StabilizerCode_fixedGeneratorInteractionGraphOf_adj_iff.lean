-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.fixedGeneratorInteractionGraphOf_adj_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:11:24.538281+00:00
-- url     : https://prove2.me/submissions/1f1f33ea-212a-4570-9edc-caed75746417

import Definitions.Def_QEC_Coding_Stabilizer_Parameters
import Definitions.Def_QEC_Locality_Graph_Core
import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction

set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open PauliSymplectic
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
omit [Fintype κ]
namespace QEC.Coding.StabilizerCode
theorem _root_.solution
    (generators : κ → Binary ι) (p q : ι) :
    (fixedGeneratorInteractionGraphOf generators).adjacent p q ↔
      p ≠ q ∧ ∃ j : κ,
        p ∈ support (generators j) ∧ q ∈ support (generators j) :=
  Iff.rfl
end QEC.Coding.StabilizerCode
