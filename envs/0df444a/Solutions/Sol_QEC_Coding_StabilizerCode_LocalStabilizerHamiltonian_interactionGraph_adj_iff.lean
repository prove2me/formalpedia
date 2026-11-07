-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.interactionGraph_adj_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:49:46.748209+00:00
-- url     : https://prove2.me/submissions/9afb48f6-6f15-4201-ac6f-57857ec5de54

import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
import Definitions.Def_QEC_Locality_Core_Definitions
import Definitions.Def_QEC_Coding_Stabilizer_LocalHamiltonian

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open PauliSymplectic
open scoped BigOperators
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
open QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
namespace QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
theorem _root_.solution
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)) (p q : ι) :
    H.interactionGraph.adjacent p q ↔
      p ≠ q ∧ ∃ j : κ,
        p ∈ H.generatorSupport j ∧ q ∈ H.generatorSupport j :=
  Iff.rfl
end QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
