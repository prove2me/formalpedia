-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.BinaryStabilizerPresentation.sym2_mk_mem_fixedGeneratorInteractions_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:16:14.733309+00:00
-- url     : https://prove2.me/submissions/a68ffe47-06b1-4173-9b70-4e906128198a

import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Definitions.Def_QEC_Locality_OptimalTradeoff_Interaction

set_option autoImplicit false
noncomputable section
open scoped Classical
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
open PauliSymplectic
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
namespace QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
theorem _root_.solution
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ)) (p q : ι) :
    s(p, q) ∈ P.fixedGeneratorInteractions ↔ s(q, p) ∈ P.fixedGeneratorInteractions := by
  rw [Sym2.eq_swap]
end QEC.Coding.StabilizerCode.BinaryStabilizerPresentation
