-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTreeAll58
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T01:38:20.389749+00:00
-- url     : https://prove2.me/submissions/7562b1bd-5cd8-4173-8c6b-f18b68f2ff26
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US010
import Theorems.Thm_OAI_UniversalTensorSquare_candidate_rowLens
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree58_0All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree58_1All
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_sg31978

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_RowCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Row Certificates. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma rowDiagram_rowLens (μ : YoungDiagram) : rowDiagram μ.rowLens = μ := by
  rw [rowDiagram_eq _ ⟨μ.rowLens_sorted,μ.pos_of_mem_rowLens⟩,
    YoungDiagram.ofRowLens_to_rowLens_eq_self]

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_ResidualTrees
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Residual Trees. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma rowDiagram_candidate {M b δ : ℕ} (hM : 4 ≤ M) :
    rowDiagram ([M+b+δ,M-1+b] ++ (List.range' 3 (M-4)).reverse ++
      List.replicate (b+1) 2 ++ List.replicate (1+δ) 1) = candidate M b δ := by
  rw [← candidate_rowLens hM, rowDiagram_rowLens]

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeTreeProof58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Tree Proof 58. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeTree58_2All : degreeTree58_2.All (RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31978,degreeTree58_0All,degreeTree58_1All⟩

lemma degreeTreeAll58_oai : degreeTree58.All
    (fun rs => SquareOccurs (candidate 8 5 1) (rowDiagram rs)) := by
  have hp : rowDiagram [14,12,6,5,4,3,2,2,2,2,2,2,1,1] = candidate 8 5 1 := rowDiagram_candidate (M := 8) (b := 5) (δ := 1) (by decide)
  rw [← hp]
  exact degreeTree58_2All

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTreeAll58_oai := @OAI.UniversalTensorSquare.degreeTreeAll58_oai
