-- Prove2me | solution 1 for UpperTheory.V.BShape.mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:42:35.551798+00:00
-- url     : https://prove2.me/submissions/7711ac9c-03aa-455d-8f1f-0666deff647d

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_LengthEqAddEigen
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_StmtFields
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_PrimeSetBoundDataOfPrimitiveChar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open UpperTheory UpperTheory.V
open Formalism.HC UpperTheory.Top
namespace UpperTheory.V
namespace BShape
theorem _root_.solution {K : BConst} {Ct : ℝ}
    {P Q : ℝ → AbF → Finset ℕ → (ℕ → AbF) → (ℝ → ℕ) → (ℝ → ℕ) → ℕ → ℕ → ℝ → ℝ → Prop}
    (h : ∀ eps M B' L e t q d X Y, P eps M B' L e t q d X Y → Q eps M B' L e t q d X Y) (hP : BShape K Ct P) :
    BShape K Ct Q := by
  intro M B' L hB eps A1 h0 h1
  obtain ⟨X0, H⟩ := hP M B' L hB eps A1 h0 h1
  refine ⟨X0, fun e t ha X hX q d hp hl => ?_⟩
  obtain ⟨Y, hY⟩ := H e t ha X hX q d hp hl
  exact ⟨Y, h _ _ _ _ _ _ _ _ _ _ hY⟩
end BShape
end UpperTheory.V
