-- Prove2me | solution 1 for P2M_GlobalTheory_CentralExponent_val_emb__scalar_9fecca134d59
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:19:47.632933+00:00
-- url     : https://prove2.me/submissions/9920fa35-cbf2-48c9-9d4e-a96967e6321c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_IrreducibleTensorCharacter
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CentralExponentBoundOver
import Theorems.Thm_P2M_GlobalTheory_SmGL_val_emb__6050fcaf31c9


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.StepData ValuativeRel Matrix Topology Filter
open scoped TensorProduct
open GlobalTheory GlobalTheory.CentralExponent
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]
variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.CentralExponent
theorem _root_.solution (e : a ⊕ b ≃ n) (z : kˣ) :
    (emb₂ k e (GeneralLinearGroup.scalar a z, 1)).val =
      diagonal fun i => if (e.symm i).isLeft then (z : k) else 1 := by
  rw [val_emb₂]
  ext i j
  obtain ⟨i, rfl⟩ := e.surjective i
  obtain ⟨j, rfl⟩ := e.surjective j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [GeneralLinearGroup.scalar, diagonal_apply, one_apply]
end GlobalTheory.CentralExponent
