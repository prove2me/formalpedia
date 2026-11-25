-- Prove2me | solution 1 for PI.LevelKSplit.W.NCH.fix_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:21:15.930851+00:00
-- url     : https://prove2.me/submissions/aab08998-c7cb-4526-9c0b-8be7fd39cf04

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnipotentRadicalActionFormula
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ToMatrixLin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_HeisenbergCocycleMemCentre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.NCH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub PI.VolSemiDirect.W PI.VolSemiDirect.W.PG
  PI.VolSemiDirect.W.PG.Dat
open scoped TensorProduct Matrix
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ} {D : Dat A n r}
namespace PI.LevelKSplit.W.NCH
theorem _root_.solution {Φ : (n → A) →ₗ[A] (n → A)} (he : ∀ a, Φ (D.e a) = D.e a) {x : n → A}
    (hx : x ∈ Submodule.span A (Set.range D.e)) : Φ x = x := by
  first
  | exact LinearMap.eqOn_span' (f := Φ) (g := LinearMap.id) (by rintro _ ⟨a, rfl⟩; exact he a) hx
  | (induction hx using Submodule.span_induction with
      | mem y hy => obtain ⟨a, rfl⟩ := hy; exact he a
      | zero => exact map_zero Φ
      | add y z _ _ hy hz => rw [map_add, hy, hz]
      | smul c y _ hy => rw [map_smul, hy])
end PI.LevelKSplit.W.NCH
