-- Prove2me | solution 1 for PI.LevelKSplit.W.SemiG.Dat.S_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:14.022851+00:00
-- url     : https://prove2.me/submissions/5e2c03ff-f58a-43fb-9ad1-b277679f665b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_HermitianIsotropicProjComplement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.SemiG
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
open PI.LevelKSplit.W.SemiG.Dat
variable {D : Dat A n r}
namespace PI.LevelKSplit.W.SemiG.Dat
theorem _root_.solution {S : (n → A) →ₗ[A] (n → A)} (hX : D.MapX S) {x : n → A}
    (hx : x ∈ Submodule.span A (Set.range D.e)) : S x ∈ Submodule.span A (Set.range D.e) := by
  have hle : Submodule.span A (Set.range D.e) ≤ (Submodule.span A (Set.range D.e)).comap S :=
    Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact hX a)
  exact hle hx
end PI.LevelKSplit.W.SemiG.Dat
