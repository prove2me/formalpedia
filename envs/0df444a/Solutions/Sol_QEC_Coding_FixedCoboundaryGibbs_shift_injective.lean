-- Prove2me | solution 1 for QEC.Coding.FixedCoboundaryGibbs.shift_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:23:28.865694+00:00
-- url     : https://prove2.me/submissions/d1bf5dc9-4e63-4c28-8e17-d558d96a5c6b

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_TwoSectorBadProjector
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_CoboundaryContainment

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.FixedCoboundaryGibbs
open Classical
open scoped BigOperators
variable {I K : Type} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
attribute [local instance] QEC.Coding.FixedCoboundaryGibbs.imageFintype
namespace QEC.Coding.FixedCoboundaryGibbs
theorem _root_.solution (P : Word (ZMod 2) I →ₗ[ZMod 2] Word (ZMod 2) K)
    (τ : LinearMap.range P) : Function.Injective (shift P τ) :=
  (shift_involutive P τ).injective
end QEC.Coding.FixedCoboundaryGibbs
