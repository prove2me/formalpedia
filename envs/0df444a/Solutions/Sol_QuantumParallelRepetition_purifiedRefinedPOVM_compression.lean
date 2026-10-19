-- Prove2me | solution 1 for QuantumParallelRepetition.purifiedRefinedPOVM_compression
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:14.37599+00:00
-- url     : https://prove2.me/submissions/5d8e5e10-d6aa-4ba2-9474-853c62a7d33b

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_purifiedRefinedEffect_compression

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
set_option maxHeartbeats 400000
namespace QuantumParallelRepetition
theorem _root_.solution
    {ι d e : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (hΓ : Matrix.conjTranspose Γ * Γ = F)
    (effect : ι → Matrix d d ℂ)
    (hpositive : ∀ a, (effect a).PosSemidef)
    (hsum : (∑ a : ι, effect a) = F)
    (a₀ a : ι) :
    Matrix.conjTranspose Γ *
      (purifiedRefinedPOVM F hF Γ hΓ effect hpositive hsum a₀).effect a *
        Γ = effect a :=
  purifiedRefinedEffect_compression F hF Γ hΓ effect
    hpositive hsum a₀ a
end QuantumParallelRepetition
