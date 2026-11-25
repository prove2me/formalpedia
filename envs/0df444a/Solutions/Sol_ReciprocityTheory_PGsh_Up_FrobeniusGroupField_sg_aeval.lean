-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.FrobeniusGroupField.sg_aeval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:43:57.977766+00:00
-- url     : https://prove2.me/submissions/1581ca4c-5345-46d7-973c-b47850a3948e

import Definitions.Def_ReciprocityTheory_DualLattices_EigPowEqOne
import Definitions.Def_ReciprocityTheory_DualLattices_IsAdicCompleteOfBasis
import Definitions.Def_ReciprocityTheory_DualLattices_SgAlgebraMap
import Theorems.Thm_ReciprocityTheory_PGsh_Up_FrobeniusGroupField_sg_algebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix Polynomial
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.FrobeniusGroupField
variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]
namespace ReciprocityTheory.PGsh.Up.FrobeniusGroupField
theorem _root_.solution (hv : v.Integers R) {p : ℕ} [Fact p.Prime]
    [Algebra ℤ_[p] R] {n : Type} [Fintype n] [DecidableEq n] {ι : Type}
    {O : Type} [CommRing O] [Algebra ℤ_[p] O] (ρ : O →ₐ[ℤ_[p]] Matrix n n ℤ_[p])
    (εT : ι → Matrix n n R) (sg : ι → O →+* R)
    (heig : ∀ a j, (ρ a).map (algebraMap ℤ_[p] R) * εT j = sg j a • εT j) (j : ι) (hj : εT j ≠ 0)
    (a : O) (Q : ℤ_[p][X]) : sg j (aeval a Q) = aeval (sg j a) Q := by
  have hc : (sg j).comp (algebraMap ℤ_[p] O) = algebraMap ℤ_[p] R :=
    RingHom.ext fun z => sg_algebraMap hv ρ εT sg heig j hj z
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂, hc]
end ReciprocityTheory.PGsh.Up.FrobeniusGroupField
