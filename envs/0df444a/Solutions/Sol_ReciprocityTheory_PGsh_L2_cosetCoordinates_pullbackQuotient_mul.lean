-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.cosetCoordinates_pullbackQuotient_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:21:08.51851+00:00
-- url     : https://prove2.me/submissions/03752fdd-6802-4a9c-a97a-a673cfd71e88

import Definitions.Def_ReciprocityTheory_DualLattices_TensorSpan
import Definitions.Def_ReciprocityTheory_DualLattices_IsUnitDetOfSpanEq
import Definitions.Def_ReciprocityTheory_DualLattices_ValuationDetLeOneOfEntriesIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
namespace ReciprocityTheory.PGsh.L2
theorem _root_.solution (K : AddSubgroup N) [DecidablePred (· ∈ K)] (β : Matrix K K C) (e : N ⧸ K → C) (f : N → C)
    (x : N) : h3co K β (pullQ (R := R) K e * f) x = e (x : N ⧸ K) • h3co K β f x := by
  have hE : (fun k : K => (pullQ (R := R) K e * f) (x + k)) =
      e (x : N ⧸ K) • fun k : K => f (x + k) := by
    ext k
    show e ((x + k : N) : N ⧸ K) * f (x + k) = e (x : N ⧸ K) * f (x + k)
    rw [QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff _).mpr k.2, add_zero]
  show β⁻¹ *ᵥ (fun k : K => (pullQ (R := R) K e * f) (x + k)) = _
  rw [hE, Matrix.mulVec_smul]
  rfl
end ReciprocityTheory.PGsh.L2
