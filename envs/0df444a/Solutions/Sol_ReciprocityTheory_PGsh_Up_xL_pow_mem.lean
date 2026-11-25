-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.xL_pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:09:17.245327+00:00
-- url     : https://prove2.me/submissions/8d68cd22-9819-4dd1-992c-9932c4a90eed

import Definitions.Def_ReciprocityTheory_DualLattices_LiftMonomialDeterminantStatement
import Definitions.Def_ReciprocityTheory_DualLattices_PowMemCarrier
import Definitions.Def_ReciprocityTheory_DualLattices_HasLenCokerDet
import Definitions.Def_ReciprocityTheory_DualLattices_EigenLiftsFrobenius

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} {H : HodgeTateDatum p g v R O σ cp} {U : UnramData p g v R O σ cp H}
  {X : Fin U.m → NNReal}
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution (D : Lifts H U X) (hp : 2 ≤ p) (j : Ix g) :
    (fun y => xL D j y ^ p) ∈ sqIdeal (augIdeal H.AA.carrier) := by
  have hx : xL D j ∈ augIdeal H.AA.carrier := D.x_mem j
  have hxA : xL D j ∈ H.AA.carrier := hx.1
  have hx0 : xL D j 0 = 0 := hx.2
  have hpow : ∀ n : ℕ, xL D j ^ (n + 1) ∈ augIdeal H.AA.carrier := by
    intro n
    induction n with
    | zero => simpa using hx
    | succ n ih =>
      refine ⟨?_, ?_⟩
      · rw [pow_succ]
        exact H.AA.mul_mem _ _ ih.1 hxA
      · show (xL D j ^ (n + 1 + 1)) 0 = 0
        rw [Pi.pow_apply, hx0, zero_pow (by omega)]
  have heq : (fun y => xL D j y ^ p) = xL D j * xL D j ^ (p - 1 - 1 + 1) := by
    funext y
    rw [Pi.mul_apply, Pi.pow_apply, ← pow_succ']
    congr 1
    omega
  rw [heq]
  exact Submodule.subset_span ⟨_, hx, _, hpow _, rfl⟩
end ReciprocityTheory.PGsh.Up
