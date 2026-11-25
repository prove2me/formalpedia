-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.monX_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:39:04.38302+00:00
-- url     : https://prove2.me/submissions/82306043-30f6-447c-9aef-6e3231306359

import Definitions.Def_ReciprocityTheory_DualLattices_LiftMonomialDeterminantStatement
import Definitions.Def_ReciprocityTheory_DualLattices_PowMemCarrier
import Definitions.Def_ReciprocityTheory_DualLattices_IsLocalOfIntegers
import Definitions.Def_ReciprocityTheory_DualLattices_MemOfSumSingleEqZero
import Definitions.Def_ReciprocityTheory_DualLattices_EigenLiftsFrobenius
import Definitions.Def_ReciprocityTheory_DualLattices_HasLenLeOfSurj
import Theorems.Thm_ReciprocityTheory_PGsh_Up_monX_eq

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
theorem _root_.solution (D : Lifts H U X) (α : Nb p g) : monX D α ∈ H.AA.carrier := by
  have hx : ∀ j, xL D j ∈ H.AA.carrier := fun j => (Submodule.mem_inf.mp (D.x_mem j)).1
  have hpow : ∀ (f : Nb p g → C) (n : ℕ), f ∈ H.AA.carrier → f ^ n ∈ H.AA.carrier := by
    intro f n hf
    induction n with
    | zero => simpa using H.AA.one_mem
    | succ n ih =>
      rw [pow_succ]
      exact H.AA.mul_mem _ _ ih hf
  rw [monX_eq]
  exact Finset.prod_induction _ (· ∈ H.AA.carrier) (fun a b ha hb => H.AA.mul_mem a b ha hb)
    H.AA.one_mem (fun j _ => hpow _ _ (hx j))
end ReciprocityTheory.PGsh.Up
