-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.U3.exists_charEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:38:59.18352+00:00
-- url     : https://prove2.me/submissions/e58d72c6-6df7-464a-807e-12051eee7d17

import Definitions.Def_ReciprocityTheory_DualLattices_SumLambdaWeight
import Definitions.Def_ReciprocityTheory_DualLattices_FourierMapSmulLambdaWeight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.U3
open ReciprocityTheory.PGsh.L2
variable {p : ℕ} [hp : Fact p.Prime] {C : Type} [Field C] {v : Valuation C NNReal}
  {R : Type} [CommRing R] [Algebra R C]
namespace ReciprocityTheory.PGsh.Up.U3
theorem _root_.solution [NeZero p] {ζ : C} (hζ : IsPrimitiveRoot ζ p) :
    ∃ e : ZMod p ≃ AddChar (ZMod p) C, (∀ h h', e (h + h') = e h * e h') ∧
      ∀ h a, e h a = ζ ^ (h * a).val := by
  have hp1 : ζ ^ p = 1 := hζ.pow_eq_one
  let ψ : AddChar (ZMod p) C := AddChar.zmodChar p hp1
  have hψ : ∀ a, ψ a = ζ ^ a.val := fun a => AddChar.zmodChar_apply hp1 a
  let f : ZMod p → AddChar (ZMod p) C := fun h => ψ.mulShift h
  have hf : ∀ h a, f h a = ζ ^ (h * a).val := fun h a => by
    simp only [f, AddChar.mulShift_apply, hψ]
  have hgen : ∀ (χ : AddChar (ZMod p) C) (a : ZMod p), χ a = χ 1 ^ a.val := by
    intro χ a
    conv_lhs => rw [← ZMod.natCast_zmod_val a, ← nsmul_one]
    exact AddChar.map_nsmul_eq_pow χ _ _
  have hinj : Function.Injective f := by
    intro h h' hh
    have := congrArg (fun χ : AddChar (ZMod p) C => χ 1) hh
    simp only [hf, mul_one] at this
    exact ZMod.val_injective _ (hζ.pow_inj (ZMod.val_lt h) (ZMod.val_lt h') this)
  have hsurj : Function.Surjective f := by
    intro χ
    have h1 : χ 1 ^ p = 1 := by
      rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, mul_one, ZMod.natCast_self, AddChar.map_zero_eq_one]
    obtain ⟨k, hk, hkχ⟩ := hζ.eq_pow_of_pow_eq_one h1
    refine ⟨(k : ZMod p), ?_⟩
    ext a
    rw [hgen χ a, hgen (f k) a, hf, mul_one, ZMod.val_natCast, Nat.mod_eq_of_lt hk, hkχ]
  refine ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, ?_, ?_⟩
  · intro h h'
    ext a
    show (ψ.mulShift (h + h')) a = ψ.mulShift h a * ψ.mulShift h' a
    rw [AddChar.mulShift_apply, AddChar.mulShift_apply, AddChar.mulShift_apply, add_mul,
      AddChar.map_add_eq_mul]
  · intro h a
    exact hf h a
end ReciprocityTheory.PGsh.Up.U3
