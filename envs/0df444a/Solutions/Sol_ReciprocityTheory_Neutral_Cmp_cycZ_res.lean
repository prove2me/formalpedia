-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Cmp.cycZ_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:32:23.281258+00:00
-- url     : https://prove2.me/submissions/aa5c3e3b-cf2e-43a1-9758-76a07921d5fa

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ContinuousGK
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_Inertia
import Theorems.Thm_ReciprocityTheory_Neutral_Cmp_res_spec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Cmp
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]
namespace ReciprocityTheory.Neutral.Cmp
theorem _root_.solution (ι : Ω →+* PadicAlgCl p) (l : ℕ) [Fact l.Prime] (σ : GK F ι) :
    cycZ F Ω l (res ι σ) = cyclotomicCharacter (PadicAlgCl p) l (σ : PadicAlgCl p ≃+* PadicAlgCl p) := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have : NeZero (l : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩
  have : NeZero (l : ℚ_[p]) := ⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩
  apply Units.ext
  refine PadicInt.ext_of_toZModPow.mp fun n => ?_
  change (cyclotomicCharacter Ω l (MulSemiringAction.toRingAut _ Ω (res ι σ))).val.toZModPow n = _
  rw [cyclotomicCharacter.toZModPow]
  refine (modularCyclotomicCharacter.unique _ _ _ ?_).symm
  intro t ht
  apply ι.injective
  have ht' : (t : Ω) ^ l ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 ht, Units.val_one]
  have h1 : ι (t : Ω) ^ l ^ n = 1 := by rw [← map_pow, ht', map_one]
  have := cyclotomicCharacter.spec (L := PadicAlgCl p) l (σ : PadicAlgCl p ≃+* PadicAlgCl p) (ι t) h1
  rw [map_pow]
  change ι (res ι σ t) = _
  rw [res_spec]
  exact this
end ReciprocityTheory.Neutral.Cmp
