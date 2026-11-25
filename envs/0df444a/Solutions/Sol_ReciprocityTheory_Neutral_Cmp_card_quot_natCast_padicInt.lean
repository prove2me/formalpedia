-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Cmp.card_quot_natCast_padicInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:34:43.997386+00:00
-- url     : https://prove2.me/submissions/4ba3d65a-31e9-49ce-98a9-7c5a4cef3bc4

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ModelA
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_Inertia
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ModelF

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
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain ValuativeRel
namespace ReciprocityTheory.Neutral.Cmp
theorem _root_.solution (p : ℕ) [Fact p.Prime] {n : ℕ} (hn : n ≠ 0) :
    Nat.card (ℤ_[p] ⧸ Ideal.span {(n : ℤ_[p])}) = p ^ padicValNat p n := by
  have hp := (Fact.out : p.Prime)
  have hdec : n = p ^ padicValNat p n * (n / p ^ padicValNat p n) := by
    have h1 := Nat.ordProj_mul_ordCompl_eq_self n p
    rw [Nat.factorization_def n hp] at h1
    exact h1.symm
  have hnd : ¬ p ∣ n / p ^ padicValNat p n := by
    have h1 := Nat.not_dvd_ordCompl hp hn
    rwa [Nat.factorization_def n hp] at h1
  have hu : IsUnit (((n / p ^ padicValNat p n : ℕ) : ℤ_[p])) := by
    rw [PadicInt.isUnit_iff]
    by_contra hne
    have hlt : ‖(((n / p ^ padicValNat p n : ℕ) : ℤ_[p]))‖ < 1 :=
      lt_of_le_of_ne (PadicInt.norm_le_one _) hne
    rw [PadicInt.norm_lt_one_iff_dvd] at hlt
    obtain ⟨c, hc⟩ := hlt
    have h1 := congrArg PadicInt.toZMod hc
    rw [map_natCast, map_mul, map_natCast, ZMod.natCast_self, zero_mul,
      ZMod.natCast_eq_zero_iff] at h1
    exact hnd h1
  have hspan : Ideal.span {(n : ℤ_[p])} = Ideal.span {(p : ℤ_[p]) ^ padicValNat p n} := by
    conv_lhs => rw [hdec]
    push_cast
    exact Ideal.span_singleton_mul_right_unit hu _
  rw [hspan, ← PadicInt.ker_toZModPow]
  rw [Nat.card_congr (RingHom.quotientKerEquivOfSurjective
    (ZMod.ringHom_surjective (PadicInt.toZModPow (p := p) (padicValNat p n)))).toEquiv, Nat.card_zmod]
end ReciprocityTheory.Neutral.Cmp
