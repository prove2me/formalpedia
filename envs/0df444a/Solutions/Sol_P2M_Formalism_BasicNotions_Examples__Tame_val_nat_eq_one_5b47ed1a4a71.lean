-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__Tame_val_nat_eq_one_5b47ed1a4a71
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:52:05.296953+00:00
-- url     : https://prove2.me/submissions/e3a97239-2da0-4c01-8386-95639525990b

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExistsTameGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.Tame
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω)
namespace Formalism.BasicNotions.Examples₂.Tame
theorem _root_.solution (p N : ℕ) (hp : A.valuation (p : Ω) < 1) (hc : N.Coprime p) :
    A.valuation (N : Ω) = 1 := by
  have hle : ∀ z : ℤ, A.valuation (z : Ω) ≤ 1 := fun z => (A.valuation_le_one_iff _).mpr (intCast_mem A z)
  have hN : A.valuation (N : Ω) ≤ 1 := by exact_mod_cast hle N
  refine le_antisymm hN (not_lt.mp fun hlt => ?_)
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hc
  have e : (a : Ω) * N + (b : Ω) * p = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
  have : A.valuation ((a : Ω) * N + (b : Ω) * p) < 1 := by
    refine Valuation.map_add_lt _ ?_ ?_ <;> rw [map_mul]
    · exact lt_of_le_of_lt (mul_le_of_le_one_left' (hle a)) hlt
    · exact lt_of_le_of_lt (mul_le_of_le_one_left' (hle b)) hp
  rw [e, map_one] at this
  exact lt_irrefl _ this
end Formalism.BasicNotions.Examples₂.Tame
