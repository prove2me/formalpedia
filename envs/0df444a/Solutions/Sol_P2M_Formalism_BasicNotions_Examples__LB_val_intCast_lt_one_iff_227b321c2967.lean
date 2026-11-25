-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__LB_val_intCast_lt_one_iff_227b321c2967
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:50:54.151807+00:00
-- url     : https://prove2.me/submissions/afae6565-a71e-48aa-ba84-d2264b77ea77

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocA
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_val_intCast_le_one_76c256b9728d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.LB
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Pointwise
variable (l : ℕ) [hl : Fact l.Prime]
variable {l} {Ω : Type} [Field Ω]
namespace Formalism.BasicNotions.Examples₂.LB
theorem _root_.solution (A : ValuationSubring Ω) (hA : A.valuation ((l : ℕ) : Ω) < 1) (n : ℤ) :
    A.valuation (n : Ω) < 1 ↔ ((l : ℕ) : ℤ) ∣ n := by
  constructor
  · intro h
    by_contra hnd
    have hp : Prime ((l : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hl.out
    have hc : IsCoprime ((l : ℕ) : ℤ) n := (Irreducible.coprime_iff_not_dvd hp.irreducible).2 hnd
    obtain ⟨u, w, huw⟩ := hc
    have h1 : A.valuation ((u : Ω) * ((l : ℕ) : Ω)) < 1 := by
      rw [map_mul]
      exact (mul_le_of_le_one_left' (val_intCast_le_one A u)).trans_lt hA
    have h2 : A.valuation ((w : Ω) * (n : Ω)) < 1 := by
      rw [map_mul]
      exact (mul_le_of_le_one_left' (val_intCast_le_one A w)).trans_lt h
    have h3 := Valuation.map_add_lt A.valuation h1 h2
    have h4 : ((u : Ω) * ((l : ℕ) : Ω)) + (w : Ω) * (n : Ω) = 1 := by
      have := congrArg (Int.cast (R := Ω)) huw
      push_cast at this
      exact this
    rw [h4, map_one] at h3
    exact lt_irrefl _ h3
  · rintro ⟨m, rfl⟩
    push_cast
    rw [map_mul]
    exact (mul_le_of_le_one_right' (val_intCast_le_one A m)).trans_lt hA
end Formalism.BasicNotions.Examples₂.LB
