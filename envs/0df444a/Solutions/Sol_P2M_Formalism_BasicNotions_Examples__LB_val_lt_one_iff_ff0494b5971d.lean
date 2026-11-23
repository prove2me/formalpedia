-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__LB_val_lt_one_iff_ff0494b5971d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:22.103289+00:00
-- url     : https://prove2.me/submissions/7fad3da4-f752-41ae-96c1-9d536c111142

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocA

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
theorem _root_.solution {A : ValuationSubring Ω} {j : Ω →+* PadicAlgCl l}
    (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) (y : Ω) : A.valuation y < 1 ↔ ‖j y‖ < 1 := by
  by_cases hy : y = 0
  · simp [hy]
  · have hjy : j y ≠ 0 := (map_ne_zero j).2 hy
    have hpos : 0 < ‖j y‖ := norm_pos_iff.2 hjy
    have e1 := (Valuation.one_lt_val_iff A.valuation (inv_ne_zero hy)).symm
    rw [inv_inv] at e1
    rw [e1, ← not_le, ValuationSubring.valuation_le_one_iff, hj, map_inv₀, norm_inv, not_le]
    first
      | exact one_lt_inv₀ hpos
      | (rw [one_lt_inv_iff₀]; simp [hpos])
end Formalism.BasicNotions.Examples₂.LB
