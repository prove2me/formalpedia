-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__LB_isPlaceOver_vQ_17c88a143786
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:25:52.572905+00:00
-- url     : https://prove2.me/submissions/2d4a0c1c-5d0d-48db-9e9b-fb86776937dc

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocA
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_intCast_mem_vQ_b647479a58db
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_val_intCast_lt_one_iff_227b321c2967

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
theorem _root_.solution [Algebra ℚ Ω] (A : ValuationSubring Ω) (hA : A.valuation ((l : ℕ) : Ω) < 1) :
    IsPlaceOver (F := ℚ) A (vQ l) := by
  unfold IsPlaceOver
  intro x
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, ((n : 𝓞 ℚ)) = x :=
    ⟨Rat.ringOfIntegersEquiv x, by
      rw [← eq_intCast Rat.ringOfIntegersEquiv.symm, RingEquiv.symm_apply_apply]⟩
  rw [intCast_mem_vQ, ← val_intCast_lt_one_iff A hA n]
  first
    | simp
    | (push_cast; rfl)
    | norm_cast
end Formalism.BasicNotions.Examples₂.LB
