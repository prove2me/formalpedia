-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__LB_intCast_mem_vQ_b647479a58db
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:11:37.06759+00:00
-- url     : https://prove2.me/submissions/2e112f57-f461-4be7-a39f-2c22d689978b

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
theorem _root_.solution (n : ℤ) : ((n : ℤ) : 𝓞 ℚ) ∈ (vQ l).asIdeal ↔ ((l : ℕ) : ℤ) ∣ n := by
  rw [show (vQ l).asIdeal = Ideal.span {((l : ℕ) : 𝓞 ℚ)} from rfl, Ideal.mem_span_singleton,
    ← map_dvd_iff Rat.ringOfIntegersEquiv]
  simp
end Formalism.BasicNotions.Examples₂.LB
