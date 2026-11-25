-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__LB_val_intCast_le_one_76c256b9728d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:11:40.193959+00:00
-- url     : https://prove2.me/submissions/08d1caf8-5596-4bda-8cf0-ec98ec0c8e68

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
theorem _root_.solution (A : ValuationSubring Ω) (n : ℤ) : A.valuation (n : Ω) ≤ 1 := by
  rw [ValuationSubring.valuation_le_one_iff]
  exact intCast_mem A n
end Formalism.BasicNotions.Examples₂.LB
