-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__Tame_rat_princ_898da29e513d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:32:26.368848+00:00
-- url     : https://prove2.me/submissions/eedff2fb-de85-4747-88a6-3fe16457baf2

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExistsTameGen
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__Tame_rat_val_7ae8de760e36

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
theorem _root_.solution {σ : G E Ω} (hσ : σ ∈ Ine (F := E) A) (u : Ωˣ) (hu : A.valuation u = 1) :
    rat σ u ∈ A.principalUnitGroup := by
  rw [ValuationSubring.mem_principalUnitGroup_iff, rat_val, div_sub_one u.ne_zero, map_div₀, hu, div_one]
  exact hσ.2 _ hu.le
end Formalism.BasicNotions.Examples₂.Tame
