-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.prod_fder
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:38:14.647007+00:00
-- url     : https://prove2.me/submissions/799017d9-ab9f-4971-8f16-a84bd7ce9651

import Definitions.Def_ReciprocityTheory_DualLattices_ColengthSqBlockVandermonde
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsUnitMinor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {v : Valuation C NNReal}
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution {n : ℕ} (a : Fin n → C) : ∏ τ, fder a τ = discr a := rfl
end ReciprocityTheory.PGsh.Up
