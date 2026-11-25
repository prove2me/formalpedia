-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.core_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:55:54.407029+00:00
-- url     : https://prove2.me/submissions/6aa31089-41cf-49db-8292-5b632e1e2974

import Definitions.Def_ReciprocityTheory_DualLattices_EigenLengthFrobeniusStatement
import Definitions.Def_ReciprocityTheory_DualLattices_EigenLiftsFrobeniusStatement

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
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution (hL : EigenLiftsStatement) (hB : EigenLiftsBasisStatement) (hF : EigenLiftsFrobeniusStatement) :
    EigenLengthFrobeniusStatement := by
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hp hS H U X hX hprod i
  obtain ⟨D⟩ := hL p g C v R O σ cp hp hS H U X hX
  exact hF p g C v R O σ cp hp hS H U X D (hB p g C v R O σ cp hS H U X hprod D) i
end ReciprocityTheory.PGsh.Up
