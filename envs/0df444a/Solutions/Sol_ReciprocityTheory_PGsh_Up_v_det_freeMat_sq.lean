-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.v_det_freeMat_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:08:04.512415+00:00
-- url     : https://prove2.me/submissions/661a6a9b-8ff1-4f62-8d5a-9a3f8568af57

import Definitions.Def_ReciprocityTheory_DualLattices_DiscriminantColengthStatement
import Definitions.Def_ReciprocityTheory_DualLattices_ColengthSqBlockVandermonde
import Theorems.Thm_ReciprocityTheory_PGsh_Up_det_freeMat
import Theorems.Thm_ReciprocityTheory_PGsh_Up_v_det_vandermonde_sq

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
theorem _root_.solution {n : ℕ} (a : Fin n → C) (s : ℕ) :
    v (freeMat a s).det ^ 2 = v (discr a) ^ s := by
  rw [det_freeMat, map_pow, pow_right_comm, v_det_vandermonde_sq]
end ReciprocityTheory.PGsh.Up
