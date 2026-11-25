-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ProdUnitInert.not_small_sq_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:41:27.819437+00:00
-- url     : https://prove2.me/submissions/149198ea-0af2-4b6a-8d15-d71fa696849a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertUnitProduct_NatCastNormLeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ProdUnitInert
variable {p : ℕ} [Fact p.Prime]
namespace PI.UnitaryGroupMassFormula.ProdUnitInert
theorem _root_.solution (d : ℕ) (hd : ¬ IsSquare (((-(d : ℤ) : ℤ) : ZMod p))) (t : ℤ_[p]) :
    ¬ ‖t ^ 2 + (d : ℤ_[p])‖ < 1 := by
  intro h
  have hmem : t ^ 2 + (d : ℤ_[p]) ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
    rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]; exact h
  rw [RingHom.mem_ker, map_add, map_pow, map_natCast] at hmem
  apply hd
  refine ⟨PadicInt.toZMod t, ?_⟩
  push_cast
  linear_combination (-1 : ZMod p) * hmem
end PI.UnitaryGroupMassFormula.ProdUnitInert
