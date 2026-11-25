-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnitDetRoot.single_mem_stdLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:47:42.64917+00:00
-- url     : https://prove2.me/submissions/60d1b768-a8d0-469f-9924-1fb66fc50d99

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_NsmulRelIdxMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_DetMemOfEntries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnitDetRoot
open PI
namespace PI.UnitaryGroupMassFormula.UnitDetRoot
theorem _root_.solution {a : ℕ} {b : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}
    {m : Type} [DecidableEq m] (j : m) :
    Pi.single j (lam * a) ∈ UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m := by
  rw [UnitDetRootDefs.stdLat, AddSubgroup.mem_pi]
  intro i _
  by_cases h : i = j
  · subst h
    rw [Pi.single_eq_same]
    exact (UnitDetRootDefs.cmL a b d ha hd lam hlam).ω₁_mem_lattice
  · rw [Pi.single_eq_of_ne h]
    exact zero_mem _
end PI.UnitaryGroupMassFormula.UnitDetRoot
