-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnitDetRoot.stdLat_le_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:12:12.757854+00:00
-- url     : https://prove2.me/submissions/7a57bca0-0ab7-4ae3-aa72-cabb3dd2a0c1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_GlobalLUnit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_NsmulRelIdxMem
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_mem_cmL
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_mem_stdLat
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_area_cmL
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_pair_im
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_altE_stdH

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
    {m : Type} [Fintype m] [DecidableEq m] {x : m → ℂ} (hx : x ∈ UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) :
    x ∈ UnitDetRootDefs.dualLat (UnitDetRootDefs.stdH (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) (UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) := by
  intro y hy
  rw [mem_stdLat] at hx hy
  choose p q hpq using fun i => (mem_cmL (ha := ha) (hd := hd) (hlam := hlam)).mp (hx i)
  choose p' q' hpq' using fun i => (mem_cmL (ha := ha) (hd := hd) (hlam := hlam)).mp (hy i)
  refine ⟨∑ i, (q i * p' i - p i * q' i), ?_⟩
  rw [altE_stdH]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hpq i, hpq' i, pair_im, area_cmL]
  have h1 : 0 < Complex.normSq lam := Complex.normSq_pos.mpr hlam
  have h2 : (0 : ℝ) < a := by exact_mod_cast ha
  have h3 : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  push_cast
  field_simp
end PI.UnitaryGroupMassFormula.UnitDetRoot
