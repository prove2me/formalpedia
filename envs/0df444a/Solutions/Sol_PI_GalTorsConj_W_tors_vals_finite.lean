-- Prove2me | solution 1 for PI.GalTorsConj.W.tors_vals_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:56:46.806467+00:00
-- url     : https://prove2.me/submissions/98061778-2d20-4b41-9293-45b08b1059dd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_IncAdjInclusion
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_WpOnto
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_AddDbl
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_TorsValsFinite
import Theorems.Thm_PI_GalTorsConj_W_mulStable_nat
import Theorems.Thm_Formalism_L2_Th1_F_kerRepsExist
import Theorems.Thm_PI_GalTorsConj_W_wp_add_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.GalTorsConj PI.GalTorsConj.W
open Polynomial Formalism.L2.Th1.F
namespace PI.GalTorsConj.W
theorem _root_.solution (L : PeriodPair) (n : ℕ) (hn : 0 < n) :
    {v : ℂ | ∃ s, (n : ℂ) * s ∈ L.lattice ∧ s ∉ L.lattice ∧ L.weierstrassP s = v}.Finite := by
  have hα : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  obtain ⟨S, hS⟩ := kerRepsExist L (n : ℂ) hα (mulStable_nat L n)
  refine (S.finite_toSet.image L.weierstrassP).subset ?_
  rintro v ⟨s, h1, h2, rfl⟩
  obtain ⟨P, hP, hsP⟩ := hS.2.2 s h1 h2
  refine ⟨P, hP, ?_⟩
  have e : s = P + (s - P) := by ring
  rw [e, wp_add_mem L P hsP]
end PI.GalTorsConj.W
