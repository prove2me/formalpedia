-- Prove2me | solution 1 for PI.GalTorsConj.W.tors_of_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:42:25.993213+00:00
-- url     : https://prove2.me/submissions/35f8f5f7-95b7-478c-ba6a-8c0e6a61efd2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_MulDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_AddLaw
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_AddDbl
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_WpOnto
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_MulMain
import Theorems.Thm_Formalism_L2_Th1_F_mulStableIntegral


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
open Formalism.L2.Th1.F
namespace PI.GalTorsConj.W
theorem _root_.solution {L : PeriodPair} {c P : ℂ} (hc0 : c ≠ 0) (hc : MulStable L c)
    (hP : c * P ∈ L.lattice) : ∃ m : ℕ, 0 < m ∧ (m : ℂ) * P ∈ L.lattice := by
  obtain ⟨t, n, ht, hn, -⟩ := mulStableIntegral L c hc
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have h1 : (n : ℂ) = (Complex.normSq c : ℂ) := by rw [← hn, Complex.mul_conj]
    have h2 : (n : ℝ) = Complex.normSq c := by exact_mod_cast h1
    rw [h2]
    exact Complex.normSq_pos.mpr hc0
  have hn0' : 0 < n := by exact_mod_cast hn0
  refine ⟨n.toNat, by omega, ?_⟩
  have e : ((n.toNat : ℕ) : ℂ) * P = (t : ℤ) • (c * P) - c * (c * P) := by
    have : ((n.toNat : ℕ) : ℂ) = (n : ℂ) := by
      have : ((n.toNat : ℤ)) = n := Int.toNat_of_nonneg hn0'.le
      exact_mod_cast this
    rw [this, ← hn, zsmul_eq_mul]
    have hconj : (starRingEnd ℂ) c = (t : ℂ) - c := by rw [← ht]; ring
    rw [hconj]
    ring
  rw [e]
  exact L.lattice.sub_mem (L.lattice.smul_mem _ hP) (hc _ hP)
end PI.GalTorsConj.W
