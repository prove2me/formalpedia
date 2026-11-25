-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.box_lattice_point_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:21:18.87469+00:00
-- url     : https://prove2.me/submissions/2d219d7d-8be6-4077-91b5-c3e12e7f12f3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_BoxBoundAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SymmetricDistance_SymDistOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeMultiplicity_EncardLeOfFinset
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_BoxBound
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_BoxB_hs_exp_le
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_BoxB_hs_unitary_mul
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_REAL_polar_decomposition_holds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
open BoxB
namespace PI.UnitaryGroupMassFormula.LCG
theorem _root_.solution : BoxBound := by
  intro n ε g
  have hK : ∀ k : Matrix (Fin n) (Fin n) ℂ, k ∈ Formalism.REAL.Kset ε → kᴴ * k = 1 := by
    intro k hk
    simp only [Formalism.REAL.Kset, Set.mem_setOf_eq] at hk
    exact Matrix.mem_unitaryGroup_iff'.mp hk.1
  have hP : Formalism.REAL.Polar := Formalism.REAL.polar_decomposition_holds
  have hgi : Formalism.REAL.inUJ ε (((g : (Matrix (Fin n) (Fin n) ℂ)ˣ)) : Matrix (Fin n) (Fin n) ℂ) := g.2
  obtain ⟨k0, X0, hk0, hX0, hg0⟩ := (hP n ε).1 _ hgi
  set S := {t | ∃ k X : Matrix (Fin n) (Fin n) ℂ, k ∈ Formalism.REAL.Kset ε ∧ Formalism.REAL.inP ε X ∧
      ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = k * NormedSpace.exp X ∧
      t = Real.sqrt (Formalism.REAL.hs X)} with hS
  have hne : S.Nonempty := ⟨_, k0, X0, hk0, hX0, hg0, rfl⟩
  have hbound : ∀ t ∈ S, hsN (Formalism.MainNotions.S.uMat g) ≤ Real.sqrt n * Real.exp t := by
    rintro t ⟨k, X, hk, _, hgk, rfl⟩
    unfold hsN Formalism.MainNotions.S.uMat
    rw [hgk, hs_unitary_mul (hK k hk)]
    calc Real.sqrt (Formalism.REAL.hs (NormedSpace.exp X))
        ≤ Real.sqrt ((Real.sqrt n * Real.exp (Real.sqrt (Formalism.REAL.hs X))) ^ 2) :=
          Real.sqrt_le_sqrt (hs_exp_le X)
      _ = Real.sqrt n * Real.exp (Real.sqrt (Formalism.REAL.hs X)) := Real.sqrt_sq (by positivity)
  show hsN (Formalism.MainNotions.S.uMat g) ≤ Real.sqrt n * Real.exp (sInf S)
  by_contra hlt
  push_neg at hlt
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    have h0 : hsN (Formalism.MainNotions.S.uMat g) = 0 := by
      unfold hsN Formalism.REAL.hs
      simp
    rw [h0] at hlt
    simp at hlt
  · have hsqpos : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hnpos)
    set a := hsN (Formalism.MainNotions.S.uMat g) with ha
    have hapos : 0 < a := lt_of_le_of_lt (by positivity) hlt
    have h1 : sInf S < Real.log (a / Real.sqrt n) := by
      rw [Real.lt_log_iff_exp_lt (div_pos hapos hsqpos), lt_div_iff₀ hsqpos, mul_comm]
      exact hlt
    obtain ⟨t, htS, htlt⟩ := exists_lt_of_csInf_lt hne h1
    have h2 := hbound t htS
    have h3 : Real.exp t < a / Real.sqrt n := by
      rw [← Real.exp_log (div_pos hapos hsqpos)]
      exact Real.exp_lt_exp.mpr htlt
    rw [lt_div_iff₀ hsqpos] at h3
    linarith
end PI.UnitaryGroupMassFormula.LCG
