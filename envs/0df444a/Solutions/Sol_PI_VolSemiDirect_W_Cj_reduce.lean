-- Prove2me | solution 1 for PI.VolSemiDirect.W.Cj.reduce
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:14:36.927452+00:00
-- url     : https://prove2.me/submissions/6116cecf-7221-432c-879e-a1aa6710b381

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_CjDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_GlGeneratedTransvectionsDiag
import Theorems.Thm_PI_VolSemiDirect_W_Cj_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W PI.VolSemiDirect.W.Cj
open Matrix
variable {A : Type} [CommRing A] {k : ℕ}
namespace PI.VolSemiDirect.W.Cj
theorem _root_.solution (hA : HasStableRangeOne A) : ∀ n : ℕ, ∀ X : GL (Fin k) A,
    Red (k - n) (X : Matrix (Fin k) (Fin k) A) → X ∈ Subgroup.closure (genSet A k) := by
  intro n
  induction n with
  | zero =>
    intro X hX
    have hX1 : X = 1 := Units.ext (Matrix.ext fun i j => by
      rw [Units.val_one]
      exact hX i j (Or.inl (by have := i.isLt; omega)))
    rw [hX1]
    exact Subgroup.one_mem _
  | succ n ih =>
    intro X hX
    by_cases hkn : k ≤ n
    · have e : k - (n + 1) = k - n := by omega
      rw [e] at hX
      exact ih X hX
    · have hm : k - (n + 1) < k := by omega
      obtain ⟨g, hg, h, hh, hred⟩ := step hA (k - (n + 1)) hm X hX
      have e : k - (n + 1) + 1 = k - n := by omega
      rw [e] at hred
      have hmem := ih _ hred
      have hX' : X = g⁻¹ * (g * X * h) * h⁻¹ := by group
      rw [hX']
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hg) hmem) (Subgroup.inv_mem _ hh)
end PI.VolSemiDirect.W.Cj
