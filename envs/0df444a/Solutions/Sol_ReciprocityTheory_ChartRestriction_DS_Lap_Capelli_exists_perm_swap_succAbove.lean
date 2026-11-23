-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.exists_perm_swap_succAbove
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:03:43.420849+00:00
-- url     : https://prove2.me/submissions/887611be-dc19-4897-b7cf-be53c391de7a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowAnti
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_ProdOfFnUpdateEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowColA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
open ReciprocityTheory.ChartRestriction.DS
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
theorem _root_.solution {p : ℕ} (i s : Fin (p + 1)) (h : i ≠ s) :
    ∃ π : Equiv.Perm (Fin p), ((Equiv.Perm.sign π : ℤˣ) : ℤ) = (-1) ^ ((i : ℕ) + (s : ℕ) + 1) ∧
      ∀ t, Equiv.swap i s (i.succAbove t) = s.succAbove (π t) := by
  classical
  have hsa : ∀ (j : Fin (p + 1)) (u : Fin p), j.succAbove u = j.cycleRange.symm u.succ := fun j u =>
    ((Equiv.symm_apply_eq _).mpr (Fin.cycleRange_succAbove j u).symm).symm
  let ρ : Equiv.Perm (Fin (p + 1)) := s.cycleRange * Equiv.swap i s * i.cycleRange.symm
  have hρapp : ∀ x, ρ x = s.cycleRange (Equiv.swap i s (i.cycleRange.symm x)) := fun x => rfl
  have hρ0 : ρ 0 = 0 := by
    rw [hρapp, Fin.cycleRange_symm_zero, Equiv.swap_apply_left, Fin.cycleRange_self]
  let π : Equiv.Perm (Fin p) := (Equiv.Perm.decomposeFin ρ).2
  have hdec : Equiv.Perm.decomposeFin.symm ((Equiv.Perm.decomposeFin ρ).1, π) = ρ :=
    Equiv.Perm.decomposeFin.symm_apply_apply ρ
  have h1 : (Equiv.Perm.decomposeFin ρ).1 = 0 := by
    have := congrArg (fun g : Equiv.Perm (Fin (p + 1)) => g 0) hdec
    simp only [Equiv.Perm.decomposeFin_symm_apply_zero] at this
    rw [this, hρ0]
  rw [h1] at hdec
  refine ⟨π, ?_, ?_⟩
  · have hs : Equiv.Perm.sign ρ = Equiv.Perm.sign π := by
      rw [← hdec, Equiv.Perm.decomposeFin.symm_sign]
      simp
    have hs2 : Equiv.Perm.sign ρ = (-1) ^ (s : ℕ) * (-1) * (-1) ^ (i : ℕ) := by
      simp only [ρ, Equiv.Perm.sign_mul, Equiv.Perm.sign_symm, Fin.sign_cycleRange,
        Equiv.Perm.sign_swap h]
    rw [← hs, hs2]
    push_cast
    ring
  · intro t
    have h2 : (π t).succ = ρ t.succ := by
      rw [← hdec, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply]
    rw [hsa s, h2, hρapp, ← hsa i, Equiv.symm_apply_apply]
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
