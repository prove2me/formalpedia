-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.rhoSq_ge
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-23T03:17:38.953983+00:00
-- url     : https://prove2.me/submissions/2403cab9-a945-42d7-a7c5-d9a9e95df203

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_RhoSqInsSucc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
theorem AuxRS_L {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) : Lsq x l ≤ Lsq x (Fin.last p) := by
  unfold Lsq
  have : ∀ j : Fin p, (if j.val < l.val then ‖x.1 j‖ ^ 2 else 0) ≤
      (if j.val < (Fin.last p).val then ‖x.1 j‖ ^ 2 else 0) := by
    intro j
    have hj : j.val < (Fin.last p).val := by simp [j.isLt]
    rw [if_pos hj]
    split_ifs
    · exact le_rfl
    · positivity
  linarith [Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => this j]

theorem AuxRS_ge {p m : ℕ} (x : Xp p m) (l l' : Fin (p + 1)) : Lsq x l' ≤ rhoSq x l := by
  unfold rhoSq
  have h1 := AuxRS_L x l'
  have h2 : 0 ≤ ∑ i, ‖x.2.2.1 i‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have h3 : 0 ≤ ∑ j : Fin p, (if l.val ≤ j.val then ‖x.2.1 j‖ ^ 2 else 0) :=
    Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity
  linarith


theorem ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.rhoSq_ge {p m : ℕ} (x : Xp p m) (l l' : Fin (p + 1)) : Lsq x l' ≤ rhoSq x l := by
  exact AuxRS_ge x l l'


end

theorem solution {p m : ℕ} (x : ReciprocityTheory.ChartRestriction.DS.Xi.Xp p m) (l l' : Fin (p + 1)) :
    ReciprocityTheory.ChartRestriction.DS.Xi.Lsq x l' ≤ ReciprocityTheory.ChartRestriction.DS.Xi.rhoSq x l :=
  ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.rhoSq_ge x l l'
