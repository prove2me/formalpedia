-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.de_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-23T03:17:55.701542+00:00
-- url     : https://prove2.me/submissions/7eaa7d4d-0df1-4eab-91e1-c07f16655ec1

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

theorem AuxDG_L1 {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) : 1 ≤ Lsq x l := by
  unfold Lsq
  have : 0 ≤ ∑ j : Fin p, (if j.val < l.val then ‖x.1 j‖ ^ 2 else 0) :=
    Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity
  linarith


theorem ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.de_ge_one {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) : 1 ≤ de x l := by
  unfold de
  have h1 := AuxDG_L1 x l
  have h2 : 1 ≤ rhoSq x l := (AuxDG_L1 x l).trans (AuxRS_ge x l l)
  have h3 : 0 ≤ ‖bco x l‖ ^ 2 := by positivity
  have h4 : 1 ≤ Lsq x l * rhoSq x l + ‖bco x l‖ ^ 2 := by nlinarith
  rw [show (1:ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_le_sqrt h4


end

theorem solution {p m : ℕ} (x : ReciprocityTheory.ChartRestriction.DS.Xi.Xp p m) (l : Fin (p + 1)) :
    1 ≤ ReciprocityTheory.ChartRestriction.DS.Xi.de x l :=
  ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.de_ge_one x l
