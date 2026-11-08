-- Prove2me | solution 1 for RobustMarkovAssort.Duality.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:18:26.06338+00:00
-- url     : https://prove2.me/submissions/f7aecdaf-ce52-463d-911b-50364d67dc17

import Definitions.Def_RobustMarkovAssort_Duality_MCPrograms

open RobustMarkovAssort.Duality in
theorem solution {n : ℕ} (M : RobustMarkovAssort.Duality.MCUncertainty n)
    (h2 : RobustMarkovAssort.Duality.Assumption2 M) :
    RobustMarkovAssort.Duality.Assumption3 (RobustMarkovAssort.Duality.specialization M) ∧
      RobustMarkovAssort.Duality.Assumption4 (RobustMarkovAssort.Duality.specialization M) := by
  refine ⟨fun u hu i => ?_, fun u hu => ⟨fun i => ?_, fun i j hij => ?_, fun i => ?_⟩⟩
  · have hu' : u.1 ∈ M.arrivals ∧ ∀ i, u.2 i ∈ M.rows i := hu
    exact h2.1 u.1 hu'.1 i
  · have hu' : u.1 ∈ M.arrivals ∧ ∀ i, u.2 i ∈ M.rows i := hu
    show 0 < (1 - u.2) i i
    rw [Matrix.sub_apply, Matrix.one_apply_eq, M.rows_diag i (u.2 i) (hu'.2 i)]
    norm_num
  · have hu' : u.1 ∈ M.arrivals ∧ ∀ i, u.2 i ∈ M.rows i := hu
    show (1 - u.2) i j ≤ 0
    rw [Matrix.sub_apply, Matrix.one_apply_ne hij]
    linarith [M.rows_nonneg i (u.2 i) (hu'.2 i) j]
  · have hu' : u.1 ∈ M.arrivals ∧ ∀ i, u.2 i ∈ M.rows i := hu
    show 0 < ∑ j, (1 - u.2) i j
    have h := h2.2 i (u.2 i) (hu'.2 i)
    have e : ∑ j, (1 - u.2) i j = 1 - ∑ j, u.2 i j := by
      simp only [Matrix.sub_apply, Finset.sum_sub_distrib, Matrix.one_apply, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]
    rw [e]
    linarith
