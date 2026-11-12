-- Prove2me | solution 1 for RobustMarkovAssort.Duality.theorem_1
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-12T01:56:18.994512+00:00
-- url     : https://prove2.me/submissions/80ad6f1c-e28c-4e9b-8fd2-dadb2afea309

import Definitions.Def_RobustMarkovAssort_Duality_MCPrograms

namespace RobustMarkovAssort.Duality

private def ceUncertainty : MCUncertainty 2 where
  r := ![0, 1]
  r_nonneg := by
    intro i
    fin_cases i <;> norm_num
  arrivals := {fun _ => (1 / 2 : ℝ)}
  arrivals_nonempty := ⟨fun _ => (1 / 2 : ℝ), rfl⟩
  rows := fun i =>
    if i = 0 then {q : Vec 2 | q 0 = 0 ∧ 0 < q 1 ∧ q 1 < 1 / 2}
    else {0}
  rows_nonempty := by
    intro i
    fin_cases i
    · refine ⟨![0, 1 / 4], ?_⟩
      simp
      norm_num
    · simp
  rows_nonneg := by
    intro i q hq j
    fin_cases i
    · simp at hq
      fin_cases j <;> simp <;> linarith
    · simp at hq
      subst hq
      simp
  rows_diag := by
    intro i q hq
    fin_cases i
    · simp at hq
      exact hq.1
    · simp at hq
      subst hq
      simp
  rows_subprob := by
    intro i q hq
    rw [Fin.sum_univ_two]
    fin_cases i
    · simp at hq
      linarith
    · simp at hq
      subst hq
      norm_num

private lemma ceAssumption2 : Assumption2 ceUncertainty := by
  refine ⟨?_, ?_⟩
  · intro l hl i
    simp [ceUncertainty] at hl
    subst hl
    norm_num
  · intro i q hq
    rw [Fin.sum_univ_two]
    fin_cases i
    · simp [ceUncertainty] at hq
      linarith
    · simp [ceUncertainty] at hq
      subst hq
      norm_num

end RobustMarkovAssort.Duality

open RobustMarkovAssort.Duality in
theorem solution : ¬ (∀ {n : ℕ} (M : MCUncertainty n) (h2 : Assumption2 M),
    ∃ m : Vec n → Vec n, (∀ v i, MCRowMin M v i (m v i)) ∧
      ∃ v : Vec n, fixedMap M.r m v = v ∧
        (∀ w, fixedMap M.r m w = w → w = v) ∧
        ∃ z : ℝ, MaxMin Set.univ (mcRevenue M h2) z ∧
          MinMax Set.univ (mcRevenue M h2) z ∧
          MinValue Set.univ (mcRevenue M h2 (tightSet M.r v)) z) := by
  intro hall
  obtain ⟨m, hm, _⟩ := hall ceUncertainty ceAssumption2
  have hmin : MCRowMin ceUncertainty (![0, 1]) 0 (m (![0, 1]) 0) := hm (![0, 1]) 0
  rcases hmin with ⟨⟨q, hq, hmq⟩, hlb⟩
  dsimp only at hmq
  simp [ceUncertainty] at hq
  have hval : m (![0, 1]) 0 = q 1 := by
    rw [← hmq, Fin.sum_univ_two]
    simp [hq.1]
  have hpos : 0 < m (![0, 1]) 0 := by linarith [hq.2.1]
  have hlt : m (![0, 1]) 0 < 1 / 2 := by linarith [hq.2.2]
  let q' : Vec 2 := ![0, m (![0, 1]) 0 / 2]
  have hq'_mem : q' ∈ ceUncertainty.rows 0 := by
    simp [ceUncertainty, q']
    constructor <;> linarith
  have hle : m (![0, 1]) 0 ≤ ∑ j : Fin 2, q' j * (![0, 1] : Vec 2) j :=
    hlb ⟨q', hq'_mem, rfl⟩
  rw [Fin.sum_univ_two] at hle
  simp [q'] at hle
  linarith
