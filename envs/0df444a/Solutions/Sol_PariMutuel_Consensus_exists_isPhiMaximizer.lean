-- Prove2me | solution 1 for PariMutuel.Consensus.exists_isPhiMaximizer
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T12:21:47.02873+00:00
-- url     : https://prove2.me/submissions/ef568946-ab8f-4915-9f1d-725d4ee34c9c

import Mathlib
import Definitions.Def_PariMutuel_Consensus_Market
import Definitions.Def_PariMutuel_Consensus_Phi



namespace PariMutuel.Consensus

theorem pm_inner_update {m n : ℕ} (M : Market m n) (ξ : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n)
    (t : ℝ) : ∑ s, M.P i s * Function.update (ξ i) j t s
      = ∑ s, M.P i s * ξ i s + M.P i j * (t - ξ i j) := by
  have : ∀ s, M.P i s * Function.update (ξ i) j t s
      = M.P i s * ξ i s + (if s = j then M.P i j * (t - ξ i j) else 0) := by
    intro s
    rw [Function.update_apply]
    split_ifs with h
    · subst h; ring
    · ring
  simp_rw [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem pm_hasDeriv {m n : ℕ} (M : Market m n) (ξ : Fin m → Fin n → ℝ)
    (hξ : ∀ i, 0 < ∑ j, M.P i j * ξ i j) (i : Fin m) (j : Fin n) :
    HasDerivAt (fun t : ℝ => M.phi (Function.update ξ i (Function.update (ξ i) j t)))
      (M.b i * M.P i j / ∑ s, M.P i s * ξ i s) (ξ i j) := by
  unfold Market.phi
  have key : ∀ i' ∈ (Finset.univ : Finset (Fin m)),
      HasDerivAt (fun t : ℝ => M.b i' * Real.log (∑ s, M.P i' s *
        Function.update ξ i (Function.update (ξ i) j t) i' s))
        (if i' = i then M.b i * M.P i j / ∑ s, M.P i s * ξ i s else 0) (ξ i j) := by
    intro i' _
    by_cases hi : i' = i
    · subst hi
      simp only [Function.update_self, if_true, pm_inner_update]
      have h0 := hξ i'
      have := ((((hasDerivAt_id (ξ i' j)).sub_const (ξ i' j)).const_mul (M.P i' j)).const_add
        (∑ s, M.P i' s * ξ i' s)).log (by simp; exact h0.ne')
      have := this.const_mul (M.b i')
      refine this.congr_deriv ?_
      simp
      ring
    · simp only [Function.update_of_ne hi, hi, if_false]
      exact hasDerivAt_const _ _
  have := HasDerivAt.fun_sum key
  refine this.congr_deriv ?_
  rw [Finset.sum_ite_eq']
  simp


theorem pm_inner_le_one {m n : ℕ} (M : Market m n) (η : Fin m → Fin n → ℝ) (hη : η ∈ D m n)
    (i : Fin m) : ∑ j, M.P i j * η i j ≤ 1 := by
  obtain ⟨h0, h1⟩ := hη
  calc ∑ j, M.P i j * η i j ≤ ∑ j, M.P i j := by
        apply Finset.sum_le_sum
        intro j _
        have : η i j ≤ 1 := by
          rw [← h1 j]
          exact Finset.single_le_sum (f := fun i => η i j) (fun i _ => h0 i j) (Finset.mem_univ i)
        nlinarith [M.P_nonneg i j]
    _ = 1 := M.P_row_sum i

theorem pm_inner_nonneg {m n : ℕ} (M : Market m n) (η : Fin m → Fin n → ℝ) (hη : η ∈ D m n)
    (i : Fin m) : 0 ≤ ∑ j, M.P i j * η i j :=
  Finset.sum_nonneg (fun j _ => mul_nonneg (M.P_nonneg i j) (hη.1 i j))

theorem pm_phi_le_term {m n : ℕ} (M : Market m n) (η : Fin m → Fin n → ℝ) (hη : η ∈ D m n)
    (i : Fin m) : M.phi η ≤ M.b i * Real.log (∑ j, M.P i j * η i j) := by
  unfold Market.phi
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have : ∑ k ∈ Finset.univ.erase i, M.b k * Real.log (∑ j, M.P k j * η k j) ≤ 0 := by
    apply Finset.sum_nonpos
    intro k _
    exact mul_nonpos_of_nonneg_of_nonpos (M.b_pos k).le
      (Real.log_nonpos (pm_inner_nonneg M η hη k) (pm_inner_le_one M η hη k))
  linarith

theorem pm_exists_max {m n : ℕ} (M : Market m n) : ∃ ξ, M.IsPhiMaximizer ξ := by
  have hm : 0 < m := by
    obtain ⟨i, _⟩ := M.univ_nonempty
    exact Fin.pos i
  set ξ0 : Fin m → Fin n → ℝ := fun _ _ => 1 / (m : ℝ) with hξ0
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hξ0D : ξ0 ∈ D m n := by
    refine ⟨fun i j => by positivity, fun j => ?_⟩
    simp [hξ0]
    field_simp
  have hξ0s : ∀ i, ∑ j, M.P i j * ξ0 i j = 1 / m := by
    intro i
    simp only [hξ0]
    rw [← Finset.sum_mul, M.P_row_sum]; ring
  set c := M.phi ξ0 with hc
  set K : Set (Fin m → Fin n → ℝ) :=
    {η | (∀ i j, 0 ≤ η i j) ∧ (∀ j, ∑ i, η i j = 1) ∧
      ∀ i, Real.exp (c / M.b i) ≤ ∑ j, M.P i j * η i j} with hK
  have hKD : ∀ η ∈ K, η ∈ D m n := fun η h => ⟨h.1, h.2.1⟩
  have hKpos : ∀ η ∈ K, ∀ i, 0 < ∑ j, M.P i j * η i j :=
    fun η h i => lt_of_lt_of_le (Real.exp_pos _) (h.2.2 i)
  have hKclosed : IsClosed K := by
    simp only [hK, Set.setOf_and, Set.setOf_forall]
    refine IsClosed.inter ?_ (IsClosed.inter ?_ ?_)
    · exact isClosed_iInter fun i => isClosed_iInter fun j =>
        isClosed_le continuous_const (by fun_prop)
    · exact isClosed_iInter fun j => isClosed_eq (by fun_prop) continuous_const
    · exact isClosed_iInter fun i => isClosed_le continuous_const (by fun_prop)
  have hKsub : K ⊆ Set.Icc 0 1 := by
    intro η h
    refine ⟨fun i j => h.1 i j, fun i j => ?_⟩
    show η i j ≤ 1
    rw [← h.2.1 j]
    exact Finset.single_le_sum (f := fun i => η i j) (fun i _ => h.1 i j) (Finset.mem_univ i)
  have hKc : IsCompact K := IsCompact.of_isClosed_subset isCompact_Icc hKclosed hKsub
  have hξ0K : ξ0 ∈ K := by
    refine ⟨hξ0D.1, hξ0D.2, fun i => ?_⟩
    have h1 := pm_phi_le_term M ξ0 hξ0D i
    rw [← hc] at h1
    have h2 : c / M.b i ≤ Real.log (∑ j, M.P i j * ξ0 i j) := by
      rw [div_le_iff₀ (M.b_pos i)]; linarith
    calc Real.exp (c / M.b i) ≤ Real.exp (Real.log (∑ j, M.P i j * ξ0 i j)) := Real.exp_le_exp.2 h2
      _ = _ := Real.exp_log (by rw [hξ0s i]; positivity)
  have hcont : ContinuousOn M.phi K := by
    unfold Market.phi
    apply continuousOn_finset_sum
    intro i _
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.log (by fun_prop)
    intro η h
    exact (hKpos η h i).ne'
  obtain ⟨ξ, hξK, hmax⟩ := hKc.exists_isMaxOn ⟨ξ0, hξ0K⟩ hcont
  refine ⟨ξ, hKD ξ hξK, hKpos ξ hξK, fun η hη hηpos => ?_⟩
  by_cases hηK : η ∈ K
  · exact hmax hηK
  · have : ∃ i, ∑ j, M.P i j * η i j < Real.exp (c / M.b i) := by
      by_contra hne
      push_neg at hne
      exact hηK ⟨hη.1, hη.2, hne⟩
    obtain ⟨i, hi⟩ := this
    have h1 := pm_phi_le_term M η hη i
    have h2 : Real.log (∑ j, M.P i j * η i j) < c / M.b i :=
      (Real.log_lt_iff_lt_exp (hηpos i)).2 hi
    have h3 : M.b i * Real.log (∑ j, M.P i j * η i j) < c := by
      have := (lt_div_iff₀ (M.b_pos i)).1 h2
      linarith
    have h4 : M.phi ξ0 ≤ M.phi ξ := hmax hξ0K
    linarith

end PariMutuel.Consensus

open PariMutuel.Consensus


theorem solution {m n : ℕ} (M : Market m n) : ∃ ξ, M.IsPhiMaximizer ξ := by
  exact pm_exists_max M
