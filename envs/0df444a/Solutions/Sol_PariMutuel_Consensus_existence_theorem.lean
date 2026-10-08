-- Prove2me | solution 1 for PariMutuel.Consensus.existence_theorem
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T12:26:00.644738+00:00
-- url     : https://prove2.me/submissions/18aad71e-fe73-4be1-8bf1-4965fdb0f880

import Mathlib
import Definitions.Def_PariMutuel_Consensus_Market
import Definitions.Def_PariMutuel_Consensus_Phi



namespace PariMutuel.Consensus

open Finset

theorem pm_prob_pos {m n : ℕ} (M : Market m n) (π : Fin n → ℝ) (β : Fin m → Fin n → ℝ)
    (h : M.IsEquilibrium π β) (j : Fin n) : 0 < π j := by
  obtain ⟨hπ, hβ, hb, hc, hq⟩ := h
  rcases (hπ j).lt_or_eq with h1 | h1
  · exact h1
  exfalso
  obtain ⟨i, hi⟩ := M.P_col_pos j
  have : ∃ s, 0 < β i s := by
    by_contra hne
    push_neg at hne
    have : ∑ s, β i s ≤ 0 := Finset.sum_nonpos (fun s _ => hne s)
    have := M.b_pos i
    linarith [hb i]
  obtain ⟨s, hs⟩ := this
  have h2 := hq i s hs j
  rw [← h1] at h2
  have h3 : β i s ≤ π s := by
    rw [← hc s]
    exact Finset.single_le_sum (f := fun i => β i s) (fun i _ => hβ i s) (Finset.mem_univ i)
  have : 0 < M.P i j * π s := mul_pos hi (by linarith)
  linarith

theorem pm_sum_one {m n : ℕ} (M : Market m n) (π : Fin n → ℝ) (β : Fin m → Fin n → ℝ)
    (h : M.IsEquilibrium π β) : ∑ k, π k = 1 := by
  obtain ⟨hπ, hβ, hb, hc, hq⟩ := h
  simp_rw [← hc]
  rw [Finset.sum_comm]
  simp_rw [hb]
  exact M.b_sum

theorem pm_cs {n : ℕ} (π π' : Fin n → ℝ) (hπ : ∀ k, 0 < π k)
    (hs : ∑ k, π k = 1) (hs' : ∑ k, π' k = 1)
    (h : ∑ k, π' k * π' k / π k ≤ 1) : π' = π := by
  have key : ∑ k, (π' k - π k) ^ 2 / π k = ∑ k, π' k * π' k / π k - 1 := by
    have : ∀ k, (π' k - π k) ^ 2 / π k = π' k * π' k / π k - 2 * π' k + π k := by
      intro k
      have := (hπ k).ne'
      field_simp
      ring
    simp_rw [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hs, hs']
    ring
  have hle : ∑ k, (π' k - π k) ^ 2 / π k ≤ 0 := by linarith
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => div_nonneg (sq_nonneg _) (hπ k).le)).1
    (le_antisymm hle (Finset.sum_nonneg (fun k _ => div_nonneg (sq_nonneg _) (hπ k).le)))
  funext k
  have := hz k (Finset.mem_univ k)
  rw [div_eq_zero_iff] at this
  rcases this with h1 | h1
  · nlinarith [sq_nonneg (π' k - π k)]
  · exact absurd h1 (hπ k).ne'

theorem pm_sumsq {m n : ℕ} (M : Market m n) (π π' : Fin n → ℝ)
    (β β' : Fin m → Fin n → ℝ) (h : M.IsEquilibrium π β) (h' : M.IsEquilibrium π' β') :
    ∑ k, π' k * π' k / π k ≤ 1 := by
  have hp := pm_prob_pos M π β h
  have hp' := pm_prob_pos M π' β' h'
  have hs' := pm_sum_one M π' β' h'
  obtain ⟨-, hβ, hb, hc, hq⟩ := h
  obtain ⟨-, hβ', hb', hc', hq'⟩ := h'
  rcases (Finset.univ : Finset (Fin n)).eq_empty_or_nonempty with hn | hn
  · rw [hn, Finset.sum_empty]; norm_num
  set μ : Fin m → ℝ := fun i => Finset.univ.sup' hn (fun s => M.P i s / π s) with hμ
  set μ' : Fin m → ℝ := fun i => Finset.univ.sup' hn (fun s => M.P i s / π' s) with hμ'
  have ha : ∀ i s, M.P i s ≤ μ i * π s := by
    intro i s
    have : M.P i s / π s ≤ μ i := Finset.le_sup' (fun s => M.P i s / π s) (Finset.mem_univ s)
    rwa [div_le_iff₀ (hp s)] at this
  have ha' : ∀ i s, M.P i s ≤ μ' i * π' s := by
    intro i s
    have : M.P i s / π' s ≤ μ' i := Finset.le_sup' (fun s => M.P i s / π' s) (Finset.mem_univ s)
    rwa [div_le_iff₀ (hp' s)] at this
  have hbb : ∀ i k, 0 < β i k → μ i * π k ≤ M.P i k := by
    intro i k hk
    have : μ i ≤ M.P i k / π k := by
      apply Finset.sup'_le
      intro s _
      rw [div_le_div_iff₀ (hp s) (hp k)]
      exact hq i k hk s
    rwa [le_div_iff₀ (hp k)] at this
  have hbb' : ∀ i k, 0 < β' i k → μ' i * π' k ≤ M.P i k := by
    intro i k hk
    have : μ' i ≤ M.P i k / π' k := by
      apply Finset.sup'_le
      intro s _
      rw [div_le_div_iff₀ (hp' s) (hp' k)]
      exact hq' i k hk s
    rwa [le_div_iff₀ (hp' k)] at this
  have hμ'pos : ∀ i, 0 < μ' i := by
    intro i
    have h1 : ∑ s, M.P i s ≤ ∑ s, μ' i * π' s := Finset.sum_le_sum (fun s _ => ha' i s)
    rw [M.P_row_sum, ← Finset.mul_sum, hs'] at h1
    linarith
  -- step 1
  have e1 : ∑ k, π' k * π' k / π k = ∑ i, ∑ k, β' i k * (π' k / π k) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [← Finset.sum_mul, hc']
    ring
  have s1 : ∀ i, ∑ k, β' i k * (π' k / π k) ≤ M.b i * (μ i / μ' i) := by
    intro i
    rw [← hb' i, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro k _
    rcases (hβ' i k).lt_or_eq with hk | hk
    · apply mul_le_mul_of_nonneg_left _ (hβ' i k)
      rw [div_le_div_iff₀ (hp k) (hμ'pos i)]
      have := hbb' i k hk
      have := ha i k
      nlinarith
    · rw [← hk]; simp
  have s2 : ∀ i, M.b i * (μ i / μ' i) ≤ ∑ k, β i k * (π' k / π k) := by
    intro i
    rw [← hb i, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro k _
    rcases (hβ i k).lt_or_eq with hk | hk
    · apply mul_le_mul_of_nonneg_left _ (hβ i k)
      rw [div_le_div_iff₀ (hμ'pos i) (hp k)]
      have := hbb i k hk
      have := ha' i k
      nlinarith
    · rw [← hk]; simp
  have e2 : ∑ i, ∑ k, β i k * (π' k / π k) = 1 := by
    rw [Finset.sum_comm, ← hs']
    apply Finset.sum_congr rfl
    intro k _
    rw [← Finset.sum_mul, hc k]
    field_simp [(hp k).ne']
  calc ∑ k, π' k * π' k / π k = ∑ i, ∑ k, β' i k * (π' k / π k) := e1
    _ ≤ ∑ i, M.b i * (μ i / μ' i) := Finset.sum_le_sum (fun i _ => s1 i)
    _ ≤ ∑ i, ∑ k, β i k * (π' k / π k) := Finset.sum_le_sum (fun i _ => s2 i)
    _ = 1 := e2

theorem pm_unique {m n : ℕ} (M : Market m n) (π π' : Fin n → ℝ)
    (β β' : Fin m → Fin n → ℝ) (h : M.IsEquilibrium π β) (h' : M.IsEquilibrium π' β') :
    π = π' :=
  (pm_cs π π' (pm_prob_pos M π β h) (pm_sum_one M π β h) (pm_sum_one M π' β' h')
    (pm_sumsq M π π' β β' h h')).symm


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


theorem pm_log_diff {a s : ℝ} (ha : 0 < a) (hs : 0 < s) : (a - s) / a ≤ Real.log a - Real.log s := by
  have h := Real.one_sub_inv_le_log_of_pos (div_pos ha hs)
  rw [Real.log_div ha.ne' hs.ne', inv_div] at h
  have : (a - s) / a = 1 - s / a := by field_simp
  linarith

theorem pm_kkt_eps {m n : ℕ} (M : Market m n) (ξ : Fin m → Fin n → ℝ)
    (hξ : M.IsPhiMaximizer ξ) (i k : Fin m) (hki : k ≠ i) (j : Fin n) (hij : 0 < ξ i j)
    (ε : ℝ) (he : 0 < ε) (he' : ε < ξ i j) :
    M.b k * M.P k j / (∑ s, M.P k s * ξ k s + M.P k j * ε)
      ≤ M.b i * M.P i j / (∑ s, M.P i s * ξ i s - M.P i j * ε) := by
  obtain ⟨hD, hpos, hmax⟩ := hξ
  set S : Fin m → ℝ := fun i' => ∑ s, M.P i' s * ξ i' s with hS
  set d : Fin m → ℝ := fun i' => (if i' = k then ε else 0) - (if i' = i then ε else 0) with hd
  set η : Fin m → Fin n → ℝ := fun i' j' => ξ i' j' + (if j' = j then d i' else 0) with hη
  have hdk : d k = ε := by simp [hd, hki]
  have hdi : d i = -ε := by simp [hd, hki.symm]
  have hdo : ∀ i', i' ≠ k ∧ i' ≠ i → d i' = 0 := by
    intro i' h; simp [hd, h.1, h.2]
  have hsumd : ∑ i', d i' = 0 := by
    simp [hd, Finset.sum_sub_distrib]
  have hinner : ∀ i', ∑ s, M.P i' s * η i' s = S i' + M.P i' j * d i' := by
    intro i'
    simp only [hη, hS, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  have hSi : M.P i j * ξ i j ≤ S i :=
    Finset.single_le_sum (f := fun s => M.P i s * ξ i s)
      (fun s _ => mul_nonneg (M.P_nonneg i s) (hD.1 i s)) (Finset.mem_univ j)
  have hSi' : 0 < S i - M.P i j * ε := by
    rcases (M.P_nonneg i j).lt_or_eq with hp | hp
    · nlinarith
    · rw [← hp]; simp; exact hpos i
  have hposη : ∀ i', 0 < S i' + M.P i' j * d i' := by
    intro i'
    by_cases h1 : i' = i
    · subst h1; rw [hdi]; linarith
    · have hd0 : 0 ≤ d i' := by simp [hd, h1]; split_ifs <;> linarith
      have hp1 := hpos i'
      have hp2 := mul_nonneg (M.P_nonneg i' j) hd0
      simp only [hS] at *
      linarith
  have hηD : η ∈ D m n := by
    refine ⟨fun i' j' => ?_, fun j' => ?_⟩
    · simp only [hη]
      have := hD.1 i' j'
      split_ifs with h
      · subst h
        by_cases h1 : i' = i
        · subst h1; rw [hdi]; linarith
        · have : 0 ≤ d i' := by simp [hd, h1]; split_ifs <;> linarith
          linarith
      · linarith
    · simp only [hη, Finset.sum_add_distrib, hD.2 j']
      split_ifs <;> simp [hsumd]
  have hle := hmax η hηD (fun i' => by rw [hinner]; exact hposη i')
  unfold Market.phi at hle
  simp only [hinner] at hle
  have h2 : ∑ i', M.b i' * ((M.P i' j * d i') / (S i' + M.P i' j * d i')) ≤ 0 := by
    have : ∑ i', M.b i' * ((M.P i' j * d i') / (S i' + M.P i' j * d i'))
        ≤ ∑ i', (M.b i' * Real.log (S i' + M.P i' j * d i') - M.b i' * Real.log (S i')) := by
      apply Finset.sum_le_sum
      intro i' _
      rw [← mul_sub]
      apply mul_le_mul_of_nonneg_left _ (M.b_pos i').le
      have := pm_log_diff (s := S i') (hposη i') (hpos i')
      have e : M.P i' j * d i' = S i' + M.P i' j * d i' - S i' := by ring
      calc M.P i' j * d i' / (S i' + M.P i' j * d i')
          = (S i' + M.P i' j * d i' - S i') / (S i' + M.P i' j * d i') := by rw [← e]
        _ ≤ _ := this
    rw [Finset.sum_sub_distrib] at this
    simp only [hS] at this
    linarith
  rw [Fintype.sum_eq_add k i hki (fun x hx => by rw [hdo x hx]; simp)] at h2
  rw [hdk, hdi] at h2
  have hk' : 0 < S k + M.P k j * ε := by have := hposη k; rwa [hdk] at this
  have hi' : 0 < S i + M.P i j * -ε := by have := hposη i; rwa [hdi] at this
  have e1 : M.b k * (M.P k j * ε / (S k + M.P k j * ε)) = ε * (M.b k * M.P k j / (S k + M.P k j * ε)) := by
    field_simp
  have e2 : M.b i * (M.P i j * -ε / (S i + M.P i j * -ε)) = -(ε * (M.b i * M.P i j / (S i - M.P i j * ε))) := by
    have : S i + M.P i j * -ε = S i - M.P i j * ε := by ring
    rw [this]; field_simp
  rw [e1, e2] at h2
  have : ε * (M.b k * M.P k j / (S k + M.P k j * ε)) ≤ ε * (M.b i * M.P i j / (S i - M.P i j * ε)) := by
    linarith
  exact le_of_mul_le_mul_left this he

theorem pm_kkt {m n : ℕ} (M : Market m n) (ξ : Fin m → Fin n → ℝ)
    (hξ : M.IsPhiMaximizer ξ) (i k : Fin m) (j : Fin n) (hij : 0 < ξ i j) :
    M.b k * M.P k j / (∑ s, M.P k s * ξ k s) ≤ M.b i * M.P i j / (∑ s, M.P i s * ξ i s) := by
  by_cases hki : k = i
  · rw [hki]
  have hpos := hξ.2.1
  set F : ℝ → ℝ := fun ε => M.b k * M.P k j / (∑ s, M.P k s * ξ k s + M.P k j * ε) with hF
  set G : ℝ → ℝ := fun ε => M.b i * M.P i j / (∑ s, M.P i s * ξ i s - M.P i j * ε) with hG
  have hFt : Filter.Tendsto F (nhdsWithin 0 (Set.Ioi 0)) (nhds (F 0)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    apply ContinuousAt.tendsto
    apply ContinuousAt.div continuousAt_const (by fun_prop)
    simp; exact (hpos k).ne'
  have hGt : Filter.Tendsto G (nhdsWithin 0 (Set.Ioi 0)) (nhds (G 0)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    apply ContinuousAt.tendsto
    apply ContinuousAt.div continuousAt_const (by fun_prop)
    simp; exact (hpos i).ne'
  have hev : F ≤ᶠ[nhdsWithin 0 (Set.Ioi 0)] G := by
    filter_upwards [Ioo_mem_nhdsGT hij] with ε hε
    exact pm_kkt_eps M ξ hξ i k hki j hij ε hε.1 hε.2
  have := le_of_tendsto_of_tendsto hFt hGt hev
  simpa [hF, hG] using this

theorem pm_track_eq {m n : ℕ} (M : Market m n) (ξ : Fin m → Fin n → ℝ)
    (hξ : M.IsPhiMaximizer ξ) (i : Fin m) (j : Fin n) (hij : 0 < ξ i j) :
    M.trackProb ξ j = M.b i * M.P i j / ∑ s, M.P i s * ξ i s := by
  unfold Market.trackProb
  apply le_antisymm
  · apply Finset.sup'_le
    intro k _
    exact pm_kkt M ξ hξ i k j hij
  · exact Finset.le_sup' (fun i => M.b i * M.P i j / ∑ s, M.P i s * ξ i s) (Finset.mem_univ i)

theorem pm_track_ge {m n : ℕ} (M : Market m n) (ξ : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) :
    M.b i * M.P i j / ∑ s, M.P i s * ξ i s ≤ M.trackProb ξ j :=
  Finset.le_sup' (fun i => M.b i * M.P i j / ∑ s, M.P i s * ξ i s) (Finset.mem_univ i)

theorem pm_track_pos {m n : ℕ} (M : Market m n) (ξ : Fin m → Fin n → ℝ)
    (hξ : M.IsPhiMaximizer ξ) (j : Fin n) : 0 < M.trackProb ξ j := by
  obtain ⟨i, hi⟩ := M.P_col_pos j
  have := pm_track_ge M ξ i j
  have h2 : 0 < M.b i * M.P i j / ∑ s, M.P i s * ξ i s :=
    div_pos (mul_pos (M.b_pos i) hi) (hξ.2.1 i)
  linarith

theorem pm_existence {m n : ℕ} (M : Market m n) (ξ : Fin m → Fin n → ℝ)
    (hξ : M.IsPhiMaximizer ξ) : M.IsEquilibrium (M.trackProb ξ) (M.bets ξ) := by
  have hD := hξ.1
  have hpos := hξ.2.1
  have hπ := pm_track_pos M ξ hξ
  refine ⟨fun j => (hπ j).le, fun i j => mul_nonneg (hD.1 i j) (hπ j).le, fun i => ?_,
    fun j => ?_, fun i j hβ s => ?_⟩
  · have : ∀ j, M.bets ξ i j = M.b i / (∑ s, M.P i s * ξ i s) * (M.P i j * ξ i j) := by
      intro j
      unfold Market.bets
      rcases (hD.1 i j).lt_or_eq with h | h
      · rw [pm_track_eq M ξ hξ i j h]; ring
      · rw [← h]; ring
    simp_rw [this, ← Finset.mul_sum]
    field_simp [(hpos i).ne']
  · unfold Market.bets
    rw [← Finset.sum_mul, hD.2 j, one_mul]
  · have hξij : 0 < ξ i j := by
      unfold Market.bets at hβ
      by_contra hc
      have : ξ i j = 0 := le_antisymm (not_lt.1 hc) (hD.1 i j)
      rw [this, zero_mul] at hβ
      exact lt_irrefl _ hβ
    rw [pm_track_eq M ξ hξ i j hξij]
    have h1 := pm_track_ge M ξ i s
    have h2 : M.P i s * (M.b i * M.P i j / ∑ s, M.P i s * ξ i s)
        = M.P i j * (M.b i * M.P i s / ∑ s, M.P i s * ξ i s) := by ring
    rw [h2]
    exact mul_le_mul_of_nonneg_left h1 (M.P_nonneg i j)

theorem pm_goal {m n : ℕ} (M : Market m n) :
    ∃! π : Fin n → ℝ, ∃ β : Fin m → Fin n → ℝ, M.IsEquilibrium π β := by
  obtain ⟨ξ, hξ⟩ := pm_exists_max M
  refine ⟨M.trackProb ξ, ⟨M.bets ξ, pm_existence M ξ hξ⟩, ?_⟩
  rintro π' ⟨β', h'⟩
  exact pm_unique M π' (M.trackProb ξ) β' (M.bets ξ) h' (pm_existence M ξ hξ)

end PariMutuel.Consensus

open PariMutuel.Consensus


theorem solution {m n : ℕ} (M : Market m n) (ξ : Fin m → Fin n → ℝ)
    (hξ : M.IsPhiMaximizer ξ) : M.IsEquilibrium (M.trackProb ξ) (M.bets ξ) := by
  exact pm_existence M ξ hξ
