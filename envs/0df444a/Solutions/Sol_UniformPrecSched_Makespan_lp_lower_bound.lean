-- Prove2me | solution 1 for UniformPrecSched.Makespan.lp_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-24T03:53:49.427995+00:00
-- url     : https://prove2.me/submissions/b1dbfe78-643b-4065-8f8f-b064f5cf9212

import Mathlib
import Definitions.Def_UniformPrecSched_Makespan_Model
import Definitions.Def_UniformPrecSched_Makespan_LP

set_option autoImplicit false

open UniformPrecSched.Makespan in
theorem LPLB.classSpeed_mem {n m : ℕ} (I : Instance n m) (κ : Fin (numSpeeds I)) :
    ∃ i, I.s i = classSpeed I κ := by
  have h : classSpeed I κ ∈ speedSet I := Finset.orderEmbOfFin_mem _ _ _
  simpa [speedSet] using h

open UniformPrecSched.Makespan in
theorem LPLB.classSpeed_pos {n m : ℕ} (I : Instance n m) (κ : Fin (numSpeeds I)) :
    0 < classSpeed I κ := by
  obtain ⟨i, hi⟩ := LPLB.classSpeed_mem I κ
  rw [← hi]; exact I.s_pos i

open UniformPrecSched.Makespan in
theorem LPLB.classCount_pos {n m : ℕ} (I : Instance n m) (κ : Fin (numSpeeds I)) :
    0 < classCount I κ := by
  obtain ⟨i, hi⟩ := LPLB.classSpeed_mem I κ
  unfold classCount
  exact Finset.card_pos.mpr ⟨i, by simp [hi]⟩

open UniformPrecSched.Makespan in
theorem LPLB.numSpeeds_pos {n m : ℕ} (I : Instance n m) : 0 < numSpeeds I := by
  unfold numSpeeds
  exact Finset.card_pos.mpr ⟨I.s ⟨0, I.m_pos⟩, by simp [speedSet]⟩

open UniformPrecSched.Makespan in
theorem LPLB.exists_class {n m : ℕ} (I : Instance n m) (i : Fin m) :
    ∃ κ, classSpeed I κ = I.s i := by
  have h : I.s i ∈ Set.range ((speedSet I).orderEmbOfFin
      (rfl : (speedSet I).card = numSpeeds I)) := by
    rw [Finset.range_orderEmbOfFin]; simp [speedSet]
  obtain ⟨κ', hκ'⟩ := h
  exact ⟨Fin.rev κ', (congrArg ((speedSet I).orderEmbOfFin rfl) (Fin.rev_rev κ')).trans hκ'⟩

open UniformPrecSched.Makespan in
theorem LPLB.le_makespan {n m : ℕ} {I : Instance n m} (σ : Schedule I) (j : Fin n) :
    σ.C j ≤ σ.makespan := by
  unfold Schedule.makespan
  split_ifs with h
  · exact Finset.le_sup' σ.C (Finset.mem_univ j)
  · exact absurd ⟨j, Finset.mem_univ j⟩ h

open UniformPrecSched.Makespan in
theorem LPLB.makespan_nonneg {n m : ℕ} {I : Instance n m} (σ : Schedule I) :
    0 ≤ σ.makespan := by
  unfold Schedule.makespan
  split_ifs with h
  · obtain ⟨j, _⟩ := h
    refine le_trans ?_ (Finset.le_sup' σ.C (Finset.mem_univ j))
    unfold Schedule.C
    have h1 := σ.S_nonneg j
    have h2 := div_pos (I.p_pos j) (I.s_pos (σ.μ j))
    linarith
  · exact le_rfl

open UniformPrecSched.Makespan in
/-- Jobs on one machine occupy disjoint intervals inside `[0, C_max]`, so their total
processing time is at most `C_max`. -/
theorem LPLB.machine_load {n m : ℕ} {I : Instance n m} (σ : Schedule I) (i : Fin m) :
    ∑ j ∈ Finset.univ.filter (fun j => σ.μ j = i), I.p j / I.s (σ.μ j) ≤ σ.makespan := by
  classical
  have key : ∀ T : Finset (Fin n), (∀ j ∈ T, σ.μ j = i) → ∀ M : ℝ, 0 ≤ M →
      (∀ j ∈ T, σ.C j ≤ M) → ∑ j ∈ T, I.p j / I.s (σ.μ j) ≤ M := by
    intro T
    refine Finset.induction_on_max_value (motive := fun T : Finset (Fin n) =>
      (∀ j ∈ T, σ.μ j = i) → ∀ M : ℝ, 0 ≤ M →
      (∀ j ∈ T, σ.C j ≤ M) → ∑ j ∈ T, I.p j / I.s (σ.μ j) ≤ M) σ.S T ?_ ?_
    · intro _ M hM _
      simpa using hM
    · intro a T haT hmax ih hT M hM hC
      have hLa : 0 < I.p a / I.s (σ.μ a) := div_pos (I.p_pos a) (I.s_pos _)
      have hmu : ∀ l ∈ T, σ.μ l = σ.μ a := fun l hl =>
        (hT l (Finset.mem_insert_of_mem hl)).trans (hT a (Finset.mem_insert_self a T)).symm
      have hend : ∀ l ∈ T, σ.C l ≤ σ.S a := by
        intro l hl
        have hne : l ≠ a := fun h => haT (h ▸ hl)
        rcases σ.noOverlap l a hne (hmu l hl) with h | h
        · exact h
        · have := hmax l hl
          linarith
      have hsum := ih (fun l hl => hT l (Finset.mem_insert_of_mem hl)) (σ.S a)
        (σ.S_nonneg a) hend
      rw [Finset.sum_insert haT]
      have hCa := hC a (Finset.mem_insert_self a T)
      unfold Schedule.C at hCa
      linarith
  refine key _ (fun j hj => (Finset.mem_filter.mp hj).2) _ (LPLB.makespan_nonneg σ) ?_
  intro j _
  exact LPLB.le_makespan σ j

open UniformPrecSched.Makespan in
/-- Every feasible schedule yields a feasible LP solution with `D = C_max`. -/
theorem LPLB.sched_feasible {n m : ℕ} {I : Instance n m} (σ : Schedule I) :
    ∃ x C, LPFeasible I x C σ.makespan := by
  classical
  choose k hk using fun j => LPLB.exists_class I (σ.μ j)
  have hp : ∀ j, ∑ κ, I.p j / classSpeed I κ * xhat I k κ j = I.p j / I.s (σ.μ j) := by
    intro j
    simp [xhat, hk]
  refine ⟨xhat I k, σ.C, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j; simp [xhat]
  · intro κ
    have hs := LPLB.classSpeed_pos I κ
    have hc : (0 : ℝ) < classCount I κ := Nat.cast_pos.mpr (LPLB.classCount_pos I κ)
    have hsum : ∑ j, I.p j * xhat I k κ j
        = ∑ j ∈ Finset.univ.filter (fun j => k j = κ), I.p j := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun j _ => ?_
      unfold xhat
      by_cases h : k j = κ
      · subst h; simp
      · simp [h, Ne.symm h]
    have hmaps : ∀ j ∈ Finset.univ.filter (fun j => k j = κ),
        σ.μ j ∈ Finset.univ.filter (fun i => I.s i = classSpeed I κ) := by
      intro j hj
      have hkj := (Finset.mem_filter.mp hj).2
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [← hk j, hkj]
    have hload : ∑ j ∈ Finset.univ.filter (fun j => k j = κ), I.p j / classSpeed I κ
        ≤ (classCount I κ : ℝ) * σ.makespan := by
      calc ∑ j ∈ Finset.univ.filter (fun j => k j = κ), I.p j / classSpeed I κ
          = ∑ j ∈ Finset.univ.filter (fun j => k j = κ), I.p j / I.s (σ.μ j) := by
            refine Finset.sum_congr rfl fun j hj => ?_
            rw [← hk j, (Finset.mem_filter.mp hj).2]
        _ = ∑ i ∈ Finset.univ.filter (fun i => I.s i = classSpeed I κ),
              ∑ j ∈ (Finset.univ.filter (fun j => k j = κ)).filter (fun j => σ.μ j = i),
                I.p j / I.s (σ.μ j) :=
            (Finset.sum_fiberwise_of_maps_to hmaps _).symm
        _ ≤ ∑ i ∈ Finset.univ.filter (fun i => I.s i = classSpeed I κ), σ.makespan := by
            refine Finset.sum_le_sum fun i _ => ?_
            refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (LPLB.machine_load σ i)
            · intro j hj
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
              exact hj.2
            · intro j _ _
              exact (div_pos (I.p_pos j) (I.s_pos _)).le
        _ = (classCount I κ : ℝ) * σ.makespan := by
            simp [classCount]
    rw [hsum]
    rw [← Finset.sum_div, div_le_iff₀ hs] at hload
    rw [one_div, inv_mul_le_iff₀ (mul_pos hc hs)]
    linarith
  · intro j
    rw [hp j]
    unfold Schedule.C
    linarith [σ.S_nonneg j]
  · intro j' j h
    rw [hp j]
    have := σ.precedence j' j h
    unfold Schedule.C
    linarith
  · intro j
    exact LPLB.le_makespan σ j
  · intro κ j
    unfold xhat
    split_ifs <;> norm_num

open UniformPrecSched.Makespan in
/-- The LP is feasible: put every job on the first speed class and let `C_j` be the total
processing time of `j` and its predecessors. -/
theorem LPLB.exists_feasible {n m : ℕ} (I : Instance n m) : ∃ x C D, LPFeasible I x C D := by
  classical
  obtain ⟨κ0⟩ : Nonempty (Fin (numSpeeds I)) := ⟨⟨0, LPLB.numSpeeds_pos I⟩⟩
  have hs0 := LPLB.classSpeed_pos I κ0
  have hq : ∀ l, 0 ≤ I.p l / classSpeed I κ0 := fun l => (div_pos (I.p_pos l) hs0).le
  have hpb : ∀ j, ∑ κ, I.p j / classSpeed I κ * (if κ = κ0 then (1 : ℝ) else 0)
      = I.p j / classSpeed I κ0 := by
    intro j; simp
  refine ⟨fun κ j => if κ = κ0 then 1 else 0,
    fun j => ∑ l ∈ Finset.univ.filter (fun l => I.prec l j ∨ l = j), I.p l / classSpeed I κ0,
    ∑ l, I.p l / classSpeed I κ0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j; simp
  · intro κ
    by_cases h : κ = κ0
    · subst h
      simp only [if_true, mul_one]
      have hc : (1 : ℝ) ≤ classCount I κ := Nat.one_le_cast.mpr (LPLB.classCount_pos I κ)
      have hP : 0 ≤ ∑ j, I.p j := Finset.sum_nonneg fun j _ => (I.p_pos j).le
      calc 1 / ((classCount I κ : ℝ) * classSpeed I κ) * ∑ j, I.p j
          ≤ 1 / classSpeed I κ * ∑ j, I.p j :=
            mul_le_mul_of_nonneg_right
              (one_div_le_one_div_of_le hs0 (le_mul_of_one_le_left hs0.le hc)) hP
        _ = ∑ l, I.p l / classSpeed I κ := by
            rw [← Finset.sum_div]; ring
    · simp only [h, if_false, mul_zero, Finset.sum_const_zero]
      exact Finset.sum_nonneg fun l _ => hq l
  · intro j
    rw [hpb]
    exact Finset.single_le_sum (fun l _ => hq l)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr rfl⟩)
  · intro j' j h
    rw [hpb]
    have hj : j ∈ Finset.univ.filter (fun l => I.prec l j ∨ l = j) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr rfl⟩
    have hsub : Finset.univ.filter (fun l => I.prec l j' ∨ l = j') ⊆
        (Finset.univ.filter (fun l => I.prec l j ∨ l = j)).erase j := by
      intro l hl
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and] at hl ⊢
      refine ⟨?_, ?_⟩
      · rintro rfl
        rcases hl with h' | h'
        · exact I.prec_irrefl l (I.prec_trans _ _ _ h' h)
        · subst h'
          exact I.prec_irrefl l h
      · rcases hl with h' | h'
        · exact Or.inl (I.prec_trans _ _ _ h' h)
        · subst h'
          exact Or.inl h
    have h1 := Finset.add_sum_erase _ (fun l => I.p l / classSpeed I κ0) hj
    have h2 := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun l _ _ => hq l)
    simp only at h1 h2 ⊢
    linarith
  · intro j
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun l _ _ => hq l)
  · intro κ j
    show (0 : ℝ) ≤ if κ = κ0 then 1 else 0
    split_ifs <;> norm_num

open UniformPrecSched.Makespan in
/-- The LP attains its minimum: the feasible points with `D ≤ D₀` form a compact set. -/
theorem LPLB.exists_optimal {n m : ℕ} (I : Instance n m) : ∃ x C D, LPOptimal I x C D := by
  classical
  obtain ⟨x0, C0, D0, h0⟩ := LPLB.exists_feasible I
  obtain ⟨κ0⟩ : Nonempty (Fin (numSpeeds I)) := ⟨⟨0, LPLB.numSpeeds_pos I⟩⟩
  obtain ⟨S, hS⟩ : ∃ S : Set ((Fin (numSpeeds I) → Fin n → ℝ) × (Fin n → ℝ) × ℝ),
      S = {v | LPFeasible I v.1 v.2.1 v.2.2 ∧ v.2.2 ≤ D0} := ⟨_, rfl⟩
  have hbox : S ⊆ (Set.univ.pi fun _ => Set.univ.pi fun _ => Set.Icc (0:ℝ) 1) ×ˢ
      ((Set.univ.pi fun _ => Set.Icc (0:ℝ) D0) ×ˢ Set.Icc (0:ℝ) D0) := by
    rintro ⟨x, C, D⟩ hv
    rw [hS] at hv
    obtain ⟨⟨h1, h2, h3, _, h5, h6⟩, hD⟩ := hv
    have hCnn : ∀ j, 0 ≤ C j := fun j => le_trans (Finset.sum_nonneg fun κ _ =>
      mul_nonneg (div_pos (I.p_pos j) (LPLB.classSpeed_pos I κ)).le (h6 κ j)) (h3 j)
    have hDnn : 0 ≤ D := le_trans (mul_nonneg
      (div_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _) (LPLB.classSpeed_pos I κ0).le))
      (Finset.sum_nonneg fun j _ => mul_nonneg (I.p_pos j).le (h6 κ0 j))) (h2 κ0)
    refine ⟨?_, ?_, ?_⟩
    · simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
      intro κ j
      refine ⟨h6 κ j, ?_⟩
      rw [← h1 j]
      exact Finset.single_le_sum (fun κ' _ => h6 κ' j) (Finset.mem_univ κ)
    · simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
      intro j
      exact ⟨hCnn j, (h5 j).trans hD⟩
    · exact ⟨hDnn, hD⟩
  have hclosed : IsClosed S := by
    rw [hS]
    simp only [LPFeasible, Set.ofPred_and, Set.ofPred_forall]
    repeat' first
      | apply IsClosed.inter
      | (apply isClosed_iInter; intro _)
      | exact isClosed_le (by fun_prop) (by fun_prop)
      | exact isClosed_eq (by fun_prop) (by fun_prop)
  have hcpt : IsCompact S :=
    IsCompact.of_isClosed_subset
      ((isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc).prod
        ((isCompact_univ_pi fun _ => isCompact_Icc).prod isCompact_Icc)) hclosed hbox
  have hne : S.Nonempty := ⟨(x0, C0, D0), by rw [hS]; exact ⟨h0, le_rfl⟩⟩
  obtain ⟨v, hvS, hmin⟩ := hcpt.exists_isMinOn hne
    (f := fun v : (Fin (numSpeeds I) → Fin n → ℝ) × (Fin n → ℝ) × ℝ => v.2.2)
    (continuous_snd.comp continuous_snd).continuousOn
  have hvS' := hvS
  rw [hS] at hvS'
  refine ⟨v.1, v.2.1, v.2.2, hvS'.1, ?_⟩
  intro x' C' D' hf
  by_cases hD : D' ≤ D0
  · have hmem : (x', C', D') ∈ S := by rw [hS]; exact ⟨hf, hD⟩
    exact isMinOn_iff.mp hmin _ hmem
  · exact le_trans hvS'.2 (le_of_not_ge hD)

open UniformPrecSched.Makespan in
theorem solution {n m : ℕ} (I : Instance n m) :
    (∃ x C D, LPOptimal I x C D) ∧
      ∀ x C D, LPOptimal I x C D → ∀ σ : Schedule I, D ≤ σ.makespan := by
  refine ⟨LPLB.exists_optimal I, ?_⟩
  intro x C D hopt σ
  obtain ⟨x', C', hf⟩ := LPLB.sched_feasible σ
  exact hopt.2 x' C' _ hf
