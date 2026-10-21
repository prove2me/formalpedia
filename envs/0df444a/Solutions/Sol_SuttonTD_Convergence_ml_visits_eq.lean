-- Prove2me | solution 1 for SuttonTD.Convergence.ml_visits_eq
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T21:20:33.044548+00:00
-- url     : https://prove2.me/submissions/8eeea027-9939-4212-99f6-b93beea4c303

import Mathlib
import Definitions.Def_SuttonTD_Convergence_TrainingSet

set_option autoImplicit false
open Filter Topology Matrix SuttonTD.Convergence

section comb
variable {N : Type*} [DecidableEq N]

lemma std_cnt_cons (C : Finset N) (a : N) (t : List N) :
    ∑ i ∈ C, (a :: t).count i = ∑ i ∈ C, t.count i + if a ∈ C then 1 else 0 := by
  simp [List.count_cons, Finset.sum_add_distrib]

lemma std_pair_cons (C C' : Finset N) (a b : N) (z : List (N × N)) :
    ∑ i ∈ C, ∑ j ∈ C', ((a, b) :: z).count (i, j) =
      ∑ i ∈ C, ∑ j ∈ C', z.count (i, j) + if a ∈ C ∧ b ∈ C' then 1 else 0 := by
  simp only [List.count_cons, Finset.sum_add_distrib, beq_iff_eq, Prod.mk.injEq]
  congr 1
  by_cases ha : a ∈ C
  · by_cases hb : b ∈ C'
    · simp [ha, hb, ite_and, Finset.sum_ite_eq]
    · simp [ha, hb, ite_and, Finset.sum_ite_eq]
  · simp [ha, ite_and, Finset.sum_ite_eq]

lemma std_list_le (C C' : Finset N) : ∀ l : List N,
    ∑ i ∈ C, ∑ j ∈ C', (l.zip l.tail).count (i, j) ≤ ∑ i ∈ C, l.count i := by
  intro l
  induction l with
  | nil => simp
  | cons a t ih =>
    cases t with
    | nil => simp
    | cons b t' =>
      have e : ((a :: b :: t').zip (a :: b :: t').tail)
          = (a, b) :: ((b :: t').zip t') := rfl
      simp only [List.tail_cons] at ih
      rw [e, std_pair_cons, std_cnt_cons]
      by_cases ha : a ∈ C <;> by_cases hb : b ∈ C' <;> simp [ha, hb] <;> omega

lemma std_list_lt (C : Finset N) : ∀ l : List N,
    (∑ i ∈ C, ∑ j ∈ C, (l.zip l.tail).count (i, j)) ≤ ∑ i ∈ C, l.count i ∧
    (0 < ∑ i ∈ C, l.count i →
      (∑ i ∈ C, ∑ j ∈ C, (l.zip l.tail).count (i, j)) < ∑ i ∈ C, l.count i) := by
  intro l
  induction l with
  | nil => simp
  | cons a t ih =>
    cases t with
    | nil =>
      by_cases ha : a ∈ C <;> simp [std_cnt_cons, ha]
    | cons b t' =>
      have e : ((a :: b :: t').zip (a :: b :: t').tail)
          = (a, b) :: ((b :: t').zip t') := rfl
      simp only [List.tail_cons] at ih
      rw [e, std_pair_cons, std_cnt_cons]
      have hA' : b ∈ C → 0 < ∑ i ∈ C, (b :: t').count i := by
        intro hb
        rw [std_cnt_cons]; simp [hb]
      obtain ⟨ih1, ih2⟩ := ih
      by_cases ha : a ∈ C <;> by_cases hb : b ∈ C
      · have := ih2 (hA' hb)
        simp [ha, hb]; omega
      · simp [ha, hb]; constructor <;> intros <;> omega
      · simp [ha, hb]; exact ⟨ih1, ih2⟩
      · simp [ha, hb]; exact ⟨ih1, ih2⟩
end comb

section analytic
variable {N : Type*} [Fintype N] [DecidableEq N]

lemma std_pow_nonneg (Q : Matrix N N ℝ) (hnn : ∀ i j, 0 ≤ Q i j) (n : ℕ) :
    ∀ i j, 0 ≤ (Q ^ n) i j := by
  induction n with
  | zero => intro i j; rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ n ih =>
    intro i j; rw [pow_succ', Matrix.mul_apply]
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (hnn _ _) (ih _ _))

lemma std_absorbing_of (Q : Matrix N N ℝ) (hnn : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j ≤ 1)
    (hC : ∀ C : Finset N, C.Nonempty → ∃ i ∈ C, ∑ j ∈ C, Q i j < 1) :
    Tendsto (fun n : ℕ => Q ^ n) atTop (𝓝 0) := by
  have hP := std_pow_nonneg Q hnn
  set u : ℕ → N → ℝ := fun n => (Q ^ n) *ᵥ (fun _ => (1 : ℝ)) with hu
  have hu_apply : ∀ n i, u n i = ∑ j, (Q ^ n) i j := by
    intro n i; simp [hu, Matrix.mulVec, dotProduct]
  have hu0 : ∀ n i, 0 ≤ u n i := fun n i => by
    rw [hu_apply]; exact Finset.sum_nonneg (fun j _ => hP n i j)
  have hustep : ∀ n, u (n+1) = Q *ᵥ u n := by
    intro n; simp only [hu]; rw [pow_succ', ← Matrix.mulVec_mulVec]
  have hanti : ∀ n i, u (n+1) i ≤ u n i := by
    intro n
    induction n with
    | zero =>
      intro i
      rw [hustep 0]
      have : u 0 = fun _ => (1 : ℝ) := by simp [hu]
      rw [this]
      simpa [Matrix.mulVec, dotProduct] using hrow i
    | succ n ih =>
      intro i
      rw [hustep (n+1)]
      conv_rhs => rw [hustep n]
      simp only [Matrix.mulVec, dotProduct]
      exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (ih j) (hnn i j)
  have hanti' : ∀ i, Antitone (fun n => u n i) := fun i => antitone_nat_of_succ_le (fun n => hanti n i)
  set L : N → ℝ := fun i => ⨅ n, u n i with hLdef
  have hconv : Tendsto u atTop (𝓝 L) :=
    tendsto_pi_nhds.2 fun i => tendsto_atTop_ciInf (hanti' i)
      ⟨0, by rintro _ ⟨n, rfl⟩; exact hu0 n i⟩
  have hL0 : ∀ i, 0 ≤ L i := fun i =>
    ge_of_tendsto (tendsto_pi_nhds.1 hconv i) (Eventually.of_forall fun n => hu0 n i)
  have hfix : Q *ᵥ L = L := by
    have h1 : Tendsto (fun n => Q *ᵥ u n) atTop (𝓝 (Q *ᵥ L)) :=
      ((Continuous.matrix_mulVec continuous_const continuous_id).tendsto L).comp hconv
    have h2 : Tendsto (fun n => Q *ᵥ u n) atTop (𝓝 L) := by
      have := hconv.comp (tendsto_add_atTop_nat 1)
      refine this.congr (fun n => ?_)
      simp [Function.comp, hustep]
    exact tendsto_nhds_unique h1 h2
  have hLzero : L = 0 := by
    by_contra hne
    obtain ⟨j0, hj0⟩ : ∃ j, L j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hne (funext h)
    obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image Finset.univ L ⟨j0, Finset.mem_univ _⟩
    have hm : 0 < L i0 := by
      by_contra hle
      push_neg at hle
      apply hne
      funext j
      exact le_antisymm (le_trans (hi0 j (Finset.mem_univ _)) hle) (hL0 j)
    set m := L i0 with hmdef
    set C := Finset.univ.filter (fun i => L i = m) with hCdef
    have hCne : C.Nonempty := ⟨i0, by simp [hCdef, hmdef]⟩
    obtain ⟨i, hiC, hlt⟩ := hC C hCne
    have hLi : L i = m := (Finset.mem_filter.1 hiC).2
    have hid : ∑ j, Q i j * L j = m := by
      have := congrFun hfix i
      simp only [Matrix.mulVec, dotProduct] at this
      rw [this, hLi]
    have hsum : ∑ j, Q i j * (m - L j) = m * ∑ j, Q i j - m := by
      simp only [mul_sub, Finset.sum_sub_distrib, hid, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have hnn2 : ∀ j ∈ (Finset.univ : Finset N), 0 ≤ Q i j * (m - L j) := fun j _ =>
      mul_nonneg (hnn i j) (sub_nonneg.2 (hi0 j (Finset.mem_univ _)))
    have hs2 : 0 ≤ ∑ j, Q i j * (m - L j) := Finset.sum_nonneg hnn2
    have hr := hrow i
    have h1 : ∑ j, Q i j = 1 := by
      by_contra hne1
      have hlt1 : ∑ j, Q i j < 1 := lt_of_le_of_ne hr hne1
      nlinarith
    have hs0 : ∑ j, Q i j * (m - L j) = 0 := by rw [hsum, h1]; ring
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn2).1 hs0
    have hC1 : ∑ j ∈ C, Q i j = ∑ j, Q i j := by
      apply Finset.sum_filter_of_ne
      intro j _ hj
      have := hz j (Finset.mem_univ _)
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hj
      · linarith
    rw [hC1, h1] at hlt
    exact lt_irrefl _ hlt
  have hu0' : Tendsto u atTop (𝓝 0) := hLzero ▸ hconv
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have hi := tendsto_pi_nhds.1 hu0' i
  refine squeeze_zero (fun n => hP n i j) (fun n => ?_) hi
  rw [hu_apply]
  exact Finset.single_le_sum (f := fun j => (Q ^ n) i j) (fun j _ => hP n i j) (Finset.mem_univ j)
end analytic

theorem std_Qhat_absorbing {N : Type*} [Fintype N] [DecidableEq N] {S : ℕ}
    (D : TrainingSet N S) (happ : ∀ i, 0 < D.visits i) :
    Tendsto (fun n : ℕ => D.Qhat ^ n) atTop (𝓝 0) := by
  have hd : ∀ i, (0:ℝ) < D.visits i := fun i => by exact_mod_cast happ i
  apply std_absorbing_of
  · intro i j
    simp only [TrainingSet.Qhat, Matrix.of_apply]
    positivity
  · intro i
    simp only [TrainingSet.Qhat, Matrix.of_apply]
    rw [← Finset.sum_div, div_le_one (hd i)]
    have h1 : ∑ j, D.transitions i j ≤ D.visits i := by
      simp only [TrainingSet.transitions, TrainingSet.visits]
      rw [Finset.sum_comm]
      apply Finset.sum_le_sum
      intro s _
      have := std_list_le {i} Finset.univ (D.path s)
      simpa using this
    exact_mod_cast h1
  · intro C hCne
    by_contra hcon
    push_neg at hcon
    have hrow : ∀ i ∈ C, D.visits i ≤ ∑ j ∈ C, D.transitions i j := by
      intro i hi
      have h := hcon i hi
      simp only [TrainingSet.Qhat, Matrix.of_apply] at h
      rw [← Finset.sum_div, le_div_iff₀ (hd i), one_mul] at h
      exact_mod_cast h
    have hsum : ∑ i ∈ C, D.visits i ≤ ∑ i ∈ C, ∑ j ∈ C, D.transitions i j :=
      Finset.sum_le_sum hrow
    have e1 : ∑ i ∈ C, D.visits i = ∑ s, ∑ i ∈ C, (D.path s).count i := by
      simp only [TrainingSet.visits]; exact Finset.sum_comm
    have e2 : ∑ i ∈ C, ∑ j ∈ C, D.transitions i j =
        ∑ s, ∑ i ∈ C, ∑ j ∈ C, ((D.path s).zip (D.path s).tail).count (i, j) := by
      simp only [TrainingSet.transitions]
      calc _ = ∑ i ∈ C, ∑ s, ∑ j ∈ C, ((D.path s).zip (D.path s).tail).count (i, j) := by
            apply Finset.sum_congr rfl; intro i _; exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    obtain ⟨i0, hi0⟩ := hCne
    have hpos : ∃ s, 0 < ∑ i ∈ C, (D.path s).count i := by
      by_contra hno
      push_neg at hno
      have h1 : D.visits i0 ≤ ∑ i ∈ C, D.visits i :=
        Finset.single_le_sum (f := fun i => D.visits i) (fun _ _ => Nat.zero_le _) hi0
      have h2 : ∑ s, ∑ i ∈ C, (D.path s).count i = 0 :=
        Finset.sum_eq_zero fun s _ => Nat.le_zero.1 (hno s)
      have := happ i0
      omega
    obtain ⟨s0, hs0⟩ := hpos
    have hlt : ∑ s, ∑ i ∈ C, ∑ j ∈ C, ((D.path s).zip (D.path s).tail).count (i, j) <
        ∑ s, ∑ i ∈ C, (D.path s).count i := by
      apply Finset.sum_lt_sum
      · intro s _; exact (std_list_lt C (D.path s)).1
      · exact ⟨s0, Finset.mem_univ _, (std_list_lt C (D.path s0)).2 hs0⟩
    rw [e1, e2] at hsum
    omega


lemma std_isUnit {N : Type*} [Fintype N] [DecidableEq N] (A : Matrix N N ℝ)
    (hA : Tendsto (fun n : ℕ => A ^ n) atTop (𝓝 0)) : IsUnit (1 - A) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro x y hxy
  have h0 : (1 - A).mulVec (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hxy, sub_self]
  set z := x - y with hz
  have hAz : A.mulVec z = z := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0
    exact h0.symm
  have hpow : ∀ n : ℕ, (A ^ n).mulVec z = z := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', ← Matrix.mulVec_mulVec, ih, hAz]
  have hcont : Continuous (fun M : Matrix N N ℝ => M.mulVec z) :=
    Continuous.matrix_mulVec continuous_id continuous_const
  have ht : Tendsto (fun n : ℕ => (A ^ n).mulVec z) atTop (𝓝 ((0 : Matrix N N ℝ).mulVec z)) :=
    (hcont.tendsto 0).comp hA
  simp only [hpow, Matrix.zero_mulVec] at ht
  have : z = 0 := tendsto_nhds_unique tendsto_const_nhds ht
  exact sub_eq_zero.mp this

lemma std_list_start {N : Type*} [Fintype N] [DecidableEq N] (j : N) : ∀ l : List N,
    ∑ i, (l.zip l.tail).count (i, j) + (if l.head? = some j then 1 else 0) = l.count j := by
  intro l
  induction l with
  | nil => simp
  | cons a t ih =>
    cases t with
    | nil => by_cases h : a = j <;> simp [List.count_cons, h]
    | cons b t' =>
      have e : ((a :: b :: t').zip (a :: b :: t').tail)
          = (a, b) :: ((b :: t').zip t') := rfl
      simp only [List.tail_cons] at ih
      have hp := std_pair_cons Finset.univ {j} a b ((b :: t').zip t')
      simp only [Finset.sum_singleton, Finset.mem_univ, Finset.mem_singleton, true_and] at hp
      rw [e, hp]
      by_cases ha : a = j <;> by_cases hb : b = j <;>
        simp [List.count_cons, ha, hb] at ih ⊢ <;> omega

theorem solution {N : Type*} [Fintype N] [DecidableEq N] {S : ℕ}
    (D : TrainingSet N S) (happ : ∀ i, 0 < D.visits i) :
    (fun i => (D.visits i : ℝ)) = (fun i => (D.starts i : ℝ)) ᵥ* (1 - D.Qhat)⁻¹ := by
  have hd : ∀ i, (0:ℝ) < D.visits i := fun i => by exact_mod_cast happ i
  have hU : IsUnit (1 - D.Qhat) := std_isUnit _ (std_Qhat_absorbing D happ)
  have hdet : IsUnit (1 - D.Qhat).det := (Matrix.isUnit_iff_isUnit_det _).mp hU
  -- counting identity: ∑_i η_ij + μ_j = d_j
  have hcount : ∀ j, ∑ i, D.transitions i j + D.starts j = D.visits j := by
    intro j
    have h1 : D.starts j = ∑ s, (if (D.path s).head? = some j then 1 else 0) := by
      unfold TrainingSet.starts
      rw [Finset.card_filter]
    rw [h1]
    simp only [TrainingSet.transitions, TrainingSet.visits]
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => std_list_start j (D.path s)
  have hmain : (fun i => (D.visits i : ℝ)) ᵥ* (1 - D.Qhat) = fun i => (D.starts i : ℝ) := by
    funext j
    rw [Matrix.vecMul_sub, Matrix.vecMul_one]
    have hQ : ((fun i => (D.visits i : ℝ)) ᵥ* D.Qhat) j = ∑ i, (D.transitions i j : ℝ) := by
      simp only [Matrix.vecMul, dotProduct, TrainingSet.Qhat, Matrix.of_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp [(hd i).ne']
    simp only [Pi.sub_apply, hQ]
    have := hcount j
    have h2 : (∑ i, (D.transitions i j : ℝ)) + (D.starts j : ℝ) = (D.visits j : ℝ) := by
      exact_mod_cast this
    linarith
  rw [← hmain, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hdet, Matrix.vecMul_one]
