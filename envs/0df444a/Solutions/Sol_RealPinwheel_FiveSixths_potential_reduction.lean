-- Prove2me | solution 1 for RealPinwheel.FiveSixths.potential_reduction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:20:20.61148+00:00
-- url     : https://prove2.me/submissions/598162b5-b3ad-4cb8-9b9e-c3810d44db25

import Theorems.Thm_RealPinwheel_FiveSixths_unfolding
open RealPinwheel.FiveSixths

private lemma potential_eq {r : ℕ} (A : Instance (r + 1)) :
    potential A = ∑ i : Fin r, 1 / A.period i.castSucc := by
  unfold potential
  rw [Fin.sum_univ_castSucc]
  simp

private lemma density_potential {r : ℕ} (A : Instance (r + 1)) :
    density A = potential A + 1 / A.period (Fin.last r) := by
  rw [potential_eq]
  exact Fin.sum_univ_castSucc _

private lemma folded_one_le {r : ℕ} (A : Instance (r + 2)) (hr : 1 ≤ r)
    (hP : potential A ≤ (5 : ℝ) / 6) :
    1 ≤ A.period ⟨r, by omega⟩ / 2 := by
  let j : Fin (r + 2) := ⟨r, by omega⟩
  have hj : 0 < A.period j := lt_of_lt_of_le (by norm_num) (A.one_le j)
  have hy : (r + 1 : ℝ) * (1 / A.period j) ≤ potential A := by
    rw [potential_eq]
    calc
      _ = ∑ i : Fin (r + 1), 1 / A.period j := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => by
        apply one_div_le_one_div_of_le
        · exact lt_of_lt_of_le (by norm_num) (A.one_le i.castSucc)
        · apply A.ordered
          change i.val ≤ r
          omega
  have hr' : (2 : ℝ) ≤ r + 1 := by exact_mod_cast (show 2 ≤ r + 1 by omega)
  have htwo : 2 * (1 / A.period j) ≤ (5 : ℝ) / 6 := by
    have hd := le_of_lt (one_div_pos.mpr hj)
    nlinarith
  have hi : (1 / A.period j) * A.period j = 1 := by field_simp
  change 1 ≤ A.period j / 2
  nlinarith

private noncomputable def rawFold {r : ℕ} (A : Instance (r + 2)) : Fin (r + 1) → ℝ :=
  Fin.snoc (fun i : Fin r => A.period ⟨i.val, by omega⟩)
    (A.period ⟨r, by omega⟩ / 2)

private lemma rawFold_le {r : ℕ} (A : Instance (r + 2)) (i : Fin (r + 1)) :
    rawFold A i ≤ A.period ⟨r, by omega⟩ := by
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simp only [rawFold, Fin.snoc_last]
    have := A.one_le ⟨r, by omega⟩
    linarith
  · simp only [rawFold, Fin.snoc_castSucc]
    apply A.ordered
    change k.val ≤ r
    omega

private noncomputable def foldedInstance {r : ℕ} (A : Instance (r + 2)) (hr : 1 ≤ r)
    (hP : potential A ≤ (5 : ℝ) / 6) : Instance (r + 1) where
  positive_dimension := by omega
  period := rawFold A ∘ Tuple.sort (rawFold A)
  one_le := by
    intro i
    have hc : ∀ k, 1 ≤ rawFold A k := by
      intro k
      refine Fin.lastCases ?_ (fun l => ?_) k
      · simpa only [rawFold, Fin.snoc_last] using folded_one_le A hr hP
      · simpa only [rawFold, Fin.snoc_castSucc] using A.one_le ⟨l.val, by omega⟩
    exact hc _
  ordered := Tuple.monotone_sort _

private lemma folded_potential {r : ℕ} (A : Instance (r + 2)) (hr : 1 ≤ r)
    (hP : potential A ≤ (5 : ℝ) / 6) :
    potential (foldedInstance A hr hP) ≤ potential A := by
  let B := foldedInstance A hr hP
  let j : Fin (r + 2) := ⟨r, by omega⟩
  have hj : 0 < A.period j := lt_of_lt_of_le (by norm_num) (A.one_le j)
  have hlast : B.period (Fin.last r) ≤ A.period j := rawFold_le A _
  have hlast' : 0 < B.period (Fin.last r) := lt_of_lt_of_le (by norm_num) (B.one_le _)
  have hi : 1 / A.period j ≤ 1 / B.period (Fin.last r) :=
    one_div_le_one_div_of_le hlast' hlast
  have hsum : density B = ∑ i : Fin (r + 1), 1 / rawFold A i := by
    exact Equiv.sum_comp (Tuple.sort (rawFold A)) (fun i => 1 / rawFold A i)
  have hsum' : density B =
      (∑ i : Fin r, 1 / A.period ⟨i.val, by omega⟩) + 2 / A.period j := by
    rw [hsum, Fin.sum_univ_castSucc]
    simp only [rawFold, Fin.snoc_last, Fin.snoc_castSucc]
    dsimp [j]
    congr 1
    field_simp
  have hpot : potential A =
      (∑ i : Fin r, 1 / A.period ⟨i.val, by omega⟩) + 1 / A.period j := by
    rw [potential_eq, Fin.sum_univ_castSucc]
    rfl
  have hd := density_potential B
  change potential B ≤ potential A
  rw [hsum', hpot] at *
  simp only [div_eq_mul_inv, one_mul] at *
  linarith

private lemma unfolding_mem {n : ℕ} (a : Fin n → ℝ) (j : Fin n) (q : ℕ)
    (x : Fin n ⊕ Fin q) :
    x ∈ unfoldedLabels a j q ↔ (∀ k, x = Sum.inl k → k ≠ j) := by
  classical
  cases x <;> simp [unfoldedLabels, List.mem_mergeSort, unfoldingLabels]

private noncomputable def liftLabel {r : ℕ} (A : Instance (r + 2)) :
    Fin (r + 1) ⊕ Fin 2 → Fin (r + 2)
  | Sum.inl k => ⟨(Tuple.sort (rawFold A) k).val, by omega⟩
  | Sum.inr k => ⟨r + k.val, by omega⟩

private lemma lift_preimage {r : ℕ} (A : Instance (r + 2)) (hr : 1 ≤ r)
    (hP : potential A ≤ (5 : ℝ) / 6) (k : Fin (r + 2)) :
    let B := foldedInstance A hr hP
    let j := (Tuple.sort (rawFold A)).symm (Fin.last r)
    ∃ u : Fin (unfoldedLabels B.period j 2).length,
      liftLabel A ((unfoldedLabels B.period j 2).get u) = k ∧
      unfoldedPeriods B.period j 2 u ≤ A.period k := by
  classical
  dsimp only
  let B := foldedInstance A hr hP
  let σ := Tuple.sort (rawFold A)
  let j := σ.symm (Fin.last r)
  by_cases hk : k.val < r
  · let l : Fin (r + 1) := ⟨k.val, by omega⟩
    let b := σ.symm l
    have hbj : b ≠ j := by
      intro he
      have he' : l = Fin.last r := σ.symm.injective he
      have hv := congrArg Fin.val he'
      dsimp [l] at hv
      omega
    have hm : Sum.inl b ∈ unfoldedLabels B.period j 2 := by
      rw [unfolding_mem]
      intro v hv
      cases hv
      exact hbj
    obtain ⟨u, hu⟩ := List.mem_iff_get.mp hm
    refine ⟨u, ?_, ?_⟩
    · rw [hu]
      dsimp [liftLabel, b, σ]
      simp only [Equiv.apply_symm_apply]
      exact Fin.ext rfl
    · change unfoldingPeriod B.period j 2 ((unfoldedLabels B.period j 2).get u) ≤ _
      rw [hu]
      change rawFold A (σ b) ≤ _
      rw [show σ b = l from σ.apply_symm_apply l]
      have he : l = (⟨k.val, hk⟩ : Fin r).castSucc := rfl
      rw [he]
      simp only [rawFold, Fin.snoc_castSucc]
      exact le_rfl
  · let b : Fin 2 := ⟨k.val - r, by omega⟩
    have hm : Sum.inr b ∈ unfoldedLabels B.period j 2 := by
      rw [unfolding_mem]
      intro v hv
      cases hv
    obtain ⟨u, hu⟩ := List.mem_iff_get.mp hm
    refine ⟨u, ?_, ?_⟩
    · rw [hu]
      apply Fin.ext
      dsimp [liftLabel, b]
      omega
    · change unfoldingPeriod B.period j 2 ((unfoldedLabels B.period j 2).get u) ≤ _
      rw [hu]
      change (2 : ℝ) * rawFold A (σ (σ.symm (Fin.last r))) ≤ _
      rw [σ.apply_symm_apply]
      simp only [rawFold, Fin.snoc_last]
      have hh : A.period ⟨r, by omega⟩ ≤ A.period k := A.ordered (by change r ≤ k.val; omega)
      linarith

private lemma lift_schedulable {r : ℕ} (A : Instance (r + 2)) (hr : 1 ≤ r)
    (hP : potential A ≤ (5 : ℝ) / 6)
    (hB : Schedulable (foldedInstance A hr hP).period) : Schedulable A.period := by
  classical
  let B := foldedInstance A hr hP
  let j := (Tuple.sort (rawFold A)).symm (Fin.last r)
  obtain ⟨U, hU⟩ := unfolding B hB j 2 (by decide)
  let φ : Fin (unfoldedLabels B.period j 2).length → Fin (r + 2) :=
    fun u => liftLabel A ((unfoldedLabels B.period j 2).get u)
  refine ⟨φ ∘ U, ?_⟩
  intro k ell hell m
  obtain ⟨u, hu, ha⟩ := lift_preimage A hr hP k
  apply (hU u ell hell m).trans
  apply Finset.card_mono
  intro t ht
  simp only [Finset.mem_filter, Finset.mem_range] at ht ⊢
  refine ⟨lt_of_lt_of_le ht.1 (Nat.ceil_mono (mul_le_mul_of_nonneg_left ha (Nat.cast_nonneg ell))), ?_⟩
  dsimp [φ, Function.comp_apply]
  rw [ht.2]
  exact hu

theorem solution {n : ℕ} (A : Instance n) (hn : 9 ≤ n)
    (hP : potential A ≤ (5 : ℝ) / 6) :
    ∃ B : Instance 9, potential B ≤ (5 : ℝ) / 6 ∧
      (Schedulable B.period → Schedulable A.period) := by
  suffices H : ∀ m : ℕ, ∀ C : Instance m, 9 ≤ m → potential C ≤ (5 : ℝ) / 6 →
      ∃ B : Instance 9, potential B ≤ (5 : ℝ) / 6 ∧
        (Schedulable B.period → Schedulable C.period) by
    exact H n A hn hP
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro C hm hC
    by_cases he : m = 9
    · subst m
      exact ⟨C, hC, fun h => h⟩
    obtain ⟨r, hr⟩ : ∃ r, m = r + 2 := ⟨m - 2, by omega⟩
    subst m
    have hr' : 1 ≤ r := by omega
    let F := foldedInstance C hr' hC
    have hF : potential F ≤ (5 : ℝ) / 6 := (folded_potential C hr' hC).trans hC
    obtain ⟨B, hPB, hBF⟩ := ih (r + 1) (by omega) F (by omega) hF
    exact ⟨B, hPB, fun hB => lift_schedulable C hr' hC (hBF hB)⟩
