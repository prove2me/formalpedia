-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P33.epsilonDeltaMeasureFinite
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T16:58:01.484369+00:00
-- url     : https://prove2.me/submissions/35c992ef-fa59-4149-9e0a-70287ed5d129

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P33
noncomputable section

open MeasureTheory

open scoped ENNReal

open QAlgorithms.Papers.Independent.Next46.P33

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem g62i_diff {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega) [IsFiniteMeasure mu]
    {A B : Set Omega} (hB : MeasurableSet B) (hBA : B ⊆ A) :
    mu.real (A \ B) = mu.real A - mu.real B := by
  have := measureReal_inter_add_sdiff (μ := mu) (s := A) hB
  rw [Set.inter_eq_right.2 hBA] at this
  linarith

theorem g62i_atomR {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega) [IsFiniteMeasure mu]
    (hAtomless : SubsetAtomless mu) (A : Set Omega) (hA : MeasurableSet A) (hpos : 0 < mu.real A) :
    ∃ B, MeasurableSet B ∧ B ⊆ A ∧ 0 < mu.real B ∧ mu.real B < mu.real A := by
  have h0 : 0 < mu A := by
    rw [Measure.real] at hpos
    exact ENNReal.toReal_pos_iff.1 hpos |>.1
  obtain ⟨B, hB, hBA, hBpos, hBlt⟩ := hAtomless A hA h0
  refine ⟨B, hB, hBA, ?_, ?_⟩
  · exact ENNReal.toReal_pos hBpos.ne' (measure_ne_top _ _)
  · exact (ENNReal.toReal_lt_toReal (measure_ne_top _ _) (measure_ne_top _ _)).2 hBlt

theorem g62i_small {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega) [IsFiniteMeasure mu]
    (hAtomless : SubsetAtomless mu) (A : Set Omega) (hA : MeasurableSet A) (hpos : 0 < mu.real A) :
    ∀ n : ℕ, ∃ B, MeasurableSet B ∧ B ⊆ A ∧ 0 < mu.real B ∧ mu.real B ≤ mu.real A / 2 ^ n := by
  intro n
  induction n with
  | zero => exact ⟨A, hA, subset_rfl, hpos, by simp⟩
  | succ n ih =>
    obtain ⟨B, hB, hBA, hBpos, hBle⟩ := ih
    obtain ⟨C, hC, hCB, hCpos, hClt⟩ := g62i_atomR mu hAtomless B hB hBpos
    have hd := g62i_diff mu hC hCB
    by_cases hc : mu.real C ≤ mu.real B / 2
    · refine ⟨C, hC, hCB.trans hBA, hCpos, ?_⟩
      rw [pow_succ, ← div_div]; linarith [div_le_div_of_nonneg_right hBle (by norm_num : (0:ℝ) ≤ 2)]
    · refine ⟨B \ C, hB.diff hC, Set.sdiff_subset.trans hBA, by linarith, ?_⟩
      rw [pow_succ, ← div_div]; linarith [div_le_div_of_nonneg_right hBle (by norm_num : (0:ℝ) ≤ 2)]

theorem g62i_small' {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega) [IsFiniteMeasure mu]
    (hAtomless : SubsetAtomless mu) (A : Set Omega) (hA : MeasurableSet A) (hpos : 0 < mu.real A)
    (η : ℝ) (hη : 0 < η) :
    ∃ B, MeasurableSet B ∧ B ⊆ A ∧ 0 < mu.real B ∧ mu.real B < η := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hη hpos) (by norm_num : (1/2 : ℝ) < 1)
  obtain ⟨B, hB, hBA, hBpos, hBle⟩ := g62i_small mu hAtomless A hA hpos n
  refine ⟨B, hB, hBA, hBpos, lt_of_le_of_lt hBle ?_⟩
  rw [div_lt_iff₀ (by positivity)]
  rw [lt_div_iff₀ hpos, one_div_pow] at hn
  have : (0:ℝ) < 2 ^ n := by positivity
  rw [div_mul_eq_mul_div, div_lt_iff₀ this] at hn
  linarith

theorem g62i_medium {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    [IsFiniteMeasure mu] (hAtomless : SubsetAtomless mu) (θ : ℝ) (hθ : 0 < θ)
    (A : Set Omega) (hA : MeasurableSet A) (hAθ : θ / 2 ≤ mu.real A) :
    ∃ B, MeasurableSet B ∧ B ⊆ A ∧ θ / 2 ≤ mu.real B ∧ mu.real B < θ := by
  by_contra hno
  push_neg at hno
  -- no medium subsets: small means very small
  have nm : ∀ B, MeasurableSet B → B ⊆ A → mu.real B < θ → mu.real B < θ / 2 := by
    intro B hB hBA hlt
    by_contra h
    push_neg at h
    exact absurd (hno B hB hBA h) (not_le.2 hlt)
  let T : Set ℝ := {r | ∃ B, MeasurableSet B ∧ B ⊆ A ∧ mu.real B < θ / 2 ∧ r = mu.real B}
  have hTne : T.Nonempty := ⟨0, ∅, MeasurableSet.empty, Set.empty_subset _, by simp; linarith, by simp⟩
  have hTbdd : BddAbove T := ⟨θ / 2, by rintro r ⟨B, -, -, hB, rfl⟩; exact hB.le⟩
  set t := sSup T with ht
  have hchoose : ∀ n : ℕ, ∃ B, MeasurableSet B ∧ B ⊆ A ∧ mu.real B < θ / 2 ∧
      t - 1 / ((n : ℝ) + 1) < mu.real B := by
    intro n
    have : t - 1 / ((n : ℝ) + 1) < t := by
      have : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
      linarith
    obtain ⟨r, ⟨B, hB, hBA, hBlt, rfl⟩, hr⟩ := exists_lt_of_lt_csSup hTne this
    exact ⟨B, hB, hBA, hBlt, hr⟩
  choose Bs hBs hBsA hBslt hBsgt using hchoose
  let E : ℕ → Set Omega := fun n => Nat.rec (Bs 0) (fun k Ek => Ek ∪ Bs (k + 1)) n
  have hE0 : E 0 = Bs 0 := rfl
  have hEs : ∀ n, E (n + 1) = E n ∪ Bs (n + 1) := fun n => rfl
  have hEgood : ∀ n, MeasurableSet (E n) ∧ E n ⊆ A ∧ mu.real (E n) < θ / 2 := by
    intro n
    induction n with
    | zero => rw [hE0]; exact ⟨hBs 0, hBsA 0, hBslt 0⟩
    | succ n ih =>
      rw [hEs]
      obtain ⟨h1, h2, h3⟩ := ih
      refine ⟨h1.union (hBs _), Set.union_subset h2 (hBsA _), ?_⟩
      apply nm _ (h1.union (hBs _)) (Set.union_subset h2 (hBsA _))
      linarith [measureReal_union_le (μ := mu) (E n) (Bs (n + 1)), hBslt (n + 1)]
  have hBE : ∀ n, Bs n ⊆ E n := by
    intro n
    cases n with
    | zero => rw [hE0]
    | succ n => rw [hEs]; exact Set.subset_union_right
  have hEmono : Monotone E := monotone_nat_of_le_succ fun n => by
    rw [hEs]; exact Set.subset_union_left
  let Es := ⋃ n, E n
  have hEsm : MeasurableSet Es := MeasurableSet.iUnion fun n => (hEgood n).1
  have hEsA : Es ⊆ A := Set.iUnion_subset fun n => (hEgood n).2.1
  have hEsle : mu.real Es ≤ θ / 2 := by
    have : mu Es ≤ ENNReal.ofReal (θ / 2) := by
      rw [hEmono.measure_iUnion]
      refine iSup_le fun n => ?_
      have := (hEgood n).2.2
      rw [Measure.real] at this
      rw [← ENNReal.ofReal_toReal (measure_ne_top mu (E n))]
      exact ENNReal.ofReal_le_ofReal this.le
    rw [Measure.real]
    exact ENNReal.toReal_le_of_le_ofReal (by linarith) this
  have hEslt : mu.real Es < θ / 2 := nm Es hEsm hEsA (by linarith)
  have hEsT : mu.real Es ≤ t := le_csSup hTbdd ⟨Es, hEsm, hEsA, hEslt, rfl⟩
  have hEsge : t ≤ mu.real Es := by
    by_contra h
    push_neg at h
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / (t - mu.real Es))
    have hpos : 0 < t - mu.real Es := by linarith
    have h1 : 1 / ((n : ℝ) + 1) < t - mu.real Es := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hpos] at hn
      nlinarith
    have h2 : mu.real (Bs n) ≤ mu.real Es :=
      measureReal_mono ((hBE n).trans (Set.subset_iUnion E n))
    linarith [hBsgt n]
  -- the rest of A is null
  have hrest : mu.real (A \ Es) = 0 := by
    by_contra h
    have hp : 0 < mu.real (A \ Es) := lt_of_le_of_ne measureReal_nonneg (Ne.symm h)
    obtain ⟨B', hB', hB'A, hB'pos, hB'lt⟩ :=
      g62i_small' mu hAtomless (A \ Es) (hA.diff hEsm) hp (θ / 2)
        (by linarith)
    have hdisj : Disjoint Es B' := by
      rw [Set.disjoint_iff]
      intro x ⟨hx1, hx2⟩
      exact (hB'A hx2).2 hx1
    have hu := measureReal_union (μ := mu) hdisj hB'
    have hUA : Es ∪ B' ⊆ A := Set.union_subset hEsA (hB'A.trans Set.sdiff_subset)
    have hlt := nm (Es ∪ B') (hEsm.union hB') hUA (by linarith)
    have := le_csSup hTbdd ⟨Es ∪ B', hEsm.union hB', hUA, hlt, rfl⟩
    linarith
  have := g62i_diff mu hEsm hEsA
  linarith

theorem g62i_bound {Omega : Type*} [MeasurableSpace Omega] (mu nu : Measure Omega)
    [IsFiniteMeasure mu] (hAtomless : SubsetAtomless mu) (θ : ℝ) (hθ : 0 < θ)
    (hsmall : ∀ A, MeasurableSet A → mu.real A < θ → nu A < 1) :
    ∀ k : ℕ, ∀ A, MeasurableSet A → mu.real A < k * (θ / 2) → nu A ≤ k := by
  intro k
  induction k with
  | zero =>
    intro A _ h
    simp at h
    linarith [measureReal_nonneg (μ := mu) (s := A)]
  | succ k ih =>
    intro A hA h
    by_cases hc : mu.real A < θ
    · exact (hsmall A hA hc).le.trans (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.succ_ne_zero k))
    · push_neg at hc
      obtain ⟨B, hB, hBA, hB1, hB2⟩ := g62i_medium mu hAtomless θ hθ A hA (by linarith)
      have hd := g62i_diff mu hB hBA
      have h1 := ih (A \ B) (hA.diff hB) (by push_cast at h; linarith)
      have h2 := hsmall B hB hB2
      calc nu A = nu (B ∪ (A \ B)) := by rw [Set.union_sdiff_cancel hBA]
        _ ≤ nu B + nu (A \ B) := measure_union_le _ _
        _ ≤ 1 + k := add_le_add h2.le h1
        _ = ((k + 1 : ℕ) : ℝ≥0∞) := by push_cast; ring

theorem solution
    {Omega : Type*} [MeasurableSpace Omega] (mu nu : Measure Omega)
    [IsProbabilityMeasure mu] (hAtomless : SubsetAtomless mu)
    (hContinuity : MeasureEpsilonDelta nu mu) : nu Set.univ < ⊤ := by
  obtain ⟨δ, hδ, hδc⟩ := hContinuity 1 one_pos
  have hsmall : ∀ A, MeasurableSet A → mu.real A < δ → nu A < 1 := by
    intro A hA h
    have := hδc A hA ((ENNReal.lt_ofReal_iff_toReal_lt (measure_ne_top mu A)).2 h)
    simpa using this
  obtain ⟨k, hk⟩ := exists_nat_gt (2 / δ)
  have hb := g62i_bound mu nu hAtomless δ hδ hsmall k Set.univ MeasurableSet.univ (by
    rw [probReal_univ]
    rw [div_lt_iff₀ hδ] at hk
    linarith)
  exact lt_of_le_of_lt hb (ENNReal.natCast_lt_top k)

end
