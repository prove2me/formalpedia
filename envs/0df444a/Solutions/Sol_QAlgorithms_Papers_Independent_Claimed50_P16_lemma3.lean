-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P16.lemma3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T05:23:09.621873+00:00
-- url     : https://prove2.me/submissions/86ac3e94-c0cb-4577-901e-0cb20b858088

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P16

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal BigOperators

namespace X6C16

/-- Greedy choice: if finitely many subspaces meet in `⊥`, at most `finrank` of them do. -/
theorem pick {K E ι : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    (W : ι → Submodule K E) (s : Finset ι) (hs : ∀ c : E, (∀ i ∈ s, c ∈ W i) → c = 0) :
    ∀ d : ℕ, ∀ U : Submodule K E, Module.finrank K U ≤ d →
      ∃ t ⊆ s, t.card ≤ d ∧ ∀ c ∈ U, (∀ i ∈ t, c ∈ W i) → c = 0 := by
  classical
  intro d
  induction d with
  | zero =>
    intro U hU
    refine ⟨∅, Finset.empty_subset _, by simp, ?_⟩
    intro c hc _
    have : U = ⊥ := Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hU)
    subst this
    simpa using hc
  | succ d ih =>
    intro U hU
    by_cases hU0 : U = ⊥
    · refine ⟨∅, Finset.empty_subset _, by simp, ?_⟩
      intro c hc _
      subst hU0
      simpa using hc
    · -- some `W j` cuts `U` strictly
      have : ∃ j ∈ s, ¬ U ≤ W j := by
        by_contra hcon
        push Not at hcon
        apply hU0
        rw [eq_bot_iff]
        intro c hc
        simpa using hs c (fun i hi => hcon i hi hc)
      obtain ⟨j, hj, hUj⟩ := this
      have hlt : U ⊓ W j < U := lt_of_le_of_ne inf_le_left (fun h => hUj (h ▸ inf_le_right))
      have hrank : Module.finrank K ↥(U ⊓ W j) < Module.finrank K U :=
        Submodule.finrank_lt_finrank_of_lt hlt
      obtain ⟨t, hts, htc, ht⟩ := ih (U ⊓ W j) (by omega)
      refine ⟨insert j t, Finset.insert_subset hj hts, ?_, ?_⟩
      · calc (insert j t).card ≤ t.card + 1 := Finset.card_insert_le _ _
          _ ≤ d + 1 := by omega
      · intro c hc hct
        exact ht c ⟨hc, hct j (Finset.mem_insert_self _ _)⟩
          (fun i hi => hct i (Finset.mem_insert_of_mem hi))

/-- The subspace of coefficient vectors annihilating `f` a.e. on `B`. -/
def V {n : ℕ} (f : Fin n → ℝ → ℂ) (B : Set ℝ) : Submodule ℂ (Fin n → ℂ) where
  carrier := {c | ∀ᵐ x ∂volume.restrict B, (∑ i, c i * f i x) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro c d hc hd
    show ∀ᵐ x ∂volume.restrict B, _
    filter_upwards [hc, hd] with x h1 h2
    simp [add_mul, Finset.sum_add_distrib, h1, h2]
  smul_mem' := by
    intro r c hc
    show ∀ᵐ x ∂volume.restrict B, _
    filter_upwards [hc] with x h1
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, h1, mul_zero]

/-- pieces of the interval -/
def B (a b h : ℝ) (k : ℕ) : Set ℝ := Set.Icc a b ∩ Set.Icc (a + k * h) (a + (k + 1) * h)

theorem main {n : ℕ} (a b : ℝ) (f : Fin n → ℝ → ℂ)
    (hind : QAlgorithms.Papers.Independent.Claimed50.P16.aeIndependent f (Set.Icc a b))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ A : Set ℝ, A ⊆ Set.Icc a b ∧ NullMeasurableSet A volume ∧
      volume A < ENNReal.ofReal epsilon ∧
      QAlgorithms.Papers.Independent.Claimed50.P16.aeIndependent f A := by
  classical
  set h : ℝ := epsilon / (n + 1) with hh
  have hpos : 0 < h := by positivity
  set N : ℕ := ⌈(b - a) / h⌉₊ + 1
  -- the pieces cover the interval
  have cover : Set.Icc a b ⊆ ⋃ k ∈ Finset.range N, B a b h k := by
    intro x hx
    simp only [Set.mem_iUnion, Finset.mem_range]
    refine ⟨⌊(x - a) / h⌋₊, ?_, hx, ?_, ?_⟩
    · have h1 : (x - a) / h ≤ (b - a) / h := by
        apply div_le_div_of_nonneg_right _ hpos.le; linarith [hx.2]
      have h2 : ⌊(x - a) / h⌋₊ ≤ ⌈(b - a) / h⌉₊ :=
        Nat.cast_le.mp (le_trans (Nat.floor_le (div_nonneg (by linarith [hx.1]) hpos.le))
          (le_trans h1 (Nat.le_ceil _)))
      omega
    · have := Nat.floor_le (div_nonneg (by linarith [hx.1] : (0:ℝ) ≤ x - a) hpos.le)
      have := (le_div_iff₀ hpos).mp this
      linarith
    · have := Nat.lt_floor_add_one ((x - a) / h)
      have := (div_lt_iff₀ hpos).mp this
      push_cast
      linarith
  have hs : ∀ c : Fin n → ℂ, (∀ k ∈ Finset.range N, c ∈ V f (B a b h k)) → c = 0 := by
    intro c hc
    apply hind
    have : ∀ᵐ x ∂volume.restrict (⋃ k ∈ Finset.range N, B a b h k), (∑ i, c i * f i x) = 0 :=
      (ae_restrict_biUnion_finset_iff _ _ _).mpr (fun k hk => hc k hk)
    exact ae_restrict_of_ae_restrict_of_subset cover this
  obtain ⟨t, -, htc, ht⟩ := pick (fun k => V f (B a b h k)) (Finset.range N) hs
    n ⊤ (by simpa using (Submodule.finrank_le (⊤ : Submodule ℂ (Fin n → ℂ))))
  refine ⟨⋃ k ∈ t, B a b h k, ?_, ?_, ?_, ?_⟩
  · intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨k, -, hk⟩ := hx
    exact hk.1
  · refine (Finset.measurableSet_biUnion _ fun k _ => ?_).nullMeasurableSet
    exact measurableSet_Icc.inter measurableSet_Icc
  · have hB : ∀ k, volume (B a b h k) ≤ ENNReal.ofReal h := by
      intro k
      calc volume (B a b h k) ≤ volume (Set.Icc (a + k * h) (a + (k + 1) * h)) :=
            measure_mono Set.inter_subset_right
        _ = ENNReal.ofReal h := by rw [Real.volume_Icc]; congr 1; ring
    calc volume (⋃ k ∈ t, B a b h k) ≤ ∑ k ∈ t, volume (B a b h k) := measure_biUnion_finset_le _ _
      _ ≤ ∑ _k ∈ t, ENNReal.ofReal h := Finset.sum_le_sum fun k _ => hB k
      _ = ENNReal.ofReal (t.card * h) := by
          rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_natCast]
      _ < ENNReal.ofReal epsilon := by
          rw [ENNReal.ofReal_lt_ofReal_iff hepsilon]
          have : (t.card : ℝ) ≤ n := by exact_mod_cast htc
          calc (t.card : ℝ) * h ≤ n * h := by gcongr
            _ < (n + 1) * h := by linarith
            _ = epsilon := by rw [hh]; field_simp
  · intro c hc
    apply ht c Submodule.mem_top
    intro k hk
    show ∀ᵐ x ∂volume.restrict (B a b h k), (∑ i, c i * f i x) = 0
    exact ae_restrict_of_ae_restrict_of_subset (Set.subset_biUnion_of_mem hk) hc

end X6C16

open QAlgorithms.Papers.Independent.Claimed50.P16 in
theorem solution {n : ℕ} (a b : ℝ) (f : Fin n → ℝ → ℂ)
    (hmeas : ∀ i, AEMeasurable (f i) (volume.restrict (Set.Icc a b)))
    (hind : aeIndependent f (Set.Icc a b)) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ A : Set ℝ, A ⊆ Set.Icc a b ∧ NullMeasurableSet A volume ∧
      volume A < ENNReal.ofReal epsilon ∧ aeIndependent f A :=
  X6C16.main a b f hind epsilon hepsilon
