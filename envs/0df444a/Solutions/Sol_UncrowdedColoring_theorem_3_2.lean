-- Prove2me | solution 1 for UncrowdedColoring.theorem_3_2
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-20T16:32:27.186958+00:00
-- url     : https://prove2.me/submissions/75dd175a-76bf-4732-91d0-4bc00c2aa384

import Mathlib

open MeasureTheory ProbabilityTheory

/-- Asymmetric Lovász local lemma: auxiliary form used to derive the symmetric version. -/
theorem asym_lll {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (A : Fin n → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (D : Fin n → Finset (Fin n)) (hD : ∀ i, i ∉ D i)
    (hind : ∀ i, Indep (MeasurableSpace.generateFrom {A i})
      (MeasurableSpace.generateFrom (A '' {j | j ∉ D i ∧ j ≠ i})) μ)
    (h₁ : ∀ i, μ.real (A i) ≤ 1 / 4)
    (h₂ : ∀ i, ∑ j ∈ D i, μ.real (A j) ≤ 1 / 4) :
    0 < μ (⋂ i, (A i)ᶜ) := by
  classical
  let B : Finset (Fin n) → Set Ω := fun S => ⋂ j ∈ S, (A j)ᶜ
  let x : Fin n → ℝ := fun i => 2 * μ.real (A i)
  have hB_meas : ∀ S, MeasurableSet (B S) := by
    intro S
    dsimp only [B]
    exact Finset.measurableSet_biInter S (fun j _ => (hA j).compl)
  have hB_empty : B ∅ = Set.univ := by
    dsimp only [B]
    simp
  have hB_insert : ∀ (a : Fin n) (S : Finset (Fin n)), a ∉ S →
      B (insert a S) = (A a)ᶜ ∩ B S := by
    intro a S ha
    dsimp only [B]
    rw [Finset.set_biInter_insert]
  have hB_mono : ∀ S T : Finset (Fin n), S ⊆ T → B T ⊆ B S := by
    intro S T hST y hy
    dsimp only [B] at hy ⊢
    simp only [Set.mem_iInter, Set.mem_compl_iff] at hy ⊢
    exact fun j hj => hy j (hST hj)
  have hB_union : ∀ S T : Finset (Fin n), B (S ∪ T) = B S ∩ B T := by
    intro S T
    dsimp only [B]
    rw [Finset.set_biInter_inter]
  have hB_compl : ∀ S : Finset (Fin n), B S = (⋃ j ∈ S, A j)ᶜ := by
    intro S
    dsimp only [B]
    ext y
    simp
  have hind_real : ∀ (i : Fin n) (T : Finset (Fin n)),
      (∀ j ∈ T, j ∉ D i ∧ j ≠ i) →
      μ.real (A i ∩ B T) = μ.real (A i) * μ.real (B T) := by
    intro i T hT
    have hm1 : MeasurableSet[MeasurableSpace.generateFrom {A i}] (A i) :=
      MeasurableSpace.measurableSet_generateFrom (Set.mem_singleton (A i))
    have hm2 : MeasurableSet[MeasurableSpace.generateFrom (A '' {j | j ∉ D i ∧ j ≠ i})]
        (B T) := by
      dsimp only [B]
      exact Finset.measurableSet_biInter T (fun j hj =>
        (MeasurableSpace.measurableSet_generateFrom
          (Set.mem_image_of_mem A (hT j hj))).compl)
    have h := (Indep_iff (MeasurableSpace.generateFrom {A i})
      (MeasurableSpace.generateFrom (A '' {j | j ∉ D i ∧ j ≠ i})) μ).1 (hind i)
      (A i) (B T) hm1 hm2
    rw [measureReal_def, measureReal_def, measureReal_def, h, ENNReal.toReal_mul]
  have hx_nonneg : ∀ i, 0 ≤ x i := by
    intro i
    simp only [x]
    have := measureReal_nonneg (μ := μ) (s := A i)
    linarith
  have hx_le : ∀ i, x i ≤ 1 / 2 := by
    intro i
    simp only [x]
    linarith [h₁ i]
  have hx_sum : ∀ i, ∑ j ∈ D i, x j ≤ 1 / 2 := by
    intro i
    have h : ∑ j ∈ D i, x j = 2 * ∑ j ∈ D i, μ.real (A j) := by
      rw [Finset.mul_sum]
    rw [h]
    linarith [h₂ i]
  have hAi_half : ∀ i, μ.real (A i) = x i / 2 := by
    intro i
    simp only [x]
    ring
  have keyP : ∀ (k : ℕ) (S : Finset (Fin n)), S.card = k → ∀ i, i ∉ S →
      μ.real (A i ∩ B S) ≤ x i * μ.real (B S) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro S hS i hi
      have hS1_sub : S ∩ D i ⊆ S := Finset.inter_subset_left
      have hS2_sub : S \ D i ⊆ S := Finset.sdiff_subset
      have hS1D : ∀ j ∈ S ∩ D i, j ∈ D i := fun j hj => (Finset.mem_inter.mp hj).2
      have hS2nd : ∀ j ∈ S \ D i, j ∉ D i := fun j hj => (Finset.mem_sdiff.mp hj).2
      have hpart : S ∩ D i ∪ S \ D i = S := by
        rw [Finset.union_comm]
        exact Finset.sdiff_union_inter S (D i)
      have hU_meas : MeasurableSet (⋃ j ∈ S ∩ D i, A j) :=
        Set.Finite.measurableSet_biUnion (S ∩ D i).finite_toSet (fun j _ => hA j)
      have hB_split : B S = B (S ∩ D i) ∩ B (S \ D i) := by
        conv_lhs => rw [← hpart]
        exact hB_union _ _
      have hB_S1 : B (S ∩ D i) = (⋃ j ∈ S ∩ D i, A j)ᶜ := hB_compl _
      have hB_decomp : B S = B (S \ D i) \ (⋃ j ∈ S ∩ D i, A j) := by
        rw [hB_split, hB_S1, Set.sdiff_eq, Set.inter_comm]
      have hdisj : Disjoint (B (S \ D i) \ ⋃ j ∈ S ∩ D i, A j)
          (B (S \ D i) ∩ ⋃ j ∈ S ∩ D i, A j) := by
        rw [Set.disjoint_left]
        intro y hy1 hy2
        exact ((Set.mem_sdiff y).mp hy1).2 ((Set.mem_inter_iff y _ _).mp hy2).2
      have hmeasure_split :
          μ.real (B (S \ D i)) =
            μ.real (B S) + μ.real (B (S \ D i) ∩ ⋃ j ∈ S ∩ D i, A j) := by
        have h1 : B (S \ D i) =
            (B (S \ D i) \ ⋃ j ∈ S ∩ D i, A j) ∪
              (B (S \ D i) ∩ ⋃ j ∈ S ∩ D i, A j) :=
          (Set.sdiff_union_inter _ _).symm
        calc μ.real (B (S \ D i))
            = μ.real (B (S \ D i) \ ⋃ j ∈ S ∩ D i, A j) +
                μ.real (B (S \ D i) ∩ ⋃ j ∈ S ∩ D i, A j) := by
              conv_lhs => rw [h1]
              exact measureReal_union hdisj ((hB_meas (S \ D i)).inter hU_meas)
                (measure_ne_top μ _) (measure_ne_top μ _)
          _ = μ.real (B S) + μ.real (B (S \ D i) ∩ ⋃ j ∈ S ∩ D i, A j) := by
              rw [← hB_decomp]
      have hU_bound : μ.real (B (S \ D i) ∩ ⋃ j ∈ S ∩ D i, A j) ≤
          ∑ j ∈ S ∩ D i, μ.real (B (S \ D i) ∩ A j) := by
        have hEq : B (S \ D i) ∩ ⋃ j ∈ S ∩ D i, A j =
            ⋃ j ∈ S ∩ D i, (B (S \ D i) ∩ A j) := by
          ext y
          simp only [Set.mem_inter_iff, Set.mem_iUnion, exists_prop]
          constructor
          · rintro ⟨hy, j, hj, hyj⟩
            exact ⟨j, hj, hy, hyj⟩
          · rintro ⟨j, hj, hy, hyj⟩
            exact ⟨hy, j, hj, hyj⟩
        rw [hEq]
        exact measureReal_biUnion_finset_le (S ∩ D i)
          (fun j => B (S \ D i) ∩ A j)
      have hterm : ∀ j ∈ S ∩ D i, μ.real (B (S \ D i) ∩ A j) ≤
          x j * μ.real (B (S \ D i)) := by
        intro j hj
        have hjD : j ∈ D i := hS1D j hj
        have hjS : j ∈ S := hS1_sub hj
        have hjS2 : j ∉ S \ D i := by
          rw [Finset.mem_sdiff]
          exact fun h => h.2 hjD
        have hcard : (S \ D i).card < k := by
          have hssub : S \ D i ⊂ S := by
            refine Finset.ssubset_iff_subset_ne.mpr ⟨hS2_sub, ?_⟩
            intro hEq
            have hj' : j ∈ S \ D i := by rw [hEq]; exact hjS
            exact hjS2 hj'
          rw [← hS]
          exact Finset.card_lt_card hssub
        have hIH := ih (S \ D i).card hcard (S \ D i) rfl j hjS2
        rwa [Set.inter_comm] at hIH
      have hlow : (1 - ∑ j ∈ S ∩ D i, x j) * μ.real (B (S \ D i)) ≤
          μ.real (B S) := by
        have hsum : ∑ j ∈ S ∩ D i, μ.real (B (S \ D i) ∩ A j) ≤
            ∑ j ∈ S ∩ D i, x j * μ.real (B (S \ D i)) :=
          Finset.sum_le_sum hterm
        have hsum2 : ∑ j ∈ S ∩ D i, x j * μ.real (B (S \ D i)) =
            (∑ j ∈ S ∩ D i, x j) * μ.real (B (S \ D i)) :=
          (Finset.sum_mul ..).symm
        have hnonneg : 0 ≤ μ.real (B (S \ D i)) := measureReal_nonneg
        nlinarith [hmeasure_split, hU_bound, hsum, hsum2, hnonneg]
      have hhalf : (1 : ℝ) / 2 ≤ 1 - ∑ j ∈ S ∩ D i, x j := by
        have hsub : ∑ j ∈ S ∩ D i, x j ≤ ∑ j ∈ D i, x j :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
            (fun j _ _ => hx_nonneg j)
        linarith [hx_sum i]
      have hchain : μ.real (A i ∩ B S) ≤ μ.real (A i) * μ.real (B (S \ D i)) := by
        have hsub : A i ∩ B S ⊆ A i ∩ B (S \ D i) := by
          intro y hy
          exact ⟨hy.1, hB_mono (S \ D i) S hS2_sub hy.2⟩
        calc μ.real (A i ∩ B S) ≤ μ.real (A i ∩ B (S \ D i)) := measureReal_mono hsub
          _ = μ.real (A i) * μ.real (B (S \ D i)) :=
              hind_real i (S \ D i) (fun j hj => ⟨hS2nd j hj, by
                have hjS : j ∈ S := hS2_sub hj
                intro hji
                exact hi (by rw [← hji]; exact hjS)⟩)
      have hpos2 : 0 ≤ μ.real (B (S \ D i)) := measureReal_nonneg
      calc μ.real (A i ∩ B S) ≤ μ.real (A i) * μ.real (B (S \ D i)) := hchain
        _ ≤ (x i / 2) * μ.real (B (S \ D i)) :=
            mul_le_mul_of_nonneg_right (le_of_eq (hAi_half i)) hpos2
        _ = x i * ((1 / 2) * μ.real (B (S \ D i))) := by ring
        _ ≤ x i * μ.real (B S) := by
            apply mul_le_mul_of_nonneg_left _ (hx_nonneg i)
            calc (1 / 2) * μ.real (B (S \ D i))
                ≤ (1 - ∑ j ∈ S ∩ D i, x j) * μ.real (B (S \ D i)) :=
                  mul_le_mul_of_nonneg_right hhalf hpos2
              _ ≤ μ.real (B S) := hlow
  have keyQ : ∀ S : Finset (Fin n), ∏ j ∈ S, (1 - x j) ≤ μ.real (B S) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      rw [hB_empty]
      simp
    | insert a S ha ih =>
      have hBins : B (insert a S) = B S \ A a := by
        rw [hB_insert a S ha, Set.sdiff_eq, Set.inter_comm]
      have hdisj : Disjoint (B S \ A a) (B S ∩ A a) := by
        rw [Set.disjoint_left]
        intro y hy1 hy2
        exact ((Set.mem_sdiff y).mp hy1).2 ((Set.mem_inter_iff y _ _).mp hy2).2
      have hsplit : μ.real (B S) =
          μ.real (B (insert a S)) + μ.real (B S ∩ A a) := by
        have h1 : B S = (B S \ A a) ∪ (B S ∩ A a) := (Set.sdiff_union_inter _ _).symm
        calc μ.real (B S) = μ.real (B S \ A a) + μ.real (B S ∩ A a) := by
              conv_lhs => rw [h1]
              exact measureReal_union hdisj ((hB_meas S).inter (hA a))
                (measure_ne_top μ _) (measure_ne_top μ _)
          _ = μ.real (B (insert a S)) + μ.real (B S ∩ A a) := by rw [← hBins]
      have hPa : μ.real (B S ∩ A a) ≤ x a * μ.real (B S) := by
        have h := keyP S.card S rfl a ha
        rwa [Set.inter_comm] at h
      calc ∏ j ∈ insert a S, (1 - x j) = (1 - x a) * ∏ j ∈ S, (1 - x j) :=
            Finset.prod_insert ha
        _ ≤ (1 - x a) * μ.real (B S) := by
            apply mul_le_mul_of_nonneg_left ih
            linarith [hx_le a]
        _ = μ.real (B S) - x a * μ.real (B S) := by ring
        _ ≤ μ.real (B (insert a S)) := by linarith [hsplit, hPa]
  have hfinal : (1 / 2 : ℝ) ^ n ≤ μ.real (B Finset.univ) := by
    have h1 : ∏ j ∈ Finset.univ, (1 - x j) ≤ μ.real (B Finset.univ) := keyQ _
    have h3 : ∏ j ∈ (Finset.univ : Finset (Fin n)), (1 / 2 : ℝ) = (1 / 2) ^ n := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have h2 : (1 / 2 : ℝ) ^ n ≤ ∏ j ∈ Finset.univ, (1 - x j) := by
      rw [← h3]
      exact Finset.prod_le_prod (fun j _ => by norm_num) (fun j _ => by linarith [hx_le j])
    linarith
  have hpos : 0 < μ.real (B Finset.univ) := lt_of_lt_of_le (by positivity) hfinal
  have huniv : B Finset.univ = ⋂ i, (A i)ᶜ := by
    dsimp only [B]
    simp
  rw [huniv] at hpos
  have hne : μ (⋂ i, (A i)ᶜ) ≠ 0 := by
    intro h0
    rw [measureReal_def, h0] at hpos
    simp at hpos
  exact pos_iff_ne_zero.mpr hne

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (A : Fin n → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p < 1) (hpA : ∀ i, μ.real (A i) ≤ p)
    (dLLL : ℕ) (S : Fin n → Finset (Fin n)) (hS : ∀ i, i ∉ S i)
    (hcard : ∀ i, ((Finset.univ.erase i) \ S i).card ≤ dLLL)
    (hind : ∀ i, Indep (MeasurableSpace.generateFrom {A i})
      (MeasurableSpace.generateFrom (A '' (S i : Set (Fin n)))) μ)
    (h4 : 4 * p * (dLLL : ℝ) ≤ 1) :
    0 < μ (⋂ i, (A i)ᶜ) := by
  classical
  rcases Nat.eq_zero_or_pos dLLL with hd0 | hdpos
  · -- Case `dLLL = 0`: all events are mutually independent.
    have hS_eq : ∀ i, S i = Finset.univ.erase i := by
      intro i
      have hzero : ((Finset.univ.erase i) \ S i).card = 0 := by
        have h := hcard i
        rw [hd0] at h
        omega
      have hempty : (Finset.univ.erase i) \ S i = ∅ := Finset.card_eq_zero.mp hzero
      have hsub1 : Finset.univ.erase i ⊆ S i := Finset.sdiff_eq_empty_iff_subset.mp hempty
      have hsub2 : S i ⊆ Finset.univ.erase i := by
        intro j hj
        exact Finset.mem_erase.mpr ⟨fun h => hS i (h ▸ hj), Finset.mem_univ j⟩
      exact Finset.Subset.antisymm hsub2 hsub1
    have hind' : ∀ i, Indep (MeasurableSpace.generateFrom {A i})
        (MeasurableSpace.generateFrom (A '' (Finset.univ.erase i : Set (Fin n)))) μ := by
      intro i
      have h := hind i
      rw [hS_eq i] at h
      exact h
    let B : Finset (Fin n) → Set Ω := fun T => ⋂ j ∈ T, (A j)ᶜ
    have hB_empty : B ∅ = Set.univ := by
      dsimp only [B]
      simp
    have hB_insert : ∀ (a : Fin n) (T : Finset (Fin n)), a ∉ T →
        B (insert a T) = (A a)ᶜ ∩ B T := by
      intro a T ha
      dsimp only [B]
      rw [Finset.set_biInter_insert]
    have hind_real : ∀ (i : Fin n) (T : Finset (Fin n)), T ⊆ Finset.univ.erase i →
        μ.real ((A i)ᶜ ∩ B T) = μ.real ((A i)ᶜ) * μ.real (B T) := by
      intro i T hT
      have hm1 : MeasurableSet[MeasurableSpace.generateFrom {A i}] ((A i)ᶜ) :=
        (MeasurableSpace.measurableSet_generateFrom (Set.mem_singleton (A i))).compl
      have hm2 : MeasurableSet[MeasurableSpace.generateFrom
          (A '' (Finset.univ.erase i : Set (Fin n)))] (B T) := by
        dsimp only [B]
        refine Finset.measurableSet_biInter T (fun j hj => ?_)
        have hj' : j ∈ (Finset.univ.erase i : Set (Fin n)) := by
          simpa using hT hj
        exact (MeasurableSpace.measurableSet_generateFrom
          (Set.mem_image_of_mem A hj')).compl
      have h := (Indep_iff _ _ μ).1 (hind' i) ((A i)ᶜ) (B T) hm1 hm2
      rw [measureReal_def, measureReal_def, measureReal_def, h, ENNReal.toReal_mul]
    have hprod : ∀ T : Finset (Fin n),
        μ.real (B T) = ∏ j ∈ T, (1 - μ.real (A j)) := by
      intro T
      induction T using Finset.induction_on with
      | empty =>
        rw [hB_empty]
        simp
      | insert a T ha ih =>
        have hstep : μ.real (B (insert a T)) = μ.real ((A a)ᶜ) * μ.real (B T) := by
          rw [hB_insert a T ha]
          exact hind_real a T (by
            intro j hj
            exact Finset.mem_erase.mpr ⟨fun h => ha (h ▸ hj), Finset.mem_univ j⟩)
        rw [hstep, ih, Finset.prod_insert ha]
        have hc : μ.real ((A a)ᶜ) = 1 - μ.real (A a) := by
          rw [measureReal_compl (hA a)]
          simp
        rw [hc]
    have hpos : 0 < μ.real (B Finset.univ) := by
      rw [hprod]
      apply Finset.prod_pos
      intro j _
      linarith [hpA j, hp₁]
    have hunivB : B Finset.univ = ⋂ i, (A i)ᶜ := by
      dsimp only [B]
      simp
    rw [hunivB] at hpos
    have hne : μ (⋂ i, (A i)ᶜ) ≠ 0 := by
      intro h0
      rw [measureReal_def, h0] at hpos
      simp at hpos
    exact pos_iff_ne_zero.mpr hne
  · -- Case `dLLL ≥ 1`: take `D i = (univ.erase i) \ S i` and apply the asymmetric LLL.
    have hD : ∀ i, i ∉ (Finset.univ.erase i) \ S i := by
      intro i h
      exact (Finset.mem_erase.mp (Finset.mem_sdiff.mp h).1).1 rfl
    have hSset : ∀ i, {j : Fin n | j ∉ (Finset.univ.erase i) \ S i ∧ j ≠ i} =
        (S i : Set (Fin n)) := by
      intro i
      ext j
      simp only [Set.mem_ofPred_eq, Finset.mem_coe]
      constructor
      · rintro ⟨hD, hji⟩
        by_contra hj
        exact hD (Finset.mem_sdiff.mpr
          ⟨Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩, hj⟩)
      · intro hj
        refine ⟨?_, ?_⟩
        · intro hD
          exact (Finset.mem_sdiff.mp hD).2 hj
        · intro hji
          exact hS i (hji ▸ hj)
    have hind' : ∀ i, Indep (MeasurableSpace.generateFrom {A i})
        (MeasurableSpace.generateFrom (A '' {j | j ∉ (Finset.univ.erase i) \ S i ∧ j ≠ i})) μ := by
      intro i
      have h := hind i
      rw [← hSset i] at h
      exact h
    have hp_le : p ≤ 1 / 4 := by
      have hd1 : (1 : ℝ) ≤ (dLLL : ℝ) := by exact_mod_cast hdpos
      have hp4 : 4 * p ≤ 4 * p * (dLLL : ℝ) := by
        have h := mul_le_mul_of_nonneg_left hd1 (by linarith : (0 : ℝ) ≤ 4 * p)
        linarith
      linarith
    have h₁' : ∀ i, μ.real (A i) ≤ 1 / 4 := fun i => by linarith [hpA i, hp_le]
    have h₂' : ∀ i, ∑ j ∈ (Finset.univ.erase i) \ S i, μ.real (A j) ≤ 1 / 4 := by
      intro i
      have hstep1 : ∑ j ∈ (Finset.univ.erase i) \ S i, μ.real (A j) ≤
          ∑ j ∈ (Finset.univ.erase i) \ S i, p :=
        Finset.sum_le_sum (fun j _ => hpA j)
      have hstep2 : ∑ j ∈ (Finset.univ.erase i) \ S i, p =
          (((Finset.univ.erase i) \ S i).card : ℝ) * p := by
        rw [Finset.sum_const, nsmul_eq_mul]
      have hstep3 : (((Finset.univ.erase i) \ S i).card : ℝ) * p ≤ (dLLL : ℝ) * p := by
        apply mul_le_mul_of_nonneg_right _ hp₀
        exact_mod_cast hcard i
      have hstep4 : (dLLL : ℝ) * p ≤ 1 / 4 := by nlinarith [h4]
      linarith
    exact asym_lll μ n A hA (fun i => (Finset.univ.erase i) \ S i) hD hind' h₁' h₂'
