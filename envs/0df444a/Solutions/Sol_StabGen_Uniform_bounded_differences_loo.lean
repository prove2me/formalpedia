-- Prove2me | solution 1 for StabGen.Uniform.bounded_differences_loo
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T00:35:31.618481+00:00
-- url     : https://prove2.me/submissions/10eb2bcb-f23d-489b-b29b-8bd01c32e482

import Mathlib
import Definitions.Def_FoundationsML_Stability_Loss
import Definitions.Def_FoundationsML_Stability_EmpiricalError
import Definitions.Def_FoundationsML_Stability_GeneralizationError
import Definitions.Def_StabGen_Hypothesis_Setting
import Definitions.Def_StabGen_Uniform_Stability

set_option autoImplicit false

open MeasureTheory FoundationsML.Stability in
theorem cce6_trainingSet_ofList {Z : Type*} (l : List Z) :
    ∃ U : Fin l.length → Z, StabGen.Hypothesis.trainingSet U = (l : Multiset Z) := by
  refine ⟨l.get, ?_⟩
  unfold StabGen.Hypothesis.trainingSet
  rw [Fin.univ_val_map, List.ofFn_get]

open MeasureTheory FoundationsML.Stability in
theorem cce6_removeAt_eq {Z : Type*} {n : ℕ} (U : Fin n → Z) (k : Fin n) :
    StabGen.Hypothesis.trainingSet U = U k ::ₘ StabGen.Hypothesis.removeAt U k := by
  classical
  unfold StabGen.Hypothesis.trainingSet StabGen.Hypothesis.removeAt
  rw [Finset.erase_val, ← Multiset.map_cons, Multiset.cons_erase (Finset.mem_univ k)]

open MeasureTheory FoundationsML.Stability in
theorem cce6_stab_ms {X Y Y' : Type*} (L : Y' → Y → ℝ)
    (A : StabGen.Hypothesis.LearningAlgorithm X Y Y') (n : ℕ) (β : ℝ)
    (hstab : StabGen.Uniform.HasUniformStability L A n β)
    (a : X × Y) (V : Multiset (X × Y)) (hc : Multiset.card (a ::ₘ V) = n) (z : X × Y) :
    |Loss L (A (a ::ₘ V)) z - Loss L (A V) z| ≤ β := by
  classical
  obtain ⟨l, hl⟩ := Quot.exists_rep (a ::ₘ V)
  have hl' : ((l : Multiset (X × Y))) = a ::ₘ V := hl
  have hlen : l.length = n := by rw [← hc, ← hl']; simp
  subst hlen
  obtain ⟨U, hU⟩ := cce6_trainingSet_ofList l
  have ha : a ∈ StabGen.Hypothesis.trainingSet U := by rw [hU, hl']; simp
  obtain ⟨k, -, hk⟩ := Multiset.mem_map.1 ha
  have h1 := hstab U k z
  have hT := cce6_removeAt_eq U k
  rw [hU, hl', hk] at hT
  have hV : StabGen.Hypothesis.removeAt U k = V := (Multiset.cons_inj_right a).1 hT.symm
  rw [hU, hl', hV] at h1
  exact h1

open MeasureTheory FoundationsML.Stability in
theorem cce6_removeAt_update {Z : Type*} {m : ℕ} (S : Fin m → Z) (i : Fin m) (z' : Z) :
    StabGen.Hypothesis.removeAt (StabGen.Hypothesis.replaceAt S i z') i
      = StabGen.Hypothesis.removeAt S i := by
  classical
  unfold StabGen.Hypothesis.removeAt StabGen.Hypothesis.replaceAt
  apply Multiset.map_congr rfl
  intro k hk
  have hk' : k ∈ (Finset.univ : Finset (Fin m)).erase i := hk
  have : k ≠ i := (Finset.mem_erase.1 hk').1
  simp [Function.update_of_ne this]

open MeasureTheory FoundationsML.Stability in
/-- For `j ≠ i`, the two leave-`j`-out sets are `S i ::ₘ V` and `z' ::ₘ V`. -/
theorem cce6_removeAt_split {Z : Type*} {m : ℕ} (S : Fin m → Z) (i j : Fin m) (z' : Z)
    (hij : j ≠ i) :
    ∃ V : Multiset Z, StabGen.Hypothesis.removeAt S j = S i ::ₘ V ∧
      StabGen.Hypothesis.removeAt (StabGen.Hypothesis.replaceAt S i z') j = z' ::ₘ V := by
  classical
  refine ⟨((Finset.univ.erase j).erase i).val.map S, ?_, ?_⟩
  · unfold StabGen.Hypothesis.removeAt
    have hi : i ∈ Finset.univ.erase j := Finset.mem_erase.2 ⟨Ne.symm hij, Finset.mem_univ i⟩
    conv_lhs => rw [← Finset.insert_erase hi]
    rw [Finset.insert_val_of_notMem (Finset.notMem_erase i _), Multiset.map_cons]
  · unfold StabGen.Hypothesis.removeAt StabGen.Hypothesis.replaceAt
    have hi : i ∈ Finset.univ.erase j := Finset.mem_erase.2 ⟨Ne.symm hij, Finset.mem_univ i⟩
    conv_lhs => rw [← Finset.insert_erase hi]
    rw [Finset.insert_val_of_notMem (Finset.notMem_erase i _), Multiset.map_cons,
      Function.update_self]
    congr 1
    apply Multiset.map_congr rfl
    intro k hk
    have hk' : k ∈ ((Finset.univ : Finset (Fin m)).erase j).erase i := hk
    have : k ≠ i := (Finset.mem_erase.1 hk').1
    simp [Function.update_of_ne this]

open MeasureTheory FoundationsML.Stability in
theorem cce6_card_removeAt {Z : Type*} {m : ℕ} (S : Fin m → Z) (j : Fin m) :
    Multiset.card (StabGen.Hypothesis.removeAt S j) = m - 1 := by
  classical
  unfold StabGen.Hypothesis.removeAt
  simp

open MeasureTheory FoundationsML.Stability in
theorem solution {X Y Y' : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (D : Measure (X × Y)) [IsProbabilityMeasure D] (L : Y' → Y → ℝ)
    (A : StabGen.Hypothesis.LearningAlgorithm X Y Y')
    (hA : ∀ n : ℕ, Measurable
      (fun p : (Fin n → X × Y) × (X × Y) => Loss L (A (StabGen.Hypothesis.trainingSet p.1)) p.2))
    (M : ℝ)
    (hbound : ∀ (T : Multiset (X × Y)) (z : X × Y), 0 ≤ Loss L (A T) z ∧ Loss L (A T) z ≤ M)
    (m : ℕ) (β : ℝ) (hstab : StabGen.Uniform.HasUniformStability L A m β)
    (hstab' : StabGen.Uniform.HasUniformStability L A (m - 1) β) :
    ∀ (S : Fin m → X × Y) (i : Fin m) (z' : X × Y),
      |(GeneralizationError D L (A (StabGen.Hypothesis.trainingSet S)) - StabGen.Hypothesis.looError L A S)
        - (GeneralizationError D L (A (StabGen.Hypothesis.trainingSet (StabGen.Hypothesis.replaceAt S i z')))
            - StabGen.Hypothesis.looError L A (StabGen.Hypothesis.replaceAt S i z'))|
        ≤ 4 * β + M / m := by
  intro S i z'
  set S' := StabGen.Hypothesis.replaceAt S i z' with hS'
  have hβ : 0 ≤ β := le_trans (abs_nonneg _) (hstab S i z')
  have hm : (0 : ℝ) < m := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt)
  -- pointwise 2β bound between the two full-sample hypotheses
  have hRR : StabGen.Hypothesis.removeAt S' i = StabGen.Hypothesis.removeAt S i :=
    cce6_removeAt_update S i z'
  have hpt : ∀ z, |Loss L (A (StabGen.Hypothesis.trainingSet S)) z
      - Loss L (A (StabGen.Hypothesis.trainingSet S')) z| ≤ 2 * β := by
    intro z
    have h1 := hstab S i z
    have h2 := hstab S' i z
    rw [hRR] at h2
    calc _ = |(Loss L (A (StabGen.Hypothesis.trainingSet S)) z
              - Loss L (A (StabGen.Hypothesis.removeAt S i)) z)
            - (Loss L (A (StabGen.Hypothesis.trainingSet S')) z
              - Loss L (A (StabGen.Hypothesis.removeAt S i)) z)| := by ring_nf
      _ ≤ _ := abs_sub _ _
      _ ≤ β + β := add_le_add h1 h2
      _ = 2 * β := by ring
  have hint : ∀ T : Fin m → X × Y,
      Integrable (fun z => Loss L (A (StabGen.Hypothesis.trainingSet T)) z) D := by
    intro T
    have hmeas : Measurable (fun z => Loss L (A (StabGen.Hypothesis.trainingSet T)) z) :=
      (hA m).comp measurable_prodMk_left
    refine Integrable.of_bound hmeas.aestronglyMeasurable M (Filter.Eventually.of_forall ?_)
    intro z
    have := hbound (StabGen.Hypothesis.trainingSet T) z
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [this.1, this.2]
  have hG : |GeneralizationError D L (A (StabGen.Hypothesis.trainingSet S))
      - GeneralizationError D L (A (StabGen.Hypothesis.trainingSet S'))| ≤ 2 * β := by
    unfold GeneralizationError
    rw [← integral_sub (hint S) (hint S')]
    have := norm_integral_le_of_norm_le_const (μ := D)
      (f := fun z => Loss L (A (StabGen.Hypothesis.trainingSet S)) z
        - Loss L (A (StabGen.Hypothesis.trainingSet S')) z)
      (C := 2 * β) (Filter.Eventually.of_forall (fun z => by
        rw [Real.norm_eq_abs]; exact hpt z))
    simpa [Real.norm_eq_abs] using this
  -- termwise loo bound
  have hterm : ∀ j : Fin m,
      |Loss L (A (StabGen.Hypothesis.removeAt S j)) (S j)
        - Loss L (A (StabGen.Hypothesis.removeAt S' j)) (S' j)|
        ≤ 2 * β + (if j = i then M else 0) := by
    intro j
    by_cases hj : j = i
    · subst hj
      rw [if_pos rfl, hRR]
      have h1 := hbound (StabGen.Hypothesis.removeAt S j) (S j)
      have h2 := hbound (StabGen.Hypothesis.removeAt S j) (S' j)
      rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    · rw [if_neg hj, add_zero]
      obtain ⟨V, h1, h2⟩ := cce6_removeAt_split S i j z' hj
      have hSj : S' j = S j := by
        rw [hS']; unfold StabGen.Hypothesis.replaceAt; exact Function.update_of_ne hj _ _
      rw [hSj]
      have hc1 : Multiset.card (S i ::ₘ V) = m - 1 := by rw [← h1]; exact cce6_card_removeAt S j
      have hc2 : Multiset.card (z' ::ₘ V) = m - 1 := by
        rw [← h2]; exact cce6_card_removeAt S' j
      have e1 := cce6_stab_ms L A (m - 1) β hstab' (S i) V hc1 (S j)
      have e2 := cce6_stab_ms L A (m - 1) β hstab' z' V hc2 (S j)
      have h2' : StabGen.Hypothesis.removeAt S' j = z' ::ₘ V := by rw [hS']; exact h2
      rw [h1, h2']
      calc _ = |(Loss L (A (S i ::ₘ V)) (S j) - Loss L (A V) (S j))
              - (Loss L (A (z' ::ₘ V)) (S j) - Loss L (A V) (S j))| := by ring_nf
        _ ≤ _ := abs_sub _ _
        _ ≤ β + β := add_le_add e1 e2
        _ = 2 * β := by ring
  have hloo : |StabGen.Hypothesis.looError L A S - StabGen.Hypothesis.looError L A S'|
      ≤ 2 * β + M / m := by
    unfold StabGen.Hypothesis.looError
    rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / m)]
    have hs : |∑ j, (Loss L (A (StabGen.Hypothesis.removeAt S j)) (S j)
        - Loss L (A (StabGen.Hypothesis.removeAt S' j)) (S' j))|
        ≤ ∑ j : Fin m, (2 * β + (if j = i then M else 0)) :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => hterm j))
    have hsum : ∑ j : Fin m, (2 * β + (if j = i then M else 0)) = m * (2 * β) + M := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        Finset.sum_ite_eq' Finset.univ i, if_pos (Finset.mem_univ i), nsmul_eq_mul]
    rw [hsum] at hs
    calc 1 / (m:ℝ) * _ ≤ 1 / (m:ℝ) * (m * (2 * β) + M) :=
          mul_le_mul_of_nonneg_left hs (by positivity)
      _ = 2 * β + M / m := by field_simp
  calc _ = |(GeneralizationError D L (A (StabGen.Hypothesis.trainingSet S))
            - GeneralizationError D L (A (StabGen.Hypothesis.trainingSet S')))
          - (StabGen.Hypothesis.looError L A S - StabGen.Hypothesis.looError L A S')| := by ring_nf
    _ ≤ _ := abs_sub _ _
    _ ≤ 2 * β + (2 * β + M / m) := add_le_add hG hloo
    _ = 4 * β + M / m := by ring
