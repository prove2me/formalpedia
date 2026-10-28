-- Prove2me | solution 1 for RobustSPA.Affiliated.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T09:15:54.33275+00:00
-- url     : https://prove2.me/submissions/58e05721-7835-46a9-92a9-764f5fb6b233

import Mathlib
import Definitions.Def_RobustSPA_Affiliated_Setting

open MeasureTheory RobustSPA.IID RobustSPA.Affiliated

namespace RAffL1

variable {n : ℕ}

/-- The event `Y = 1_T`: exactly the coordinates in `T` exceed `p`. -/
def E (p : ℝ) (T : Finset (Fin n)) : Set (Fin n → ℝ) := {v | ∀ i, (p < v i ↔ i ∈ T)}

lemma measurableSet_E (p : ℝ) (T : Finset (Fin n)) : MeasurableSet (E p T) := by
  have : E p T = ⋂ i, {v : Fin n → ℝ | (p < v i ↔ i ∈ T)} := by
    ext v; simp [E]
  rw [this]
  refine MeasurableSet.iInter fun i => ?_
  by_cases hi : i ∈ T
  · simp only [hi, iff_true]
    exact measurableSet_lt measurable_const (measurable_pi_apply i)
  · simp only [hi, iff_false]
    exact (measurableSet_lt measurable_const (measurable_pi_apply i)).compl

lemma E_disj (p : ℝ) {T T' : Finset (Fin n)} (h : T ≠ T') : Disjoint (E p T) (E p T') := by
  rw [Set.disjoint_left]
  intro v hv hv'
  apply h
  ext i
  rw [← hv i, hv' i]

/-- Exchangeability: `μ(E_T)` depends only on `|T|`. -/
lemma E_card (μ : Measure (Fin n → ℝ)) (hμ : μ ∈ Fexc n) (p : ℝ) {T T' : Finset (Fin n)}
    (h : T.card = T'.card) : μ (E p T) = μ (E p T') := by
  classical
  have hc : Fintype.card {x // x ∈ T'} = Fintype.card {x // x ∈ T} := by
    simp [Fintype.card_coe, h]
  let e : {x // x ∈ T'} ≃ {x // x ∈ T} := Fintype.equivOfCardEq hc
  let σ : Equiv.Perm (Fin n) := e.extendSubtype
  have hσ : ∀ i, σ i ∈ T ↔ i ∈ T' := by
    intro i
    by_cases hi : i ∈ T'
    · exact ⟨fun _ => hi, fun _ => e.extendSubtype_mem i hi⟩
    · exact ⟨fun h' => absurd h' (e.extendSubtype_not_mem i hi), fun h' => absurd h' hi⟩
  have hm : Measurable (fun v : Fin n → ℝ => v ∘ σ) :=
    measurable_pi_iff.mpr fun i => measurable_pi_apply (σ i)
  have hmap := hμ.2 σ
  have hpre : (fun v : Fin n → ℝ => v ∘ σ) ⁻¹' E p T' = E p T := by
    ext v
    simp only [Set.mem_preimage, E, Set.mem_setOf_eq, Function.comp_apply]
    constructor
    · intro hv j
      have := hv (σ.symm j)
      rw [← hσ, Equiv.apply_symm_apply] at this
      exact this
    · intro hv i
      rw [← hσ]
      exact hv (σ i)
  calc μ (E p T) = μ ((fun v : Fin n → ℝ => v ∘ σ) ⁻¹' E p T') := by rw [hpre]
    _ = (μ.map (fun v : Fin n → ℝ => v ∘ σ)) (E p T') :=
        (Measure.map_apply hm (measurableSet_E p T')).symm
    _ = μ (E p T') := by rw [hmap]

/-- canonical set of the first `k` coordinates -/
def Tk (n k : ℕ) : Finset (Fin n) := Finset.univ.filter (fun i => (i : ℕ) < k)

lemma card_Tk (k : ℕ) (hk : k ≤ n) : (Tk n k).card = k := by
  unfold Tk
  have : (Finset.univ.filter (fun i : Fin n => (i : ℕ) < k)) =
      (Finset.range k).attachFin (fun m hm => lt_of_lt_of_le (Finset.mem_range.mp hm) hk) := by
    ext i; simp
  rw [this, Finset.card_attachFin, Finset.card_range]

/-- The affiliation step `u_k u_1 ≤ u_{k+1} u_0`. -/
lemma aff_step (μ : Measure (Fin n → ℝ)) [IsFiniteMeasure μ] (hμ : Affiliated μ) (p : ℝ)
    (k : ℕ) (hk1 : 1 ≤ k) (hkn : k + 1 ≤ n) :
    (μ (E p (Tk n k))).toReal * (μ (E p {⟨k, by omega⟩})).toReal ≤
      (μ (E p (insert ⟨k, by omega⟩ (Tk n k)))).toReal * (μ (E p ∅)).toReal := by
  classical
  set a : Fin n := ⟨k, by omega⟩ with ha
  set z : Fin n := ⟨0, by omega⟩ with hz
  have haT : a ∉ Tk n k := by simp [Tk, a]
  have hzT : z ∈ Tk n k := by simp [Tk, z]; omega
  have hza : z ≠ a := by
    intro h; rw [Fin.ext_iff] at h; simp [z, a] at h; omega
  -- the sublattice
  let S : Set (Fin n → ℝ) := {v | ((∀ i : Fin n, (i : ℕ) < k → p < v i) ∨
    (∀ i : Fin n, (i : ℕ) < k → v i ≤ p)) ∧ ∀ i : Fin n, k < (i : ℕ) → v i ≤ p}
  let A : Set (Fin n → ℝ) := {v | p < v z}
  let B : Set (Fin n → ℝ) := {v | p < v a}
  have hSm : MeasurableSet S := by
    have h1 : MeasurableSet {v : Fin n → ℝ | ∀ i : Fin n, (i : ℕ) < k → p < v i} := by
      have : {v : Fin n → ℝ | ∀ i : Fin n, (i : ℕ) < k → p < v i} =
          ⋂ i : Fin n, ⋂ (_ : (i : ℕ) < k), {v | p < v i} := by
        ext v; simp
      rw [this]
      exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
        measurableSet_lt measurable_const (measurable_pi_apply i)
    have h2 : ∀ c : Fin n → Prop, MeasurableSet {v : Fin n → ℝ | ∀ i, c i → v i ≤ p} := by
      intro c
      have : {v : Fin n → ℝ | ∀ i, c i → v i ≤ p} = ⋂ i, ⋂ (_ : c i), {v | v i ≤ p} := by
        ext v; simp
      rw [this]
      exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
        measurableSet_le (measurable_pi_apply i) measurable_const
    exact (h1.union (h2 (fun i => (i : ℕ) < k))).inter (h2 (fun i => k < (i : ℕ)))
  have hAm : MeasurableSet A := measurableSet_lt measurable_const (measurable_pi_apply z)
  have hBm : MeasurableSet B := measurableSet_lt measurable_const (measurable_pi_apply a)
  have hAu : IsUpperSet A := fun v w hvw hv => lt_of_lt_of_le hv (hvw z)
  have hBu : IsUpperSet B := fun v w hvw hv => lt_of_lt_of_le hv (hvw a)
  have hSl : ∀ v ∈ S, ∀ w ∈ S, v ⊓ w ∈ S ∧ v ⊔ w ∈ S := by
    rintro v ⟨hv1, hv2⟩ w ⟨hw1, hw2⟩
    refine ⟨⟨?_, fun i hi => ?_⟩, ⟨?_, fun i hi => ?_⟩⟩
    · rcases hv1 with hv1 | hv1
      · rcases hw1 with hw1 | hw1
        · exact Or.inl fun i hi => lt_min (hv1 i hi) (hw1 i hi)
        · exact Or.inr fun i hi => min_le_of_right_le (hw1 i hi)
      · exact Or.inr fun i hi => min_le_of_left_le (hv1 i hi)
    · exact min_le_of_left_le (hv2 i hi)
    · rcases hv1 with hv1 | hv1
      · exact Or.inl fun i hi => lt_max_of_lt_left (hv1 i hi)
      · rcases hw1 with hw1 | hw1
        · exact Or.inl fun i hi => lt_max_of_lt_right (hw1 i hi)
        · exact Or.inr fun i hi => max_le (hv1 i hi) (hw1 i hi)
    · exact max_le (hv2 i hi) (hw2 i hi)
  have key := hμ A B S hAm hBm hSm hAu hBu hSl
  -- identify the four sets with unions of the events `E_T`
  have memE : ∀ (T : Finset (Fin n)) (v : Fin n → ℝ), v ∈ E p T ↔ ∀ i, (p < v i ↔ i ∈ T) :=
    fun _ _ => Iff.rfl
  have hlt : ∀ i : Fin n, (i : ℕ) < k ↔ i ∈ Tk n k := fun i => by simp [Tk]
  have hcases : ∀ i : Fin n, (i : ℕ) < k ∨ i = a ∨ k < (i : ℕ) := by
    intro i
    rcases lt_trichotomy (i : ℕ) k with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr h)
  -- generic description of membership in `S` together with the value of coordinate `a`
  have hS_iff : ∀ v, v ∈ S ↔ (v ∈ E p (Tk n k) ∨ v ∈ E p (insert a (Tk n k)) ∨
      v ∈ E p {a} ∨ v ∈ E p ∅) := by
    intro v
    simp only [S, Set.mem_setOf_eq, memE]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · by_cases hva : p < v a
        · right; left
          intro i
          rcases hcases i with hi | rfl | hi
          · simp [h1 i hi, (hlt i).mp hi]
          · simp [hva]
          · have hne : i ≠ a := fun h => by rw [h] at hi; simp [a] at hi
            have hnt : i ∉ Tk n k := fun h => by rw [← hlt] at h; omega
            simp [not_lt.mpr (h2 i hi), hne, hnt]
        · left
          intro i
          rcases hcases i with hi | rfl | hi
          · simp [h1 i hi, (hlt i).mp hi]
          · simp [hva, haT]
          · have hnt : i ∉ Tk n k := fun h => by rw [← hlt] at h; omega
            simp [not_lt.mpr (h2 i hi), hnt]
      · by_cases hva : p < v a
        · right; right; left
          intro i
          rcases hcases i with hi | rfl | hi
          · have hne : i ≠ a := fun h => by rw [h] at hi; simp [a] at hi
            simp [not_lt.mpr (h1 i hi), hne]
          · simp [hva]
          · have hne : i ≠ a := fun h => by rw [h] at hi; simp [a] at hi
            simp [not_lt.mpr (h2 i hi), hne]
        · right; right; right
          intro i
          rcases hcases i with hi | rfl | hi
          · simp [not_lt.mpr (h1 i hi)]
          · simp [hva]
          · simp [not_lt.mpr (h2 i hi)]
    · rintro (h | h | h | h)
      · refine ⟨Or.inl fun i hi => (h i).mpr ((hlt i).mp hi), fun i hi => ?_⟩
        have hnt : i ∉ Tk n k := fun h => by rw [← hlt] at h; omega
        exact not_lt.mp fun hc => hnt ((h i).mp hc)
      · refine ⟨Or.inl fun i hi => (h i).mpr (Finset.mem_insert_of_mem ((hlt i).mp hi)),
          fun i hi => ?_⟩
        have hnt : i ∉ insert a (Tk n k) := by
          rw [Finset.mem_insert, not_or]
          refine ⟨fun h => by rw [h] at hi; simp [a] at hi, fun h => ?_⟩
          rw [← hlt] at h; omega
        exact not_lt.mp fun hc => hnt ((h i).mp hc)
      · refine ⟨Or.inr fun i hi => ?_, fun i hi => ?_⟩
        · have hne : i ≠ a := fun h => by rw [h] at hi; simp [a] at hi
          exact not_lt.mp fun hc => hne (Finset.mem_singleton.mp ((h i).mp hc))
        · have hne : i ≠ a := fun h => by rw [h] at hi; simp [a] at hi
          exact not_lt.mp fun hc => hne (Finset.mem_singleton.mp ((h i).mp hc))
      · refine ⟨Or.inr fun i _ => ?_, fun i _ => ?_⟩
        · exact not_lt.mp fun hc => by simpa using (h i).mp hc
        · exact not_lt.mp fun hc => by simpa using (h i).mp hc
  have hET_z : ∀ v ∈ E p (Tk n k), p < v z := fun v hv => (hv z).mpr hzT
  have hETa_z : ∀ v ∈ E p (insert a (Tk n k)), p < v z :=
    fun v hv => (hv z).mpr (Finset.mem_insert_of_mem hzT)
  have hEa_z : ∀ v ∈ E p {a}, ¬ p < v z := fun v hv h => hza (Finset.mem_singleton.mp ((hv z).mp h))
  have hE0_z : ∀ v ∈ E p (∅ : Finset (Fin n)), ¬ p < v z := fun v hv h => by simpa using (hv z).mp h
  have hET_a : ∀ v ∈ E p (Tk n k), ¬ p < v a := fun v hv h => haT ((hv a).mp h)
  have hETa_a : ∀ v ∈ E p (insert a (Tk n k)), p < v a :=
    fun v hv => (hv a).mpr (Finset.mem_insert_self _ _)
  have hEa_a : ∀ v ∈ E p {a}, p < v a := fun v hv => (hv a).mpr (Finset.mem_singleton_self _)
  have hE0_a : ∀ v ∈ E p (∅ : Finset (Fin n)), ¬ p < v a := fun v hv h => by simpa using (hv a).mp h
  have eAS : A ∩ S = E p (Tk n k) ∪ E p (insert a (Tk n k)) := by
    ext v
    simp only [Set.mem_inter_iff, Set.mem_union, hS_iff]
    constructor
    · rintro ⟨hA, h | h | h | h⟩
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd hA (hEa_z v h)
      · exact absurd hA (hE0_z v h)
    · rintro (h | h)
      · exact ⟨hET_z v h, Or.inl h⟩
      · exact ⟨hETa_z v h, Or.inr (Or.inl h)⟩
  have eBS : B ∩ S = E p {a} ∪ E p (insert a (Tk n k)) := by
    ext v
    simp only [Set.mem_inter_iff, Set.mem_union, hS_iff]
    constructor
    · rintro ⟨hB, h | h | h | h⟩
      · exact absurd hB (hET_a v h)
      · exact Or.inr h
      · exact Or.inl h
      · exact absurd hB (hE0_a v h)
    · rintro (h | h)
      · exact ⟨hEa_a v h, Or.inr (Or.inr (Or.inl h))⟩
      · exact ⟨hETa_a v h, Or.inr (Or.inl h)⟩
  have eABS : A ∩ B ∩ S = E p (insert a (Tk n k)) := by
    ext v
    simp only [Set.mem_inter_iff, hS_iff]
    constructor
    · rintro ⟨⟨hA, hB⟩, h | h | h | h⟩
      · exact absurd hB (hET_a v h)
      · exact h
      · exact absurd hA (hEa_z v h)
      · exact absurd hA (hE0_z v h)
    · intro h
      exact ⟨⟨hETa_z v h, hETa_a v h⟩, Or.inr (Or.inl h)⟩
  have eS : S = (E p (Tk n k) ∪ E p (insert a (Tk n k))) ∪ (E p {a} ∪ E p ∅) := by
    ext v
    simp only [Set.mem_union, hS_iff]
    tauto
  have hne1 : Tk n k ≠ insert a (Tk n k) := fun h => haT (h ▸ Finset.mem_insert_self _ _)
  have hne2 : ({a} : Finset (Fin n)) ≠ insert a (Tk n k) := by
    intro h
    have : z ∈ ({a} : Finset (Fin n)) := h ▸ Finset.mem_insert_of_mem hzT
    exact hza (Finset.mem_singleton.mp this)
  have hne3 : ({a} : Finset (Fin n)) ≠ ∅ := Finset.singleton_ne_empty a
  have hd1 := E_disj p hne1
  have hd2 := E_disj p hne2
  have hd3 := E_disj p hne3
  have hd4 : Disjoint (E p (Tk n k) ∪ E p (insert a (Tk n k))) (E p {a} ∪ E p ∅) := by
    rw [Set.disjoint_union_left, Set.disjoint_union_right, Set.disjoint_union_right]
    refine ⟨⟨E_disj p ?_, E_disj p ?_⟩, ⟨E_disj p ?_, E_disj p ?_⟩⟩
    · intro h; exact hza (Finset.mem_singleton.mp (h ▸ hzT))
    · intro h; exact absurd (h ▸ hzT) (Finset.notMem_empty z)
    · exact hne2.symm
    · intro h; exact absurd (h ▸ Finset.mem_insert_self a (Tk n k)) (Finset.notMem_empty a)
  rw [eAS, eBS, eABS, eS, measure_union hd1 (measurableSet_E _ _),
    measure_union hd2 (measurableSet_E _ _),
    measure_union hd4 ((measurableSet_E _ _).union (measurableSet_E _ _)),
    measure_union hd1 (measurableSet_E _ _), measure_union hd3 (measurableSet_E _ _)] at key
  have key' := ENNReal.toReal_mono (by finiteness) key
  simp only [ENNReal.toReal_mul, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    at key'
  rw [ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
    ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at key'
  nlinarith [key']

end RAffL1

open RAffL1 in
theorem solution (n : ℕ) (hn : 2 ≤ n) (μ : Measure (Fin n → ℝ)) (hμ : μ ∈ Faff n) :
    ∀ p : ℝ, F1k (n - 1) μ p ^ (1 / ((n : ℝ) - 1)) ≤ F1 μ p ^ (1 / (n : ℝ)) := by
  classical
  intro p
  haveI : IsProbabilityMeasure μ := hμ.1.1.1
  set P : Finset (Fin n) → ℝ := fun T => (μ (E p T)).toReal with hP
  have hP0 : ∀ T, 0 ≤ P T := fun T => ENNReal.toReal_nonneg
  -- `u k`
  set u : ℕ → ℝ := fun k => P (Tk n k) with hu
  have hPu : ∀ T : Finset (Fin n), P T = u T.card := by
    intro T
    simp only [hP, hu]
    rw [E_card μ hμ.1 p (T := T) (T' := Tk n T.card)]
    rw [card_Tk _ (by simpa using T.card_le_univ)]
  have hu0 : ∀ k, 0 ≤ u k := fun k => hP0 _
  set a := u 0 with ha
  set b := u 1 with hb
  -- affiliation step in terms of `u`
  have hstep : ∀ k, 1 ≤ k → k + 1 ≤ n → u k * b ≤ u (k + 1) * a := by
    intro k hk1 hkn
    have h := aff_step μ hμ.2 p k hk1 hkn
    have c1 : P {⟨k, by omega⟩} = b := by rw [hPu]; simp [hb]
    have c2 : P (insert ⟨k, by omega⟩ (Tk n k)) = u (k + 1) := by
      rw [hPu, Finset.card_insert_of_notMem (by simp [Tk]), card_Tk k (by omega)]
    have c3 : P ∅ = a := by rw [hPu]; simp [ha]
    have c4 : P (Tk n k) = u k := rfl
    simp only [hP] at c1 c2 c3 c4
    rw [c1, c2, c3, c4] at h
    exact h
  -- `u_k a^{k-1} ≥ b^k`
  have hind : ∀ k, 1 ≤ k → k ≤ n → b ^ k ≤ u k * a ^ (k - 1) := by
    intro k hk1
    induction k with
    | zero => omega
    | succ k ih =>
      intro hkn
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp [hb]
      · have ih' := ih hk (by omega)
        have hs := hstep k hk (by omega)
        have hb0 : 0 ≤ b := hu0 1
        calc b ^ (k + 1) = b ^ k * b := pow_succ _ _
          _ ≤ (u k * a ^ (k - 1)) * b := mul_le_mul_of_nonneg_right ih' hb0
          _ = (u k * b) * a ^ (k - 1) := by ring
          _ ≤ (u (k + 1) * a) * a ^ (k - 1) :=
              mul_le_mul_of_nonneg_right hs (pow_nonneg (hu0 0) _)
          _ = u (k + 1) * a ^ (k + 1 - 1) := by
              rw [show k + 1 - 1 = (k - 1) + 1 by omega, pow_succ]; ring
  have hterm : ∀ T : Finset (Fin n), b ^ T.card * a ^ (n - T.card) ≤ a ^ (n - 1) * P T := by
    intro T
    rw [hPu]
    have hTn : T.card ≤ n := by simpa using T.card_le_univ
    rcases Nat.eq_zero_or_pos T.card with h0 | hpos
    · rw [h0]
      simp only [pow_zero, one_mul, Nat.sub_zero]
      rw [← ha, ← pow_succ, show n - 1 + 1 = n by omega]
    · have := hind T.card hpos hTn
      calc b ^ T.card * a ^ (n - T.card) ≤ (u T.card * a ^ (T.card - 1)) * a ^ (n - T.card) :=
            mul_le_mul_of_nonneg_right this (pow_nonneg (hu0 0) _)
        _ = a ^ (n - 1) * u T.card := by
            rw [mul_assoc, ← pow_add, show T.card - 1 + (n - T.card) = n - 1 by omega]; ring
  -- total mass
  have hsum : ∑ T : Finset (Fin n), P T ≤ 1 := by
    have hU : μ (⋃ T ∈ (Finset.univ : Finset (Finset (Fin n))), E p T) =
        ∑ T ∈ (Finset.univ : Finset (Finset (Fin n))), μ (E p T) :=
      measure_biUnion_finset (fun T _ T' _ h => E_disj p h) (fun T _ => measurableSet_E p T)
    have h1 : ∑ T : Finset (Fin n), μ (E p T) ≤ 1 := by
      rw [← hU]; exact prob_le_one
    have h2 := ENNReal.toReal_mono ENNReal.one_ne_top h1
    rwa [ENNReal.toReal_sum (fun T _ => measure_ne_top _ _), ENNReal.toReal_one] at h2
  have hbin : (b + a) ^ n ≤ a ^ (n - 1) := by
    rw [← Fin.sum_pow_mul_eq_add_pow]
    calc ∑ s : Finset (Fin n), b ^ s.card * a ^ (n - s.card)
        ≤ ∑ s : Finset (Fin n), a ^ (n - 1) * P s := Finset.sum_le_sum fun T _ => hterm T
      _ = a ^ (n - 1) * ∑ s : Finset (Fin n), P s := by rw [Finset.mul_sum]
      _ ≤ a ^ (n - 1) * 1 := mul_le_mul_of_nonneg_left hsum (pow_nonneg (hu0 0) _)
      _ = a ^ (n - 1) := mul_one _
  -- identify `F1` and `F1k`
  have hnemp : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hF1 : F1 μ p = a := by
    simp only [F1, ha, hu, hP]
    congr 2
    ext v
    simp only [Set.mem_setOf_eq, top, E, Tk]
    rw [ciSup_le_iff (Finite.bddAbove_range _)]
    simp [not_lt]
  set l : Fin n := ⟨n - 1, by omega⟩ with hl
  have hF1k : F1k (n - 1) μ p = b + a := by
    have hset : {u : Fin n → ℝ | ∀ i : Fin n, (i : ℕ) < n - 1 → u i ≤ p} =
        E p {l} ∪ E p ∅ := by
      ext v
      simp only [Set.mem_setOf_eq, Set.mem_union, E, Finset.mem_singleton,
        Finset.notMem_empty, iff_false, not_lt]
      constructor
      · intro hv
        by_cases hvl : p < v l
        · left
          intro i
          constructor
          · intro hi
            by_contra hne
            have : (i : ℕ) < n - 1 := by
              have := i.2
              have hne' : (i : ℕ) ≠ n - 1 := fun h => hne (Fin.ext h)
              omega
            exact absurd (hv i this) (not_le.mpr hi)
          · rintro rfl; exact hvl
        · right
          intro i
          by_cases hi : (i : ℕ) < n - 1
          · exact hv i hi
          · have : i = l := Fin.ext (by have := i.2; simp [l]; omega)
            rw [this]; exact not_lt.mp hvl
      · rintro (h | h) i hi
        · have hne : i ≠ l := fun h' => by rw [h'] at hi; simp [l] at hi
          exact not_lt.mp fun hc => hne ((h i).mp hc)
        · exact h i
    have hd : Disjoint (E p {l}) (E p ∅) := E_disj p (Finset.singleton_ne_empty l)
    simp only [F1k]
    rw [hset, measure_union hd (measurableSet_E _ _),
      ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    have e1 : (μ (E p {l})).toReal = b := by
      show P {l} = b; rw [hPu]; simp [hb]
    have e2 : (μ (E p ∅)).toReal = a := by
      show P ∅ = a; rw [hPu]; simp [ha]
    rw [e1, e2]
  rw [hF1, hF1k]
  -- conclude with real powers
  have hab0 : 0 ≤ b + a := add_nonneg (hu0 1) (hu0 0)
  have ha0 : 0 ≤ a := hu0 0
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hc : (0 : ℝ) ≤ 1 / ((n : ℝ) * ((n : ℝ) - 1)) := by positivity
  have h1 : (b + a) ^ (1 / ((n : ℝ) - 1)) = ((b + a) ^ n) ^ (1 / ((n : ℝ) * ((n : ℝ) - 1))) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hab0]
    congr 1
    field_simp
  have h2 : a ^ (1 / (n : ℝ)) = (a ^ (n - 1)) ^ (1 / ((n : ℝ) * ((n : ℝ) - 1))) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha0]
    congr 1
    rw [Nat.cast_sub (by omega)]
    push_cast
    field_simp
  rw [h1, h2]
  exact Real.rpow_le_rpow (pow_nonneg hab0 _) hbin hc
