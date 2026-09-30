-- Prove2me | solution 1 for UnderstandingML.erm_finite_class_bound
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T12:41:23.059183+00:00
-- url     : https://prove2.me/submissions/6f0de11e-5bd3-471b-9f41-41b881b17760

import Definitions.Def_UnderstandingML_Framework

open MeasureTheory UnderstandingML

theorem solution {X : Type*} [MeasurableSpace X] (H : Finset (X → Bool))
    (hH : ∀ h ∈ H, Measurable h) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1) (m : ℕ)
    (hm : Real.log (H.card / δ) / ε ≤ m) (D : Measure X) [IsProbabilityMeasure D] (f : X → Bool)
    (hf : Measurable f) (hreal : Realizable (↑H) D f) :
    iidLaw (labeledLaw D f) m {S | ∃ h, IsERM loss01 (↑H) S h ∧ ε < trueError D f h} ≤
      ENNReal.ofReal δ := by
  classical
  obtain ⟨hs, hsH, hs0⟩ := hreal
  have hsH' : hs ∈ H := hsH
  have hD0 : D {x | hs x ≠ f x} = 0 := by
    unfold trueError at hs0
    rw [ENNReal.toReal_eq_zero_iff] at hs0
    exact hs0.resolve_right (measure_ne_top _ _)
  have hcard : (0 : ℝ) < H.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨hs, hsH'⟩
  have hgmeas : Measurable (fun x : X ↦ (x, f x)) := measurable_id.prodMk hf
  haveI : IsProbabilityMeasure (labeledLaw D f) :=
    Measure.isProbabilityMeasure_map hgmeas.aemeasurable
  -- the good set of `h`
  let G : (X → Bool) → Set (X × Bool) := fun h ↦ {z | h z.1 = z.2}
  have hGmeas : ∀ h ∈ H, MeasurableSet (G h) := fun h hh ↦
    measurableSet_eq_fun ((hH h hh).comp measurable_fst) measurable_snd
  have hμG : ∀ h ∈ H, labeledLaw D f (G h) = D {x | h x = f x} := by
    intro h hh
    unfold labeledLaw
    rw [Measure.map_apply hgmeas (hGmeas h hh)]
    rfl
  -- the null set where `hs` makes a mistake
  let N : Set (Fin m → X × Bool) := ⋃ i, (fun S ↦ S i) ⁻¹' (G hs)ᶜ
  have hN : iidLaw (labeledLaw D f) m N = 0 := by
    apply measure_iUnion_null
    intro i
    unfold iidLaw
    apply Measure.pi_eval_preimage_null
    have : labeledLaw D f (G hs)ᶜ = D {x | hs x ≠ f x} := by
      unfold labeledLaw
      rw [Measure.map_apply hgmeas (hGmeas hs hsH').compl]
      rfl
    rw [this, hD0]
  let Hb := H.filter (fun h ↦ ε < trueError D f h)
  have hsub : {S : Fin m → X × Bool | ∃ h, IsERM loss01 (↑H) S h ∧ ε < trueError D f h} ⊆
      N ∪ ⋃ h ∈ Hb, Set.pi Set.univ (fun _ ↦ G h) := by
    rintro S ⟨h, ⟨hh, herm⟩, hεh⟩
    by_cases hSN : S ∈ N
    · exact Or.inl hSN
    right
    simp only [N, Set.mem_iUnion, Set.mem_preimage, Set.mem_compl_iff, not_exists,
      not_not] at hSN
    have hsz : empRisk loss01 S hs = 0 := by
      unfold empRisk
      have : ∀ i, loss01 hs (S i) = 0 := fun i ↦ by
        have := hSN i
        simp only [G, Set.mem_setOf_eq] at this
        simp [loss01, this]
      simp [this]
    have hle : empRisk loss01 S h ≤ 0 := hsz ▸ herm hs hsH'
    simp only [Set.mem_iUnion, Set.mem_pi, Set.mem_univ, true_implies]
    refine ⟨h, Finset.mem_filter.mpr ⟨hh, hεh⟩, fun i ↦ ?_⟩
    have hm0 : (0 : ℝ) < m := by exact_mod_cast Fin.pos i
    unfold empRisk at hle
    rw [div_le_iff₀ hm0, zero_mul] at hle
    have hnn : ∀ j ∈ Finset.univ, 0 ≤ loss01 h (S j) := fun j _ ↦ by
      unfold loss01; split_ifs <;> norm_num
    have hi := Finset.single_le_sum hnn (Finset.mem_univ i)
    show h (S i).1 = (S i).2
    by_contra hne
    have : loss01 h (S i) = 1 := by simp [loss01, hne]
    linarith
  -- the per-hypothesis bound
  have hexp : Real.exp (-(ε * m)) ≤ δ / H.card := by
    have h1 : Real.log (H.card / δ) ≤ ε * m := by
      rw [div_le_iff₀ hε] at hm; linarith
    have h2 : (H.card : ℝ) / δ ≤ Real.exp (ε * m) :=
      (Real.log_le_iff_le_exp (div_pos hcard hδ)).mp h1
    rw [Real.exp_neg, le_div_iff₀ hcard]
    rw [div_le_iff₀ hδ] at h2
    have hpos := Real.exp_pos (ε * m)
    calc (Real.exp (ε * m))⁻¹ * H.card ≤ (Real.exp (ε * m))⁻¹ * (δ * Real.exp (ε * m)) := by
          gcongr
          linarith
      _ = δ := by field_simp
  have hbound : ∀ h ∈ Hb, iidLaw (labeledLaw D f) m (Set.pi Set.univ (fun _ ↦ G h)) ≤
      ENNReal.ofReal (δ / H.card) := by
    intro h hhb
    obtain ⟨hh, hεh⟩ := Finset.mem_filter.mp hhb
    unfold iidLaw
    rw [Measure.pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hμG h hh]
    have hmeasne : MeasurableSet {x | h x ≠ f x} :=
      (measurableSet_eq_fun (hH h hh) hf).compl
    have hcompl : D {x | h x = f x} = 1 - D {x | h x ≠ f x} := by
      rw [← prob_compl_eq_one_sub hmeasne]
      congr 1; ext x; simp
    have hle1 : trueError D f h ≤ 1 := by
      unfold trueError
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
    have hreal : (D {x | h x = f x}).toReal = 1 - trueError D f h := by
      rw [hcompl, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top]
      simp [trueError]
    have hp : D {x | h x = f x} ≤ ENNReal.ofReal (1 - ε) := by
      rw [← ENNReal.ofReal_toReal (measure_ne_top D {x | h x = f x}), hreal]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    have hε1 : 0 ≤ 1 - ε := by linarith
    calc D {x | h x = f x} ^ m ≤ ENNReal.ofReal (1 - ε) ^ m := by gcongr
      _ = ENNReal.ofReal ((1 - ε) ^ m) := (ENNReal.ofReal_pow hε1 m).symm
      _ ≤ ENNReal.ofReal (Real.exp (-(ε * m))) := by
          apply ENNReal.ofReal_le_ofReal
          calc (1 - ε) ^ m ≤ Real.exp (-ε) ^ m := by
                gcongr
                linarith [Real.add_one_le_exp (-ε)]
            _ = Real.exp (-(ε * m)) := by
                rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ ENNReal.ofReal (δ / H.card) := ENNReal.ofReal_le_ofReal hexp
  calc iidLaw (labeledLaw D f) m {S | ∃ h, IsERM loss01 (↑H) S h ∧ ε < trueError D f h}
      ≤ iidLaw (labeledLaw D f) m (N ∪ ⋃ h ∈ Hb, Set.pi Set.univ (fun _ ↦ G h)) :=
        measure_mono hsub
    _ ≤ iidLaw (labeledLaw D f) m N +
        iidLaw (labeledLaw D f) m (⋃ h ∈ Hb, Set.pi Set.univ (fun _ ↦ G h)) :=
        measure_union_le _ _
    _ = iidLaw (labeledLaw D f) m (⋃ h ∈ Hb, Set.pi Set.univ (fun _ ↦ G h)) := by
        rw [hN, zero_add]
    _ ≤ ∑ h ∈ Hb, iidLaw (labeledLaw D f) m (Set.pi Set.univ (fun _ ↦ G h)) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _h ∈ Hb, ENNReal.ofReal (δ / H.card) := Finset.sum_le_sum hbound
    _ ≤ ∑ _h ∈ H, ENNReal.ofReal (δ / H.card) :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = ENNReal.ofReal δ := by
        rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 1
        field_simp
