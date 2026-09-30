-- Prove2me | solution 1 for UnderstandingML.mdl_bound
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T14:09:24.556188+00:00
-- url     : https://prove2.me/submissions/9a52d3aa-bb29-4444-882a-d4dc1cc1ad5b

import Definitions.Def_UnderstandingML_Nonuniform
import Theorems.Thm_UnderstandingML_hoeffding_inequality
import Theorems.Thm_UnderstandingML_kraft_inequality

open MeasureTheory

namespace UnderstandingML

/-- A prefix-free description language is injective on its class. -/
theorem mdlAux_injOn {Hyp : Type*} {H : Set Hyp} {d : Hyp → List Bool} (hpf : PrefixFreeOn H d) :
    Set.InjOn d H := by
  intro h hh h' hh' heq
  by_contra hne
  exact hpf h hh h' hh' hne (heq ▸ List.prefix_refl _)

/-- `e^{-n} ≤ 2^{-n}`. -/
theorem mdlAux_exp_neg_le (n : ℕ) : Real.exp (-(n : ℝ)) ≤ (1 / 2 : ℝ) ^ n := by
  have he : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  have h1 : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg]
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) he
  calc Real.exp (-(n : ℝ)) = Real.exp (-1) ^ n := by
        rw [← Real.exp_nat_mul]; ring_nf
    _ ≤ (1 / 2 : ℝ) ^ n := pow_le_pow_left₀ (Real.exp_pos _).le h1 n

/-- **Theorem 7.7** for `δ < 1`. -/
theorem mdlAux_bound {Z : Type*} [MeasurableSpace Z] {Hyp : Type*} (loss : Hyp → Z → ℝ)
    (H : Set Hyp) (hmeas : ∀ h ∈ H, Measurable (loss h))
    (hrange : ∀ h ∈ H, ∀ z, loss h z ∈ Set.Icc (0 : ℝ) 1) (d : Hyp → List Bool)
    (hpf : PrefixFreeOn H d) (m : ℕ) (hm : 0 < m) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (D : Measure Z) [IsProbabilityMeasure D] :
    iidLaw D m {S | ∃ h ∈ H,
        empRisk loss S h + Real.sqrt (((d h).length + Real.log (2 / δ)) / (2 * m)) <
          risk loss D h} ≤ ENNReal.ofReal δ := by
  have hinj := mdlAux_injOn hpf
  have hHc : H.Countable := Set.MapsTo.countable_of_injOn (Set.mapsTo_univ d H) hinj
    Set.countable_univ
  have hL : 0 < Real.log (2 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ]; linarith)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set t : Hyp → ℝ := fun h => Real.sqrt (((d h).length + Real.log (2 / δ)) / (2 * m)) with ht
  set E : Hyp → Set (Fin m → Z) := fun h =>
    {S | t h < |(∑ i, loss h (S i)) / m - ∫ x, loss h x ∂D|}
  have hsub : {S : Fin m → Z | ∃ h ∈ H,
        empRisk loss S h + Real.sqrt (((d h).length + Real.log (2 / δ)) / (2 * m)) <
          risk loss D h} ⊆ ⋃ h ∈ H, E h := by
    rintro S ⟨h, hh, hlt⟩
    refine Set.mem_biUnion hh ?_
    simp only [E, Set.mem_setOf_eq]
    simp only [empRisk, risk] at hlt
    rw [abs_sub_comm]
    exact lt_of_lt_of_le (by linarith) (le_abs_self _)
  have hE : ∀ h ∈ H, iidLaw D m (E h) ≤ ENNReal.ofReal (δ * (1 / 2 : ℝ) ^ (d h).length) := by
    intro h hh
    have htpos : 0 < t h := Real.sqrt_pos.2 (by positivity)
    have hab : ∀ᵐ z ∂D, (0 : ℝ) ≤ loss h z ∧ loss h z ≤ 1 := Filter.Eventually.of_forall
      fun z => hrange h hh z
    refine (hoeffding_inequality D (loss h) (hmeas h hh) hab m htpos).trans ?_
    apply ENNReal.ofReal_le_ofReal
    have hsq : t h ^ 2 = ((d h).length + Real.log (2 / δ)) / (2 * m) :=
      Real.sq_sqrt (by positivity)
    have hexp : 2 * (m : ℝ) * t h ^ 2 / (1 - 0) ^ 2 = (d h).length + Real.log (2 / δ) := by
      rw [hsq]; norm_num; field_simp
    rw [hexp, neg_add, Real.exp_add, Real.exp_neg (Real.log _), Real.exp_log (by positivity)]
    have := mdlAux_exp_neg_le (d h).length
    have e2 : 2 * (Real.exp (-((d h).length : ℝ)) * (2 / δ)⁻¹) =
        δ * Real.exp (-((d h).length : ℝ)) := by field_simp
    rw [e2]
    exact mul_le_mul_of_nonneg_left this hδ.le
  have hkraft : ∀ s : Finset H, ∑ h ∈ s, (1 / 2 : ℝ) ^ (d h).length ≤ 1 := by
    intro s
    have hinj' : Set.InjOn (fun h : H => d h) (s : Set H) := fun a _ b _ hab =>
      Subtype.ext (hinj a.2 b.2 hab)
    rw [← Finset.sum_image (f := fun σ => (1 / 2 : ℝ) ^ σ.length) hinj']
    refine kraft_inequality (d '' H) ?_ _ ?_
    · rintro _ ⟨h, hh, rfl⟩ _ ⟨h', hh', rfl⟩ hne
      exact hpf h hh h' hh' (fun heq => hne (heq ▸ rfl))
    · intro σ hσ
      obtain ⟨h, -, rfl⟩ := Finset.mem_image.1 hσ
      exact ⟨h, h.2, rfl⟩
  calc iidLaw D m _ ≤ iidLaw D m (⋃ h ∈ H, E h) := measure_mono hsub
    _ ≤ ∑' h : H, iidLaw D m (E h) := measure_biUnion_le _ hHc _
    _ ≤ ∑' h : H, ENNReal.ofReal (δ * (1 / 2 : ℝ) ^ (d h).length) :=
        ENNReal.tsum_le_tsum fun h => hE h h.2
    _ ≤ ENNReal.ofReal δ := by
      rw [ENNReal.tsum_eq_iSup_sum]
      refine iSup_le fun s => ?_
      rw [← ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity, ← Finset.mul_sum]
      refine ENNReal.ofReal_le_ofReal ?_
      calc δ * ∑ h ∈ s, (1 / 2 : ℝ) ^ (d h).length ≤ δ * 1 :=
            mul_le_mul_of_nonneg_left (hkraft s) hδ.le
        _ = δ := mul_one δ

end UnderstandingML

/-- **Theorem 7.7** (p. 90). -/
theorem solution {Z : Type*} [MeasurableSpace Z] {Hyp : Type*} (loss : Hyp → Z → ℝ)
    (H : Set Hyp) (hmeas : ∀ h ∈ H, Measurable (loss h))
    (hrange : ∀ h ∈ H, ∀ z, loss h z ∈ Set.Icc (0 : ℝ) 1) (d : Hyp → List Bool)
    (hpf : UnderstandingML.PrefixFreeOn H d) (m : ℕ) (hm : 0 < m) {δ : ℝ} (hδ : 0 < δ)
    (D : MeasureTheory.Measure Z) [MeasureTheory.IsProbabilityMeasure D] :
    UnderstandingML.iidLaw D m {S | ∃ h ∈ H,
        UnderstandingML.empRisk loss S h +
          Real.sqrt (((d h).length + Real.log (2 / δ)) / (2 * m)) <
          UnderstandingML.risk loss D h} ≤ ENNReal.ofReal δ := by
  rcases lt_or_ge δ 1 with hδ1 | hδ1
  · exact UnderstandingML.mdlAux_bound loss H hmeas hrange d hpf m hm hδ hδ1 D
  · calc _ ≤ UnderstandingML.iidLaw D m Set.univ := MeasureTheory.measure_mono (Set.subset_univ _)
      _ = 1 := by
        haveI : MeasureTheory.IsProbabilityMeasure (UnderstandingML.iidLaw D m) := by
          unfold UnderstandingML.iidLaw; infer_instance
        exact MeasureTheory.measure_univ
      _ ≤ ENNReal.ofReal δ := by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hδ1
