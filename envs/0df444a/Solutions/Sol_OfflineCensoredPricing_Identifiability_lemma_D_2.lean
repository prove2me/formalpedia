-- Prove2me | solution 1 for OfflineCensoredPricing.Identifiability.lemma_D_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T17:46:19.359804+00:00
-- url     : https://prove2.me/submissions/cbb477b3-adb2-4921-8bc9-ef519865b705

import Mathlib
import Definitions.Def_OfflineCensoredPricing_Identifiability_Model
import Definitions.Def_OfflineCensoredPricing_Identifiability_D2ACD
import Theorems.Thm_UnderstandingML_hoeffding_inequality

open MeasureTheory Set OfflineCensoredPricing.Identifiability

namespace OCPLemD2Aux

/-- `|sup a − sup b| ≤ α` whenever `|aᵢ − bᵢ| ≤ α` for all `i` (finite nonempty index). -/
lemma abs_iSup_sub_le {K : ℕ} [Nonempty (Fin K)] (a b : Fin K → ℝ) (α : ℝ)
    (h : ∀ i, |a i - b i| ≤ α) : |(⨆ i, a i) - ⨆ i, b i| ≤ α := by
  have ha : BddAbove (Set.range a) := Finite.bddAbove_range a
  have hb : BddAbove (Set.range b) := Finite.bddAbove_range b
  rw [abs_le]
  constructor
  · have : (⨆ i, b i) ≤ (⨆ i, a i) + α := ciSup_le (fun i => by
      have := (abs_le.1 (h i)).1
      linarith [le_ciSup ha i])
    linarith
  · have : (⨆ i, a i) ≤ (⨆ i, b i) + α := ciSup_le (fun i => by
      have := (abs_le.1 (h i)).2
      linarith [le_ciSup hb i])
    linarith

lemma gam_eq_iSup {K : ℕ} [Nonempty (Fin K)] (I : Instance K) [IsProbabilityMeasure I.μξ] :
    gam I = ⨆ i, gammaI I i := by
  obtain ⟨i0, hi0⟩ := exists_eq_ciSup_of_finite (f := fun i => I.yh i + I.b * I.p i)
  have hg : gam I = gammaI I i0 := by
    unfold gam gammaI lam; rw [← hi0]
  rw [hg]
  apply le_antisymm
  · exact le_ciSup (Finite.bddAbove_range _) i0
  · refine ciSup_le (fun i => ?_)
    unfold gammaI
    apply measureReal_mono (Iio_subset_Iio _)
    rw [hi0]
    exact le_ciSup (Finite.bddAbove_range (fun i => I.yh i + I.b * I.p i)) i

end OCPLemD2Aux

open OCPLemD2Aux in
theorem solution {K : ℕ} (I : Instance K) (hI : I.Standing) (Nv : Fin K → ℕ) {α : ℝ}
    (hα : 0 < α) :
    dataLaw I Nv {ω | α < |gammaHatMax I.toPublic (sales I ω) - gam I|} ≤
      ENNReal.ofReal (2 * K * Real.exp (-(2 * (Nmin Nv : ℝ) * α ^ 2))) := by
  obtain ⟨hP, -, -, -, -, -, -, hK, -⟩ := hI
  haveI := hP
  haveI : Nonempty (Fin K) := ⟨⟨0, by omega⟩⟩
  -- reduce to a single price index
  have hsub : {ω : Sample K Nv | α < |gammaHatMax I.toPublic (sales I ω) - gam I|} ⊆
      ⋃ i, {ω : Sample K Nv | α < |gammaHat I.toPublic (sales I ω) i - gammaI I i|} := by
    intro ω hω
    by_contra h
    simp only [mem_iUnion, mem_setOf_eq, not_exists, not_lt] at h
    have := abs_iSup_sub_le _ _ α h
    simp only [mem_setOf_eq] at hω
    unfold gammaHatMax at hω
    rw [gam_eq_iSup I] at hω
    linarith
  -- each index: Hoeffding
  have hone : ∀ i, dataLaw I Nv
      {ω : Sample K Nv | α < |gammaHat I.toPublic (sales I ω) i - gammaI I i|} ≤
      ENNReal.ofReal (2 * Real.exp (-(2 * (Nmin Nv : ℝ) * α ^ 2))) := by
    intro i
    set c := I.yh i + I.b * I.p i with hc
    set θ : ℝ → ℝ := (Iio c).indicator (fun _ => 1) with hθ
    have hθm : Measurable θ := measurable_const.indicator measurableSet_Iio
    have hab : ∀ᵐ x ∂I.μξ, (0 : ℝ) ≤ θ x ∧ θ x ≤ 1 := Filter.Eventually.of_forall (fun x => by
      simp only [hθ, indicator]; split_ifs <;> norm_num)
    have hmean : ∫ x, θ x ∂I.μξ = gammaI I i := by
      rw [hθ, integral_indicator_const _ measurableSet_Iio, smul_eq_mul, mul_one]; rfl
    have hH := UnderstandingML.hoeffding_inequality I.μξ θ hθm hab (Nv i) hα
    rw [hmean] at hH
    -- the event is the preimage of Hoeffding's event under the `i`-th coordinate
    have hset : {ω : Sample K Nv | α < |gammaHat I.toPublic (sales I ω) i - gammaI I i|} =
        (fun ω : Sample K Nv => ω i) ⁻¹'
          {x : Fin (Nv i) → ℝ | α < |(∑ j, θ (x j)) / (Nv i : ℝ) - gammaI I i|} := by
      ext ω
      simp only [mem_setOf_eq, mem_preimage]
      have : gammaHat I.toPublic (sales I ω) i = (∑ j, θ (ω i j)) / (Nv i : ℝ) := by
        unfold gammaHat
        congr 1
        rw [Finset.natCast_card_filter]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        simp only [hθ, indicator, mem_Iio, sales]
        have e : (min (ω i j - I.b * I.p i) (I.yh i) < I.yh i) ↔ ω i j < c := by
          rw [min_lt_iff]; constructor
          · rintro (h | h)
            · rw [hc]; linarith
            · exact absurd h (lt_irrefl _)
          · intro h; left; rw [hc] at h; linarith
        by_cases h : ω i j < c
        · have h' := e.2 h
          simp [h, h']
        · have h' : ¬ (min (ω i j - I.b * I.p i) (I.yh i) < I.yh i) := fun h' => h (e.1 h')
          simp [h, h']
      rw [this]
    have hmp : MeasurePreserving (Function.eval i) (dataLaw I Nv)
        (Measure.pi (fun _ : Fin (Nv i) => I.μξ)) := by
      unfold dataLaw
      exact measurePreserving_eval _ i
    rw [hset]
    refine le_trans (le_of_eq ?_) (le_trans hH ?_)
    · -- pushforward along the coordinate map
      rw [show (fun ω : Sample K Nv => ω i) = Function.eval i from rfl]
      have hmeas : Measurable (fun x : Fin (Nv i) → ℝ =>
          |(∑ j, θ (x j)) / (Nv i : ℝ) - gammaI I i|) := by
        have : Measurable (fun x : Fin (Nv i) → ℝ => ∑ j, θ (x j)) :=
          Finset.measurable_sum _ (fun j _ => hθm.comp (measurable_pi_apply j))
        exact ((this.div_const _).sub_const _).abs
      exact hmp.measure_preimage (measurableSet_lt measurable_const hmeas).nullMeasurableSet
    · apply ENNReal.ofReal_le_ofReal
      have hNi : (Nmin Nv : ℝ) ≤ Nv i := by
        exact_mod_cast ciInf_le (Finite.bddBelow_range Nv) i
      have : Real.exp (-(2 * (Nv i : ℝ) * α ^ 2 / (1 - 0) ^ 2)) ≤
          Real.exp (-(2 * (Nmin Nv : ℝ) * α ^ 2)) := by
        apply Real.exp_le_exp.2
        rw [sub_zero, one_pow, div_one]
        nlinarith [sq_nonneg α]
      linarith
  calc dataLaw I Nv {ω | α < |gammaHatMax I.toPublic (sales I ω) - gam I|}
      ≤ dataLaw I Nv (⋃ i, {ω : Sample K Nv |
          α < |gammaHat I.toPublic (sales I ω) i - gammaI I i|}) := measure_mono hsub
    _ ≤ ∑ i, dataLaw I Nv {ω : Sample K Nv |
          α < |gammaHat I.toPublic (sales I ω) i - gammaI I i|} := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : Fin K, ENNReal.ofReal (2 * Real.exp (-(2 * (Nmin Nv : ℝ) * α ^ 2))) :=
        Finset.sum_le_sum (fun i _ => hone i)
    _ = ENNReal.ofReal (2 * K * Real.exp (-(2 * (Nmin Nv : ℝ) * α ^ 2))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring
