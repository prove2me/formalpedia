-- Prove2me | solution 1 for UnderstandingML.bad_erm_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T20:24:34.72713+00:00
-- url     : https://prove2.me/submissions/60a3bce9-6687-4fb1-a128-5ecc5aa8bee8

import Definitions.Def_UnderstandingML_MulticlassLearnability

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

namespace BadERMAux

variable {X : Type*}

lemma hSet_ne_none_iff (A : {A : Set X // A.Finite ∨ Aᶜ.Finite}) (x : X) :
    hSet A x ≠ none ↔ x ∈ A.1 := by
  unfold hSet
  split_ifs with h <;> simp [h]

lemma hSet_empty (x : X) : hSet (⟨∅, Or.inl Set.finite_empty⟩ : {A : Set X // A.Finite ∨ Aᶜ.Finite}) x = none := by
  unfold hSet
  simp

lemma badDist_apply [MeasurableSpace X] [MeasurableSingletonClass X] [Fintype X] [DecidableEq X]
    (x₀ : X) (ε : ℝ) (E : Set X) [DecidablePred (· ∈ E)] :
    badDist x₀ ε E = ENNReal.ofReal (1 - 2 * ε) * E.indicator 1 x₀ +
      ENNReal.ofReal (2 * ε / (Fintype.card X - 1)) *
        (((Finset.univ.erase x₀).filter (· ∈ E)).card : ENNReal) := by
  simp only [badDist, Measure.add_apply, Measure.smul_apply, smul_eq_mul, Measure.dirac_apply,
    Measure.coe_finset_sum, Finset.sum_apply]
  congr 2
  rw [Finset.natCast_card_filter]
  refine Finset.sum_congr (by congr!) fun x _ ↦ ?_
  by_cases hx : x ∈ E <;> simp [hx]

end BadERMAux

end UnderstandingML

open UnderstandingML
open UnderstandingML.BadERMAux in
theorem solution {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    [Fintype X] (hX : 2 ≤ Fintype.card X) (x₀ : X)
    (A : Learner (X × CofinLabel X) (X → CofinLabel X)) (hA : IsBadERM A) (ε : ℝ) (hε : 0 < ε)
    (hε2 : ε < 1 / 2) (m : ℕ) (hm : (m : ℝ) ≤ (Fintype.card X - 1) / (6 * ε)) :
    ENNReal.ofReal (Real.exp (-1) / 6) ≤
      iidLaw ((badDist x₀ ε).map (fun x ↦ (x, hSet ⟨∅, Or.inl Set.finite_empty⟩ x))) m
        {S | ENNReal.ofReal ε ≤ badDist x₀ ε {x | A m S x ≠ hSet ⟨∅, Or.inl Set.finite_empty⟩ x}} := by
  classical
  set n := Fintype.card X with hn
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hX
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  set c : ℝ := 2 * ε / (n - 1) with hc
  have hcpos : 0 < c := div_pos (by linarith) hn1
  have hcn : c * ((n : ℝ) - 1) = 2 * ε := by rw [hc]; field_simp
  set P := badDist x₀ ε with hP
  have hcard : ((Finset.univ.erase x₀).card : ℝ) = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ← hn]
    push_cast [Nat.cast_sub (by omega : 1 ≤ n)]
    ring
  have hlight : P {x | x ≠ x₀} = ENNReal.ofReal (2 * ε) := by
    rw [hP, badDist_apply]
    have h1 : ({x | x ≠ x₀} : Set X).indicator 1 x₀ = (0 : ENNReal) := by simp
    rw [h1, Finset.filter_true_of_mem (fun x hx ↦ by simpa using Finset.ne_of_mem_erase hx),
      mul_zero, zero_add, ← hc]
    rw [show (((Finset.univ.erase x₀).card : ℕ) : ENNReal) =
      ENNReal.ofReal ((Finset.univ.erase x₀).card : ℝ) by rw [ENNReal.ofReal_natCast]]
    rw [← ENNReal.ofReal_mul hcpos.le, hcard, hcn]
  haveI hPprob : IsProbabilityMeasure P := by
    constructor
    have hsplit : (Set.univ : Set X) = {x₀} ∪ {x | x ≠ x₀} := by
      ext x; by_cases hx : x = x₀ <;> simp [hx]
    rw [hsplit, measure_union (by simp) (Set.toFinite _).measurableSet,
      hlight]
    have hx0 : P {x₀} = ENNReal.ofReal (1 - 2 * ε) := by
      rw [hP, badDist_apply]
      rw [Finset.filter_false_of_mem (fun x hx ↦ by simpa using Finset.ne_of_mem_erase hx)]
      simp
    rw [hx0, ← ENNReal.ofReal_add (by linarith) (by linarith)]
    simp
  set g : X → X × CofinLabel X := fun x ↦ (x, hSet ⟨∅, Or.inl Set.finite_empty⟩ x) with hg
  have hgm : Measurable g := measurable_of_finite g
  set ν := P.map g with hν
  haveI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hgm.aemeasurable
  set μ := iidLaw ν m with hμ
  haveI : IsProbabilityMeasure μ := by rw [hμ, iidLaw]; infer_instance
  -- samples carrying a label other than `∗` are null
  set G : Set (X × CofinLabel X) := {p | p.2 ≠ none} with hG
  have hGm : MeasurableSet G :=
    (show MeasurableSet {y : CofinLabel X | y ≠ none} from MeasurableSpace.measurableSet_top).preimage
      measurable_snd
  have hνG : ν G = 0 := by
    rw [hν, Measure.map_apply hgm hGm]
    have : g ⁻¹' G = ∅ := by ext x; simp [hG, hg, hSet_empty]
    rw [this, measure_empty]
  set BadLab : Set (Fin m → X × CofinLabel X) := ⋃ i, Function.eval i ⁻¹' G with hBadLab
  have hBadLab0 : μ BadLab = 0 :=
    measure_iUnion_null fun i ↦ Measure.pi_eval_preimage_null _ hνG
  -- the number of draws of light points
  set L : Set (X × CofinLabel X) := Prod.fst ⁻¹' {x | x ≠ x₀} with hL
  have hLm : MeasurableSet L := measurable_fst (measurableSet_singleton x₀).compl
  have hνL : ν L = ENNReal.ofReal (2 * ε) := by
    rw [hν, Measure.map_apply hgm hLm]
    exact hlight
  set cnt : (Fin m → X × CofinLabel X) → ENNReal :=
    fun S ↦ ∑ i, (Function.eval i ⁻¹' L).indicator 1 S with hcnt
  have hcnt_eq : ∀ S, cnt S = (((Finset.univ : Finset (Fin m)).filter
      (fun i ↦ (S i).1 ≠ x₀)).card : ENNReal) := by
    intro S
    rw [hcnt, Finset.natCast_card_filter]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    by_cases h : (S i).1 = x₀ <;> simp [hL, h]
  have hmeas_i : ∀ i : Fin m, MeasurableSet (Function.eval i ⁻¹' L) :=
    fun i ↦ (show Measurable (Function.eval i : (Fin m → X × CofinLabel X) → X × CofinLabel X)
      from measurable_pi_apply i) hLm
  have hint : ∫⁻ S, cnt S ∂μ = m * ENNReal.ofReal (2 * ε) := by
    rw [hcnt]
    simp only
    rw [lintegral_finset_sum _ (fun i _ ↦ (measurable_one.indicator (hmeas_i i)))]
    have : ∀ i : Fin m, ∫⁻ S, (Function.eval i ⁻¹' L).indicator 1 S ∂μ = ENNReal.ofReal (2 * ε) := by
      intro i
      rw [lintegral_indicator_one (hmeas_i i), hμ, iidLaw,
        (measurePreserving_eval (fun _ : Fin m ↦ ν) i).measure_preimage hLm.nullMeasurableSet,
        hνL]
    simp [this]
  -- Markov's inequality
  set t : ENNReal := ENNReal.ofReal (((n : ℝ) - 1) / 2) with ht
  have ht0 : t ≠ 0 := by rw [ht]; simp; linarith
  have httop : t ≠ ⊤ := ENNReal.ofReal_ne_top
  set Bad : Set (Fin m → X × CofinLabel X) := {S | t ≤ cnt S} with hBad
  have hMarkov : t * μ Bad ≤ m * ENNReal.ofReal (2 * ε) := by
    rw [← hint]
    exact mul_meas_ge_le_lintegral₀ (f := cnt)
      (Finset.measurable_sum _ fun i _ ↦ (measurable_one.indicator (hmeas_i i))).aemeasurable t
  have hBad23 : μ Bad ≤ ENNReal.ofReal (2 / 3) := by
    have h1 : (m : ENNReal) * ENNReal.ofReal (2 * ε) ≤ t * ENNReal.ofReal (2 / 3) := by
      rw [ht, ← ENNReal.ofReal_mul (by linarith),
        show (m : ENNReal) = ENNReal.ofReal m by rw [ENNReal.ofReal_natCast],
        ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      rw [le_div_iff₀ (by linarith)] at hm
      nlinarith
    have := hMarkov.trans h1
    exact (ENNReal.mul_le_mul_iff_right ht0 httop).1 this
  -- outside the two bad events the error is at least `ε`
  set T := {S : Fin m → X × CofinLabel X |
    ENNReal.ofReal ε ≤ P {x | A m S x ≠ hSet ⟨∅, Or.inl Set.finite_empty⟩ x}} with hT
  have hcompl : Tᶜ ⊆ BadLab ∪ Bad := by
    intro S hS
    by_contra hcon
    simp only [Set.mem_union, not_or] at hcon
    obtain ⟨hlab, hbad⟩ := hcon
    apply hS
    have hnone : ∀ i, (S i).2 = none := by
      intro i
      by_contra h
      exact hlab (Set.mem_iUnion.2 ⟨i, h⟩)
    have hcntlt : (((Finset.univ : Finset (Fin m)).filter
        (fun i ↦ (S i).1 ≠ x₀)).card : ℝ) < ((n : ℝ) - 1) / 2 := by
      have : cnt S < t := lt_of_not_ge hbad
      rw [hcnt_eq, ht, ← ENNReal.ofReal_natCast] at this
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).1 this
    show ENNReal.ofReal ε ≤ P {x | A m S x ≠ hSet ⟨∅, Or.inl Set.finite_empty⟩ x}
    rw [hA.2 m S hnone]
    set R : Set X := Set.range (fun i ↦ (S i).1) with hR
    have hE : {x | hSet ⟨Rᶜ, Or.inr (by rw [compl_compl]; exact Set.finite_range _)⟩ x ≠
        hSet ⟨∅, Or.inl Set.finite_empty⟩ x} = Rᶜ := by
      ext x
      rw [Set.mem_setOf_eq, hSet_empty, hSet_ne_none_iff]
    rw [hE, hP, badDist_apply]
    refine le_trans ?_ le_add_self
    -- count the light points missed by the sample
    set hit := (Finset.univ.erase x₀).filter (· ∈ R) with hhit
    set miss := (Finset.univ.erase x₀).filter (· ∈ Rᶜ) with hmiss
    have hsum : (hit.card : ℝ) + miss.card = n - 1 := by
      rw [← hcard, hhit, hmiss]
      have := Finset.card_filter_add_card_filter_not (s := Finset.univ.erase x₀)
        (fun x ↦ x ∈ R)
      exact_mod_cast this
    have hhitle : hit.card ≤ ((Finset.univ : Finset (Fin m)).filter
        (fun i ↦ (S i).1 ≠ x₀)).card := by
      have : hit ⊆ ((Finset.univ : Finset (Fin m)).filter (fun i ↦ (S i).1 ≠ x₀)).image
          (fun i ↦ (S i).1) := by
        intro x hx
        simp only [hhit, Finset.mem_filter, Finset.mem_erase, hR, Set.mem_range] at hx
        obtain ⟨⟨hx0, -⟩, i, hi⟩ := hx
        exact Finset.mem_image.2 ⟨i, by simp [hi, hx0], hi⟩
      exact (Finset.card_le_card this).trans Finset.card_image_le
    have hhitle' : (hit.card : ℝ) ≤ (((Finset.univ : Finset (Fin m)).filter
        (fun i ↦ (S i).1 ≠ x₀)).card : ℝ) := by exact_mod_cast hhitle
    have hmissge : ((n : ℝ) - 1) / 2 ≤ miss.card := by linarith
    rw [← hc, show ((miss.card : ℕ) : ENNReal) = ENNReal.ofReal (miss.card : ℝ) by
      rw [ENNReal.ofReal_natCast], ← ENNReal.ofReal_mul hcpos.le]
    apply ENNReal.ofReal_le_ofReal
    calc ε = c * (((n : ℝ) - 1) / 2) := by rw [mul_div_assoc', hcn]; ring
      _ ≤ c * miss.card := mul_le_mul_of_nonneg_left hmissge hcpos.le
  have hTc : μ Tᶜ ≤ ENNReal.ofReal (2 / 3) :=
    (measure_mono hcompl).trans ((measure_union_le _ _).trans (by rw [hBadLab0, zero_add]; exact hBad23))
  have hone : (1 : ENNReal) ≤ μ T + ENNReal.ofReal (2 / 3) := by
    calc (1 : ENNReal) = μ (T ∪ Tᶜ) := by rw [Set.union_compl_self, measure_univ]
      _ ≤ μ T + μ Tᶜ := measure_union_le _ _
      _ ≤ μ T + ENNReal.ofReal (2 / 3) := by gcongr
  have hT13 : ENNReal.ofReal (1 / 3) ≤ μ T := by
    have h := tsub_le_iff_right.2 hone
    have : (1 : ENNReal) - ENNReal.ofReal (2 / 3) = ENNReal.ofReal (1 / 3) := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by norm_num)]; norm_num
    rwa [this] at h
  refine le_trans ?_ hT13
  apply ENNReal.ofReal_le_ofReal
  have : Real.exp (-1) ≤ 1 := by
    rw [Real.exp_le_one_iff]; norm_num
  linarith
