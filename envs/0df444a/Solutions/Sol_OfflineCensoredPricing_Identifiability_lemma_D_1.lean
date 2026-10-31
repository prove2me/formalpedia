-- Prove2me | solution 1 for OfflineCensoredPricing.Identifiability.lemma_D_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T18:13:30.190381+00:00
-- url     : https://prove2.me/submissions/3012e45a-065e-48ac-990f-be3dffedaeca
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OfflineCensoredPricing_Identifiability_Model
import Definitions.Def_OfflineCensoredPricing_Identifiability_D2ACD
import Theorems.Thm_OfflineCensoredPricing_Identifiability_lemma_A_3

open MeasureTheory Set OfflineCensoredPricing.Identifiability

namespace OCPLemD1Aux

lemma mean_diff {n : ℕ} (hn : 0 < n) (x y : Fin n → ℝ) (c : ℝ) (h : ∀ j, |x j - y j| ≤ c) :
    |(∑ j, x j) / (n : ℝ) - (∑ j, y j) / (n : ℝ)| ≤ c := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hn', div_le_iff₀ hn']
  calc |∑ j, (x j - y j)| ≤ ∑ j, |x j - y j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin n, c := Finset.sum_le_sum (fun j _ => h j)
    _ = c * n := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

lemma integrable_min' (μ : Measure ℝ) [IsProbabilityMeasure μ] (m c y : ℝ)
    (hm : ∀ᵐ ξ ∂μ, m ≤ ξ) : Integrable (fun ξ => min (ξ - c) y) μ := by
  refine Integrable.of_bound (by fun_prop) (|y| + |m - c|) ?_
  filter_upwards [hm] with ξ hξ
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have : min (m - c) y ≤ min (ξ - c) y := min_le_min_right _ (by linarith)
    have h1 : -(|y| + |m - c|) ≤ min (m - c) y := by
      rcases min_cases (m - c) y with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;>
        linarith [neg_abs_le y, neg_abs_le (m - c), abs_nonneg y, abs_nonneg (m - c)]
    linarith
  · linarith [min_le_right (ξ - c) y, le_abs_self y, abs_nonneg (m - c)]

lemma coord_null {K : ℕ} (I : Instance K) (hP : IsProbabilityMeasure I.μξ) (Nv : Fin K → ℕ)
    (i : Fin K) (j : Fin (Nv i)) (s : Set ℝ) (hs : MeasurableSet s) (h0 : I.μξ s = 0) :
    dataLaw I Nv {ω : Sample K Nv | ω i j ∈ s} = 0 := by
  have h1 : MeasurePreserving (Function.eval i) (dataLaw I Nv)
      (Measure.pi (fun _ : Fin (Nv i) => I.μξ)) := by
    unfold dataLaw; exact measurePreserving_eval _ i
  have h2 : MeasurePreserving (Function.eval j) (Measure.pi (fun _ : Fin (Nv i) => I.μξ)) I.μξ :=
    measurePreserving_eval _ j
  have h3 := h2.comp h1
  have : {ω : Sample K Nv | ω i j ∈ s} = (Function.eval j ∘ Function.eval i) ⁻¹' s := rfl
  rw [this, h3.measure_preimage hs.nullMeasurableSet, h0]

end OCPLemD1Aux

open OCPLemD1Aux in
theorem solution {K : ℕ} [NeZero K] (I : Instance K) (hI : I.Standing) (Nv : Fin K → ℕ) {α : ℝ}
    (hα : 0 < α) :
    dataLaw I Nv {ω | ∃ q : ℝ, 0 ≤ q ∧
        q ≤ max (min (min (pTildeHat I.toPublic (sales I ω)) (pTilde I)) I.phi) 0 ∧
        3 * I.phi ^ 2 * |bHat I.toPublic (sales I ω) - I.b| + α <
          |RHat I.toPublic (sales I ω) q - RF I I.μξ q|} ≤
      ENNReal.ofReal (2 * K * Real.exp (-((Nmin Nv : ℝ) * α ^ 2 /
        ((I.y + I.bhi * I.phi) ^ 2 * I.phi ^ 2)))) := by
  have hP := hI.1
  haveI := hP
  haveI : IsProbabilityMeasure (dataLaw I Nv) := by unfold dataLaw; infer_instance
  have hplo := hI.2.2.1
  have hpb : 0 < I.phi := lt_trans hplo hI.2.2.2.1
  have hy := hI.2.1
  have hblo := hI.2.2.2.2.1
  have hbb := hI.2.2.2.2.2.1
  have hbbh := hI.2.2.2.2.2.2.1
  have hb : 0 < I.b := lt_of_lt_of_le hblo hbb
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne K)
  -- trivial case `N = 0`
  rcases Nat.eq_zero_or_pos (Nmin Nv) with hN0 | hNpos
  · rw [hN0]
    refine le_trans prob_le_one ?_
    rw [Nat.cast_zero, zero_mul, zero_div, neg_zero, Real.exp_zero, mul_one]
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hN : ∀ i, 0 < Nv i := fun i =>
    lt_of_lt_of_le hNpos (ciInf_le (Finite.bddBelow_range Nv) i)
  set ε := α / I.phi with hε
  have hεp : 0 < ε := by positivity
  set U := I.y + I.b * I.phi with hU
  have hU0 : 0 < U := by have := mul_pos hb hpb; linarith
  set f : ℝ → ℝ → ℝ := fun x p => min x (I.y + I.b * p) with hf
  set Y := Icc (0 : ℝ) I.phi with hY
  set A := ⋃ i, (Function.eval i) ⁻¹' {x : Fin (Nv i) → ℝ | ∃ p ∈ Y,
      ε < |(∑ j, f (x j) p) / (Nv i : ℝ) - ∫ z, f z p ∂I.μξ|} with hA
  set G := ⋃ i, ⋃ j : Fin (Nv i), {ω : Sample K Nv | ω i j ∈ Iio (I.b * I.phi)} with hG
  -- the inclusion
  have hsub : {ω | ∃ q : ℝ, 0 ≤ q ∧
        q ≤ max (min (min (pTildeHat I.toPublic (sales I ω)) (pTilde I)) I.phi) 0 ∧
        3 * I.phi ^ 2 * |bHat I.toPublic (sales I ω) - I.b| + α <
          |RHat I.toPublic (sales I ω) q - RF I I.μξ q|} ⊆ A ∪ G := by
    rintro ω ⟨q, hq0, hqM, hlt⟩
    by_contra hnot
    simp only [mem_union, not_or] at hnot
    obtain ⟨nA, nG⟩ := hnot
    have hG' : ∀ i j, I.b * I.phi ≤ ω i j := by
      intro i j; by_contra h; push_neg at h
      exact nG (mem_iUnion.2 ⟨i, mem_iUnion.2 ⟨j, h⟩⟩)
    have hAi : ∀ i, ∀ p ∈ Y, |(∑ j, f (ω i j) p) / (Nv i : ℝ) - ∫ z, f z p ∂I.μξ| ≤ ε := by
      intro i p hp; by_contra h; push_neg at h
      exact nA (mem_iUnion.2 ⟨i, ⟨p, hp, h⟩⟩)
    set S := sales I ω with hS
    set bh := bHat I.toPublic S with hbh
    have hbh0 : 0 < bh := lt_of_lt_of_le hblo (le_max_left _ _)
    -- `q = 0` is trivial
    rcases eq_or_lt_of_le hq0 with hq | hq
    · rw [← hq] at hlt
      have : RHat I.toPublic S 0 - RF I I.μξ 0 = 0 := by unfold RHat RF; ring
      rw [this, abs_zero] at hlt
      have : 0 ≤ 3 * I.phi ^ 2 * |bh - I.b| := by positivity
      linarith
    have hqM' : q ≤ min (min (pTildeHat I.toPublic S) (pTilde I)) I.phi := by
      rcases le_total (min (min (pTildeHat I.toPublic S) (pTilde I)) I.phi) 0 with h | h
      · rw [max_eq_right h] at hqM; linarith
      · rwa [max_eq_left h] at hqM
    have hqph : q ≤ pTildeHat I.toPublic S := le_trans hqM' (le_trans (min_le_left _ _)
      (min_le_left _ _))
    have hq1 : q ≤ I.phi := le_trans hqM' (min_le_right _ _)
    set i := iStar I.toPublic S with hi
    have hp := hI.2.2.2.2.2.2.2.2.2.1 i
    have hp0 : 0 ≤ I.p i := le_trans hplo.le hp.1
    -- `y ≤ yᵢ + b̂ (pᵢ − q)` from `q ≤ p̂~`
    have hyq : I.y ≤ I.yh i + bh * (I.p i - q) := by
      have := hqph
      unfold pTildeHat lamHat at this
      rw [le_div_iff₀ hbh0] at this
      rw [← hi, ← hbh] at this
      nlinarith
    -- the empirical mean versus the mean of `f(ξʲ, q)`
    have hm1 : |(∑ j, min (S i j + bh * I.p i - bh * q) I.y) / (Nv i : ℝ) -
        (∑ j, (f (ω i j) q - I.b * q)) / (Nv i : ℝ)| ≤ I.phi * |bh - I.b| := by
      apply mean_diff (hN i)
      intro j
      have e1 : min (S i j + bh * I.p i - bh * q) I.y =
          min (ω i j + (bh - I.b) * I.p i - bh * q) I.y := by
        rw [hS]; unfold sales
        rw [show min (ω i j - I.b * I.p i) (I.yh i) + bh * I.p i - bh * q =
          min (ω i j + (bh - I.b) * I.p i - bh * q) (I.yh i + bh * (I.p i - q)) by
            rw [← min_add_add_right, ← min_sub_sub_right]; congr 1 <;> ring]
        rw [min_assoc, min_eq_right hyq]
      have e2 : f (ω i j) q - I.b * q = min (ω i j - I.b * q) I.y := by
        simp only [hf]; rw [← min_sub_sub_right]; congr 1; ring
      rw [e1, e2]
      have hz : |I.y - I.y| ≤ I.phi * |bh - I.b| := by
        rw [sub_self, abs_zero]; positivity
      refine le_trans (abs_min_sub_min_le_max _ _ _ _) (max_le ?_ hz)
      rw [show ω i j + (bh - I.b) * I.p i - bh * q - (ω i j - I.b * q) = (bh - I.b) * (I.p i - q)
        by ring, abs_mul, mul_comm]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      rw [abs_le]; constructor <;> linarith [hp.1, hp.2]
    have hm2 : (∑ j, (f (ω i j) q - I.b * q)) / (Nv i : ℝ) =
        (∑ j, f (ω i j) q) / (Nv i : ℝ) - I.b * q := by
      have hn : (Nv i : ℝ) ≠ 0 := by exact_mod_cast (hN i).ne'
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      field_simp
    have hE : ∫ ξ, min (ξ - I.b * q) I.y ∂I.μξ = ∫ z, f z q ∂I.μξ - I.b * q := by
      have hae : ∀ᵐ ξ ∂I.μξ, I.b * I.phi ≤ ξ := by
        have h := measure_eq_zero_iff_ae_notMem.1 hI.2.2.2.2.2.2.2.2.2.2.2.1
        filter_upwards [h] with ξ hξ
        simpa using hξ
      have hint : Integrable (fun z => f z q) I.μξ := by
        have := integrable_min' I.μξ (I.b * I.phi) 0 (I.y + I.b * q) hae
        simpa [hf] using this
      have e : (fun ξ => min (ξ - I.b * q) I.y) = fun ξ => f ξ q - I.b * q := by
        funext ξ; simp only [hf]; rw [← min_sub_sub_right]; congr 1; ring
      rw [e, integral_sub hint (integrable_const _), integral_const]
      simp
    have hmain : |RHat I.toPublic S q - RF I I.μξ q| ≤ I.phi * (I.phi * |bh - I.b| + ε) := by
      have hR : RHat I.toPublic S q - RF I I.μξ q =
          q * ((∑ j, min (S i j + bh * I.p i - bh * q) I.y) / (Nv i : ℝ) -
            ∫ ξ, min (ξ - I.b * q) I.y ∂I.μξ) := by
        unfold RHat RF; ring
      rw [hR, abs_mul, abs_of_pos hq, hE]
      apply mul_le_mul hq1 _ (abs_nonneg _) hpb.le
      have h2 := hAi i q ⟨hq0, hq1⟩
      rw [hm2] at hm1
      calc |(∑ j, min (S i j + bh * I.p i - bh * q) I.y) / (Nv i : ℝ) -
            (∫ z, f z q ∂I.μξ - I.b * q)|
          ≤ |(∑ j, min (S i j + bh * I.p i - bh * q) I.y) / (Nv i : ℝ) -
              ((∑ j, f (ω i j) q) / (Nv i : ℝ) - I.b * q)| +
            |((∑ j, f (ω i j) q) / (Nv i : ℝ) - I.b * q) - (∫ z, f z q ∂I.μξ - I.b * q)| :=
            abs_sub_le _ _ _
        _ ≤ I.phi * |bh - I.b| + ε := by
            rw [show ((∑ j, f (ω i j) q) / (Nv i : ℝ) - I.b * q) - (∫ z, f z q ∂I.μξ - I.b * q) =
              (∑ j, f (ω i j) q) / (Nv i : ℝ) - ∫ z, f z q ∂I.μξ by ring]
            exact add_le_add hm1 h2
    have e3 : I.phi * (I.phi * |bh - I.b| + ε) = I.phi ^ 2 * |bh - I.b| + α := by
      rw [hε]; field_simp
    have : 0 ≤ I.phi ^ 2 * |bh - I.b| := by positivity
    linarith
  -- measure bounds
  have mG : dataLaw I Nv G = 0 := by
    rw [hG]
    refine measure_iUnion_null (fun i => measure_iUnion_null (fun j => ?_))
    exact coord_null I hP Nv i j _ measurableSet_Iio hI.2.2.2.2.2.2.2.2.2.2.2.1
  have hone : ∀ i, dataLaw I Nv ((Function.eval i) ⁻¹' {x : Fin (Nv i) → ℝ | ∃ p ∈ Y,
      ε < |(∑ j, f (x j) p) / (Nv i : ℝ) - ∫ z, f z p ∂I.μξ|}) ≤
      ENNReal.ofReal (2 * Real.exp (-((Nmin Nv : ℝ) * α ^ 2 /
        ((I.y + I.bhi * I.phi) ^ 2 * I.phi ^ 2)))) := by
    intro i
    have hmp : MeasurePreserving (Function.eval i) (dataLaw I Nv)
        (Measure.pi (fun _ : Fin (Nv i) => I.μξ)) := by
      unfold dataLaw; exact measurePreserving_eval _ i
    refine le_trans (Measure.le_map_apply hmp.measurable.aemeasurable _) ?_
    rw [hmp.map_eq]
    have hX : ∀ᵐ x ∂I.μξ, x ∈ Ici (0 : ℝ) := by
      have h := measure_eq_zero_iff_ae_notMem.1 hI.2.2.2.2.2.2.2.2.2.2.2.1
      filter_upwards [h] with ξ hξ
      simp only [mem_Iio, not_lt] at hξ
      exact le_trans (by positivity) hξ
    have hA3 := lemma_A_3 I.μξ (Ici 0) Y hX f
      (fun p _ => measurable_id.min measurable_const)
      (L := 0) (U := U) (fun x hx p hp => ⟨le_min hx (by nlinarith [hp.1]),
        le_trans (min_le_right _ _) (by nlinarith [hp.2])⟩)
      (fun p _ => Or.inl (fun x _ z _ hxz => min_le_min_right _ hxz)) (Nv i) hεp
    refine le_trans hA3 (ENNReal.ofReal_le_ofReal ?_)
    have hNi : (Nmin Nv : ℝ) ≤ Nv i := by
      exact_mod_cast ciInf_le (Finite.bddBelow_range Nv) i
    have : Real.exp (-(2 * (Nv i : ℝ) * ε ^ 2 / (U - 0) ^ 2)) ≤
        Real.exp (-((Nmin Nv : ℝ) * α ^ 2 / ((I.y + I.bhi * I.phi) ^ 2 * I.phi ^ 2))) := by
      apply Real.exp_le_exp.2
      rw [neg_le_neg_iff, sub_zero, hε]
      have e : 2 * (Nv i : ℝ) * (α / I.phi) ^ 2 / U ^ 2 = 2 * (Nv i : ℝ) * α ^ 2 /
          (U ^ 2 * I.phi ^ 2) := by field_simp
      rw [e]
      have hUb : U ^ 2 ≤ (I.y + I.bhi * I.phi) ^ 2 := by
        apply pow_le_pow_left₀ hU0.le
        rw [hU]; nlinarith
      calc (Nmin Nv : ℝ) * α ^ 2 / ((I.y + I.bhi * I.phi) ^ 2 * I.phi ^ 2)
          ≤ (Nmin Nv : ℝ) * α ^ 2 / (U ^ 2 * I.phi ^ 2) := by
            apply div_le_div_of_nonneg_left (by positivity) (by positivity)
            exact mul_le_mul_of_nonneg_right hUb (by positivity)
        _ ≤ 2 * (Nv i : ℝ) * α ^ 2 / (U ^ 2 * I.phi ^ 2) := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            have : (0 : ℝ) ≤ Nmin Nv := Nat.cast_nonneg _
            nlinarith [sq_nonneg α]
    linarith
  calc _ ≤ dataLaw I Nv (A ∪ G) := measure_mono hsub
    _ ≤ dataLaw I Nv A + dataLaw I Nv G := measure_union_le _ _
    _ = dataLaw I Nv A := by rw [mG, add_zero]
    _ ≤ ∑ i, dataLaw I Nv ((Function.eval i) ⁻¹' {x : Fin (Nv i) → ℝ | ∃ p ∈ Y,
          ε < |(∑ j, f (x j) p) / (Nv i : ℝ) - ∫ z, f z p ∂I.μξ|}) := by
        rw [hA]; exact measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : Fin K, ENNReal.ofReal (2 * Real.exp (-((Nmin Nv : ℝ) * α ^ 2 /
          ((I.y + I.bhi * I.phi) ^ 2 * I.phi ^ 2)))) := Finset.sum_le_sum (fun i _ => hone i)
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring
