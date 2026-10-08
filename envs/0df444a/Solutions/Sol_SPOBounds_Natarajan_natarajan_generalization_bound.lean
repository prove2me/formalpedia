-- Prove2me | solution 1 for SPOBounds.Natarajan.natarajan_generalization_bound
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-05T21:03:03.225447+00:00
-- url     : https://prove2.me/submissions/59995938-20f5-40e6-94a7-4759aa394382

import Mathlib
import Definitions.Def_SPOBounds_Natarajan_Model
import Definitions.Def_SPOBounds_Natarajan_Rademacher
import Definitions.Def_SPOBounds_Natarajan_NatarajanDim

set_option autoImplicit false

/- Complete checked body: HammingTools -/
section

open MeasureTheory Filter
open scoped NNReal

namespace SPOBounds.NatarajanProof

noncomputable section

variable {Ω : Type*} {n : ℕ}

def hdist (x y : Fin n → Ω) : ℝ := by
  classical
  exact (hammingDist x y : ℝ)

def HammingLipschitz (c : ℝ) (f : (Fin n → Ω) → ℝ) : Prop :=
  ∀ x y, |f x - f y| ≤ c * hdist x y

theorem hdist_sum [DecidableEq Ω] (x y : Fin n → Ω) :
    hdist x y = ∑ i, if x i = y i then (0 : ℝ) else 1 := by
  classical
  unfold hdist hammingDist
  rw [Finset.card_eq_sum_ones]
  simp only [Nat.cast_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : x i = y i <;> simp [h]

theorem hdist_nonneg (x y : Fin n → Ω) : 0 ≤ hdist x y := by
  unfold hdist
  positivity

theorem hdist_le (x y : Fin n → Ω) : hdist x y ≤ n := by
  classical
  unfold hdist
  exact_mod_cast (show hammingDist x y ≤ n by
    simpa only [Fintype.card_fin] using (hammingDist_le_card_fintype (x := x) (y := y)))

theorem hdist_cons [DecidableEq Ω] (a b : Ω) (x y : Fin n → Ω) :
    hdist (Fin.cons a x) (Fin.cons b y) =
      (if a = b then 0 else 1) + hdist x y := by
  classical
  simp only [hdist_sum, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem hdist_cons_same (a : Ω) (x y : Fin n → Ω) :
    hdist (Fin.cons a x) (Fin.cons a y) = hdist x y := by
  classical
  rw [hdist_cons]
  simp

theorem hdist_cons_right (a b : Ω) (x : Fin n → Ω) :
    hdist (Fin.cons a x) (Fin.cons b x) ≤ 1 := by
  classical
  rw [hdist_cons]
  simp only [hdist, hammingDist_self, Nat.cast_zero, add_zero]
  split_ifs <;> norm_num

/-- The metric used for extension is only an auxiliary type synonym; no Borel assumption is made. -/
theorem hamming_extend {c : ℝ} (hc : 0 ≤ c) (f : (Fin n → Ω) → ℝ)
    (s : Set (Fin n → Ω))
    (hf : ∀ x ∈ s, ∀ y ∈ s, |f x - f y| ≤ c * hdist x y) :
    ∃ g : (Fin n → Ω) → ℝ, HammingLipschitz c g ∧ Set.EqOn f g s := by
  classical
  let F : Hamming (fun _ : Fin n => Ω) → ℝ := fun x => f (Hamming.ofHamming x)
  let S : Set (Hamming (fun _ : Fin n => Ω)) := Hamming.ofHamming ⁻¹' s
  let K : ℝ≥0 := ⟨c, hc⟩
  have hK : (K : ℝ) = c := rfl
  have hF : LipschitzOnWith K F S := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [F, Real.dist_eq, Hamming.dist_eq_hammingDist, hdist, hK] using
      hf (Hamming.ofHamming x) hx (Hamming.ofHamming y) hy
  obtain ⟨g, hg, he⟩ := hF.extend_real
  refine ⟨fun x => g (Hamming.toHamming x), ?_, ?_⟩
  · intro x y
    simpa only [Real.dist_eq, Hamming.dist_eq_hammingDist, hdist, hK,
      Hamming.ofHamming_toHamming] using
      hg.dist_le_mul (Hamming.toHamming x) (Hamming.toHamming y)
  · intro x hx
    exact he hx

theorem HammingLipschitz.bounded [Nonempty Ω] {c : ℝ} {f : (Fin n → Ω) → ℝ}
    (hc : 0 ≤ c) (hf : HammingLipschitz c f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, |f x| ≤ B := by
  classical
  let x0 : Fin n → Ω := fun _ => Classical.choice ‹Nonempty Ω›
  refine ⟨|f x0| + c * n, by positivity, ?_⟩
  intro x
  calc
    |f x| ≤ |f x - f x0| + |f x0| := by
      simpa using abs_add_le (f x - f x0) (f x0)
    _ ≤ c * hdist x x0 + |f x0| := add_le_add (hf x x0) le_rfl
    _ ≤ |f x0| + c * n := by
      have := mul_le_mul_of_nonneg_left (hdist_le x x0) hc
      linarith

theorem hamming_extend_ae [MeasurableSpace Ω] {μ : Measure (Fin n → Ω)}
    {c : ℝ} (hc : 0 ≤ c) (f : (Fin n → Ω) → ℝ) (hm : AEMeasurable f μ)
    (s : Set (Fin n → Ω)) (hs : ∀ᵐ x ∂μ, x ∈ s)
    (hf : ∀ x ∈ s, ∀ y ∈ s, |f x - f y| ≤ c * hdist x y) :
    ∃ g : (Fin n → Ω) → ℝ,
      HammingLipschitz c g ∧ AEMeasurable g μ ∧ g =ᵐ[μ] f := by
  obtain ⟨g, hg, he⟩ := hamming_extend hc f s hf
  have hae : g =ᵐ[μ] f := hs.mono fun x hx => (he hx).symm
  exact ⟨g, hg, hm.congr hae.symm, hae⟩

end
end SPOBounds.NatarajanProof

end

/- Complete checked body: BoundedOscillation -/
section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace SPOBounds.NatarajanProof

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem integrable_abs_bounded {f : Ω → ℝ} {B : ℝ}
    (hm : AEMeasurable f μ) (hb : ∀ x, |f x| ≤ B) : Integrable f μ := by
  apply Integrable.of_mem_Icc (-B) B hm
  exact ae_of_all _ fun x => abs_le.mp (hb x)

theorem integrable_exp_bounded {f : Ω → ℝ} {B : ℝ}
    (hm : AEMeasurable f μ) (hb : ∀ x, |f x| ≤ B) (t : ℝ) :
    Integrable (fun x => Real.exp (t * f x)) μ := by
  exact integrable_exp_mul_of_mem_Icc hm (ae_of_all _ fun x => abs_le.mp (hb x))

/-- Sharp one-variable Hoeffding bound using the actual oscillation rather than a radius. -/
theorem oscillation_mgf {f : Ω → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hm : AEMeasurable f μ) (ho : ∀ x y, |f x - f y| ≤ c) (t : ℝ) :
    (∫ x, Real.exp (t * (f x - ∫ y, f y ∂μ)) ∂μ) ≤ Real.exp (c ^ 2 * t ^ 2 / 8) := by
  classical
  let _ : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  let x0 : Ω := Classical.choice ‹Nonempty Ω›
  have hb : BddBelow (Set.range f) := by
    refine ⟨f x0 - c, ?_⟩
    rintro _ ⟨x, rfl⟩
    have := (abs_le.mp (ho x0 x)).2
    linarith
  let a := sInf (Set.range f)
  have hi : ∀ x, f x ∈ Set.Icc a (a + c) := by
    intro x
    refine ⟨csInf_le hb (Set.mem_range_self x), ?_⟩
    have hx : f x - c ≤ a := by
      apply le_csInf (Set.range_nonempty f)
      rintro _ ⟨y, rfl⟩
      have := (abs_le.mp (ho x y)).2
      linarith
    linarith
  have h := (hasSubgaussianMGF_of_mem_Icc hm (ae_of_all _ hi)).mgf_le t
  change (∫ x, Real.exp (t * (f x - ∫ y, f y ∂μ)) ∂μ) ≤ _ at h
  convert h using 1
  congr 1
  simp only [NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat, coe_nnnorm,
    Real.norm_eq_abs, add_sub_cancel_left, abs_of_nonneg hc]
  ring

end SPOBounds.NatarajanProof

end

/- Complete checked body: ProductSections -/
section

open MeasureTheory Filter

namespace SPOBounds.NatarajanProof

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

abbrev productLaw (n : ℕ) : Measure (Fin n → Ω) := Measure.pi fun _ => μ

theorem integrable_fin_cons {n : ℕ} {f : (Fin (n + 1) → Ω) → ℝ}
    (hf : Integrable f (productLaw μ (n + 1))) :
    Integrable (fun p : Ω × (Fin n → Ω) => f (Fin.cons p.1 p.2))
      (μ.prod (productLaw μ n)) := by
  have h := ((measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm).integrable_comp_emb (MeasurableEquiv.measurableEmbedding _) |>.mpr hf
  simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, Fin.zero_succAbove, Function.comp_def, Equiv.coe_fn_mk, cast_eq] using h

theorem integral_fin_cons {n : ℕ} (f : (Fin (n + 1) → Ω) → ℝ) :
    (∫ x, f x ∂productLaw μ (n + 1)) =
      ∫ p : Ω × (Fin n → Ω), f (Fin.cons p.1 p.2) ∂μ.prod (productLaw μ n) := by
  have h := ((measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm).integral_comp' f
  simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, Fin.zero_succAbove, Function.comp_def, Equiv.coe_fn_mk, cast_eq] using h.symm

theorem HammingLipschitz.integrable {n : ℕ} {c : ℝ} {f : (Fin n → Ω) → ℝ}
    (hc : 0 ≤ c) (hl : HammingLipschitz c f) (hm : AEMeasurable f (productLaw μ n)) :
    Integrable f (productLaw μ n) := by
  let _ : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  obtain ⟨B, _, hB⟩ := hl.bounded hc
  exact integrable_abs_bounded hm hB

/-- The section integral has a globally Lipschitz, AE-equal version on the suffix product. -/
theorem section_mean_extension {n : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (f : (Fin (n + 1) → Ω) → ℝ) (hl : HammingLipschitz c f)
    (hm : AEMeasurable f (productLaw μ (n + 1))) :
    ∃ g : (Fin n → Ω) → ℝ,
      HammingLipschitz c g ∧ AEMeasurable g (productLaw μ n) ∧
      g =ᵐ[productLaw μ n] (fun y => ∫ x, f (Fin.cons x y) ∂μ) ∧
      (∫ y, g y ∂productLaw μ n) = ∫ x, f x ∂productLaw μ (n + 1) := by
  have hf := hl.integrable μ hc hm
  have hp := integrable_fin_cons μ hf
  let s : Set (Fin n → Ω) := {y | Integrable (fun x => f (Fin.cons x y)) μ}
  have hs : ∀ᵐ y ∂productLaw μ n, y ∈ s := hp.prod_left_ae
  have hg := hp.integral_prod_right.aemeasurable
  obtain ⟨g, hgl, hgm, hge⟩ := hamming_extend_ae hc
    (fun y => ∫ x, f (Fin.cons x y) ∂μ) hg s hs (by
      intro y hy z hz
      rw [← integral_sub hy hz]
      have hb : ∀ᵐ x ∂μ, ‖f (Fin.cons x y) - f (Fin.cons x z)‖ ≤ c * hdist y z := by
        apply ae_of_all
        intro x
        simpa only [Real.norm_eq_abs, hdist_cons_same] using hl (Fin.cons x y) (Fin.cons x z)
      simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
        norm_integral_le_of_norm_le_const hb)
  refine ⟨g, hgl, hgm, hge, ?_⟩
  rw [integral_congr_ae hge, integral_fin_cons μ f, integral_prod_symm _ hp]

end
end SPOBounds.NatarajanProof

end

/- Complete checked body: FiniteProductMGF -/
section

open MeasureTheory ProbabilityTheory Filter

namespace SPOBounds.NatarajanProof

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem hamming_exp_integrable {n : ℕ} {c : ℝ} (hc : 0 ≤ c)
    {f : (Fin n → Ω) → ℝ} (hl : HammingLipschitz c f)
    (hm : AEMeasurable f (productLaw μ n)) (a t : ℝ) :
    Integrable (fun x => Real.exp (t * (f x - a))) (productLaw μ n) := by
  let _ : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  obtain ⟨B, _, hb⟩ := hl.bounded hc
  apply integrable_exp_bounded (hm.sub_const a) (B := B + |a|)
  intro x
  exact (abs_sub (f x) a).trans (add_le_add (hb x) le_rfl)

/-- Sharp bounded-differences MGF on an arbitrary measurable coordinate space.
The section means are extended only on their full-measure integrable-section set. -/
theorem finite_product_mgf (n : ℕ) {c : ℝ} (hc : 0 ≤ c)
    (f : (Fin n → Ω) → ℝ) (hl : HammingLipschitz c f)
    (hm : AEMeasurable f (productLaw μ n)) (t : ℝ) :
    (∫ x, Real.exp (t * (f x - ∫ y, f y ∂productLaw μ n)) ∂productLaw μ n) ≤
      Real.exp ((n : ℝ) * c ^ 2 * t ^ 2 / 8) := by
  induction n with
  | zero =>
      let x0 : Fin 0 → Ω := fun i => Fin.elim0 i
      have hf : f = fun _ => f x0 := funext fun x => congrArg f (Subsingleton.elim x x0)
      rw [hf]
      simp
  | succ n ih =>
      obtain ⟨g, hgl, hgm, hge, hgi⟩ := section_mean_extension μ hc f hl hm
      have hgei := hamming_exp_integrable μ hc hgl hgm (∫ y, g y ∂productLaw μ n) t
      have hfi := hl.integrable μ hc hm
      have hfp := integrable_fin_cons μ hfi
      have hei := hamming_exp_integrable μ hc hl hm (∫ y, f y ∂productLaw μ (n + 1)) t
      have hep := integrable_fin_cons μ hei
      rw [integral_fin_cons μ _, integral_prod_symm _ hep]
      calc
        _ ≤ ∫ y, Real.exp (c ^ 2 * t ^ 2 / 8) *
            Real.exp (t * (g y - ∫ z, g z ∂productLaw μ n)) ∂productLaw μ n := by
          apply integral_mono_ae hep.integral_prod_right (hgei.const_mul _)
          filter_upwards [hfp.prod_left_ae, hge] with y hy hey
          have ho : ∀ a b : Ω,
              |f (Fin.cons a y) - f (Fin.cons b y)| ≤ c := by
            intro a b
            exact (hl _ _).trans (by
              simpa only [mul_one] using mul_le_mul_of_nonneg_left (hdist_cons_right a b y) hc)
          have hsec := oscillation_mgf hc hy.aemeasurable ho t
          rw [← hey] at hsec
          rw [← hgi]
          calc
            _ = (∫ a, Real.exp (t * (f (Fin.cons a y) - g y)) ∂μ) *
                Real.exp (t * (g y - ∫ z, g z ∂productLaw μ n)) := by
              rw [← integral_mul_const]
              apply integral_congr_ae
              apply ae_of_all
              intro a
              dsimp only
              rw [← Real.exp_add]
              congr 1
              ring
            _ ≤ _ := mul_le_mul_of_nonneg_right hsec (Real.exp_pos _).le
        _ = Real.exp (c ^ 2 * t ^ 2 / 8) *
            (∫ y, Real.exp (t * (g y - ∫ z, g z ∂productLaw μ n)) ∂productLaw μ n) :=
          integral_const_mul _ _
        _ ≤ Real.exp (c ^ 2 * t ^ 2 / 8) * Real.exp ((n : ℝ) * c ^ 2 * t ^ 2 / 8) :=
          mul_le_mul_of_nonneg_left (ih g hgl hgm) (Real.exp_pos _).le
        _ = Real.exp ((n + 1 : ℕ) * c ^ 2 * t ^ 2 / 8) := by
          rw [← Real.exp_add]
          congr 1
          push_cast
          ring

end
end SPOBounds.NatarajanProof

end

/- Complete checked body: SharpConcentration -/
section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SPOBounds.NatarajanProof

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem hamming_subgaussian {n : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (f : (Fin n → Ω) → ℝ) (hl : HammingLipschitz c f)
    (hm : AEMeasurable f (productLaw μ n)) :
    HasSubgaussianMGF (fun x => f x - ∫ y, f y ∂productLaw μ n)
      ⟨(n : ℝ) * c ^ 2 / 4, by positivity⟩ (productLaw μ n) := by
  constructor
  · exact hamming_exp_integrable μ hc hl hm _
  · intro t
    change (∫ x, Real.exp (t * (f x - ∫ y, f y ∂productLaw μ n)) ∂productLaw μ n) ≤
      Real.exp (((n : ℝ) * c ^ 2 / 4) * t ^ 2 / 2)
    rw [show ((n : ℝ) * c ^ 2 / 4) * t ^ 2 / 2 = (n : ℝ) * c ^ 2 * t ^ 2 / 8 by ring]
    exact finite_product_mgf μ n hc f hl hm t

theorem hamming_tail {n : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (f : (Fin n → Ω) → ℝ) (hl : HammingLipschitz c f)
    (hm : AEMeasurable f (productLaw μ n)) {e : ℝ} (he : 0 ≤ e) :
    productLaw μ n {x | e ≤ f x - ∫ y, f y ∂productLaw μ n} ≤
      ENNReal.ofReal (Real.exp (-2 * e ^ 2 / ((n : ℝ) * c ^ 2))) := by
  have h := (hamming_subgaussian μ hc f hl hm).measure_ge_le he
  change (productLaw μ n).real {x | e ≤ f x - ∫ y, f y ∂productLaw μ n} ≤
    Real.exp (-e ^ 2 / (2 * ((n : ℝ) * c ^ 2 / 4))) at h
  rw [show -e ^ 2 / (2 * ((n : ℝ) * c ^ 2 / 4)) =
    -2 * e ^ 2 / ((n : ℝ) * c ^ 2) by ring] at h
  have h' := ENNReal.ofReal_le_ofReal h
  simpa only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)] using h'

theorem hamming_confidence {n : ℕ} (hn : 0 < n) {B : ℝ} (hB : 0 < B)
    (f : (Fin n → Ω) → ℝ) (hl : HammingLipschitz (B / n) f)
    (hm : AEMeasurable f (productLaw μ n)) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    productLaw μ n {x | B * Real.sqrt (Real.log (1 / δ) / (2 * n)) ≤
      f x - ∫ y, f y ∂productLaw μ n} ≤ ENNReal.ofReal δ := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hlog : 0 ≤ Real.log (1 / δ) := Real.log_nonneg ((one_le_div hδ).mpr hδ1.le)
  have harg : 0 ≤ Real.log (1 / δ) / (2 * n) := div_nonneg hlog (by positivity)
  have h := hamming_tail μ (c := B / n) (by positivity) f hl hm
    (e := B * Real.sqrt (Real.log (1 / δ) / (2 * n))) (by positivity)
  have he : -2 * (B * Real.sqrt (Real.log (1 / δ) / (2 * n))) ^ 2 /
      ((n : ℝ) * (B / n) ^ 2) = -Real.log (1 / δ) := by
    rw [mul_pow, Real.sq_sqrt harg]
    field_simp [hnR.ne', hB.ne']
  rw [he, Real.exp_neg, Real.exp_log (by positivity), one_div, inv_inv] at h
  simpa only [one_div] using h

end
end SPOBounds.NatarajanProof

end

/- Complete checked body: ClassScoreBounds -/
section

open MeasureTheory Filter

namespace SPOBounds.NatarajanProof

noncomputable section

variable {Ω Θ : Type*}

def sampleAverage {n : ℕ} (f : Ω → ℝ) (x : Fin n → Ω) : ℝ :=
  (1 / n : ℝ) * ∑ i, f (x i)

def classSigned {n : ℕ} (loss : Θ → Ω → ℝ) (s : Fin n → Bool) (x : Fin n → Ω) : ℝ :=
  ⨆ a, (1 / n : ℝ) * ∑ i, (if s i then (1 : ℝ) else -1) * loss a (x i)

def classRademacher {n : ℕ} (loss : Θ → Ω → ℝ) (x : Fin n → Ω) : ℝ :=
  (1 / 2 ^ n : ℝ) * ∑ s : Fin n → Bool, classSigned loss s x

def classDeviation [MeasurableSpace Ω] (μ : Measure Ω) {n : ℕ}
    (loss : Θ → Ω → ℝ) (x : Fin n → Ω) : ℝ :=
  ⨆ a, (∫ z, loss a z ∂μ) - sampleAverage (loss a) x

theorem ciSup_abs_bound [Nonempty Θ] {f : Θ → ℝ} {B : ℝ}
    (hf : ∀ a, |f a| ≤ B) : |⨆ a, f a| ≤ B := by
  classical
  have hb : BddAbove (Set.range f) := ⟨B, by rintro _ ⟨a, rfl⟩; exact (abs_le.mp (hf a)).2⟩
  apply abs_le.mpr
  constructor
  · let a := Classical.choice ‹Nonempty Θ›
    exact (abs_le.mp (hf a)).1.trans (le_ciSup hb a)
  · exact ciSup_le fun a => (abs_le.mp (hf a)).2

theorem ciSup_difference_bound [Nonempty Θ] {f g : Θ → ℝ} {B c : ℝ}
    (hf : ∀ a, |f a| ≤ B) (hg : ∀ a, |g a| ≤ B)
    (hd : ∀ a, |f a - g a| ≤ c) : |(⨆ a, f a) - ⨆ a, g a| ≤ c := by
  have hbf : BddAbove (Set.range f) := ⟨B, by rintro _ ⟨a, rfl⟩; exact (abs_le.mp (hf a)).2⟩
  have hbg : BddAbove (Set.range g) := ⟨B, by rintro _ ⟨a, rfl⟩; exact (abs_le.mp (hg a)).2⟩
  have hfg : (⨆ a, f a) ≤ (⨆ a, g a) + c := by
    apply ciSup_le
    intro a
    have := (abs_le.mp (hd a)).2
    have := le_ciSup hbg a
    linarith
  have hgf : (⨆ a, g a) ≤ (⨆ a, f a) + c := by
    apply ciSup_le
    intro a
    have := (abs_le.mp (hd a)).1
    have := le_ciSup hbf a
    linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem normalized_sum_abs {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) {B : ℝ}
    (ha : ∀ i, |a i| ≤ B) : |(1 / n : ℝ) * ∑ i, a i| ≤ B := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  calc
    _ = (1 / n : ℝ) * |∑ i, a i| := by rw [abs_mul, abs_of_nonneg (by positivity)]
    _ ≤ (1 / n : ℝ) * ∑ i, |a i| := mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ (1 / n : ℝ) * ∑ _ : Fin n, B :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ha i) (by positivity)
    _ = B := by simp [hnR.ne']

theorem sampleAverage_bounds {n : ℕ} (hn : 0 < n) {f : Ω → ℝ} {B : ℝ}
    (hf : ∀ z, 0 ≤ f z ∧ f z ≤ B) (x : Fin n → Ω) :
    0 ≤ sampleAverage f x ∧ sampleAverage f x ≤ B := by
  have hp : 0 ≤ sampleAverage f x := mul_nonneg (by positivity)
    (Finset.sum_nonneg fun i _ => (hf (x i)).1)
  refine ⟨hp, ?_⟩
  have h := normalized_sum_abs hn (fun i => f (x i)) (fun i => by
    rw [abs_of_nonneg (hf (x i)).1]
    exact (hf (x i)).2)
  exact (le_abs_self _).trans h

theorem sampleAverage_hamming {n : ℕ} {f : Ω → ℝ} {B : ℝ}
    (hf : ∀ z, 0 ≤ f z ∧ f z ≤ B) (x y : Fin n → Ω) :
    |sampleAverage f x - sampleAverage f y| ≤ (B / n) * hdist x y := by
  classical
  unfold sampleAverage
  rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_nonneg (by positivity)]
  calc
    _ ≤ (1 / n : ℝ) * ∑ i, |f (x i) - f (y i)| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ (1 / n : ℝ) * ∑ i, if x i = y i then (0 : ℝ) else B := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro i _
      by_cases h : x i = y i
      · simp [h]
      · simp only [h, if_false]
        exact abs_le.mpr ⟨by linarith [(hf (x i)).1, (hf (y i)).2],
          by linarith [(hf (y i)).1, (hf (x i)).2]⟩
    _ = (B / n) * hdist x y := by
      rw [hdist_sum]
      have he : (∑ i, if x i = y i then (0 : ℝ) else B) =
          B * ∑ i, if x i = y i then (0 : ℝ) else 1 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> simp
      rw [he]
      ring

theorem classSigned_abs_bound [Nonempty Θ] {n : ℕ} (hn : 0 < n)
    {loss : Θ → Ω → ℝ} {B : ℝ} (hl : ∀ a z, 0 ≤ loss a z ∧ loss a z ≤ B)
    (s : Fin n → Bool) (x : Fin n → Ω) : |classSigned loss s x| ≤ B := by
  apply ciSup_abs_bound
  intro a
  apply normalized_sum_abs hn
  intro i
  split_ifs <;> simpa [abs_of_nonneg (hl a (x i)).1] using (hl a (x i)).2

theorem risk_bounds [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} {B : ℝ} (hm : AEMeasurable f μ) (hf : ∀ z, 0 ≤ f z ∧ f z ≤ B) :
    0 ≤ (∫ z, f z ∂μ) ∧ (∫ z, f z ∂μ) ≤ B := by
  have hi := integrable_abs_bounded hm (fun z => by simpa [abs_of_nonneg (hf z).1] using (hf z).2)
  refine ⟨integral_nonneg fun z => (hf z).1, ?_⟩
  simpa using integral_mono hi (integrable_const B) (fun z => (hf z).2)

theorem classDeviation_bounds [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [Nonempty Θ] {n : ℕ} (hn : 0 < n) {loss : Θ → Ω → ℝ} {B : ℝ}
    (hm : ∀ a, AEMeasurable (loss a) μ) (hl : ∀ a z, 0 ≤ loss a z ∧ loss a z ≤ B)
    (x : Fin n → Ω) : |classDeviation μ loss x| ≤ B := by
  apply ciSup_abs_bound
  intro a
  have h1 := risk_bounds (hm a) (hl a)
  have h2 := sampleAverage_bounds hn (hl a) x
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem classDeviation_hamming [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [Nonempty Θ] {n : ℕ} (hn : 0 < n) {loss : Θ → Ω → ℝ} {B : ℝ}
    (hm : ∀ a, AEMeasurable (loss a) μ) (hl : ∀ a z, 0 ≤ loss a z ∧ loss a z ≤ B) :
    HammingLipschitz (B / n) (classDeviation μ (n := n) loss) := by
  intro x y
  apply ciSup_difference_bound (B := B)
  · intro a
    have h1 := risk_bounds (hm a) (hl a)
    have h2 := sampleAverage_bounds hn (hl a) x
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · intro a
    have h1 := risk_bounds (hm a) (hl a)
    have h2 := sampleAverage_bounds hn (hl a) y
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · intro a
    simpa only [sub_sub_sub_cancel_left, abs_sub_comm] using sampleAverage_hamming (hl a) x y

end
end SPOBounds.NatarajanProof

end

/- Complete checked body: PairedSamples -/
section

open MeasureTheory

namespace SPOBounds.NatarajanProof

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

def mixedSample {n : ℕ} (s : Fin n → Bool) (p : (Fin n → Ω) × (Fin n → Ω)) :
    Fin n → Ω := fun i => if s i then p.2 i else p.1 i

theorem mixedSample_measurePreserving {n : ℕ} (s : Fin n → Bool) :
    MeasurePreserving (mixedSample s) ((productLaw μ n).prod (productLaw μ n))
      (productLaw μ n) := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow Ω Ω (Fin n)
  have he : MeasurePreserving e.symm ((productLaw μ n).prod (productLaw μ n))
      (Measure.pi fun _ : Fin n => μ.prod μ) :=
    (measurePreserving_arrowProdEquivProdArrow Ω Ω (Fin n) (fun _ => μ) (fun _ => μ)).symm
  have hi (i : Fin n) : MeasurePreserving (fun p : Ω × Ω => if s i then p.2 else p.1)
      (μ.prod μ) μ := by
    cases h : s i
    · simpa only [h, Bool.false_eq_true, if_false] using
        (measurePreserving_fst : MeasurePreserving Prod.fst (μ.prod μ) μ)
    · simpa only [h, if_true] using
        (measurePreserving_snd : MeasurePreserving Prod.snd (μ.prod μ) μ)
  exact (measurePreserving_pi (fun _ : Fin n => μ.prod μ) (fun _ => μ) hi).comp he

end SPOBounds.NatarajanProof

end

/- Complete checked body: SampleIntegrals -/
section

open MeasureTheory Filter

namespace SPOBounds.NatarajanProof

variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]

theorem integral_comp_preserving {μ : Measure Ω} {ν : Measure Ξ} {p : Ω → Ξ}
    (hp : MeasurePreserving p μ ν) {f : Ξ → ℝ} (hm : AEMeasurable f ν) :
    (∫ x, f (p x) ∂μ) = ∫ y, f y ∂ν := by
  have hh : AEStronglyMeasurable f (μ.map p) := by
    rw [hp.map_eq]
    exact hm.aestronglyMeasurable
  have h := integral_map hp.measurable.aemeasurable hh
  rw [hp.map_eq] at h
  exact h.symm

variable (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem sampleAverage_integrable {n : ℕ} {f : Ω → ℝ} (hf : Integrable f μ) :
    Integrable (sampleAverage f : (Fin n → Ω) → ℝ) (productLaw μ n) := by
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro i _
  exact (measurePreserving_eval (fun _ : Fin n => μ) i).integrable_comp_of_integrable hf

theorem sampleAverage_integral {n : ℕ} (hn : 0 < n) {f : Ω → ℝ} (hf : Integrable f μ) :
    (∫ x : Fin n → Ω, sampleAverage f x ∂productLaw μ n) = ∫ z, f z ∂μ := by
  unfold sampleAverage
  rw [integral_const_mul, integral_finsetSum]
  · have he (i : Fin n) : (∫ x : Fin n → Ω, f (x i) ∂productLaw μ n) = ∫ z, f z ∂μ :=
      integral_comp_preserving (measurePreserving_eval (fun _ : Fin n => μ) i) hf.aemeasurable
    simp_rw [he]
    have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hn)
    simp [hnR]
  · intro i _
    exact (measurePreserving_eval (fun _ : Fin n => μ) i).integrable_comp_of_integrable hf

end SPOBounds.NatarajanProof

end

/- Complete checked body: SymmetrizationEnvelope -/
section

open MeasureTheory Filter

namespace SPOBounds.NatarajanProof

noncomputable section

variable {Ω Θ : Type*} [Nonempty Θ] {n : ℕ}

def ghostEnvelope (loss : Θ → Ω → ℝ)
    (p : (Fin n → Ω) × (Fin n → Ω)) : ℝ :=
  (1 / 2 ^ n : ℝ) * ∑ s : Fin n → Bool,
    (classSigned loss s (mixedSample s p) +
      classSigned loss (fun i => !(s i)) (mixedSample (fun i => !(s i)) p))

omit [Nonempty Θ] in
theorem pair_difference_le_signed (hn : 0 < n) {loss : Θ → Ω → ℝ} {B : ℝ}
    (hl : ∀ a z, 0 ≤ loss a z ∧ loss a z ≤ B) (a : Θ)
    (s : Fin n → Bool) (p : (Fin n → Ω) × (Fin n → Ω)) :
    sampleAverage (loss a) p.2 - sampleAverage (loss a) p.1 ≤
      classSigned loss s (mixedSample s p) +
      classSigned loss (fun i => !(s i)) (mixedSample (fun i => !(s i)) p) := by
  have hb (s : Fin n → Bool) (x : Fin n → Ω) :
      BddAbove (Set.range fun a : Θ =>
        (1 / n : ℝ) * ∑ i, (if s i then (1 : ℝ) else -1) * loss a (x i)) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨a, rfl⟩
    apply (le_abs_self _).trans
    apply normalized_sum_abs hn
    intro i
    split_ifs <;> simpa [abs_of_nonneg (hl a (x i)).1] using (hl a (x i)).2
  have h1 := le_ciSup (hb s (mixedSample s p)) a
  have h2 := le_ciSup (hb (fun i => !(s i)) (mixedSample (fun i => !(s i)) p)) a
  apply (le_of_eq ?_).trans (add_le_add h1 h2)
  unfold sampleAverage
  rw [← mul_sub, ← mul_add, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  cases h : s i <;> simp [mixedSample, h] <;> ring

omit [Nonempty Θ] in
theorem pair_difference_le_envelope (hn : 0 < n) {loss : Θ → Ω → ℝ} {B : ℝ}
    (hl : ∀ a z, 0 ≤ loss a z ∧ loss a z ≤ B) (a : Θ)
    (p : (Fin n → Ω) × (Fin n → Ω)) :
    sampleAverage (loss a) p.2 - sampleAverage (loss a) p.1 ≤ ghostEnvelope loss p := by
  calc
    _ = (1 / 2 ^ n : ℝ) * ∑ _ : Fin n → Bool,
        (sampleAverage (loss a) p.2 - sampleAverage (loss a) p.1) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun s _ => pair_difference_le_signed hn hl a s p) (by positivity)

variable [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem ghostEnvelope_integrable (hn : 0 < n) {loss : Θ → Ω → ℝ} {B : ℝ}
    (hl : ∀ a z, 0 ≤ loss a z ∧ loss a z ≤ B)
    (hA : ∀ s : Fin n → Bool, AEMeasurable (classSigned loss s) (productLaw μ n)) :
    Integrable (ghostEnvelope loss) ((productLaw μ n).prod (productLaw μ n)) := by
  have hi (s : Fin n → Bool) : Integrable (classSigned loss s) (productLaw μ n) :=
    integrable_abs_bounded (hA s) (classSigned_abs_bound hn hl s)
  unfold ghostEnvelope
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro s _
  exact ((mixedSample_measurePreserving μ s).integrable_comp_of_integrable (hi s)).add
    ((mixedSample_measurePreserving μ (fun i => !(s i))).integrable_comp_of_integrable (hi _))

theorem ghostEnvelope_integral (hn : 0 < n) {loss : Θ → Ω → ℝ} {B : ℝ}
    (hl : ∀ a z, 0 ≤ loss a z ∧ loss a z ≤ B)
    (hA : ∀ s : Fin n → Bool, AEMeasurable (classSigned loss s) (productLaw μ n)) :
    (∫ p, ghostEnvelope loss p ∂(productLaw μ n).prod (productLaw μ n)) =
      2 * ∫ x, classRademacher loss x ∂productLaw μ n := by
  have hi (s : Fin n → Bool) : Integrable (classSigned loss s) (productLaw μ n) :=
    integrable_abs_bounded (hA s) (classSigned_abs_bound hn hl s)
  have him (s : Fin n → Bool) :=
    (mixedSample_measurePreserving μ s).integrable_comp_of_integrable (hi s)
  have he (s : Fin n → Bool) := integral_comp_preserving (mixedSample_measurePreserving μ s) (hA s)
  have hflip : (∑ s : Fin n → Bool, ∫ x, classSigned loss (fun i => !(s i)) x ∂productLaw μ n) =
      ∑ s : Fin n → Bool, ∫ x, classSigned loss s x ∂productLaw μ n := by
    exact (Equiv.piCongrRight fun _ : Fin n => Equiv.boolNot).sum_comp
      (fun s : Fin n → Bool => ∫ x, classSigned loss s x ∂productLaw μ n)
  have hsum (s : Fin n → Bool) : Integrable
      (fun p => classSigned loss s (mixedSample s p) +
        classSigned loss (fun i => !(s i)) (mixedSample (fun i => !(s i)) p))
      ((productLaw μ n).prod (productLaw μ n)) :=
    (him s).add (him (fun i => !(s i)))
  have hint (s : Fin n → Bool) :
      (∫ p, classSigned loss s (mixedSample s p) +
        classSigned loss (fun i => !(s i)) (mixedSample (fun i => !(s i)) p)
          ∂(productLaw μ n).prod (productLaw μ n)) =
        (∫ x, classSigned loss s x ∂productLaw μ n) +
          (∫ x, classSigned loss (fun i => !(s i)) x ∂productLaw μ n) :=
    (integral_add (him s) (him (fun i => !(s i)))).trans
      (congrArg₂ (fun a b : ℝ => a + b) (he s) (he (fun i => !(s i))))
  unfold ghostEnvelope classRademacher
  rw [integral_const_mul, integral_finsetSum _ (fun s _ => hsum s)]
  simp_rw [hint]
  rw [Finset.sum_add_distrib, hflip, integral_const_mul,
    integral_finsetSum _ (fun s _ => hi s)]
  ring

/-- Expected symmetrization through a finite signed envelope; no ghost supremum is integrated. -/
theorem expected_deviation_le_twice_rademacher (hn : 0 < n)
    {loss : Θ → Ω → ℝ} {B : ℝ} (hl : ∀ a z, 0 ≤ loss a z ∧ loss a z ≤ B)
    (hm : ∀ a, AEMeasurable (loss a) μ)
    (hD : AEMeasurable (classDeviation μ loss : (Fin n → Ω) → ℝ) (productLaw μ n))
    (hA : ∀ s : Fin n → Bool, AEMeasurable (classSigned loss s) (productLaw μ n)) :
    (∫ x : Fin n → Ω, classDeviation μ loss x ∂productLaw μ n) ≤
      2 * ∫ x : Fin n → Ω, classRademacher loss x ∂productLaw μ n := by
  have hE := ghostEnvelope_integrable μ hn hl hA
  have hDi := integrable_abs_bounded hD (classDeviation_bounds hn hm hl)
  rw [← ghostEnvelope_integral μ hn hl hA, integral_prod _ hE]
  apply integral_mono_ae hDi hE.integral_prod_left
  filter_upwards [hE.prod_right_ae] with x hx
  apply ciSup_le
  intro a
  have hli := integrable_abs_bounded (hm a) (fun z => by
    simpa [abs_of_nonneg (hl a z).1] using (hl a z).2)
  have hai := sampleAverage_integrable μ (n := n) hli
  have hai2 := hai.sub (integrable_const (sampleAverage (loss a) x))
  have he : (∫ z, loss a z ∂μ) - sampleAverage (loss a) x =
      ∫ y : Fin n → Ω, sampleAverage (loss a) y - sampleAverage (loss a) x ∂productLaw μ n := by
    rw [integral_sub hai (integrable_const _), sampleAverage_integral μ hn hli]
    simp
  rw [he]
  exact integral_mono hai2 hx (fun y => pair_difference_le_envelope hn hl a (x, y))

end
end SPOBounds.NatarajanProof

end

/- Complete checked body: BoundedClassGeneralization -/
section

open MeasureTheory Filter

namespace SPOBounds.NatarajanProof

variable {Ω Θ : Type*} [MeasurableSpace Ω] [Nonempty Θ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem bounded_class_generalization {n : ℕ} (hn : 0 < n)
    {loss : Θ → Ω → ℝ} {B K : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hl : ∀ a z, 0 ≤ loss a z ∧ loss a z ≤ B)
    (hm : ∀ a, AEMeasurable (loss a) μ)
    (hD : AEMeasurable (classDeviation μ loss : (Fin n → Ω) → ℝ) (productLaw μ n))
    (hA : ∀ s : Fin n → Bool, AEMeasurable (classSigned loss s) (productLaw μ n))
    (hR : (∫ x : Fin n → Ω, classRademacher loss x ∂productLaw μ n) ≤ K)
    {δ : ℝ} (hδ : 0 < δ) :
    productLaw μ n {x | ∃ a, ¬ ((∫ z, loss a z ∂μ) ≤ sampleAverage (loss a) x +
      2 * K + B * Real.sqrt (Real.log (1 / δ) / (2 * n)))} ≤ ENNReal.ofReal δ := by
  by_cases hδ1 : 1 ≤ δ
  · exact (measure_mono (Set.subset_univ _)).trans (by
      rw [measure_univ]
      exact_mod_cast ENNReal.ofReal_le_ofReal hδ1)
  have hδlt : δ < 1 := lt_of_not_ge hδ1
  rcases eq_or_lt_of_le hB with hB0 | hBpos
  · have he : {x : Fin n → Ω | ∃ a, ¬ ((∫ z, loss a z ∂μ) ≤ sampleAverage (loss a) x +
        2 * K + B * Real.sqrt (Real.log (1 / δ) / (2 * n)))} = ∅ := by
      apply Set.eq_empty_of_forall_notMem
      rintro x ⟨a, ha⟩
      have h1 := risk_bounds (hm a) (hl a)
      have h2 := sampleAverage_bounds hn (hl a) x
      simp only [← hB0, zero_mul, add_zero] at ha h1 h2
      apply ha
      linarith
    rw [he, measure_empty]
    exact zero_le
  have hmean : (∫ x : Fin n → Ω, classDeviation μ loss x ∂productLaw μ n) ≤ 2 * K :=
    (expected_deviation_le_twice_rademacher μ hn hl hm hD hA).trans
      (mul_le_mul_of_nonneg_left hR (by norm_num))
  apply (measure_mono ?_).trans
    (hamming_confidence μ hn hBpos (classDeviation μ loss)
      (classDeviation_hamming hn hm hl) hD hδ hδlt)
  rintro x ⟨a, ha⟩
  have hb : BddAbove (Set.range fun a => (∫ z, loss a z ∂μ) - sampleAverage (loss a) x) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨a, rfl⟩
    have h1 := risk_bounds (hm a) (hl a)
    have h2 := sampleAverage_bounds hn (hl a) x
    linarith
  have hle : (∫ z, loss a z ∂μ) - sampleAverage (loss a) x ≤ classDeviation μ loss x :=
    le_ciSup hb a
  have hbad := lt_of_not_ge ha
  change B * Real.sqrt (Real.log (1 / δ) / (2 * n)) ≤
    classDeviation μ loss x - ∫ y, classDeviation μ loss y ∂productLaw μ n
  linarith

end SPOBounds.NatarajanProof

end

/- Complete checked body: AttributedMassart -/
section
-- Prove2me | solution 1 for SPOBounds.Natarajan.empirical_rademacher_massart
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:53:12.501552+00:00
-- url     : https://prove2.me/submissions/caaecc98-3fd4-4c17-935c-2998b3a8235d


namespace SPOBounds.Natarajan

theorem aux_erm_quad (A B X : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ t : ℝ, 0 < t → t * X ≤ A + t ^ 2 * B) : X ≤ Real.sqrt (4 * A * B) := by
  rcases le_or_gt X 0 with hX | hX
  · exact hX.trans (Real.sqrt_nonneg _)
  rcases eq_or_lt_of_le hB with hB0 | hBpos
  · exfalso
    have := h ((A + 1) / X) (by positivity)
    rw [← hB0, div_mul_cancel₀ _ hX.ne'] at this
    linarith
  · have h1 := h (X / (2 * B)) (by positivity)
    have e1 : X / (2 * B) * X = X ^ 2 / (2 * B) := by ring
    have e2 : (X / (2 * B)) ^ 2 * B = X ^ 2 / (4 * B) := by field_simp; ring
    rw [e1, e2] at h1
    have h2 : X ^ 2 / (4 * B) ≤ A := by
      have : X ^ 2 / (2 * B) - X ^ 2 / (4 * B) = X ^ 2 / (4 * B) := by field_simp; ring
      linarith
    rw [div_le_iff₀ (by positivity)] at h2
    have := Real.abs_le_sqrt (x := X) (y := 4 * A * B) (by linarith)
    exact (le_abs_self X).trans this

theorem aux_erm_mgf {n : ℕ} (a : Fin n → ℝ) (t : ℝ) :
    (1 / 2 ^ n : ℝ) * ∑ σ : Fin n → Bool,
        Real.exp (t * ∑ i, (if σ i then (1 : ℝ) else -1) * a i) ≤
      Real.exp (t ^ 2 * ∑ i, a i ^ 2 / 2) := by
  have h1 : ∀ σ : Fin n → Bool, Real.exp (t * ∑ i, (if σ i then (1 : ℝ) else -1) * a i) =
      ∏ i, Real.exp (t * ((if σ i then (1 : ℝ) else -1) * a i)) := by
    intro σ; rw [Finset.mul_sum, Real.exp_sum]
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun i (b : Bool) => Real.exp (t * ((if b then (1 : ℝ) else -1) * a i)))]
  have h2 : ∀ i, ∑ b : Bool, Real.exp (t * ((if b then (1 : ℝ) else -1) * a i)) =
      2 * Real.cosh (t * a i) := by
    intro i
    rw [Fintype.sum_bool, Real.cosh_eq]
    simp only [if_true, Bool.false_eq_true, if_false]
    ring_nf
  simp_rw [h2]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← mul_assoc,
    one_div, inv_mul_cancel₀ (by positivity), one_mul]
  calc ∏ i, Real.cosh (t * a i) ≤ ∏ i, Real.exp ((t * a i) ^ 2 / 2) :=
        Finset.prod_le_prod (fun i _ => (Real.cosh_pos _).le) (fun i _ => Real.cosh_le_exp_half_sq _)
    _ = Real.exp (t ^ 2 * ∑ i, a i ^ 2 / 2) := by
        rw [← Real.exp_sum]; congr 1
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_); ring

theorem aux_erm_massart {ι : Type*} {n : ℕ} (T : Finset ι) (hT : T.Nonempty)
    (φ : ι → Fin n → ℝ) (K : ℝ) (hK0 : 0 ≤ K) (hK : ∀ v ∈ T, ∑ i, φ v i ^ 2 ≤ K)
    (g : (Fin n → Bool) → ℝ)
    (hg : ∀ σ, ∃ v ∈ T, g σ ≤ ∑ i, (if σ i then (1 : ℝ) else -1) * φ v i) :
    (1 / 2 ^ n : ℝ) * ∑ σ, g σ ≤ Real.sqrt (4 * Real.log T.card * (K / 2)) := by
  have hcard : (1 : ℝ) ≤ T.card := by exact_mod_cast hT.card_pos
  apply aux_erm_quad _ _ _ (Real.log_nonneg hcard) (by positivity)
  intro t ht
  set M := (1 / 2 ^ n : ℝ) * ∑ σ, g σ with hM
  -- Jensen
  have hJ : Real.exp (t * M) ≤ ∑ σ : Fin n → Bool, (1 / 2 ^ n : ℝ) * Real.exp (t * g σ) := by
    have hconv := convexOn_exp.map_sum_le (t := (Finset.univ : Finset (Fin n → Bool)))
      (w := fun _ => (1 / 2 ^ n : ℝ)) (p := fun σ => t * g σ)
      (fun _ _ => by positivity) (by simp) (fun _ _ => Set.mem_univ _)
    simp only [smul_eq_mul] at hconv
    refine le_of_eq_of_le ?_ hconv
    congr 1
    rw [hM, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun σ _ => ?_); ring
  have hpt : ∀ σ : Fin n → Bool, Real.exp (t * g σ) ≤
      ∑ v ∈ T, Real.exp (t * ∑ i, (if σ i then (1 : ℝ) else -1) * φ v i) := by
    intro σ
    obtain ⟨v, hv, hle⟩ := hg σ
    calc Real.exp (t * g σ) ≤ Real.exp (t * ∑ i, (if σ i then (1 : ℝ) else -1) * φ v i) :=
          Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hle ht.le)
      _ ≤ _ := Finset.single_le_sum (f := fun v =>
            Real.exp (t * ∑ i, (if σ i then (1 : ℝ) else -1) * φ v i))
            (fun _ _ => (Real.exp_pos _).le) hv
  have hsum : ∑ σ : Fin n → Bool, (1 / 2 ^ n : ℝ) * Real.exp (t * g σ) ≤
      T.card * Real.exp (t ^ 2 * (K / 2)) := by
    calc ∑ σ : Fin n → Bool, (1 / 2 ^ n : ℝ) * Real.exp (t * g σ)
        ≤ ∑ σ : Fin n → Bool, (1 / 2 ^ n : ℝ) *
            ∑ v ∈ T, Real.exp (t * ∑ i, (if σ i then (1 : ℝ) else -1) * φ v i) :=
          Finset.sum_le_sum (fun σ _ => mul_le_mul_of_nonneg_left (hpt σ) (by positivity))
      _ = ∑ v ∈ T, (1 / 2 ^ n : ℝ) * ∑ σ : Fin n → Bool,
            Real.exp (t * ∑ i, (if σ i then (1 : ℝ) else -1) * φ v i) := by
          simp_rw [Finset.mul_sum]; exact Finset.sum_comm
      _ ≤ ∑ v ∈ T, Real.exp (t ^ 2 * (K / 2)) := by
          refine Finset.sum_le_sum (fun v hv => (aux_erm_mgf (φ v) t).trans ?_)
          refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ (sq_nonneg t))
          rw [← Finset.sum_div]; linarith [hK v hv]
      _ = T.card * Real.exp (t ^ 2 * (K / 2)) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hfin : Real.exp (t * M) ≤ Real.exp (Real.log T.card + t ^ 2 * (K / 2)) := by
    rw [Real.exp_add, Real.exp_log (by linarith)]
    exact hJ.trans hsum
  exact Real.exp_le_exp.1 hfin

open scoped InnerProductSpace in
theorem aux_erm_gap {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d))) (hSc : IsCompact S)
    (c v w0 : EuclideanSpace ℝ (Fin d)) (hv : v ∈ S) (hw0 : w0 ∈ S) :
    ⟪c, v⟫_ℝ - ⟪c, w0⟫_ℝ ≤ linGap S c := by
  have hcont : Continuous (fun u : EuclideanSpace ℝ (Fin d) => ⟪c, u⟫_ℝ) :=
    continuous_const.inner continuous_id
  have hK := hSc.image hcont
  unfold linGap
  have h1 := le_csSup hK.bddAbove (Set.mem_image_of_mem _ hv)
  have h2 := csInf_le hK.bddBelow (Set.mem_image_of_mem _ hw0)
  linarith

open scoped InnerProductSpace in
theorem aux_erm_bddC {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d))) (hSc : IsCompact S)
    (hS : S.Nonempty) (C : Set (EuclideanSpace ℝ (Fin d))) (hCb : Bornology.IsBounded C) :
    BddAbove (linGap S '' C) := by
  obtain ⟨R, hR⟩ := hCb.exists_norm_le
  obtain ⟨M, hM⟩ := hSc.isBounded.exists_norm_le
  refine ⟨2 * (R * M), ?_⟩
  rintro _ ⟨c, hc, rfl⟩
  have hbound : ∀ v ∈ S, |⟪c, v⟫_ℝ| ≤ R * M := fun v hv =>
    (abs_real_inner_le_norm c v).trans (mul_le_mul (hR c hc) (hM v hv) (norm_nonneg _)
      ((norm_nonneg c).trans (hR c hc)))
  unfold linGap
  have h1 : sSup ((fun v => ⟪c, v⟫_ℝ) '' S) ≤ R * M :=
    csSup_le (hS.image _) (by rintro _ ⟨v, hv, rfl⟩; exact (le_abs_self _).trans (hbound v hv))
  have h2 : -(R * M) ≤ sInf ((fun v => ⟪c, v⟫_ℝ) '' S) :=
    le_csInf (hS.image _) (by
      rintro _ ⟨v, hv, rfl⟩; exact neg_le.2 ((neg_le_abs _).trans (hbound v hv)))
  linarith

end SPOBounds.Natarajan

open SPOBounds.Natarajan
open scoped InnerProductSpace

theorem SPOSource.massart {d : ℕ} {X : Type*}
    (S : Set (EuclideanSpace ℝ (Fin d))) (hS : S.Nonempty) (hSc : IsCompact S)
    (_hSv : Convex ℝ S)
    (w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hw : IsOracle S w)
    (C : Set (EuclideanSpace ℝ (Fin d))) (_hC : C.Nonempty) (hCb : Bornology.IsBounded C)
    (H : Set (X → EuclideanSpace ℝ (Fin d)))
    (n : ℕ) (hn : 0 < n) (s : Fin n → X × EuclideanSpace ℝ (Fin d)) (hsC : ∀ i, (s i).2 ∈ C)
    (hfin : (sampleDecisions w H s).Finite) :
    empRademacherSPO w H s ≤
      linGapSet S C * Real.sqrt (2 * Real.log ((sampleDecisions w H s).ncard : ℝ) / n) := by
  classical
  rcases H.eq_empty_or_nonempty with hH | hH
  · subst hH
    have hV : sampleDecisions w (∅ : Set (X → EuclideanSpace ℝ (Fin d))) s = ∅ := by
      ext v; simp [sampleDecisions]
    have hsup : ∀ σ, signedSup w (∅ : Set (X → EuclideanSpace ℝ (Fin d))) σ s = 0 := by
      intro σ; unfold signedSup; exact Real.iSup_of_isEmpty _
    simp [empRademacherSPO, hsup, hV]
  · set V := sampleDecisions w H s with hVdef
    set T := hfin.toFinset with hTdef
    have hT : T.Nonempty := by
      obtain ⟨f, hf⟩ := hH; exact ⟨_, hfin.mem_toFinset.2 ⟨f, hf, rfl⟩⟩
    set L := linGapSet S C with hLdef
    have hbdd : BddAbove (linGap S '' C) := aux_erm_bddC S hSc hS C hCb
    have hloss : ∀ v ∈ T, ∀ i, 0 ≤ ⟪(s i).2, v i⟫_ℝ - ⟪(s i).2, w (s i).2⟫_ℝ ∧
        ⟪(s i).2, v i⟫_ℝ - ⟪(s i).2, w (s i).2⟫_ℝ ≤ L := by
      intro v hv i
      obtain ⟨f, hf, rfl⟩ := hfin.mem_toFinset.1 hv
      refine ⟨sub_nonneg.2 ((hw _).2 _ (hw _).1), ?_⟩
      exact (aux_erm_gap S hSc _ _ _ (hw _).1 (hw _).1).trans
        (le_csSup hbdd (Set.mem_image_of_mem _ (hsC i)))
    have hL : 0 ≤ L := by
      obtain ⟨v, hv⟩ := hT
      exact (hloss v hv ⟨0, hn⟩).1.trans (hloss v hv ⟨0, hn⟩).2
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    let φ : (Fin n → EuclideanSpace ℝ (Fin d)) → Fin n → ℝ :=
      fun v i => (1 / n : ℝ) * (⟪(s i).2, v i⟫_ℝ - ⟪(s i).2, w (s i).2⟫_ℝ)
    have hK : ∀ v ∈ T, ∑ i, φ v i ^ 2 ≤ L ^ 2 / n := by
      intro v hv
      calc ∑ i, φ v i ^ 2 ≤ ∑ _i : Fin n, (L / n) ^ 2 := by
            refine Finset.sum_le_sum (fun i _ => ?_)
            obtain ⟨h0, h1⟩ := hloss v hv i
            have e : φ v i = (⟪(s i).2, v i⟫_ℝ - ⟪(s i).2, w (s i).2⟫_ℝ) / n := by
              simp only [φ]; ring
            rw [e]
            exact pow_le_pow_left₀ (div_nonneg h0 hnR.le) (div_le_div_of_nonneg_right h1 hnR.le) 2
        _ = L ^ 2 / n := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            field_simp
    have hg : ∀ σ : Fin n → Bool, ∃ v ∈ T,
        signedSup w H σ s ≤ ∑ i, (if σ i then (1 : ℝ) else -1) * φ v i := by
      intro σ
      let G : (Fin n → EuclideanSpace ℝ (Fin d)) → ℝ :=
        fun v => ∑ i, (if σ i then (1 : ℝ) else -1) * φ v i
      obtain ⟨v0, hv0, heq⟩ := T.exists_mem_eq_sup' hT G
      refine ⟨v0, hv0, ?_⟩
      show signedSup w H σ s ≤ G v0
      rw [← heq]
      unfold signedSup
      have : Nonempty H := hH.to_subtype
      refine ciSup_le (fun f => ?_)
      have hv : (fun i => w (f.1 (s i).1)) ∈ T := hfin.mem_toFinset.2 ⟨f.1, f.2, rfl⟩
      refine le_trans (le_of_eq ?_) (T.le_sup' G hv)
      simp only [G, φ, spoLoss, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => by ring)
    have key := aux_erm_massart T hT φ (L ^ 2 / n) (by positivity) hK
      (fun σ => signedSup w H σ s) hg
    rw [Set.ncard_eq_toFinset_card V hfin]
    unfold empRademacherSPO
    refine key.trans (le_of_eq ?_)
    rw [show 4 * Real.log T.card * (L ^ 2 / n / 2) = L ^ 2 * (2 * Real.log T.card / n) by
      field_simp; ring, Real.sqrt_mul (sq_nonneg L), Real.sqrt_sq hL]

end

/- Complete checked body: SPOEnvelope -/
section

open MeasureTheory Filter SPOBounds.Natarajan
open scoped InnerProductSpace

namespace SPOBounds.NatarajanProof

noncomputable section

variable {d : ℕ} {X : Type*} [MeasurableSpace X]

theorem spoLoss_nonneg {S : Set (EuclideanSpace ℝ (Fin d))}
    {w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hw : IsOracle S w)
    (a c : EuclideanSpace ℝ (Fin d)) : 0 ≤ spoLoss w a c :=
  sub_nonneg.mpr ((hw c).2 _ (hw a).1)

theorem spoLoss_le_gapSet (S : Set (EuclideanSpace ℝ (Fin d))) (hS : S.Nonempty)
    (hSc : IsCompact S) (w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hw : IsOracle S w) (C : Set (EuclideanSpace ℝ (Fin d))) (hCb : Bornology.IsBounded C)
    (a c : EuclideanSpace ℝ (Fin d)) (hc : c ∈ C) : spoLoss w a c ≤ linGapSet S C :=
  (aux_erm_gap S hSc c (w a) (w c) (hw a).1 (hw c).1).trans
    (le_csSup (aux_erm_bddC S hSc hS C hCb) (Set.mem_image_of_mem _ hc))

theorem gapSet_nonneg (S : Set (EuclideanSpace ℝ (Fin d))) (hS : S.Nonempty)
    (hSc : IsCompact S) (w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hw : IsOracle S w) (C : Set (EuclideanSpace ℝ (Fin d))) (hC : C.Nonempty)
    (hCb : Bornology.IsBounded C) : 0 ≤ linGapSet S C := by
  obtain ⟨c, hc⟩ := hC
  exact (spoLoss_nonneg hw c c).trans (spoLoss_le_gapSet S hS hSc w hw C hCb c c hc)

def clippedSPO (B : ℝ) (w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (H : Set (X → EuclideanSpace ℝ (Fin d))) (f : H) (z : X × EuclideanSpace ℝ (Fin d)) : ℝ :=
  min B (spoLoss w (f.1 z.1) z.2)

omit [MeasurableSpace X] in
theorem clippedSPO_bounds {B : ℝ} (hB : 0 ≤ B)
    {S : Set (EuclideanSpace ℝ (Fin d))}
    {w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} (hw : IsOracle S w)
    (H : Set (X → EuclideanSpace ℝ (Fin d))) (f : H) (z : X × EuclideanSpace ℝ (Fin d)) :
    0 ≤ clippedSPO B w H f z ∧ clippedSPO B w H f z ≤ B :=
  ⟨le_min hB (spoLoss_nonneg hw _ _), min_le_left _ _⟩

theorem clippedSPO_measurable (B : ℝ)
    (w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (H : Set (X → EuclideanSpace ℝ (Fin d)))
    (hm : ∀ f ∈ H, Measurable (fun z : X × EuclideanSpace ℝ (Fin d) => spoLoss w (f z.1) z.2))
    (f : H) : Measurable (clippedSPO B w H f) :=
  measurable_const.min (hm f.1 f.2)

theorem sample_costs_ae (D : Measure (X × EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure D]
    (C : Set (EuclideanSpace ℝ (Fin d))) (hDC : ∀ᵐ z ∂D, z.2 ∈ C) (n : ℕ) :
    ∀ᵐ x : Fin n → X × EuclideanSpace ℝ (Fin d) ∂productLaw D n, ∀ i, (x i).2 ∈ C := by
  apply ae_all_iff.mpr
  intro i
  exact (measurePreserving_eval (fun _ : Fin n => D) i).quasiMeasurePreserving.ae hDC

end
end SPOBounds.NatarajanProof

end

/- Complete checked body: SPOClipping -/
section

open MeasureTheory Filter SPOBounds.Natarajan

namespace SPOBounds.NatarajanProof

noncomputable section

variable {d : ℕ} {X : Type*} [MeasurableSpace X]
    (S : Set (EuclideanSpace ℝ (Fin d))) (hS : S.Nonempty) (hSc : IsCompact S)
    (w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hw : IsOracle S w)
    (C : Set (EuclideanSpace ℝ (Fin d))) (hCb : Bornology.IsBounded C)
    (H : Set (X → EuclideanSpace ℝ (Fin d)))

include hS hSc hw hCb

omit [MeasurableSpace X] in
theorem clippedSPO_eq (f : H) (z : X × EuclideanSpace ℝ (Fin d)) (hz : z.2 ∈ C) :
    clippedSPO (linGapSet S C) w H f z = spoLoss w (f.1 z.1) z.2 :=
  min_eq_right (spoLoss_le_gapSet S hS hSc w hw C hCb _ _ hz)

omit [MeasurableSpace X] in
theorem clipped_sampleAverage_eq {n : ℕ} (f : H)
    (x : Fin n → X × EuclideanSpace ℝ (Fin d)) (hx : ∀ i, (x i).2 ∈ C) :
    sampleAverage (clippedSPO (linGapSet S C) w H f) x = empRisk w f.1 x := by
  unfold sampleAverage empRisk
  congr 1
  exact Finset.sum_congr rfl fun i _ => clippedSPO_eq S hS hSc w hw C hCb H f (x i) (hx i)

omit [MeasurableSpace X] in
theorem clipped_signed_eq {n : ℕ} (s : Fin n → Bool)
    (x : Fin n → X × EuclideanSpace ℝ (Fin d)) (hx : ∀ i, (x i).2 ∈ C) :
    classSigned (clippedSPO (linGapSet S C) w H) s x = signedSup w H s x := by
  unfold classSigned signedSup
  apply iSup_congr
  intro f
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [clippedSPO_eq S hS hSc w hw C hCb H f (x i) (hx i)]

omit [MeasurableSpace X] in
theorem clipped_rademacher_eq {n : ℕ}
    (x : Fin n → X × EuclideanSpace ℝ (Fin d)) (hx : ∀ i, (x i).2 ∈ C) :
    classRademacher (clippedSPO (linGapSet S C) w H) x = empRademacherSPO w H x := by
  unfold classRademacher empRademacherSPO
  congr 1
  exact Finset.sum_congr rfl fun s _ => clipped_signed_eq S hS hSc w hw C hCb H s x hx

variable (D : Measure (X × EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure D]
    (hDC : ∀ᵐ z ∂D, z.2 ∈ C)

include hDC

omit [IsProbabilityMeasure D] in
theorem clipped_risk_eq (f : H) :
    (∫ z, clippedSPO (linGapSet S C) w H f z ∂D) = spoRisk D w f.1 := by
  apply integral_congr_ae
  exact hDC.mono fun z hz => clippedSPO_eq S hS hSc w hw C hCb H f z hz

omit [IsProbabilityMeasure D] in
theorem clipped_deviation_eq {n : ℕ}
    (x : Fin n → X × EuclideanSpace ℝ (Fin d)) (hx : ∀ i, (x i).2 ∈ C) :
    classDeviation D (clippedSPO (linGapSet S C) w H) x = supDeviation D w H x := by
  unfold classDeviation supDeviation
  apply iSup_congr
  intro f
  rw [clipped_risk_eq S hS hSc w hw C hCb H D hDC f,
    clipped_sampleAverage_eq S hS hSc w hw C hCb H f x hx]

theorem clipped_scores_aemeasurable (n : ℕ)
    (hD : AEMeasurable (supDeviation D w H : (Fin n → X × EuclideanSpace ℝ (Fin d)) → ℝ)
      (productLaw D n))
    (hA : ∀ s : Fin n → Bool, AEMeasurable (signedSup w H s) (productLaw D n)) :
    AEMeasurable (classDeviation D (clippedSPO (linGapSet S C) w H) :
      (Fin n → X × EuclideanSpace ℝ (Fin d)) → ℝ) (productLaw D n) ∧
    ∀ s : Fin n → Bool, AEMeasurable (classSigned (clippedSPO (linGapSet S C) w H) s)
      (productLaw D n) := by
  have hgood := sample_costs_ae D C hDC n
  constructor
  · apply hD.congr
    exact hgood.mono fun x hx => (clipped_deviation_eq S hS hSc w hw C hCb H D hDC x hx).symm
  · intro s
    apply (hA s).congr
    exact hgood.mono fun x hx => (clipped_signed_eq S hS hSc w hw C hCb H s x hx).symm

end
end SPOBounds.NatarajanProof

end

/- Complete checked body: SPOGeneralization -/
section

open MeasureTheory Filter SPOBounds.Natarajan

namespace SPOBounds.NatarajanProof

theorem spo_generalization_of_rademacher {d : ℕ} {X : Type*} [MeasurableSpace X]
    (S : Set (EuclideanSpace ℝ (Fin d))) (hS : S.Nonempty) (hSc : IsCompact S)
    (w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hw : IsOracle S w)
    (C : Set (EuclideanSpace ℝ (Fin d))) (hC : C.Nonempty) (hCb : Bornology.IsBounded C)
    (D : Measure (X × EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure D]
    (hDC : ∀ᵐ z ∂D, z.2 ∈ C) (H : Set (X → EuclideanSpace ℝ (Fin d)))
    (hℓ : ∀ f ∈ H, Measurable (fun z : X × EuclideanSpace ℝ (Fin d) => spoLoss w (f z.1) z.2))
    (n : ℕ) (hn : 0 < n)
    (hΦ : AEMeasurable (supDeviation D w H : (Fin n → X × EuclideanSpace ℝ (Fin d)) → ℝ)
      (productLaw D n))
    (hA : ∀ s : Fin n → Bool, AEMeasurable (signedSup w H s) (productLaw D n))
    (K : ℝ) (hK : 0 ≤ K)
    (hR : ∀ x : Fin n → X × EuclideanSpace ℝ (Fin d),
      (∀ i, (x i).2 ∈ C) → empRademacherSPO w H x ≤ K)
    (δ : ℝ) (hδ : 0 < δ) :
    productLaw D n {x | ∃ f ∈ H, ¬ (spoRisk D w f ≤ empRisk w f x + 2 * K +
      linGapSet S C * Real.sqrt (Real.log (1 / δ) / (2 * n)))} ≤ ENNReal.ofReal δ := by
  classical
  rcases H.eq_empty_or_nonempty with hH | hH
  · simp [hH]
  let _ : Nonempty H := hH.to_subtype
  let loss := clippedSPO (linGapSet S C) w H
  have hB := gapSet_nonneg S hS hSc w hw C hC hCb
  have hl : ∀ a z, 0 ≤ loss a z ∧ loss a z ≤ linGapSet S C :=
    clippedSPO_bounds hB hw H
  have hm : ∀ a, AEMeasurable (loss a) D := fun a =>
    (clippedSPO_measurable (linGapSet S C) w H hℓ a).aemeasurable
  obtain ⟨hD, hAs⟩ := clipped_scores_aemeasurable S hS hSc w hw C hCb H D hDC n hΦ hA
  have hi (s : Fin n → Bool) : Integrable (classSigned loss s) (productLaw D n) :=
    integrable_abs_bounded (hAs s) (classSigned_abs_bound hn hl s)
  have hRi : Integrable (classRademacher loss : (Fin n → X × EuclideanSpace ℝ (Fin d)) → ℝ)
      (productLaw D n) := by
    exact (integrable_finsetSum _ (fun s _ => hi s)).const_mul _
  have hgood := sample_costs_ae D C hDC n
  have hRint : (∫ x : Fin n → X × EuclideanSpace ℝ (Fin d),
      classRademacher loss x ∂productLaw D n) ≤ K := by
    have ha : ∀ᵐ x ∂productLaw D n, classRademacher loss x ≤ K := by
      filter_upwards [hgood] with x hx
      rw [show classRademacher loss x = empRademacherSPO w H x from
        clipped_rademacher_eq S hS hSc w hw C hCb H x hx]
      exact hR x hx
    simpa using integral_mono_ae hRi (integrable_const K) ha
  have hmain := bounded_class_generalization D hn hB hK hl hm hD hAs hRint hδ
  apply (measure_mono_ae ?_).trans hmain
  filter_upwards [hgood] with x hx
  rintro ⟨f, hf, hbad⟩
  refine ⟨⟨f, hf⟩, ?_⟩
  change ¬ ((∫ z, clippedSPO (linGapSet S C) w H ⟨f, hf⟩ z ∂D) ≤
    sampleAverage (clippedSPO (linGapSet S C) w H ⟨f, hf⟩) x + 2 * K +
      linGapSet S C * Real.sqrt (Real.log (1 / δ) / (2 * n)))
  rw [clipped_risk_eq S hS hSc w hw C hCb H D hDC,
    clipped_sampleAverage_eq S hS hSc w hw C hCb H _ x hx]
  exact hbad

end SPOBounds.NatarajanProof

end

/- Complete checked body: ExtremeActive -/
section

set_option autoImplicit false
open Filter Topology

namespace SPOBounds.NatarajanProof

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

/-- At an extreme point, a feasible point sharing all active inequalities must coincide. -/
theorem extreme_eq_of_active_subset (a : ι → E →L[ℝ] ℝ) (b : ι → ℝ)
    {x y : E} (hx : x ∈ Set.extremePoints ℝ {z : E | ∀ i, a i z ≤ b i})
    (hy : ∀ i, a i y ≤ b i) (hactive : ∀ i, a i x = b i → a i y = b i) : x = y := by
  classical
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, a i (x+t • (x-y)) ≤ b i := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : a i x = b i
    · have hyi := hactive i hi
      filter_upwards [] with t
      simp only [map_add, map_smul, map_sub, hi, hyi, sub_self, smul_zero, add_zero]
      exact le_rfl
    · have hlt : a i x < b i := lt_of_le_of_ne (hx.1 i) hi
      have hc : Continuous (fun t : ℝ => a i (x+t • (x-y))) :=
        (a i).continuous.comp (continuous_const.add (continuous_id.smul continuous_const))
      have he := hc.continuousAt.eventually_lt continuousAt_const
        (show a i (x+(0 : ℝ) • (x-y)) < b i by simpa using hlt)
      filter_upwards [he] with t ht
      exact ht.le
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hnear
  let t : ℝ := ε/2
  have ht : 0 < t := by dsimp [t]; positivity
  have hz : ∀ i, a i (x+t • (x-y)) ≤ b i := by
    apply hball
    rw [Real.dist_eq, sub_zero, abs_of_pos ht]
    dsimp only [t]
    linarith
  have hden : 0 < 1+t := by linarith
  have hseg : x ∈ openSegment ℝ y (x+t • (x-y)) := by
    refine ⟨t/(1+t), 1/(1+t), by positivity, by positivity, ?_, ?_⟩
    · field_simp
      ring
    · have he : t/(1+t)+1/(1+t) = 1 := by field_simp; ring
      have ht' : (1/(1+t))*t = t/(1+t) := by ring
      simp only [smul_add, smul_sub, smul_smul, ht']
      calc
        _ = (t/(1+t)+1/(1+t)) • x := by module
        _ = x := by rw [he, one_smul]
  exact (hx.2 hy hz hseg).symm

/-- A finite intersection of closed linear halfspaces has finitely many extreme points. -/
theorem finite_extreme_halfspaces (a : ι → E →L[ℝ] ℝ) (b : ι → ℝ) :
    (Set.extremePoints ℝ {z : E | ∀ i, a i z ≤ b i}).Finite := by
  classical
  let P := Set.extremePoints ℝ {z : E | ∀ i, a i z ≤ b i}
  let f : P → Finset ι := fun x => Finset.univ.filter (fun i => a i x = b i)
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply extreme_eq_of_active_subset a b x.property y.property.1
    intro i hi
    have him : i ∈ f x := by simp [f, hi]
    rw [hxy] at him
    simpa [f] using him
  let : Finite P := Finite.of_injective f hf
  exact Set.toFinite P

end SPOBounds.NatarajanProof

end

/- Complete checked body: ExtremePolyhedron -/
section

set_option autoImplicit false
open scoped InnerProductSpace

namespace SPOBounds.NatarajanProof

theorem finite_extremePoints_of_polyhedron {d : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin d))) (hSp : SPOBounds.Natarajan.IsPolyhedron S) :
    (Set.extremePoints ℝ S).Finite := by
  obtain ⟨m, a, b, rfl⟩ := hSp
  exact finite_extreme_halfspaces (fun i => innerSL ℝ (a i)) b

end SPOBounds.NatarajanProof

end

/- Complete checked body: MulticlassFibers -/
section

set_option autoImplicit false
open scoped BigOperators

namespace SPOBounds.NatarajanProof

variable {Y : Type*} [Fintype Y] [DecidableEq Y] {n : ℕ}

def tailFamily (A : Finset (Fin (n+1) → Y)) : Finset (Fin n → Y) := A.image Fin.tail

def fiberLabels (A : Finset (Fin (n+1) → Y)) (v : Fin n → Y) : Finset Y :=
  Finset.univ.filter (fun y => Fin.cons y v ∈ A)

def pairFamily (A : Finset (Fin (n+1) → Y)) (p : Finset Y) : Finset (Fin n → Y) :=
  (tailFamily A).filter (fun v => p ⊆ fiberLabels A v)

omit [Fintype Y] in
@[simp] theorem mem_tailFamily {A : Finset (Fin (n+1) → Y)} {v : Fin n → Y} :
    v ∈ tailFamily A ↔ ∃ f ∈ A, Fin.tail f = v := Finset.mem_image

@[simp] theorem mem_fiberLabels {A : Finset (Fin (n+1) → Y)} {v : Fin n → Y} {y : Y} :
    y ∈ fiberLabels A v ↔ Fin.cons y v ∈ A := by simp [fiberLabels]

@[simp] theorem mem_pairFamily {A : Finset (Fin (n+1) → Y)} {p : Finset Y} {v : Fin n → Y} :
    v ∈ pairFamily A p ↔ v ∈ tailFamily A ∧ ∀ y ∈ p, Fin.cons y v ∈ A := by
  simp [pairFamily, Finset.subset_iff]

theorem tail_fiber_card (A : Finset (Fin (n+1) → Y)) (v : Fin n → Y) :
    (A.filter (fun f => Fin.tail f = v)).card = (fiberLabels A v).card := by
  classical
  have he : A.filter (fun f => Fin.tail f = v) =
      (fiberLabels A v).image (fun y => Fin.cons y v) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_image, mem_fiberLabels]
    constructor
    · rintro ⟨hf, htail⟩
      refine ⟨f 0, ?_, ?_⟩
      · simpa only [← htail, Fin.cons_self_tail] using hf
      · rw [← htail, Fin.cons_self_tail]
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, by ext i; rfl⟩
  have hi : Function.Injective (fun y : Y => (Fin.cons y v : Fin (n+1) → Y)) := by
    intro y z h
    have hh := congrFun h 0
    simpa only [Fin.cons_zero] using hh
  rw [he, Finset.card_image_of_injective _ hi]

theorem card_eq_sum_fiberLabels (A : Finset (Fin (n+1) → Y)) :
    A.card = ∑ v ∈ tailFamily A, (fiberLabels A v).card := by
  rw [Finset.card_eq_sum_card_image Fin.tail A]
  exact Finset.sum_congr rfl (fun v _ => tail_fiber_card A v)

theorem card_le_one_add_choose_two (k : ℕ) : k ≤ 1+k.choose 2 := by
  cases k with
  | zero => simp
  | succ k =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    omega

theorem sum_label_pairs (A : Finset (Fin (n+1) → Y)) :
    (∑ v ∈ tailFamily A, ((fiberLabels A v).powersetCard 2).card) =
      ∑ p ∈ (Finset.univ : Finset Y).powersetCard 2, (pairFamily A p).card := by
  have hp (L : Finset Y) : L.powersetCard 2 =
      ((Finset.univ : Finset Y).powersetCard 2).filter (fun p => p ⊆ L) := by
    ext p
    simp only [Finset.mem_powersetCard, Finset.mem_filter, Finset.subset_univ, true_and]
    tauto
  calc
    _ = ∑ v ∈ tailFamily A, ∑ p ∈ (Finset.univ : Finset Y).powersetCard 2,
        if p ⊆ fiberLabels A v then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      rw [hp, Finset.card_filter]
    _ = ∑ p ∈ (Finset.univ : Finset Y).powersetCard 2, ∑ v ∈ tailFamily A,
        if p ⊆ fiberLabels A v then 1 else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _
      rw [pairFamily, Finset.card_filter]

/-- The multiclass growth recurrence counts unordered pairs of labels in each fiber. -/
theorem multiclass_card_recurrence (A : Finset (Fin (n+1) → Y)) :
    A.card ≤ (tailFamily A).card+
      ∑ p ∈ (Finset.univ : Finset Y).powersetCard 2, (pairFamily A p).card := by
  rw [card_eq_sum_fiberLabels]
  calc
    _ ≤ ∑ v ∈ tailFamily A, (1+(fiberLabels A v).card.choose 2) :=
      Finset.sum_le_sum (fun v _ => card_le_one_add_choose_two (fiberLabels A v).card)
    _ = (tailFamily A).card+∑ v ∈ tailFamily A, ((fiberLabels A v).powersetCard 2).card := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one,
        Finset.card_powersetCard]
    _ = _ := by rw [sum_label_pairs]

end SPOBounds.NatarajanProof

end

/- Complete checked body: FiniteNDimension -/
section

set_option autoImplicit false
open SPOBounds.Natarajan

namespace SPOBounds.NatarajanProof

variable {Y : Type*} [Fintype Y] [DecidableEq Y] [Nonempty Y] {n : ℕ}

def finiteNBound (A : Finset (Fin n → Y)) (k : ℕ) : Prop :=
  ∀ T : Finset (Fin n), NShatters (A : Set (Fin n → Y)) T → T.card ≤ k

def liftCoordinates (T : Finset (Fin n)) : Finset (Fin (n+1)) := T.map (Fin.succEmb n)

@[simp] theorem mem_liftCoordinates_succ (T : Finset (Fin n)) (j : Fin n) :
    j.succ ∈ liftCoordinates T ↔ j ∈ T := by simp [liftCoordinates]

@[simp] theorem zero_notMem_liftCoordinates (T : Finset (Fin n)) :
    (0 : Fin (n+1)) ∉ liftCoordinates T := by simp [liftCoordinates]

@[simp] theorem liftCoordinates_card (T : Finset (Fin n)) :
    (liftCoordinates T).card = T.card := by simp [liftCoordinates]

omit [Fintype Y] in
theorem tail_shatters_lift (A : Finset (Fin (n+1) → Y)) (T : Finset (Fin n))
    (hT : NShatters (tailFamily A : Set (Fin n → Y)) T) :
    NShatters (A : Set (Fin (n+1) → Y)) (liftCoordinates T) := by
  classical
  obtain ⟨g₁, g₂, hne, hpatterns⟩ := hT
  let y₀ : Y := Classical.choice inferInstance
  refine ⟨Fin.cons y₀ g₁, Fin.cons y₀ g₂, ?_, ?_⟩
  · intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
    simpa only [Fin.coe_succEmb, Fin.cons_succ] using hne j hj
  · intro U hU
    let V := T.filter (fun j => j.succ ∈ U)
    obtain ⟨g, hg, h₁, h₂⟩ := hpatterns V (Finset.filter_subset _ _)
    obtain ⟨f, hf, htail⟩ := mem_tailFamily.mp hg
    refine ⟨f, hf, ?_, ?_⟩
    · intro i hi
      obtain ⟨j, hj, hji⟩ := Finset.mem_map.mp (hU hi)
      subst i
      have hv : j ∈ V := Finset.mem_filter.mpr ⟨hj, hi⟩
      have hh := h₁ j hv
      change Fin.tail f j = g₁ j
      rw [htail]
      exact hh
    · intro i hi hni
      obtain ⟨j, hj, hji⟩ := Finset.mem_map.mp hi
      subst i
      have hv : j ∉ V := fun hv => hni (Finset.mem_filter.mp hv).2
      have hh := h₂ j hj hv
      change Fin.tail f j = g₂ j
      rw [htail]
      exact hh

omit [Fintype Y] in
theorem finiteNBound_tail (A : Finset (Fin (n+1) → Y)) (k : ℕ) (hA : finiteNBound A k) :
    finiteNBound (tailFamily A) k := by
  intro T hT
  simpa only [liftCoordinates_card] using hA (liftCoordinates T) (tail_shatters_lift A T hT)

omit [Nonempty Y] in
/-- Two available labels above every prefix add one shattered coordinate. -/
theorem pair_shatters_lift (A : Finset (Fin (n+1) → Y)) (a b : Y) (hab : a ≠ b)
    (T : Finset (Fin n))
    (hT : NShatters (pairFamily A {a,b} : Set (Fin n → Y)) T) :
    NShatters (A : Set (Fin (n+1) → Y)) (insert 0 (liftCoordinates T)) := by
  classical
  obtain ⟨g₁, g₂, hne, hpatterns⟩ := hT
  refine ⟨Fin.cons a g₁, Fin.cons b g₂, ?_, ?_⟩
  · intro i hi
    cases i using Fin.cases with
    | zero => simpa only [Fin.cons_zero] using hab
    | succ j =>
      have hj : j ∈ T := by simpa using hi
      simpa only [Fin.cons_succ] using hne j hj
  · intro U hU
    let V := T.filter (fun j => j.succ ∈ U)
    obtain ⟨g, hg, h₁, h₂⟩ := hpatterns V (Finset.filter_subset _ _)
    have hlabels := (mem_pairFamily.mp hg).2
    let f : Fin (n+1) → Y := Fin.cons (if (0 : Fin (n+1)) ∈ U then a else b) g
    have hf : f ∈ A := by
      dsimp only [f]
      split_ifs
      · exact hlabels a (by simp)
      · exact hlabels b (by simp)
    refine ⟨f, hf, ?_, ?_⟩
    · intro i hi
      cases i using Fin.cases with
      | zero => simp [f, hi]
      | succ j =>
        have hj : j ∈ T := by simpa using hU hi
        have hv : j ∈ V := Finset.mem_filter.mpr ⟨hj, hi⟩
        simpa only [f, Fin.cons_succ] using h₁ j hv
    · intro i hi hni
      cases i using Fin.cases with
      | zero => simp [f, hni]
      | succ j =>
        have hj : j ∈ T := by simpa using hi
        have hv : j ∉ V := fun hv => hni (Finset.mem_filter.mp hv).2
        simpa only [f, Fin.cons_succ] using h₂ j hj hv

omit [Nonempty Y] in
theorem finiteNBound_pair (A : Finset (Fin (n+1) → Y)) (k : ℕ)
    (hA : finiteNBound A (k+1)) (p : Finset Y) (hp : p.card = 2) :
    finiteNBound (pairFamily A p) k := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hp
  intro T hT
  have h := hA _ (pair_shatters_lift A a b hab T hT)
  simp only [Finset.card_insert_of_notMem (zero_notMem_liftCoordinates T), liftCoordinates_card] at h
  omega

omit [Nonempty Y] in
theorem pairFamily_empty_of_zero (A : Finset (Fin (n+1) → Y)) (hA : finiteNBound A 0)
    (p : Finset Y) (hp : p.card = 2) : pairFamily A p = ∅ := by
  classical
  by_contra he
  obtain ⟨g, hg⟩ := Finset.nonempty_iff_ne_empty.mpr he
  have hsh : NShatters (pairFamily A p : Set (Fin n → Y)) ∅ := by
    refine ⟨g, g, by simp, ?_⟩
    intro U hU
    have hU0 : U = ∅ := Finset.subset_empty.mp hU
    exact ⟨g, hg, by simp [hU0], by simp⟩
  obtain ⟨a, b, hab, hp'⟩ := Finset.card_eq_two.mp hp
  rw [hp'] at hsh
  have h := hA _ (pair_shatters_lift A a b hab ∅ hsh)
  simp [liftCoordinates] at h

end SPOBounds.NatarajanProof

end

/- Complete checked body: MulticlassCounting -/
section

set_option autoImplicit false
open scoped BigOperators

namespace SPOBounds.NatarajanProof

variable {Y : Type*} [Fintype Y] [DecidableEq Y] [Nonempty Y]

/-- The pair recurrence yields a convenient polynomial without a binomial-tail estimate. -/
theorem finiteNBound_card (n k : ℕ) (A : Finset (Fin n → Y)) (hA : finiteNBound A k) :
    A.card ≤ (1+n*(Fintype.card Y).choose 2)^k := by
  induction n generalizing k with
  | zero =>
    have h := Finset.card_le_univ A
    simpa using h
  | succ n ih =>
    have hrec := multiclass_card_recurrence A
    cases k with
    | zero =>
      have hp : ∀ p ∈ (Finset.univ : Finset Y).powersetCard 2,
          (pairFamily A p).card = 0 := by
        intro p hp
        rw [pairFamily_empty_of_zero A hA p (Finset.mem_powersetCard.mp hp).2]
        rfl
      simp only [Finset.sum_eq_zero hp, add_zero] at hrec
      exact hrec.trans (by simpa using ih 0 (tailFamily A) (finiteNBound_tail A 0 hA))
    | succ k =>
      have ht := ih (k+1) (tailFamily A) (finiteNBound_tail A (k+1) hA)
      have hp : (∑ p ∈ (Finset.univ : Finset Y).powersetCard 2, (pairFamily A p).card) ≤
          (Fintype.card Y).choose 2 * (1+n*(Fintype.card Y).choose 2)^k := by
        calc
          _ ≤ ∑ p ∈ (Finset.univ : Finset Y).powersetCard 2,
              (1+n*(Fintype.card Y).choose 2)^k := by
            apply Finset.sum_le_sum
            intro p hp
            exact ih k (pairFamily A p)
              (finiteNBound_pair A k hA p (Finset.mem_powersetCard.mp hp).2)
          _ = _ := by simp
      let q := (Fintype.card Y).choose 2
      let x := 1+n*q
      calc
        A.card ≤ x^(k+1)+q*x^k := hrec.trans (add_le_add ht hp)
        _ = (x+q)*x^k := by rw [pow_succ]; ring
        _ ≤ (x+q)*(x+q)^k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) k)
        _ = (1+(n+1)*q)^(k+1) := by
          have he : x+q = 1+(n+1)*q := by dsimp [x]; ring
          rw [he, pow_succ]
          ring

lemma one_add_choose_two_le_sq (m : ℕ) (hm : 0 < m) : 1+m.choose 2 ≤ m^2 := by
  have hch : m.choose 2 ≤ m*(m-1) := by
    rw [Nat.choose_two_right]
    exact Nat.div_le_self _ _
  have hmul : m*(m-1)+m = m^2 := by
    calc
      m*(m-1)+m = m*((m-1)+1) := by ring
      _ = m^2 := by rw [Nat.sub_add_cancel hm, pow_two]
  omega

theorem finiteNBound_card_power (n k : ℕ) (hn : 0 < n)
    (A : Finset (Fin n → Y)) (hA : finiteNBound A k) :
    A.card ≤ (n*(Fintype.card Y)^2)^k := by
  apply (finiteNBound_card n k A hA).trans
  apply Nat.pow_le_pow_left
  have hm : 0 < Fintype.card Y := Fintype.card_pos
  calc
    1+n*(Fintype.card Y).choose 2 ≤ n*(1+(Fintype.card Y).choose 2) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    _ ≤ n*(Fintype.card Y)^2 := Nat.mul_le_mul_left _ (one_add_choose_two_le_sq _ hm)

end SPOBounds.NatarajanProof

end

/- Complete checked body: SampleShattering -/
section

set_option autoImplicit false
open SPOBounds.Natarajan

namespace SPOBounds.NatarajanProof

variable {X Y : Type*} [Nonempty Y] {n : ℕ}

omit [Nonempty Y] in
/-- A shattered sample contains no two copies of the same feature point. -/
theorem sample_shattering_injective (F : Set (X → Y)) (xs : Fin n → X)
    (T : Finset (Fin n))
    (hT : NShatters ((fun f : X → Y => f ∘ xs) '' F) T) :
    Set.InjOn xs (T : Set (Fin n)) := by
  classical
  obtain ⟨g₁, g₂, hne, hp⟩ := hT
  intro i hi j hj heq
  by_contra hij
  obtain ⟨f₀, ⟨g₀, _, rfl⟩, _, h₀⟩ := hp ∅ (Finset.empty_subset T)
  have h₂ij : g₂ i = g₂ j := by
    rw [← h₀ i hi (by simp), ← h₀ j hj (by simp)]
    exact congrArg g₀ heq
  obtain ⟨f₁, ⟨g, _, rfl⟩, h₁, h₂⟩ := hp {i} (by simpa using hi)
  have he : g₁ i = g₂ j := by
    rw [← h₁ i (by simp), ← h₂ j hj (by simpa using Ne.symm hij)]
    exact congrArg g heq
  exact hne i hi (he.trans h₂ij.symm)

noncomputable def extendSampleLabels (xs : Fin n → X) (T : Finset (Fin n))
    (g : Fin n → Y) (x : X) : Y := by
  classical
  exact if h : ∃ i ∈ T, xs i = x then g h.choose else Classical.choice inferInstance

lemma extendSampleLabels_apply (xs : Fin n → X) (T : Finset (Fin n))
    (hinj : Set.InjOn xs (T : Set (Fin n))) (g : Fin n → Y)
    (i : Fin n) (hi : i ∈ T) : extendSampleLabels xs T g (xs i) = g i := by
  classical
  have hex : ∃ j ∈ T, xs j = xs i := ⟨i, hi, rfl⟩
  rw [extendSampleLabels, dif_pos hex]
  congr 1
  exact hinj hex.choose_spec.1 hi hex.choose_spec.2

/-- Natarajan shattering of sample positions transfers to their distinct feature values. -/
theorem sample_shattering_image [DecidableEq X] (F : Set (X → Y)) (xs : Fin n → X)
    (T : Finset (Fin n))
    (hT : NShatters ((fun f : X → Y => f ∘ xs) '' F) T) :
    NShatters F (T.image xs) := by
  classical
  have hinj := sample_shattering_injective F xs T hT
  obtain ⟨g₁, g₂, hne, hp⟩ := hT
  refine ⟨extendSampleLabels xs T g₁, extendSampleLabels xs T g₂, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    simpa only [extendSampleLabels_apply xs T hinj _ i hi] using hne i hi
  · intro U hU
    let V := T.filter (fun i => xs i ∈ U)
    obtain ⟨f, ⟨g, hg, rfl⟩, h₁, h₂⟩ := hp V (Finset.filter_subset _ _)
    refine ⟨g, hg, ?_, ?_⟩
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hU hx)
      rw [extendSampleLabels_apply xs T hinj _ i hi]
      exact h₁ i (Finset.mem_filter.mpr ⟨hi, hx⟩)
    · intro x hx hnx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      rw [extendSampleLabels_apply xs T hinj _ i hi]
      exact h₂ i hi (by simp [V, hnx])

theorem sample_shattering_card_le [DecidableEq X] (F : Set (X → Y)) (xs : Fin n → X)
    (k : ℕ) (hk : ∀ T : Finset X, NShatters F T → T.card ≤ k)
    (T : Finset (Fin n))
    (hT : NShatters ((fun f : X → Y => f ∘ xs) '' F) T) : T.card ≤ k := by
  have h := hk (T.image xs) (sample_shattering_image F xs T hT)
  rwa [Finset.card_image_of_injOn (sample_shattering_injective F xs T hT)] at h

end SPOBounds.NatarajanProof

end

/- Complete checked body: FiniteLabelRestrictions -/
section

set_option autoImplicit false
open SPOBounds.Natarajan

namespace SPOBounds.NatarajanProof

/-- Finite-label Natarajan counting, including repeated sample points and empty classes. -/
theorem restrictions_finite_card {X Y : Type*} (F : Set (X → Y)) (V : Set Y)
    (hV : V.Finite) (hlabels : ∀ f ∈ F, ∀ x, f x ∈ V)
    (k : ℕ) (hk : ∀ T : Finset X, NShatters F T → T.card ≤ k)
    (n : ℕ) (hn : 0 < n) (xs : Fin n → X) :
    ((fun f : X → Y => f ∘ xs) '' F).Finite ∧
      ((fun f : X → Y => f ∘ xs) '' F).ncard ≤ (n*V.ncard^2)^k := by
  classical
  by_cases hF : F = ∅
  · simp [hF]
  have hFn : F.Nonempty := Set.nonempty_iff_ne_empty.mpr hF
  obtain ⟨f₀, hf₀⟩ := hFn
  let v₀ : V := ⟨f₀ (xs ⟨0, hn⟩), hlabels f₀ hf₀ _⟩
  let : Nonempty V := ⟨v₀⟩
  let : Fintype V := hV.fintype
  let F' : Set (X → V) := {g | ∃ f ∈ F, ∀ x, (g x : Y) = f x}
  have hk' : ∀ T : Finset X, NShatters F' T → T.card ≤ k := by
    intro T hT
    apply hk T
    obtain ⟨g₁, g₂, hne, hp⟩ := hT
    refine ⟨fun x => (g₁ x : Y), fun x => (g₂ x : Y), ?_, ?_⟩
    · intro x hx he
      exact hne x hx (Subtype.ext he)
    · intro U hU
      obtain ⟨g, ⟨f, hf, hgf⟩, h₁, h₂⟩ := hp U hU
      refine ⟨f, hf, ?_, ?_⟩
      · intro x hx
        rw [← hgf x, h₁ x hx]
      · intro x hx hnx
        rw [← hgf x, h₂ x hx hnx]
  let R' : Set (Fin n → V) := (fun f : X → V => f ∘ xs) '' F'
  have hR' : R'.Finite := Set.toFinite _
  let A := hR'.toFinset
  have hA : finiteNBound A k := by
    intro T hT
    apply sample_shattering_card_le F' xs k hk' T
    simpa only [A, Set.Finite.coe_toFinset, R'] using hT
  have hcount := finiteNBound_card_power n k hn A hA
  let forget : (Fin n → V) → (Fin n → Y) := fun v i => (v i : Y)
  have he : ((fun f : X → Y => f ∘ xs) '' F) = forget '' R' := by
    ext v
    constructor
    · rintro ⟨f, hf, rfl⟩
      let g : X → V := fun x => ⟨f x, hlabels f hf x⟩
      refine ⟨g ∘ xs, ?_, rfl⟩
      exact ⟨g, ⟨f, hf, fun _ => rfl⟩, rfl⟩
    · rintro ⟨v', ⟨g, ⟨f, hf, hgf⟩, rfl⟩, rfl⟩
      refine ⟨f, hf, ?_⟩
      funext i
      exact (hgf (xs i)).symm
  have hi : Function.Injective forget := by
    intro v w he
    funext i
    exact Subtype.ext (congrFun he i)
  rw [he]
  refine ⟨hR'.image forget, ?_⟩
  rw [Set.ncard_image_of_injective R' hi]
  have hc : Fintype.card V = V.ncard := Set.fintypeCard_eq_ncard V
  rw [hc] at hcount
  simpa only [A, ← Set.ncard_eq_toFinset_card R' hR'] using hcount

end SPOBounds.NatarajanProof

end

/- Complete checked body: EmpiricalComplexity -/
section

set_option autoImplicit false
open SPOBounds.Natarajan

namespace SPOBounds.NatarajanProof

variable {d : ℕ} {X : Type*}

 theorem sampleDecisions_card_bound
    (S : Set (EuclideanSpace ℝ (Fin d))) (hSp : IsPolyhedron S)
    (w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hwv : ∀ c, w c ∈ Set.extremePoints ℝ S)
    (H : Set (X → EuclideanSpace ℝ (Fin d))) (k : ℕ)
    (hk : ∀ T : Finset X, NShatters (oracleClass w H) T → T.card ≤ k)
    (n : ℕ) (hn : 0 < n) (s : Fin n → X × EuclideanSpace ℝ (Fin d)) :
    (sampleDecisions w H s).Finite ∧
      (sampleDecisions w H s).ncard ≤ (n*(Set.extremePoints ℝ S).ncard^2)^k := by
  have he : sampleDecisions w H s =
      (fun f : X → EuclideanSpace ℝ (Fin d) => f ∘ (fun i => (s i).1)) '' oracleClass w H := by
    ext v
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact ⟨fun x => w (f x), ⟨f, hf, rfl⟩, rfl⟩
    · rintro ⟨g, ⟨f, hf, rfl⟩, rfl⟩
      exact ⟨f, hf, rfl⟩
  rw [he]
  apply restrictions_finite_card _ _ (finite_extremePoints_of_polyhedron S hSp) _ k hk n hn
  rintro g ⟨f, _, rfl⟩ x
  exact hwv (f x)

/-- The actual finite Massart theorem combined with the exact multiclass restriction count. -/
theorem empirical_complexity_bound
    (S : Set (EuclideanSpace ℝ (Fin d))) (hS : S.Nonempty) (hSc : IsCompact S)
    (hSv : Convex ℝ S) (hSp : IsPolyhedron S)
    (w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hw : IsOracle S w)
    (hwv : ∀ c, w c ∈ Set.extremePoints ℝ S)
    (C : Set (EuclideanSpace ℝ (Fin d))) (hC : C.Nonempty) (hCb : Bornology.IsBounded C)
    (H : Set (X → EuclideanSpace ℝ (Fin d))) (k : ℕ)
    (hk : ∀ T : Finset X, NShatters (oracleClass w H) T → T.card ≤ k)
    (n : ℕ) (hn : 0 < n) (s : Fin n → X × EuclideanSpace ℝ (Fin d))
    (hsC : ∀ i, (s i).2 ∈ C) :
    empRademacherSPO w H s ≤ linGapSet S C *
      Real.sqrt (2*k*Real.log ((n : ℝ)*((Set.extremePoints ℝ S).ncard : ℝ)^2)/n) := by
  classical
  have hB : 0 ≤ linGapSet S C := by
    obtain ⟨c, hc⟩ := hC
    have h0 : 0 ≤ linGap S c := by
      simpa only [sub_self] using aux_erm_gap S hSc c (w c) (w c) (hw c).1 (hw c).1
    exact h0.trans (le_csSup (aux_erm_bddC S hSc hS C hCb) ⟨c, hc, rfl⟩)
  by_cases hH : H = ∅
  · subst H
    have hz : empRademacherSPO w (∅ : Set (X → EuclideanSpace ℝ (Fin d))) s = 0 := by
      simp only [empRademacherSPO, signedSup, Real.iSup_of_isEmpty, Finset.sum_const_zero, mul_zero]
    rw [hz]
    exact mul_nonneg hB (Real.sqrt_nonneg _)
  obtain ⟨hfin, hcard⟩ := sampleDecisions_card_bound S hSp w hwv H k hk n hn s
  have hnonempty : (sampleDecisions w H s).Nonempty := by
    obtain ⟨f, hf⟩ := Set.nonempty_iff_ne_empty.mpr hH
    exact ⟨fun i => w (f (s i).1), f, hf, rfl⟩
  have hpos : (0 : ℝ) < (sampleDecisions w H s).ncard :=
    Nat.cast_pos.mpr ((Set.ncard_pos hfin).mpr hnonempty)
  have hcardR : ((sampleDecisions w H s).ncard : ℝ) ≤
      ((n : ℝ)*((Set.extremePoints ℝ S).ncard : ℝ)^2)^k := by exact_mod_cast hcard
  have hlog := Real.log_le_log hpos hcardR
  rw [Real.log_pow] at hlog
  apply (SPOSource.massart S hS hSc hSv w hw C hC hCb H n hn s hsC hfin).trans
  apply mul_le_mul_of_nonneg_left _ hB
  apply Real.sqrt_le_sqrt
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  calc
    2 * Real.log ((sampleDecisions w H s).ncard : ℝ) ≤
        2 * ((k : ℝ)*Real.log ((n : ℝ)*((Set.extremePoints ℝ S).ncard : ℝ)^2)) := by linarith
    _ = _ := by ring

end SPOBounds.NatarajanProof

end

/- Complete checked body: NatarajanRoot -/
section

open MeasureTheory

namespace SPOBounds.Natarajan

/-- **Theorem 2, second display** (arXiv:1905.11488v3, p. 11). Let `S` be a nonempty compact
convex polyhedron with extreme-point set `𝔖`, let the oracle `w` return extreme points of `S`,
let every set N-shattered by `w*(H)` have at most `k` elements, and let the cost vectors lie
almost surely in the nonempty bounded set `C`. For any `δ > 0`, with probability at least
`1 − δ` over an i.i.d. sample of size `n ≥ 1`, every `f ∈ H` satisfies
`R_SPO(f) ≤ R̂_SPO(f) + 2 ω_S(C) √(2 k log(n |𝔖|²) / n) + ω_S(C) √(log(1/δ) / (2n))`.
Stated as: the (outer) `Dⁿ`-measure of the samples on which some `f ∈ H` violates the bound is
at most `δ`. The measurability hypotheses `hℓ`, `hΦ`, `hA` are added (the paper is silent). -/
theorem natarajan_generalization_bound {d : ℕ} {X : Type*} [MeasurableSpace X]
    (S : Set (EuclideanSpace ℝ (Fin d))) (hS : S.Nonempty) (hSc : IsCompact S)
    (hSv : Convex ℝ S) (hSp : IsPolyhedron S)
    (w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hw : IsOracle S w)
    (hwv : ∀ c, w c ∈ Set.extremePoints ℝ S)
    (C : Set (EuclideanSpace ℝ (Fin d))) (hC : C.Nonempty) (hCb : Bornology.IsBounded C)
    (D : Measure (X × EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure D]
    (hDC : ∀ᵐ z ∂D, z.2 ∈ C)
    (H : Set (X → EuclideanSpace ℝ (Fin d)))
    (hℓ : ∀ f ∈ H, Measurable (fun z : X × EuclideanSpace ℝ (Fin d) => spoLoss w (f z.1) z.2))
    (k : ℕ) (hk : ∀ T : Finset X, NShatters (oracleClass w H) T → T.card ≤ k)
    (n : ℕ) (hn : 0 < n)
    (hΦ : AEMeasurable (fun s : Fin n → X × EuclideanSpace ℝ (Fin d) => supDeviation D w H s)
      (Measure.pi fun _ : Fin n => D))
    (hA : ∀ σ : Fin n → Bool,
      AEMeasurable (fun s : Fin n → X × EuclideanSpace ℝ (Fin d) => signedSup w H σ s)
        (Measure.pi fun _ : Fin n => D))
    (δ : ℝ) (hδ : 0 < δ) :
    Measure.pi (fun _ : Fin n => D)
        {s | ∃ f ∈ H, ¬ (spoRisk D w f ≤ empRisk w f s +
          2 * linGapSet S C * Real.sqrt (2 * k *
            Real.log ((n : ℝ) * ((Set.extremePoints ℝ S).ncard : ℝ) ^ 2) / n) +
          linGapSet S C * Real.sqrt (Real.log (1 / δ) / (2 * n)))} ≤ ENNReal.ofReal δ := by
  have hB := SPOBounds.NatarajanProof.gapSet_nonneg S hS hSc w hw C hC hCb
  have h := SPOBounds.NatarajanProof.spo_generalization_of_rademacher
    S hS hSc w hw C hC hCb D hDC H hℓ n hn hΦ hA
    (linGapSet S C * Real.sqrt (2 * k *
      Real.log ((n : ℝ) * ((Set.extremePoints ℝ S).ncard : ℝ)^2) / n))
    (mul_nonneg hB (Real.sqrt_nonneg _))
    (fun x hx => SPOBounds.NatarajanProof.empirical_complexity_bound
      S hS hSc hSv hSp w hw hwv C hC hCb H k hk n hn x hx) δ hδ
  simpa only [mul_assoc] using h

end SPOBounds.Natarajan

end

open MeasureTheory SPOBounds.Natarajan

theorem solution {d : ℕ} {X : Type*} [MeasurableSpace X]
    (S : Set (EuclideanSpace ℝ (Fin d))) (hS : S.Nonempty) (hSc : IsCompact S)
    (hSv : Convex ℝ S) (hSp : IsPolyhedron S)
    (w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hw : IsOracle S w)
    (hwv : ∀ c, w c ∈ Set.extremePoints ℝ S)
    (C : Set (EuclideanSpace ℝ (Fin d))) (hC : C.Nonempty) (hCb : Bornology.IsBounded C)
    (D : Measure (X × EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure D]
    (hDC : ∀ᵐ z ∂D, z.2 ∈ C)
    (H : Set (X → EuclideanSpace ℝ (Fin d)))
    (hℓ : ∀ f ∈ H, Measurable (fun z : X × EuclideanSpace ℝ (Fin d) => spoLoss w (f z.1) z.2))
    (k : ℕ) (hk : ∀ T : Finset X, NShatters (oracleClass w H) T → T.card ≤ k)
    (n : ℕ) (hn : 0 < n)
    (hΦ : AEMeasurable (fun s : Fin n → X × EuclideanSpace ℝ (Fin d) => supDeviation D w H s)
      (Measure.pi fun _ : Fin n => D))
    (hA : ∀ σ : Fin n → Bool,
      AEMeasurable (fun s : Fin n → X × EuclideanSpace ℝ (Fin d) => signedSup w H σ s)
        (Measure.pi fun _ : Fin n => D))
    (δ : ℝ) (hδ : 0 < δ) :
    Measure.pi (fun _ : Fin n => D)
        {s | ∃ f ∈ H, ¬ (spoRisk D w f ≤ empRisk w f s +
          2 * linGapSet S C * Real.sqrt (2 * k *
            Real.log ((n : ℝ) * ((Set.extremePoints ℝ S).ncard : ℝ) ^ 2) / n) +
          linGapSet S C * Real.sqrt (Real.log (1 / δ) / (2 * n)))} ≤ ENNReal.ofReal δ := by
  exact SPOBounds.Natarajan.natarajan_generalization_bound S hS hSc hSv hSp w hw hwv C hC hCb D hDC H hℓ k hk n hn hΦ hA δ hδ

#print axioms SPOBounds.Natarajan.natarajan_generalization_bound
#print axioms solution
