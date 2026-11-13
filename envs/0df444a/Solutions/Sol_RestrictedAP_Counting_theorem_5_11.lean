-- Prove2me | solution 1 for RestrictedAP.Counting.theorem_5_11
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T22:20:27.979594+00:00
-- url     : https://prove2.me/submissions/4573ec63-028e-43fe-a3b3-b8ef80d6515f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BraneBrauer_Orthogonal_ComplexGaussian
import Theorems.Thm_RestrictedAP_Counting_theorem_A_1_real

section
set_option autoImplicit false

open MeasureTheory ComplexOrder

namespace RestrictedAP.Counting.Dev.R511
open RestrictedAP.Counting Matrix

noncomputable section

/-- The real `2 × 2` block of a complex number `c`: `[[re c, -im c], [im c, re c]]`. -/
def blk (a b : Fin 2) (c : ℂ) : ℝ :=
  if a = 0 then (if b = 0 then c.re else -c.im) else (if b = 0 then c.im else c.re)

/-- Coordinate `a` of a complex number: real part for `a = 0`, imaginary part for `a = 1`. -/
def cmp (a : Fin 2) (c : ℂ) : ℝ := if a = 0 then c.re else c.im

variable {ℓ n : ℕ}

/-- Realification of a complex matrix. -/
def realify (M : Matrix (Fin ℓ × Fin n) (Fin ℓ × Fin n) ℂ) :
    Matrix (Fin ℓ × (Fin n × Fin 2)) (Fin ℓ × (Fin n × Fin 2)) ℝ :=
  fun p q => blk p.2.2 q.2.2 (M (p.1, p.2.1) (q.1, q.2.1))

/-- Realification of a complex vector. -/
def re2 (v : Fin ℓ × Fin n → ℂ) : Fin ℓ × (Fin n × Fin 2) → ℝ :=
  fun p => cmp p.2.2 (v (p.1, p.2.1))

/-- The inverse of `re2`. -/
def unre2 (u : Fin ℓ × (Fin n × Fin 2) → ℝ) : Fin ℓ × Fin n → ℂ :=
  fun p => (u (p.1, (p.2, 0)) : ℂ) + (u (p.1, (p.2, 1)) : ℂ) * Complex.I

lemma unre2_re2 (v : Fin ℓ × Fin n → ℂ) : unre2 (re2 v) = v := by
  funext p
  apply Complex.ext <;> simp [unre2, re2, cmp]

lemma re2_unre2 (u : Fin ℓ × (Fin n × Fin 2) → ℝ) : re2 (unre2 u) = u := by
  funext ⟨j, k, a⟩
  fin_cases a <;> simp [unre2, re2, cmp]

lemma realify_mulVec (M : Matrix (Fin ℓ × Fin n) (Fin ℓ × Fin n) ℂ)
    (v : Fin ℓ × Fin n → ℂ) : realify M *ᵥ re2 v = re2 (M *ᵥ v) := by
  funext ⟨j, k, a⟩
  simp only [Matrix.mulVec, dotProduct, realify, re2, Fintype.sum_prod_type, Fin.sum_univ_two]
  fin_cases a <;>
    simp [blk, cmp, Complex.re_sum, Complex.im_sum, Complex.mul_re, Complex.mul_im,
      sub_eq_add_neg]
  all_goals exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

lemma re2_dot (u w : Fin ℓ × Fin n → ℂ) : re2 u ⬝ᵥ re2 w = (star u ⬝ᵥ w).re := by
  simp only [dotProduct, re2, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp [cmp, Complex.re_sum, Complex.mul_re]

lemma realify_mul (M N : Matrix (Fin ℓ × Fin n) (Fin ℓ × Fin n) ℂ) :
    realify (M * N) = realify M * realify N := by
  ext ⟨j, k, a⟩ ⟨j', k', b⟩
  simp only [Matrix.mul_apply, realify, Fintype.sum_prod_type, Fin.sum_univ_two]
  fin_cases a <;> fin_cases b <;>
    simp [blk, Complex.re_sum, Complex.im_sum, Complex.mul_re, Complex.mul_im,
      sub_eq_add_neg, add_comm]
  all_goals simp only [← Finset.sum_neg_distrib, neg_add]

lemma realify_conjTranspose (M : Matrix (Fin ℓ × Fin n) (Fin ℓ × Fin n) ℂ) :
    realify M.conjTranspose = (realify M).transpose := by
  ext ⟨j, k, a⟩ ⟨j', k', b⟩
  fin_cases a <;> fin_cases b <;> simp [realify, blk]

lemma realify_sub_smul_one (M : Matrix (Fin ℓ × Fin n) (Fin ℓ × Fin n) ℂ) (η : ℝ) :
    realify (M - (η : ℂ) • (1 : Matrix (Fin ℓ × Fin n) (Fin ℓ × Fin n) ℂ)) =
      realify M - η • (1 : Matrix (Fin ℓ × (Fin n × Fin 2)) (Fin ℓ × (Fin n × Fin 2)) ℝ) := by
  ext ⟨j, k, a⟩ ⟨j', k', b⟩
  fin_cases a <;> fin_cases b <;>
    by_cases h : (j, k) = (j', k') <;>
    simp_all [realify, blk]

lemma realify_posSemidef (H : Matrix (Fin ℓ × Fin n) (Fin ℓ × Fin n) ℂ) (hH : H.PosSemidef) :
    (realify H).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec] at hH ⊢
  refine ⟨?_, fun x => ?_⟩
  · change (realify H).conjTranspose = realify H
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, ← realify_conjTranspose, hH.1.eq]
  · rw [star_trivial, ← re2_unre2 x, realify_mulVec, re2_dot]
    exact (Complex.nonneg_iff.mp (hH.2 _)).1

/-! ### The measure-theoretic part -/

open ProbabilityTheory

/-- The scalar `1/√2`, as a complex number. -/
def c2 : ℂ := (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)

/-- `v ↦ (v 0 + i v 1)/√2`, from `ℝ²` to `ℂ`. -/
def φ (v : Fin 2 → ℝ) : ℂ :=
  (((Real.sqrt 2)⁻¹ * v 0 : ℝ) : ℂ) + (((Real.sqrt 2)⁻¹ * v 1 : ℝ) : ℂ) * Complex.I

lemma continuous_φ : Continuous φ := by unfold φ; fun_prop

lemma map_scale :
    (gaussianReal 0 1).map (fun x : ℝ => (Real.sqrt 2)⁻¹ * x) = gaussianReal 0 (1 / 2 : NNReal) := by
  rw [gaussianReal_map_const_mul]
  congr 1
  · simp
  · ext
    simp [inv_pow]

lemma map_φ : (Measure.pi fun _ : Fin 2 => gaussianReal 0 1).map φ =
    BraneBrauer.Orthogonal.complexGaussian := by
  have hφ : φ = (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ∘
      (Prod.map (fun x : ℝ => (Real.sqrt 2)⁻¹ * x) (fun x : ℝ => (Real.sqrt 2)⁻¹ * x) ∘
        (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ)) := by
    funext v
    rfl
  have hm1 : Measurable (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) := by fun_prop
  have hm2 : Measurable (fun x : ℝ => (Real.sqrt 2)⁻¹ * x) := by fun_prop
  rw [hφ, ← Measure.map_map hm1 ((hm2.prodMap hm2).comp (MeasurableEquiv.measurable _)),
    ← Measure.map_map (hm2.prodMap hm2) (MeasurableEquiv.measurable _),
    (measurePreserving_finTwoArrow (gaussianReal 0 1)).map_eq,
    ← Measure.map_prod_map _ _ hm2 hm2, map_scale]
  rfl

instance : IsProbabilityMeasure BraneBrauer.Orthogonal.complexGaussian := by
  rw [← map_φ]
  exact Measure.isProbabilityMeasure_map continuous_φ.measurable.aemeasurable

/-- The map `w ↦ (w₀ + i w₁)/√2` from real to complex coordinates. -/
def C (w : Fin ℓ × (Fin n × Fin 2) → ℝ) : Fin ℓ × Fin n → ℂ := c2 • unre2 w

lemma mp_C : MeasurePreserving (C : (Fin ℓ × (Fin n × Fin 2) → ℝ) → _)
    (Measure.pi fun _ => gaussianReal 0 1)
    (Measure.pi fun _ : Fin ℓ × Fin n => BraneBrauer.Orthogonal.complexGaussian) := by
  let e : Fin ℓ × (Fin n × Fin 2) ≃ (Fin ℓ × Fin n) × Fin 2 :=
    (Equiv.prodAssoc (Fin ℓ) (Fin n) (Fin 2)).symm
  have h1 := measurePreserving_piCongrLeft (fun _ : (Fin ℓ × Fin n) × Fin 2 => gaussianReal 0 1) e
  have h2 : MeasurePreserving (MeasurableEquiv.curry (Fin ℓ × Fin n) (Fin 2) ℝ)
      (Measure.pi fun _ : (Fin ℓ × Fin n) × Fin 2 => gaussianReal 0 1)
      (Measure.pi fun _ : Fin ℓ × Fin n => Measure.pi fun _ : Fin 2 => gaussianReal 0 1) := by
    refine ⟨MeasurableEquiv.measurable _, ?_⟩
    have := Measure.infinitePi_map_curry (ι := Fin ℓ × Fin n) (κ := Fin 2) (X := ℝ)
      (fun _ _ => gaussianReal 0 1)
    simpa only [Measure.infinitePi_eq_pi] using this
  have h3 : MeasurePreserving (fun (u : Fin ℓ × Fin n → Fin 2 → ℝ) p => φ (u p))
      (Measure.pi fun _ : Fin ℓ × Fin n => Measure.pi fun _ : Fin 2 => gaussianReal 0 1)
      (Measure.pi fun _ : Fin ℓ × Fin n => BraneBrauer.Orthogonal.complexGaussian) :=
    measurePreserving_pi _ _ fun _ => ⟨continuous_φ.measurable, map_φ⟩
  have h := h3.comp (h2.comp h1)
  convert h using 1
  funext w p
  simp [C, c2, unre2, φ, Function.comp, e, MeasurableEquiv.coe_piCongrLeft,
    Equiv.piCongrLeft_apply_eq_cast]
  ring

/-- The map back from real coordinates: `u ↦ (u₀ + i u₁)/√2`. -/
lemma realify_mulVec_eq (A : Matrix (Fin ℓ × Fin n) (Fin ℓ × Fin n) ℂ)
    (w : Fin ℓ × (Fin n × Fin 2) → ℝ) : C (realify A *ᵥ w) = A *ᵥ C w := by
  conv_lhs => rw [← re2_unre2 w, realify_mulVec]
  simp only [C, unre2_re2, Matrix.mulVec_smul]

lemma transfer (A : Matrix (Fin ℓ × Fin n) (Fin ℓ × Fin n) ℂ)
    (F : (Fin ℓ × Fin n → ℂ) → ℝ) (hF : Measurable F) :
    ∫ g, F g ∂((Measure.pi fun _ : Fin ℓ × Fin n => BraneBrauer.Orthogonal.complexGaussian).map
        (fun z => A *ᵥ z)) =
      ∫ u, F (C u) ∂((Measure.pi fun _ : Fin ℓ × (Fin n × Fin 2) => gaussianReal 0 1).map
        (fun z => realify A *ᵥ z)) := by
  have hA : Measurable (fun z : Fin ℓ × Fin n → ℂ => A *ᵥ z) :=
    (Continuous.matrix_mulVec continuous_const continuous_id).measurable
  have hB : Measurable (fun z : Fin ℓ × (Fin n × Fin 2) → ℝ => realify A *ᵥ z) :=
    (Continuous.matrix_mulVec continuous_const continuous_id).measurable
  have hCm : Measurable (C : (Fin ℓ × (Fin n × Fin 2) → ℝ) → _) := mp_C.measurable
  rw [integral_map (f := fun u => F (C u)) hB.aemeasurable (hF.comp hCm).aestronglyMeasurable,
    ← (mp_C (ℓ := ℓ) (n := n)).map_eq, Measure.map_map hA hCm,
    integral_map (hA.comp hCm).aemeasurable hF.aestronglyMeasurable]
  congr 1
  funext w
  simp only [Function.comp, realify_mulVec_eq]

end

end RestrictedAP.Counting.Dev.R511

namespace RestrictedAP.Counting
open RestrictedAP.Counting.Dev.R511 in
theorem chk_theorem_5_11 (ℓ n : ℕ) (hn : 1 ≤ n) (η : ℝ) (hη : 0 < η)
    (A : Matrix (Fin ℓ × Fin n) (Fin ℓ × Fin n) ℂ)
    (hblock : ∀ (j : Fin ℓ) (k k' : Fin n),
      (A * A.conjTranspose) (j, k) (j, k') = if k = k' then 1 else 0)
    (hcov : (A * A.conjTranspose - (η : ℂ) • (1 : Matrix (Fin ℓ × Fin n) (Fin ℓ × Fin n) ℂ)).PosSemidef)
    (f : Fin ℓ → (Fin n → ℂ) → ℝ) (hf : ∀ j, Measurable (f j))
    (hf01 : ∀ j z, 0 ≤ f j z ∧ f j z ≤ 1) :
    let lawG : Measure (Fin ℓ × Fin n → ℂ) :=
      (Measure.pi (fun _ : Fin ℓ × Fin n => BraneBrauer.Orthogonal.complexGaussian)).map
        (fun z => A.mulVec z)
    (∏ j, ∫ g, f j (fun k => g (j, k)) ∂lawG) ^ (1 / η) ≤
      ∫ g, ∏ j, f j (fun k => g (j, k)) ∂lawG := by
  intro lawG
  have : Nonempty (Fin n × Fin 2) := ⟨(⟨0, hn⟩, 0)⟩
  let ft : Fin ℓ → (Fin n × Fin 2 → ℝ) → ℝ := fun j u =>
    f j (fun k => c2 * ((u (k, 0) : ℂ) + (u (k, 1) : ℂ) * Complex.I))
  have hftm : ∀ j, Measurable (ft j) := fun j => (hf j).comp (by fun_prop)
  have hft01 : ∀ j x, 0 ≤ ft j x ∧ ft j x ≤ 1 := fun j _ => hf01 j _
  have hblock' : ∀ (j : Fin ℓ) (k k' : Fin n × Fin 2),
      (realify A * (realify A).transpose) (j, k) (j, k') = if k = k' then 1 else 0 := by
    rintro j ⟨k, a⟩ ⟨k', b⟩
    rw [← realify_conjTranspose, ← realify_mul]
    simp only [realify]
    rw [hblock]
    by_cases h : k = k' <;> fin_cases a <;> fin_cases b <;> simp [blk, h]
  have hcov' : (realify A * (realify A).transpose -
      η • (1 : Matrix (Fin ℓ × (Fin n × Fin 2)) (Fin ℓ × (Fin n × Fin 2)) ℝ)).PosSemidef := by
    rw [← realify_conjTranspose, ← realify_mul, ← realify_sub_smul_one]
    exact realify_posSemidef _ hcov
  have h := theorem_A_1_real ℓ (Fin n × Fin 2) η hη (realify A) hblock' hcov' ft hftm hft01
  simp only at h
  have hproj : ∀ j : Fin ℓ, Measurable (fun g : Fin ℓ × Fin n → ℂ => fun k => g (j, k)) :=
    fun j => by fun_prop
  have e1 : ∀ j, ∫ g, f j (fun k => g (j, k)) ∂lawG =
      ∫ g, ft j (fun k => g (j, k)) ∂((Measure.pi fun _ : Fin ℓ × (Fin n × Fin 2) =>
        ProbabilityTheory.gaussianReal 0 1).map (fun z => Matrix.mulVec (realify A) z)) :=
    fun j => transfer A _ ((hf j).comp (hproj j))
  have e2 : ∫ g, ∏ j, f j (fun k => g (j, k)) ∂lawG =
      ∫ g, ∏ j, ft j (fun k => g (j, k)) ∂((Measure.pi fun _ : Fin ℓ × (Fin n × Fin 2) =>
        ProbabilityTheory.gaussianReal 0 1).map (fun z => Matrix.mulVec (realify A) z)) :=
    transfer A _ (Finset.measurable_prod _ fun j _ => (hf j).comp (hproj j))
  rw [Finset.prod_congr rfl fun j _ => e1 j, e2]
  exact h

end RestrictedAP.Counting
end

theorem solution : type_of% @RestrictedAP.Counting.chk_theorem_5_11 := @RestrictedAP.Counting.chk_theorem_5_11
