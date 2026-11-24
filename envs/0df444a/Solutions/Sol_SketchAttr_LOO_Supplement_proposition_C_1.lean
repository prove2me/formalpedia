-- Prove2me | solution 1 for SketchAttr.LOO.Supplement.proposition_C_1
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T22:37:35.332415+00:00
-- url     : https://prove2.me/submissions/c9076945-89fa-4ca1-980f-0582b29f7650

import Mathlib
import Definitions.Def_SketchAttr_LOO_Supplement_Quadratic

open MeasureTheory ProbabilityTheory SketchAttr.LOO.Supplement

namespace C1aux


instance h442 : ENNReal.HolderTriple 4 4 2 := ⟨by
  rw [show (4:ENNReal) = 2 * 2 by norm_num, ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top),
    ← two_mul, ← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]⟩

lemma int4 {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} {f g h k : Ω → ℝ}
    (hf : MemLp f 4 μ) (hg : MemLp g 4 μ) (hh : MemLp h 4 μ) (hk : MemLp k 4 μ) :
    Integrable (fun ω => f ω * g ω * (h ω * k ω)) μ := by
  have h1 : MemLp (fun ω => f ω * g ω) 2 μ := hg.mul hf
  have h2 : MemLp (fun ω => h ω * k ω) 2 μ := hk.mul hh
  exact h1.integrable_mul h2





lemma d_exp (p : Polynomial ℝ) :
    deriv (fun t : ℝ => p.eval t * Real.exp (t ^ 2 / 2)) =
      fun t => (Polynomial.derivative p + Polynomial.X * p).eval t * Real.exp (t ^ 2 / 2) := by
  ext t
  have h1 : HasDerivAt (fun t : ℝ => p.eval t) ((Polynomial.derivative p).eval t) t := p.hasDerivAt t
  have h2 : HasDerivAt (fun t : ℝ => Real.exp (t ^ 2 / 2)) (Real.exp (t ^ 2 / 2) * t) t := by
    have := ((hasDerivAt_pow 2 t).div_const 2).exp
    convert this using 1
    simp
  have := h1.mul h2
  have h3 : HasDerivAt (fun t : ℝ => p.eval t * Real.exp (t ^ 2 / 2)) _ t := this
  rw [h3.deriv]
  simp; ring

lemma m4 : ∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1 = 3 := by
  have hint : 0 ∈ interior (integrableExpSet (fun x : ℝ => x) (gaussianReal 0 1)) := by
    simp
  have h := iteratedDeriv_mgf_zero hint 4
  rw [mgf_fun_id_gaussianReal] at h
  have e : (fun t : ℝ => Real.exp (0 * t + 1 * t ^ 2 / 2)) = fun t => (1 : Polynomial ℝ).eval t * Real.exp (t ^ 2 / 2) := by
    ext t; simp
  simp only [NNReal.coe_one] at h
  rw [e] at h
  simp only [iteratedDeriv_succ, iteratedDeriv_zero] at h
  rw [d_exp, d_exp, d_exp, d_exp] at h
  simp at h
  have h' : (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1) = (∫ x, (fun x : ℝ => x) x ^ 4 ∂gaussianReal 0 1) := rfl
  rw [← h]; norm_num


lemma m1 : ∫ x : ℝ, x ∂gaussianReal 0 1 = 0 := by simp

lemma m2 : ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1 = 1 := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral measurable_id'.aemeasurable] at h
  simpa using h

section
variable {ι Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} {X : ι → Ω → ℝ}

lemma mom_int (hm : ∀ p, Measurable (X p)) (hl : ∀ p, μ.map (X p) = gaussianReal 0 1) (p : ι)
    (F : ℝ → ℝ) (hF : Measurable F) :
    ∫ ω, F (X p ω) ∂μ = ∫ x, F x ∂gaussianReal 0 1 := by
  rw [← hl p, integral_map (hm p).aemeasurable hF.aestronglyMeasurable]

lemma memLp4 (hm : ∀ p, Measurable (X p)) (hl : ∀ p, μ.map (X p) = gaussianReal 0 1) (p : ι) :
    MemLp (X p) 4 μ := by
  have h : MemLp id 4 (μ.map (X p)) := by
    rw [hl p]; exact memLp_id_gaussianReal 4
  exact (memLp_map_measure_iff aestronglyMeasurable_id (hm p).aemeasurable).1 h

lemma mom_pair (hi : iIndepFun X μ) (hm : ∀ p, Measurable (X p))
    (hl : ∀ p, μ.map (X p) = gaussianReal 0 1) {p q : ι} (hpq : p ≠ q) :
    ∫ ω, X p ω ^ 2 * X q ω ^ 2 ∂μ = 1 := by
  have h := (hi.indepFun hpq).comp (φ := fun x : ℝ => x ^ 2) (ψ := fun x : ℝ => x ^ 2)
    (by fun_prop) (by fun_prop)
  have h2 := h.integral_mul_eq_mul_integral ((hm p).pow_const 2).aestronglyMeasurable
    ((hm q).pow_const 2).aestronglyMeasurable
  have e1 := mom_int hm hl p (fun x => x ^ 2) (by fun_prop)
  have e2 := mom_int hm hl q (fun x => x ^ 2) (by fun_prop)
  simp only [Function.comp_def, Pi.mul_apply] at h2
  rw [h2, e1, e2, m2]; norm_num

lemma mom_four (hm : ∀ p, Measurable (X p)) (hl : ∀ p, μ.map (X p) = gaussianReal 0 1) (p : ι) :
    ∫ ω, X p ω * X p ω * (X p ω * X p ω) ∂μ = 3 := by
  have e1 := mom_int hm hl p (fun x => x ^ 4) (by fun_prop)
  rw [← m4]
  rw [← e1]
  congr 1; ext ω; ring

lemma mom_zero (hi : iIndepFun X μ) (hm : ∀ p, Measurable (X p))
    (hl : ∀ p, μ.map (X p) = gaussianReal 0 1) {p q s t : ι} (hq : p ≠ q) (hs : p ≠ s) (ht : p ≠ t) :
    ∫ ω, X p ω * X q ω * (X s ω * X t ω) ∂μ = 0 := by
  classical
  have hd : Disjoint ({p} : Finset ι) {q, s, t} := by
    simp [hq, hs, ht]
  have h := hi.indepFun_finset {p} {q, s, t} hd hm
  have hφ : Measurable (fun f : ({p} : Finset ι) → ℝ => f ⟨p, by simp⟩) := measurable_pi_apply _
  have hψ : Measurable (fun g : ({q, s, t} : Finset ι) → ℝ =>
      g ⟨q, by simp⟩ * (g ⟨s, by simp⟩ * g ⟨t, by simp⟩)) :=
    Measurable.fun_mul (measurable_pi_apply _)
      (Measurable.fun_mul (measurable_pi_apply _) (measurable_pi_apply _))
  have h2 := h.comp (φ := fun f : ({p} : Finset ι) → ℝ => f ⟨p, by simp⟩)
    (ψ := fun g : ({q, s, t} : Finset ι) → ℝ => g ⟨q, by simp⟩ * (g ⟨s, by simp⟩ * g ⟨t, by simp⟩))
    hφ hψ
  have h3 := h2.integral_mul_eq_mul_integral (hm p).aestronglyMeasurable
    ((hm q).mul ((hm s).mul (hm t))).aestronglyMeasurable
  simp only [Function.comp_def, Pi.mul_apply] at h3
  have e1 := mom_int hm hl p (fun x => x) (by fun_prop)
  have : ∫ ω, X p ω * X q ω * (X s ω * X t ω) ∂μ = ∫ ω, X p ω * (X q ω * (X s ω * X t ω)) ∂μ := by
    congr 1; ext ω; ring
  rw [this, h3, e1, m1]; simp

end

def flat (r n : ℕ) (G : Matrix (Fin r) (Fin n) ℝ) : Fin r × Fin n → ℝ := fun p => G p.1 p.2

lemma measurable_flat (r n : ℕ) : Measurable (flat r n) := by
  unfold flat
  exact measurable_pi_lambda _ (fun p => by
    have h1 : Measurable (fun G : Fin r → Fin n → ℝ => G p.1) := measurable_pi_apply _
    exact (measurable_pi_apply p.2).comp h1)

lemma map_flat (r n : ℕ) :
    (realGaussianMatrix r n).map (flat r n) =
      Measure.pi (fun _ : Fin r × Fin n => gaussianReal 0 1) := by
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (measurable_flat r n) (MeasurableSet.univ_pi hs)]
  have : flat r n ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun a : Fin r => Set.univ.pi (fun k : Fin n => s (a, k))) := by
    ext G; exact ⟨fun h a _ k _ => h (a,k) trivial, fun h p _ => h p.1 trivial p.2 trivial⟩
  rw [this]
  have e : realGaussianMatrix r n (Set.univ.pi fun a : Fin r => Set.univ.pi fun k : Fin n => s (a, k))
      = ∏ a : Fin r, ∏ k : Fin n, gaussianReal 0 1 (s (a, k)) :=
    (Measure.pi_pi _ _).trans (Finset.prod_congr rfl fun a _ => Measure.pi_pi _ _)
  rw [e, ← Fintype.prod_prod_type (f := fun p : Fin r × Fin n => (gaussianReal 0 1) (s p))]

instance probRGM (r n : ℕ) : IsProbabilityMeasure (realGaussianMatrix r n) := by
  exact (inferInstance : IsProbabilityMeasure (Measure.pi fun _ : Fin r => Measure.pi fun _ : Fin n => gaussianReal 0 1))

lemma indep_flat (r n : ℕ) :
    iIndepFun (fun (p : Fin r × Fin n) (G : Matrix (Fin r) (Fin n) ℝ) => G p.1 p.2)
      (realGaussianMatrix r n) := by
  have hm : ∀ p : Fin r × Fin n, Measurable (fun G : Matrix (Fin r) (Fin n) ℝ => G p.1 p.2) :=
    fun p => (measurable_pi_apply p).comp (measurable_flat r n)
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun p => (hm p).aemeasurable)]
  have h1 : (realGaussianMatrix r n).map (fun G (p : Fin r × Fin n) => G p.1 p.2) = _ := map_flat r n
  have h2 : ∀ p : Fin r × Fin n, (realGaussianMatrix r n).map (fun G : Matrix (Fin r) (Fin n) ℝ => G p.1 p.2) = gaussianReal 0 1 := by
    intro p
    have : (fun G : Matrix (Fin r) (Fin n) ℝ => G p.1 p.2) = (fun f : Fin r × Fin n → ℝ => f p) ∘ flat r n := rfl
    rw [this, ← Measure.map_map (measurable_pi_apply p) (measurable_flat r n), map_flat]
    haveI : ∀ _ : Fin r × Fin n, IsProbabilityMeasure (gaussianReal 0 1) := fun _ => inferInstance
    rw [Measure.pi_map_eval]
    simp
  simp_rw [h2]
  exact h1


lemma law_coord (r n : ℕ) (p : Fin r × Fin n) :
    (realGaussianMatrix r n).map (fun G : Matrix (Fin r) (Fin n) ℝ => G p.1 p.2) = gaussianReal 0 1 := by
  have : (fun G : Matrix (Fin r) (Fin n) ℝ => G p.1 p.2) = (fun f : Fin r × Fin n → ℝ => f p) ∘ flat r n := rfl
  rw [this, ← Measure.map_map (measurable_pi_apply p) (measurable_flat r n), map_flat]
  haveI : ∀ _ : Fin r × Fin n, IsProbabilityMeasure (gaussianReal 0 1) := fun _ => inferInstance
  rw [Measure.pi_map_eval]
  simp

lemma frob_sq (r n : ℕ) (G : Matrix (Fin r) (Fin n) ℝ) :
    matrixFrobNorm (gram G) ^ 2 = ∑ i, ∑ j, ∑ a, ∑ b, G a i * G a j * (G b i * G b j) := by
  unfold matrixFrobNorm SketchAttr.LOO.frobNorm matrixTensor
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => by positivity))]
  rw [← (finTwoArrowEquiv (Fin n)).symm.sum_comp]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  have h0 : ((finTwoArrowEquiv (Fin n)).symm (i, j)) 0 = i := rfl
  have h1 : ((finTwoArrowEquiv (Fin n)).symm (i, j)) 1 = j := rfl
  simp only [h0, h1, Complex.norm_real, Real.norm_eq_abs, sq_abs, gram]
  rw [sq, Finset.sum_mul_sum]

abbrev Xc (r n : ℕ) (p : Fin r × Fin n) (G : Matrix (Fin r) (Fin n) ℝ) : ℝ := G p.1 p.2

lemma meas_Xc (r n : ℕ) (p : Fin r × Fin n) : Measurable (Xc r n p) :=
  (measurable_pi_apply p).comp (measurable_flat r n)

lemma term_int (r n : ℕ) (i j : Fin n) (a b : Fin r) :
    Integrable (fun G : Matrix (Fin r) (Fin n) ℝ => G a i * G a j * (G b i * G b j))
      (realGaussianMatrix r n) :=
  int4 (memLp4 (X := Xc r n) (meas_Xc r n) (law_coord r n) (a, i))
    (memLp4 (X := Xc r n) (meas_Xc r n) (law_coord r n) (a, j))
    (memLp4 (X := Xc r n) (meas_Xc r n) (law_coord r n) (b, i))
    (memLp4 (X := Xc r n) (meas_Xc r n) (law_coord r n) (b, j))

lemma term_val (r n : ℕ) (i j : Fin n) (a b : Fin r) :
    ∫ G : Matrix (Fin r) (Fin n) ℝ, G a i * G a j * (G b i * G b j) ∂realGaussianMatrix r n =
      (if a = b then 1 else 0) + (if i = j then 1 else 0) + (if a = b ∧ i = j then 1 else 0) := by
  have hm := meas_Xc r n
  have hl := law_coord r n
  have hi := indep_flat r n
  by_cases hab : a = b <;> by_cases hij : i = j
  · subst hab; subst hij
    have := mom_four (X := Xc r n) (μ := realGaussianMatrix r n) hm hl (a, i)
    simp only [if_true, and_self]
    norm_num; exact this
  · subst hab
    have := mom_pair (μ := realGaussianMatrix r n) hi hm hl (p := (a, i)) (q := (a, j))
      (by simp [hij])
    have e : ∫ G : Matrix (Fin r) (Fin n) ℝ, G a i * G a j * (G a i * G a j) ∂realGaussianMatrix r n
        = ∫ G : Matrix (Fin r) (Fin n) ℝ, Xc r n (a, i) G ^ 2 * Xc r n (a, j) G ^ 2 ∂realGaussianMatrix r n := by
      congr 1; ext G; simp only [Xc]; ring
    rw [e, this]; simp [hij]
  · subst hij
    have := mom_pair (μ := realGaussianMatrix r n) hi hm hl (p := (a, i)) (q := (b, i))
      (by simp [hab])
    have e : ∫ G : Matrix (Fin r) (Fin n) ℝ, G a i * G a i * (G b i * G b i) ∂realGaussianMatrix r n
        = ∫ G : Matrix (Fin r) (Fin n) ℝ, Xc r n (a, i) G ^ 2 * Xc r n (b, i) G ^ 2 ∂realGaussianMatrix r n := by
      congr 1; ext G; simp only [Xc]; ring
    rw [e, this]; simp [hab]
  · have := mom_zero (μ := realGaussianMatrix r n) hi hm hl (p := (a, i)) (q := (a, j))
      (s := (b, i)) (t := (b, j)) (by simp [hij]) (by simp [hab]) (by simp [hab])
    simp only [Xc] at this
    rw [this]; simp [hab, hij]

end C1aux

open C1aux in
theorem solution (r n : ℕ) (hn : 1 ≤ n) :
    Integrable (fun G : Matrix (Fin r) (Fin n) ℝ => matrixFrobNorm (gram G) ^ 2)
      (realGaussianMatrix r n) ∧
    (∫ G : Matrix (Fin r) (Fin n) ℝ, matrixFrobNorm (gram G) ^ 2 ∂realGaussianMatrix r n) =
      (n : ℝ) * r * (r + n + 1) := by
  simp_rw [frob_sq]
  have hI : ∀ i j : Fin n, ∀ a : Fin r, Integrable (fun G : Matrix (Fin r) (Fin n) ℝ =>
      ∑ b, G a i * G a j * (G b i * G b j)) (realGaussianMatrix r n) := fun i j a =>
    integrable_finsetSum (Finset.univ : Finset (Fin r)) (fun b _ => term_int r n i j a b)
  have hII : ∀ i j : Fin n, Integrable (fun G : Matrix (Fin r) (Fin n) ℝ =>
      ∑ a, ∑ b, G a i * G a j * (G b i * G b j)) (realGaussianMatrix r n) := fun i j =>
    integrable_finsetSum (Finset.univ : Finset (Fin r)) (fun a _ => hI i j a)
  have hIII : ∀ i : Fin n, Integrable (fun G : Matrix (Fin r) (Fin n) ℝ =>
      ∑ j, ∑ a, ∑ b, G a i * G a j * (G b i * G b j)) (realGaussianMatrix r n) := fun i =>
    integrable_finsetSum (Finset.univ : Finset (Fin n)) (fun j _ => hII i j)
  refine ⟨integrable_finsetSum (Finset.univ : Finset (Fin n)) (fun i _ => hIII i), ?_⟩
  rw [integral_finsetSum _ (fun i _ => hIII i)]
  have e : ∀ i : Fin n, ∫ G : Matrix (Fin r) (Fin n) ℝ,
      ∑ j, ∑ a, ∑ b, G a i * G a j * (G b i * G b j) ∂realGaussianMatrix r n =
      ∑ j : Fin n, ∑ a : Fin r, ∑ b : Fin r, ((if a = b then (1:ℝ) else 0) + (if i = j then 1 else 0) +
        (if a = b ∧ i = j then 1 else 0)) := by
    intro i
    rw [integral_finsetSum _ (fun j _ => hII i j)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [integral_finsetSum _ (fun a _ => hI i j a)]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [integral_finsetSum _ (fun b _ => term_int r n i j a b)]
    exact Finset.sum_congr rfl (fun b _ => term_val r n i j a b)
  simp_rw [e]
  simp [Finset.sum_add_distrib, ite_and]
  ring
