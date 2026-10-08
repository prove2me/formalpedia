-- Prove2me | solution 1 for RadGauss.Kernel.complexity_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T06:20:33.442996+00:00
-- url     : https://prove2.me/submissions/5228567b-0fcb-4f01-954d-bbd2a3865e13

import Mathlib
import Definitions.Def_RadGauss_Kernel_Complexity
import Definitions.Def_RadGauss_Kernel_KernelClass

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace RGK73898060

open RadGauss.Kernel

lemma kern_symm {X : Type*} [TopologicalSpace X] {k : X → X → ℝ} (hk : IsKernel k) (a b : X) :
    k a b = k b a := by
  have h := (hk.gram_posSemidef 2 ![a, b]).1.apply 0 1
  simpa using h.symm

lemma kern_quad {X : Type*} [TopologicalSpace X] {k : X → X → ℝ} (hk : IsKernel k) (m : ℕ)
    (y : Fin m → X) (v : Fin m → ℝ) : 0 ≤ ∑ i, ∑ j, v i * v j * k (y i) (y j) := by
  have h := (hk.gram_posSemidef m y).dotProduct_mulVec_nonneg v
  simp only [star_trivial, dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum] at h
  refine h.trans_eq (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_)
  ring

lemma kern_cs {X : Type*} [TopologicalSpace X] {k : X → X → ℝ} (hk : IsKernel k) (n m : ℕ)
    (x : Fin n → X) (c : Fin m → X) (w : Fin n → ℝ) (α : Fin m → ℝ) :
    (∑ i, ∑ j, w i * α j * k (x i) (c j)) ^ 2 ≤
      (∑ i, ∑ i', w i * w i' * k (x i) (x i')) * (∑ j, ∑ j', α j * α j' * k (c j) (c j')) := by
  set P := ∑ i, ∑ j, w i * α j * k (x i) (c j)
  set Q := ∑ i, ∑ i', w i * w i' * k (x i) (x i')
  set A := ∑ j, ∑ j', α j * α j' * k (c j) (c j')
  have key : ∀ t : ℝ, 0 ≤ Q * (t * t) + (2 * P) * t + A := by
    intro t
    have h := kern_quad hk (n + m) (Fin.append x c) (Fin.append (fun i => t * w i) α)
    simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, Finset.sum_add_distrib] at h
    have e1 : ∑ i, ∑ i', (t * w i) * (t * w i') * k (x i) (x i') = Q * (t * t) := by
      simp only [Q, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    have e2 : ∑ i, ∑ j, (t * w i) * α j * k (x i) (c j) = P * t := by
      simp only [P, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    have e3 : ∑ j, ∑ i, α j * (t * w i) * k (c j) (x i) = P * t := by
      rw [Finset.sum_comm]
      simp only [P, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [kern_symm hk (c j) (x i)]
      ring
    linarith
  have hd := discrim_le_zero key
  unfold discrim at hd
  nlinarith

lemma kern_bound {X : Type*} [TopologicalSpace X] {k : X → X → ℝ} (hk : IsKernel k) {B : ℝ}
    (hB : 0 ≤ B) {n : ℕ} (x : Fin n → X) (w : Fin n → ℝ) (f : X → ℝ) (hf : f ∈ kernelClass k B) :
    |∑ i, w i * f (x i)| ≤ B * Real.sqrt (∑ i, ∑ l, w i * w l * k (x i) (x l)) := by
  obtain ⟨m, c, α, hA, rfl⟩ := hf
  have hQ := kern_quad hk n x w
  have hA0 := kern_quad hk m c α
  have hP : ∑ i, w i * ∑ j, α j * k (x i) (c j) = ∑ i, ∑ j, w i * α j * k (x i) (c j) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hP]
  have hcs := kern_cs hk n m x c w α
  have h2 : (∑ i, ∑ j, w i * α j * k (x i) (c j)) ^ 2 ≤
      (B * Real.sqrt (∑ i, ∑ l, w i * w l * k (x i) (x l))) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hQ]
    calc _ ≤ _ := hcs
      _ ≤ _ := mul_le_mul_of_nonneg_left hA hQ
      _ = _ := by ring
  have := Real.abs_le_sqrt h2
  rwa [Real.sqrt_sq (by positivity)] at this

lemma sup_bound {X : Type*} [TopologicalSpace X] {k : X → X → ℝ} (hk : IsKernel k) {B : ℝ}
    (hB : 0 ≤ B) {n : ℕ} (x : Fin n → X) (w : Fin n → ℝ) :
    (⨆ f ∈ kernelClass k B, ENNReal.ofReal |(2 / (n : ℝ)) * ∑ i, w i * f (x i)|) ≤
      ENNReal.ofReal ((2 / (n : ℝ)) * B * Real.sqrt (∑ i, ∑ l, w i * w l * k (x i) (x l))) := by
  refine iSup₂_le fun f hf => ENNReal.ofReal_le_ofReal ?_
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 / (n : ℝ)), mul_assoc]
  exact mul_le_mul_of_nonneg_left (kern_bound hk hB x w f hf) (by positivity)

lemma rad_moment (n : ℕ) (i l : Fin n) :
    ∑ σ : Fin n → ℤˣ, ((σ i : ℤ) : ℝ) * ((σ l : ℤ) : ℝ) = if i = l then (2 : ℝ) ^ n else 0 := by
  split_ifs with h
  · subst h
    have : ∀ σ : Fin n → ℤˣ, ((σ i : ℤ) : ℝ) * ((σ i : ℤ) : ℝ) = 1 := by
      intro σ
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
      simp
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_units_int,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    push_cast
    ring
  · set φ : (Fin n → ℤˣ) → (Fin n → ℤˣ) := fun σ => Function.update σ i (-σ i) with hφdef
    have hφ : Function.Involutive φ := by
      intro σ
      funext j
      by_cases hj : j = i
      · subst hj; simp [φ]
      · simp [φ, Function.update_of_ne hj]
    have hrel := Fintype.sum_equiv (Function.Involutive.toPerm φ hφ)
      (fun σ : Fin n → ℤˣ => ((σ i : ℤ) : ℝ) * ((σ l : ℤ) : ℝ))
      (fun σ => -(((σ i : ℤ) : ℝ) * ((σ l : ℤ) : ℝ))) (by
        intro σ
        simp [φ, Function.update_of_ne (Ne.symm h)])
    rw [Finset.sum_neg_distrib] at hrel
    linarith

lemma rad_avg {X : Type*} (k : X → X → ℝ) {n : ℕ} (x : Fin n → X) :
    ∑ σ : Fin n → ℤˣ, (1 / (2 : ℝ) ^ n) *
      (∑ i, ∑ l, ((σ i : ℤ) : ℝ) * ((σ l : ℤ) : ℝ) * k (x i) (x l)) = ∑ i, k (x i) (x i) := by
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin n → ℤˣ))) (t := Finset.univ)]
  simp_rw [← Finset.sum_mul, rad_moment, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp

lemma gauss_sq : ∫ y, y * y ∂(gaussianReal 0 1) = 1 := by
  have h := variance_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral measurable_id.aemeasurable] at h
  simp only [id, integral_id_gaussianReal, sub_zero] at h
  simpa [sq] using h

lemma gauss_moment (n : ℕ) (i l : Fin n) :
    Integrable (fun g : Fin n → ℝ => g i * g l) (Measure.pi fun _ : Fin n => gaussianReal 0 1) ∧
      ∫ g, g i * g l ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) = if i = l then 1 else 0 := by
  let f : Fin n → ℝ → ℝ := fun j y => (if j = i then y else 1) * (if j = l then y else 1)
  have hfun : (fun g : Fin n → ℝ => g i * g l) = fun g => ∏ j, f j (g j) := by
    funext g
    simp only [f]
    rw [Finset.prod_mul_distrib]
    simp
  have hint1 : Integrable (fun y : ℝ => y) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal 1).integrable le_rfl
  have hint2 : Integrable (fun y : ℝ => y * y) (gaussianReal 0 1) := by
    have := (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_sq
    simpa [sq] using this
  have hfi : ∀ j, Integrable (f j) (gaussianReal 0 1) := by
    intro j
    by_cases hi : j = i <;> by_cases hl : j = l
    · simp only [f, if_pos hi, if_pos hl]; exact hint2
    · simp only [f, if_pos hi, if_neg hl, mul_one]; exact hint1
    · simp only [f, if_neg hi, if_pos hl, one_mul]; exact hint1
    · simp only [f, if_neg hi, if_neg hl, mul_one]; exact integrable_const _
  refine ⟨?_, ?_⟩
  · rw [hfun]; exact Integrable.fintype_prod hfi
  · rw [hfun, integral_fintype_prod_eq_prod]
    split_ifs with h
    · subst h
      rw [Finset.prod_eq_single i]
      · simp [f, gauss_sq]
      · intro j _ hj; simp [f, hj]
      · simp
    · apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [f, h, integral_id_gaussianReal]

lemma gauss_avg {X : Type*} (k : X → X → ℝ) {n : ℕ} (x : Fin n → X) :
    Integrable (fun g : Fin n → ℝ => ∑ i, ∑ l, g i * g l * k (x i) (x l))
        (Measure.pi fun _ : Fin n => gaussianReal 0 1) ∧
      ∫ g, (∑ i, ∑ l, g i * g l * k (x i) (x l)) ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)
        = ∑ i, k (x i) (x i) := by
  have hti : ∀ i l, Integrable (fun g : Fin n → ℝ => g i * g l * k (x i) (x l))
      (Measure.pi fun _ : Fin n => gaussianReal 0 1) := fun i l => (gauss_moment n i l).1.mul_const _
  refine ⟨integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun l _ => hti i l, ?_⟩
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun l _ => hti i l]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun l _ => hti i l]
  simp_rw [integral_mul_const, (gauss_moment n i _).2, ite_mul, one_mul, zero_mul]
  simp

lemma lint_sqrt_le {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
    (h : α → ℝ) (h0 : ∀ a, 0 ≤ h a) (hi : Integrable h ν) (c : ℝ) (hc : 0 ≤ c) :
    ∫⁻ a, ENNReal.ofReal (c * Real.sqrt (h a)) ∂ν ≤ ENNReal.ofReal (c * Real.sqrt (∫ a, h a ∂ν)) := by
  have hs : Integrable (fun a => Real.sqrt (h a)) ν := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add hi)
      (Real.continuous_sqrt.comp_aestronglyMeasurable hi.1) (ae_of_all _ fun a => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    show Real.sqrt (h a) ≤ 1 + h a
    nlinarith [Real.sq_sqrt (h0 a), Real.sqrt_nonneg (h a)]
  rw [← ofReal_integral_eq_lintegral_ofReal (hs.const_mul c)
    (ae_of_all _ fun a => by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [integral_const_mul]
  apply mul_le_mul_of_nonneg_left _ hc
  exact Real.strictConcaveOn_sqrt.concaveOn.le_map_integral Real.continuous_sqrt.continuousOn
    isClosed_Ici (ae_of_all _ fun a => h0 a) hi hs

lemma pi_single {E : Type*} [MeasurableSpace E] (ν : Measure E) [IsProbabilityMeasure ν] {n : ℕ}
    (i : Fin n) (φ : E → ℝ) (hφ : Integrable φ ν) :
    Integrable (fun x : Fin n → E => φ (x i)) (Measure.pi fun _ => ν) ∧
      ∫ x, φ (x i) ∂(Measure.pi fun _ => ν) = ∫ y, φ y ∂ν := by
  let f : Fin n → E → ℝ := fun j y => if j = i then φ y else 1
  have hfun : (fun x : Fin n → E => φ (x i)) = fun x => ∏ j, f j (x j) := by
    funext x
    simp [f]
  have hfi : ∀ j, Integrable (f j) ν := by
    intro j
    by_cases hj : j = i <;> simp [f, hj, hφ]
  refine ⟨?_, ?_⟩
  · rw [hfun]; exact Integrable.fintype_prod hfi
  · rw [hfun, integral_fintype_prod_eq_prod, Finset.prod_eq_single i]
    · simp [f]
    · intro j _ hj; simp [f, hj]
    · simp

lemma real_ident (n : ℕ) (B E : ℝ) (hE : 0 ≤ E) :
    (2 / (n : ℝ)) * B * Real.sqrt ((n : ℝ) * E) = 2 * B * Real.sqrt (E / n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs := Real.sq_sqrt hn'.le
  have hsp : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn'
  rw [Real.sqrt_mul hn'.le, Real.sqrt_div' _ hn'.le]
  field_simp
  rw [hs]
  ring

end RGK73898060

open MeasureTheory RadGauss.Kernel in
theorem solution {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (k : X → X → ℝ) (hk : IsKernel k)
    (B : ℝ) (hB : 0 ≤ B) (n : ℕ) :
    RadGauss.Classification.rademacherComplexity μ n (kernelClass k B)
        ≤ ENNReal.ofReal (2 * B * Real.sqrt ((∫ x, k x x ∂μ) / n)) ∧
      RadGauss.LipschitzGaussian.gaussianComplexity μ n (kernelClass k B)
        ≤ ENNReal.ofReal (2 * B * Real.sqrt ((∫ x, k x x ∂μ) / n)) := by
  have := hk.compactSpace
  have hdiag : ∀ y, 0 ≤ k y y := by
    intro y
    have := RGK73898060.kern_quad hk 1 (fun _ => y) (fun _ => 1)
    simpa using this
  have hcont : Continuous fun y => k y y :=
    hk.continuous.comp (continuous_id.prodMk continuous_id)
  have hkint : Integrable (fun y => k y y) μ := by
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hcont.continuousOn
    exact Integrable.of_bound hcont.aestronglyMeasurable C
      (ae_of_all _ fun y => hC y (Set.mem_univ y))
  have hE : 0 ≤ ∫ x, k x x ∂μ := integral_nonneg hdiag
  have hS0 : ∀ x : Fin n → X, 0 ≤ ∑ i, k (x i) (x i) :=
    fun x => Finset.sum_nonneg fun i _ => hdiag _
  have hSi : Integrable (fun x : Fin n → X => ∑ i, k (x i) (x i)) (Measure.pi fun _ : Fin n => μ) :=
    integrable_finsetSum _ fun i _ => (RGK73898060.pi_single μ i (fun y => k y y) hkint).1
  have hSint : ∫ x, (∑ i, k (x i) (x i)) ∂(Measure.pi fun _ : Fin n => μ) = n * ∫ x, k x x ∂μ := by
    rw [integral_finsetSum _ fun i _ => (RGK73898060.pi_single μ i (fun y => k y y) hkint).1]
    rw [Finset.sum_congr rfl fun i _ => (RGK73898060.pi_single μ i (fun y => k y y) hkint).2]
    simp
  have hfinal : ∫⁻ x, ENNReal.ofReal ((2 / (n : ℝ)) * B * Real.sqrt (∑ i, k (x i) (x i)))
      ∂(Measure.pi fun _ : Fin n => μ) ≤ ENNReal.ofReal (2 * B * Real.sqrt ((∫ x, k x x ∂μ) / n)) := by
    calc _ ≤ ENNReal.ofReal ((2 / (n : ℝ)) * B *
          Real.sqrt (∫ x, (∑ i, k (x i) (x i)) ∂(Measure.pi fun _ : Fin n => μ))) :=
          RGK73898060.lint_sqrt_le _ _ hS0 hSi _ (by positivity)
      _ = _ := by rw [hSint, RGK73898060.real_ident n B _ hE]
  constructor
  · unfold RadGauss.Classification.rademacherComplexity
    refine le_trans (lintegral_mono fun x => ?_) hfinal
    unfold RadGauss.Classification.empiricalRademacher
    have hc : (0 : ℝ) ≤ (2 / (n : ℝ)) * B := by positivity
    calc _ ≤ (2 ^ n : ENNReal)⁻¹ * ∑ σ : Fin n → ℤˣ, ENNReal.ofReal ((2 / (n : ℝ)) * B *
            Real.sqrt (∑ i, ∑ l, ((σ i : ℤ) : ℝ) * ((σ l : ℤ) : ℝ) * k (x i) (x l))) := by
          gcongr with σ
          exact RGK73898060.sup_bound hk hB x (fun i => ((σ i : ℤ) : ℝ))
      _ = ENNReal.ofReal (∑ σ : Fin n → ℤˣ, (1 / (2 : ℝ) ^ n) • ((2 / (n : ℝ)) * B *
            Real.sqrt (∑ i, ∑ l, ((σ i : ℤ) : ℝ) * ((σ l : ℤ) : ℝ) * k (x i) (x l)))) := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun σ _ => by positivity), Finset.mul_sum]
          refine Finset.sum_congr rfl fun σ _ => ?_
          rw [smul_eq_mul, ENNReal.ofReal_mul (p := 1 / (2 : ℝ) ^ n) (by positivity), one_div,
            ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num)]
          simp
      _ ≤ ENNReal.ofReal ((2 / (n : ℝ)) * B * Real.sqrt (∑ σ : Fin n → ℤˣ, (1 / (2 : ℝ) ^ n) •
            (∑ i, ∑ l, ((σ i : ℤ) : ℝ) * ((σ l : ℤ) : ℝ) * k (x i) (x l)))) := by
          apply ENNReal.ofReal_le_ofReal
          simp_rw [smul_eq_mul, mul_left_comm (1 / (2 : ℝ) ^ n) ((2 / (n : ℝ)) * B)]
          rw [← Finset.mul_sum]
          apply mul_le_mul_of_nonneg_left _ hc
          have := Real.strictConcaveOn_sqrt.concaveOn.le_map_sum (t := Finset.univ)
            (w := fun _ : Fin n → ℤˣ => 1 / (2 : ℝ) ^ n)
            (p := fun σ : Fin n → ℤˣ =>
              ∑ i, ∑ l, ((σ i : ℤ) : ℝ) * ((σ l : ℤ) : ℝ) * k (x i) (x l))
            (fun _ _ => by positivity) (by
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
                Fintype.card_units_int, Fintype.card_fin, nsmul_eq_mul]
              push_cast
              field_simp)
            (fun σ _ => RGK73898060.kern_quad hk n x _)
          simpa [smul_eq_mul] using this
      _ = _ := by
          simp only [smul_eq_mul]
          rw [RGK73898060.rad_avg]
  · unfold RadGauss.LipschitzGaussian.gaussianComplexity
    refine le_trans (lintegral_mono fun x => ?_) hfinal
    unfold RadGauss.LipschitzGaussian.empiricalGaussian
    calc _ ≤ ∫⁻ g : Fin n → ℝ, ENNReal.ofReal ((2 / (n : ℝ)) * B *
            Real.sqrt (∑ i, ∑ l, g i * g l * k (x i) (x l)))
            ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) :=
          lintegral_mono fun g => RGK73898060.sup_bound hk hB x g
      _ ≤ _ := RGK73898060.lint_sqrt_le _ _ (fun g => RGK73898060.kern_quad hk n x g) (RGK73898060.gauss_avg k x).1 _
          (by positivity)
      _ = _ := by rw [(RGK73898060.gauss_avg k x).2]
