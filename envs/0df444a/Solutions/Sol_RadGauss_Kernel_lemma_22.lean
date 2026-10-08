-- Prove2me | solution 1 for RadGauss.Kernel.lemma_22
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T20:06:40.95364+00:00
-- url     : https://prove2.me/submissions/b46c803f-128e-410e-bad9-32c88feaed65

import Mathlib
import Definitions.Def_RadGauss_Kernel_Complexity
import Definitions.Def_RadGauss_Kernel_KernelClass



namespace RadGauss.Kernel

noncomputable def qfL22 {X : Type*} (k : X → X → ℝ) {N : ℕ} (y : Fin N → X) (u v : Fin N → ℝ) : ℝ :=
  ∑ i, ∑ j, u i * v j * k (y i) (y j)

lemma ksymm_L22 {X : Type*} [TopologicalSpace X] {k : X → X → ℝ} (hk : IsKernel k) (a b : X) :
    k a b = k b a := by
  have h := (hk.gram_posSemidef 2 ![a, b]).1
  have := congrFun (congrFun h 1) 0
  simpa [Matrix.conjTranspose_apply] using this

lemma qf_nonneg_L22 {X : Type*} [TopologicalSpace X] {k : X → X → ℝ} (hk : IsKernel k)
    {N : ℕ} (y : Fin N → X) (u : Fin N → ℝ) : 0 ≤ qfL22 k y u u := by
  have h := (hk.gram_posSemidef N y).dotProduct_mulVec_nonneg u
  refine h.trans_eq ?_
  simp only [qfL22, dotProduct, Matrix.mulVec, Matrix.of_apply, star_trivial, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma qf_cs_L22 {X : Type*} [TopologicalSpace X] {k : X → X → ℝ} (hk : IsKernel k)
    {N : ℕ} (y : Fin N → X) (u v : Fin N → ℝ) :
    qfL22 k y u v ^ 2 ≤ qfL22 k y u u * qfL22 k y v v := by
  have hsym : qfL22 k y v u = qfL22 k y u v := by
    unfold qfL22; rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [ksymm_L22 hk]; ring
  have hexp : ∀ t : ℝ, qfL22 k y (u + t • v) (u + t • v)
      = qfL22 k y v v * (t * t) + 2 * qfL22 k y u v * t + qfL22 k y u u := by
    intro t
    rw [← hsym]
    have : qfL22 k y v v * (t * t) + 2 * qfL22 k y v u * t + qfL22 k y u u
        = qfL22 k y v v * t * t + qfL22 k y v u * t + qfL22 k y u v * t + qfL22 k y u u := by
      rw [hsym]; ring
    rw [this]
    simp only [qfL22, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hd := discrim_le_zero (fun t => (hexp t) ▸ qf_nonneg_L22 hk y (u + t • v))
  unfold discrim at hd
  nlinarith

lemma f_bound_L22 {X : Type*} [TopologicalSpace X] {k : X → X → ℝ} (hk : IsKernel k)
    {B : ℝ} (hB : 0 ≤ B) {n : ℕ} (x : Fin n → X) (s : Fin n → ℝ) (f : X → ℝ)
    (hf : f ∈ kernelClass k B) :
    |∑ i, s i * f (x i)| ≤ B * Real.sqrt (qfL22 k x s s) := by
  obtain ⟨m, c, α, hle, rfl⟩ := hf
  set y : Fin (n + m) → X := Fin.append x c
  set u : Fin (n + m) → ℝ := Fin.append s 0
  set v : Fin (n + m) → ℝ := Fin.append 0 α
  have h1 : qfL22 k y u v = ∑ i, s i * ∑ j, α j * k (x i) (c j) := by
    simp only [qfL22, y, u, v, Fin.sum_univ_add, Fin.append_left, Fin.append_right,
      Pi.zero_apply, zero_mul, mul_zero, Finset.sum_const_zero, add_zero, zero_add,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have h2 : qfL22 k y u u = qfL22 k x s s := by
    simp [qfL22, y, u, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  have h3 : qfL22 k y v v = ∑ i, ∑ j, α i * α j * k (c i) (c j) := by
    simp [qfL22, y, v, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  have hcs := qf_cs_L22 hk y u v
  rw [h1, h2, h3] at hcs
  show |∑ i, s i * ∑ j, α j * k (x i) (c j)| ≤ _
  have ha := qf_nonneg_L22 hk x s
  calc |∑ i, s i * ∑ j, α j * k (x i) (c j)|
      ≤ Real.sqrt (qfL22 k x s s * B ^ 2) := by
        apply Real.abs_le_sqrt
        exact hcs.trans (mul_le_mul_of_nonneg_left hle ha)
    _ = B * Real.sqrt (qfL22 k x s s) := by
        rw [Real.sqrt_mul ha, Real.sqrt_sq hB, mul_comm]

lemma sup_bound_L22 {X : Type*} [TopologicalSpace X] {k : X → X → ℝ} (hk : IsKernel k)
    {B : ℝ} (hB : 0 ≤ B) {n : ℕ} (x : Fin n → X) (s : Fin n → ℝ) :
    (⨆ f ∈ kernelClass k B, ENNReal.ofReal |(2 / (n : ℝ)) * ∑ i, s i * f (x i)|)
      ≤ ENNReal.ofReal (2 * B / n * Real.sqrt (qfL22 k x s s)) := by
  refine iSup₂_le fun f hf => ENNReal.ofReal_le_ofReal ?_
  rw [abs_mul, abs_of_nonneg (by positivity)]
  calc 2 / (n:ℝ) * |∑ i, s i * f (x i)| ≤ 2 / n * (B * Real.sqrt (qfL22 k x s s)) :=
        mul_le_mul_of_nonneg_left (f_bound_L22 hk hB x s f hf) (by positivity)
    _ = _ := by ring

open MeasureTheory ProbabilityTheory

lemma sign_sum_L22 (n : ℕ) (i j : Fin n) :
    ∑ σ : Fin n → ℤˣ, ((σ i : ℤ) : ℝ) * ((σ j : ℤ) : ℝ) = if i = j then (2:ℝ) ^ n else 0 := by
  split_ifs with hij
  · subst hij
    have : ∀ σ : Fin n → ℤˣ, ((σ i : ℤ) : ℝ) * ((σ i : ℤ) : ℝ) = 1 := by
      intro σ
      rcases Int.units_eq_one_or (σ i) with h | h <;> rw [h] <;> simp
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_units_int,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    push_cast; ring
  · set τ : Fin n → ℤˣ := Function.update 1 i (-1)
    set F : (Fin n → ℤˣ) → ℝ := fun σ => ((σ i : ℤ) : ℝ) * ((σ j : ℤ) : ℝ)
    have hF : ∀ σ, F (τ * σ) = - F σ := by
      intro σ
      simp only [F, τ, Pi.mul_apply, Function.update_self, Function.update_of_ne (Ne.symm hij),
        Pi.one_apply, one_mul]
      push_cast; ring
    have h := Equiv.sum_comp (Equiv.mulLeft τ) F
    simp only [Equiv.coe_mulLeft, hF, Finset.sum_neg_distrib] at h
    show ∑ σ, F σ = 0
    linarith

lemma rad_sum_L22 {X : Type*} (k : X → X → ℝ) {n : ℕ} (x : Fin n → X) :
    ∑ σ : Fin n → ℤˣ, qfL22 k x (fun i => ((σ i : ℤ) : ℝ)) (fun i => ((σ i : ℤ) : ℝ))
      = 2 ^ n * ∑ i, k (x i) (x i) := by
  simp only [qfL22]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (γ := Fin n → ℤˣ), ← Finset.sum_mul, sign_sum_L22]
  simp [Finset.mul_sum]

lemma rad_bound_L22 {X : Type*} [TopologicalSpace X] {k : X → X → ℝ} (hk : IsKernel k)
    {B : ℝ} (hB : 0 ≤ B) {n : ℕ} (x : Fin n → X) :
    RadGauss.Classification.empiricalRademacher (kernelClass k B) n x
        ≤ ENNReal.ofReal (2 * B / n * Real.sqrt (∑ i, k (x i) (x i))) := by
  unfold RadGauss.Classification.empiricalRademacher
  set c : ℝ := 2 * B / n
  have hc : 0 ≤ c := by positivity
  set q : (Fin n → ℤˣ) → ℝ := fun σ => qfL22 k x (fun i => ((σ i : ℤ) : ℝ)) (fun i => ((σ i : ℤ) : ℝ))
  have hq : ∀ σ, 0 ≤ q σ := fun σ => qf_nonneg_L22 hk x _
  calc (2 ^ n : ENNReal)⁻¹ * ∑ σ : Fin n → ℤˣ,
        ⨆ f ∈ kernelClass k B, ENNReal.ofReal |(2 / (n : ℝ)) * ∑ i, ((σ i : ℤ) : ℝ) * f (x i)|
      ≤ (2 ^ n : ENNReal)⁻¹ * ∑ σ : Fin n → ℤˣ, ENNReal.ofReal (c * Real.sqrt (q σ)) := by
        gcongr with σ
        exact sup_bound_L22 hk hB x _
    _ = ENNReal.ofReal (((2:ℝ) ^ n)⁻¹ * ∑ σ : Fin n → ℤˣ, c * Real.sqrt (q σ)) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg (fun σ _ => by
          have := Real.sqrt_nonneg (q σ); positivity),
          ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num)]
        simp
    _ ≤ ENNReal.ofReal (c * Real.sqrt (∑ i, k (x i) (x i))) := by
        apply ENNReal.ofReal_le_ofReal
        rw [← Finset.mul_sum]
        have hT : 0 ≤ ∑ i, k (x i) (x i) := by
          have h := rad_sum_L22 k x
          have : 0 ≤ ∑ σ, q σ := Finset.sum_nonneg fun σ _ => hq σ
          have h2 : (0:ℝ) < 2 ^ n := by positivity
          nlinarith
        have hS : ∑ σ : Fin n → ℤˣ, Real.sqrt (q σ) ≤ 2 ^ n * Real.sqrt (∑ i, k (x i) (x i)) := by
          have h1 := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun σ => Real.sqrt (q σ))
          simp only [Real.sq_sqrt (hq _), Finset.card_univ, Fintype.card_fun,
            Fintype.card_units_int, Fintype.card_fin] at h1
          have h2 : ∑ σ, q σ = 2 ^ n * ∑ i, k (x i) (x i) := rad_sum_L22 k x
          rw [h2] at h1
          have h3 : (∑ σ : Fin n → ℤˣ, Real.sqrt (q σ)) ^ 2
              ≤ (2 ^ n * Real.sqrt (∑ i, k (x i) (x i))) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt hT]; push_cast at h1; linarith
          have h0 : 0 ≤ ∑ σ : Fin n → ℤˣ, Real.sqrt (q σ) :=
            Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
          exact (pow_le_pow_iff_left₀ h0 (by positivity) two_ne_zero).1 h3
        have h2 : (0:ℝ) < 2 ^ n := by positivity
        calc ((2:ℝ) ^ n)⁻¹ * (c * ∑ σ, Real.sqrt (q σ))
            ≤ ((2:ℝ) ^ n)⁻¹ * (c * (2 ^ n * Real.sqrt (∑ i, k (x i) (x i)))) := by gcongr
          _ = c * Real.sqrt (∑ i, k (x i) (x i)) := by field_simp

lemma coord_memLp_L22 (n : ℕ) (i : Fin n) :
    MemLp (fun g : Fin n → ℝ => g i) 2 (Measure.pi fun _ : Fin n => gaussianReal 0 1) :=
  (memLp_id_gaussianReal 2).comp_measurePreserving (measurePreserving_eval _ i)

lemma coord_int_L22 (n : ℕ) (i : Fin n) :
    ∫ g : Fin n → ℝ, g i ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) = 0 := by
  have h := (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i).map_eq
  change Measure.map (fun g : Fin n → ℝ => g i) _ = _ at h
  have e : ∫ g : Fin n → ℝ, g i ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)
      = ∫ y, y ∂(Measure.map (fun g : Fin n → ℝ => g i) (Measure.pi fun _ : Fin n => gaussianReal 0 1)) :=
    (integral_map (μ := Measure.pi fun _ : Fin n => gaussianReal 0 1) (φ := fun g : Fin n → ℝ => g i)
      (f := fun y : ℝ => y) (measurable_pi_apply i).aemeasurable (by fun_prop)).symm
  rw [e, h, integral_id_gaussianReal]

lemma gauss_int_L22 (n : ℕ) (i j : Fin n) :
    ∫ g : Fin n → ℝ, g i * g j ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)
      = if i = j then 1 else 0 := by
  split_ifs with hij
  · subst hij
    have h := (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i).map_eq
    change Measure.map (fun g : Fin n → ℝ => g i) _ = _ at h
    have hv := variance_id_gaussianReal (μ := 0) (v := 1)
    have hm : ∫ y, y ∂gaussianReal 0 1 = 0 := integral_id_gaussianReal
    rw [variance_eq_integral aemeasurable_id] at hv
    simp only [id] at hv
    rw [hm] at hv
    have e : ∫ g : Fin n → ℝ, g i * g i ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)
        = ∫ y, y * y ∂(Measure.map (fun g : Fin n → ℝ => g i) (Measure.pi fun _ : Fin n => gaussianReal 0 1)) :=
      (integral_map (μ := Measure.pi fun _ : Fin n => gaussianReal 0 1) (φ := fun g : Fin n → ℝ => g i)
        (f := fun y : ℝ => y * y) (measurable_pi_apply i).aemeasurable (by fun_prop)).symm
    rw [e, h]
    simpa [sq] using hv
  · have hind := (iIndepFun_pi (μ := fun _ : Fin n => gaussianReal 0 1)
      (X := fun _ => (id : ℝ → ℝ)) (fun _ => aemeasurable_id)).indepFun hij
    show ∫ g : Fin n → ℝ, id (g i) * id (g j) ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) = 0
    rw [hind.integral_fun_mul_eq_mul_integral (measurable_pi_apply i).aestronglyMeasurable
      (measurable_pi_apply j).aestronglyMeasurable]
    simp only [id]
    rw [coord_int_L22, zero_mul]

lemma gauss_q_int_L22 {X : Type*} (k : X → X → ℝ) {n : ℕ} (x : Fin n → X) :
    Integrable (fun g : Fin n → ℝ => qfL22 k x g g) (Measure.pi fun _ : Fin n => gaussianReal 0 1)
      ∧ ∫ g : Fin n → ℝ, qfL22 k x g g ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)
        = ∑ i, k (x i) (x i) := by
  have hint : ∀ i j, Integrable (fun g : Fin n → ℝ => g i * g j * k (x i) (x j))
      (Measure.pi fun _ : Fin n => gaussianReal 0 1) := fun i j =>
    ((coord_memLp_L22 n i).integrable_mul (coord_memLp_L22 n j)).mul_const _
  refine ⟨?_, ?_⟩
  · unfold qfL22
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j
  · unfold qfL22
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => hint i j]
    simp_rw [integral_mul_const, gauss_int_L22]
    simp

lemma gauss_bound_L22 {X : Type*} [TopologicalSpace X] {k : X → X → ℝ} (hk : IsKernel k)
    {B : ℝ} (hB : 0 ≤ B) {n : ℕ} (x : Fin n → X) :
    empiricalGaussian (kernelClass k B) n x
        ≤ ENNReal.ofReal (2 * B / n * Real.sqrt (∑ i, k (x i) (x i))) := by
  unfold empiricalGaussian
  set ν := Measure.pi fun _ : Fin n => gaussianReal 0 1
  set c : ℝ := 2 * B / n
  have hc : 0 ≤ c := by positivity
  obtain ⟨hqi, hqe⟩ := gauss_q_int_L22 k x
  have hmeas : Measurable fun g : Fin n → ℝ => ENNReal.ofReal (Real.sqrt (qfL22 k x g g)) := by
    unfold qfL22; fun_prop
  calc ∫⁻ g : Fin n → ℝ, ⨆ f ∈ kernelClass k B,
          ENNReal.ofReal |(2 / (n : ℝ)) * ∑ i, g i * f (x i)| ∂ν
      ≤ ∫⁻ g, ENNReal.ofReal c * ENNReal.ofReal (Real.sqrt (qfL22 k x g g)) ∂ν := by
        refine lintegral_mono fun g => ?_
        rw [← ENNReal.ofReal_mul hc]
        exact sup_bound_L22 hk hB x g
    _ = ENNReal.ofReal c * ∫⁻ g, ENNReal.ofReal (Real.sqrt (qfL22 k x g g)) ∂ν :=
        lintegral_const_mul _ hmeas
    _ ≤ ENNReal.ofReal c * ENNReal.ofReal (Real.sqrt (∑ i, k (x i) (x i))) := by
        gcongr
        have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two
          hmeas.aemeasurable (aemeasurable_const (b := (1 : ENNReal)))
        simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, measure_univ] at hH
        refine hH.trans (le_of_eq ?_)
        have h2 : ∀ g : Fin n → ℝ, ENNReal.ofReal (Real.sqrt (qfL22 k x g g)) ^ (2:ℝ)
            = ENNReal.ofReal (qfL22 k x g g) := by
          intro g
          rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num),
            Real.rpow_two, Real.sq_sqrt (qf_nonneg_L22 hk x g)]
        simp_rw [h2]
        have hT : 0 ≤ ∑ i, k (x i) (x i) := by
          rw [← hqe]; exact integral_nonneg fun g => qf_nonneg_L22 hk x g
        have hae : 0 ≤ᵐ[ν] fun g => qfL22 k x g g :=
          Filter.Eventually.of_forall fun g => qf_nonneg_L22 hk x g
        rw [← ofReal_integral_eq_lintegral_ofReal hqi hae, hqe,
          ENNReal.ofReal_rpow_of_nonneg hT (by norm_num), Real.sqrt_eq_rpow]
    _ = ENNReal.ofReal (c * Real.sqrt (∑ i, k (x i) (x i))) := by rw [ENNReal.ofReal_mul hc]

theorem l22_core {X : Type*} [TopologicalSpace X] (k : X → X → ℝ) (hk : IsKernel k)
    (B : ℝ) (hB : 0 ≤ B) (n : ℕ) (x : Fin n → X) :
    empiricalGaussian (kernelClass k B) n x
        ≤ ENNReal.ofReal (2 * B / n * Real.sqrt (∑ i, k (x i) (x i))) ∧
      RadGauss.Classification.empiricalRademacher (kernelClass k B) n x
        ≤ ENNReal.ofReal (2 * B / n * Real.sqrt (∑ i, k (x i) (x i))) :=
  ⟨gauss_bound_L22 hk hB x, rad_bound_L22 hk hB x⟩

end RadGauss.Kernel

open RadGauss.Kernel


theorem solution {X : Type*} [TopologicalSpace X] (k : X → X → ℝ) (hk : IsKernel k)
    (B : ℝ) (hB : 0 ≤ B) (n : ℕ) (x : Fin n → X) :
    empiricalGaussian (kernelClass k B) n x
        ≤ ENNReal.ofReal (2 * B / n * Real.sqrt (∑ i, k (x i) (x i))) ∧
      RadGauss.Classification.empiricalRademacher (kernelClass k B) n x
        ≤ ENNReal.ofReal (2 * B / n * Real.sqrt (∑ i, k (x i) (x i))) := by
  exact l22_core k hk B hB n x
