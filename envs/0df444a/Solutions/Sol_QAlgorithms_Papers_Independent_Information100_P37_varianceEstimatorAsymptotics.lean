-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P37.varianceEstimatorAsymptotics
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T17:07:39.364926+00:00
-- url     : https://prove2.me/submissions/7adff346-4589-482e-b3a8-10f7cda70c0c

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

open scoped BigOperators Topology ENNReal

namespace X7V

variable {S : Type*} [MeasurableSpace S] (ν : Measure S) [IsProbabilityMeasure ν]

lemma map_restrict (N : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => ν)).map (fun ω (i : Fin N) => ω i) =
      Measure.pi (fun _ : Fin N => ν) := by
  refine (Measure.pi_eq fun s hs => ?_).symm
  have hm : Measurable (fun ω : ℕ → S => fun i : Fin N => ω i) := by fun_prop
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  let t : ℕ → Set S := fun n => if h : n < N then s ⟨n, h⟩ else univ
  have hpre : (fun ω : ℕ → S => fun i : Fin N => ω i) ⁻¹' (univ.pi s) =
      Set.pi (↑(Finset.range N)) t := by
    ext ω
    simp only [mem_preimage, Set.mem_pi, Finset.coe_range, mem_Iio, t]
    constructor
    · intro h n hn; simp only [dif_pos hn]; exact h ⟨n, hn⟩ (mem_univ _)
    · intro h i _; have := h i.1 i.2; simpa only [dif_pos i.2] using this
  rw [hpre, Measure.infinitePi_pi]
  · rw [← Fin.prod_univ_eq_prod_range (fun n => ν (t n))]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [t, i.2]
  · intro n hn
    simp only [t]
    split_ifs
    · exact hs _
    · exact MeasurableSet.univ

/-- L¹-smallness implies convergence in measure to 0. -/
lemma tim_of_L1 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (f : ℕ → Ω → ℝ) (g : ℕ → Ω → ℝ) (e : ℕ → ℝ)
    (hle : ∀ᶠ n in atTop, ∀ ω, |f n ω| ≤ g n ω) (hg : ∀ n, Integrable (g n) P)
    (hint : ∀ᶠ n in atTop, ∫ ω, g n ω ∂P ≤ e n) (he : Tendsto e atTop (𝓝 0))
    (hfm : ∀ n, AEStronglyMeasurable (f n) P) :
    TendstoInMeasure P f atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro ε hε
  have hup : Tendsto (fun n => e n / ε) atTop (𝓝 0) := by simpa using he.div_const ε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun n => measureReal_nonneg) ?_
  filter_upwards [hle, hint] with n hn hn2
  have hg0 : 0 ≤ᵐ[P] g n := Eventually.of_forall fun ω => (abs_nonneg _).trans (hn ω)
  have hM := mul_meas_ge_le_integral_of_nonneg hg0 (hg n) ε
  have hsub : P.real {x | ε ≤ ‖f n x - 0‖} ≤ P.real {x | ε ≤ g n x} := by
    refine measureReal_mono (fun x hx => ?_)
    simp only [mem_ofPred_eq, sub_zero, Real.norm_eq_abs] at hx ⊢
    exact hx.trans (hn x)
  rw [le_div_iff₀ hε]
  nlinarith


local notation "PP" => Measure.infinitePi (fun _ : ℕ => ν)

omit [IsProbabilityMeasure ν] in
lemma eval_int [IsProbabilityMeasure ν] (f : S → ℝ) (hf : Measurable f) (i : ℕ) :
    ∫ ω, f (ω i) ∂PP = ∫ s, f s ∂ν := by
  have h := Measure.infinitePi_map_eval (fun _ : ℕ => ν) i
  rw [← integral_map (measurable_pi_apply i).aemeasurable hf.aestronglyMeasurable, h]

/-- Integrability of continuous functions of finitely many bounded coordinates. -/
lemma intF (X : S → ℝ) (hX : Measurable X) (C : ℝ) (hC : ∀ s, |X s| ≤ C) (n : ℕ)
    (F : (Fin n → ℝ) → ℝ) (hF : Continuous F) :
    Integrable (fun ω : ℕ → S => F (fun i => X (ω i))) PP := by
  obtain ⟨B, hB⟩ := (isCompact_univ_pi fun _ : Fin n =>
    isCompact_Icc (a := -C) (b := C)).exists_bound_of_continuousOn hF.continuousOn
  refine Integrable.of_bound (hF.measurable.comp (by fun_prop)).aestronglyMeasurable B
    (Eventually.of_forall fun ω => hB _ fun i _ => ?_)
  exact abs_le.1 (hC _)

lemma sq_sum (g : S → ℝ) (hg : Measurable g) (B : ℝ) (hB : ∀ s, |g s| ≤ B)
    (h0 : ∫ s, g s ∂ν = 0) (n : ℕ) :
    ∫ ω, (∑ i : Fin n, g (ω i)) ^ 2 ∂PP = n * ∫ s, g s ^ 2 ∂ν := by
  have hint : ∀ i j : Fin n, Integrable (fun ω : ℕ → S => g (ω i) * g (ω j)) PP := fun i j =>
    intF ν g hg B hB n (fun x => x i * x j) (by fun_prop)
  simp_rw [sq, Finset.sum_mul_sum]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
  have hind := iIndepFun_infinitePi (P := fun _ : ℕ => ν) (X := fun _ => g) (fun _ => hg)
  have : ∀ i : Fin n, ∫ ω, ∑ j : Fin n, g (ω i) * g (ω j) ∂PP = ∫ s, g s * g s ∂ν := by
    intro i
    rw [integral_finsetSum _ fun j _ => hint i j, Finset.sum_eq_single i]
    · exact eval_int ν (fun s => g s * g s) (hg.mul hg) i
    · intro j _ hji
      have hij : (i : ℕ) ≠ j := fun h => hji (Fin.ext h).symm
      have := (hind.indepFun hij).integral_mul_eq_mul_integral
        (hg.comp (measurable_pi_apply _)).aestronglyMeasurable
        (hg.comp (measurable_pi_apply _)).aestronglyMeasurable
      simp only [Pi.mul_apply] at this
      rw [this, eval_int ν g hg, h0, zero_mul]
    · simp
  simp_rw [this]
  simp

lemma alg (n : ℕ) (hn : n ≠ 0) (x : Fin n → ℝ) (m : ℝ) :
    ∑ i, (x i - (∑ j, x j) / n) ^ 2 = ∑ i, (x i - m) ^ 2 - (∑ i, (x i - m)) ^ 2 / n := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have key : ∀ i, x i - (∑ j, x j) / n = (x i - m) - (∑ j, (x j - m)) / n := by
    intro i; rw [Finset.sum_sub_distrib]; simp; field_simp; ring
  simp_rw [key]
  generalize hy : (fun i => x i - m) = y
  have : ∀ i, x i - m = y i := fun i => by rw [← hy]
  simp_rw [this]
  simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

lemma map_eval (h : S → ℝ) (hh : Measurable h) (i : ℕ) :
    (PP).map (fun ω => h (ω i)) = ν.map h := by
  have := Measure.map_map hh (measurable_pi_apply i) (μ := PP)
  rw [Measure.infinitePi_map_eval] at this
  exact this.symm

def SVg (n : ℕ) (x : Fin n → ℝ) : ℝ := (∑ i, (x i - (∑ j, x j) / n) ^ 2) / ((n : ℝ) - 1)

lemma SVg_cont (n : ℕ) : Continuous (SVg n) := by
  unfold SVg; fun_prop

lemma SVg_eq (n : ℕ) (hn : n ≠ 0) (x : Fin n → ℝ) (m : ℝ) :
    SVg n x = (∑ i, (x i - m) ^ 2 - (∑ i, (x i - m)) ^ 2 / n) / ((n : ℝ) - 1) := by
  rw [SVg, alg n hn x m]

lemma SVg_nonneg (n : ℕ) (x : Fin n → ℝ) : 0 ≤ SVg n x := by
  unfold SVg
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact div_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _)
      (by have : (1:ℝ) ≤ n := by exact_mod_cast hn
          linarith)

variable (X : S → ℝ)

def mX : ℝ := ∫ s, X s ∂ν
def s2 : ℝ := ∫ s, (X s - mX ν X) ^ 2 ∂ν
def m4 : ℝ := ∫ s, (X s - mX ν X) ^ 4 ∂ν

variable (hX : Measurable X) (C : ℝ) (hC : ∀ s, |X s| ≤ C)
include hX hC

lemma intν (f : ℝ → ℝ) (hf : Continuous f) : Integrable (fun s => f (X s)) ν := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := -C) (b := C)).exists_bound_of_continuousOn hf.continuousOn
  exact Integrable.of_bound (hf.measurable.comp hX).aestronglyMeasurable B
    (Eventually.of_forall fun s => hB _ (abs_le.1 (hC s)))

lemma centered_bound : ∀ s, |X s - mX ν X| ≤ C + |mX ν X| := fun s =>
  (abs_sub _ _).trans (by linarith [hC s])

lemma centered_mean : ∫ s, (X s - mX ν X) ∂ν = 0 := by
  have hi : Integrable X ν := intν ν X hX C hC id continuous_id
  rw [integral_sub hi (integrable_const _)]
  simp [mX]

lemma mean_SV (n : ℕ) (hn : 2 ≤ n) :
    ∫ ω, SVg n (fun i => X (ω i)) ∂PP = s2 ν X := by
  have hn0 : n ≠ 0 := by omega
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn0
  simp_rw [SVg_eq n hn0 _ (mX ν X)]
  rw [integral_div, integral_sub, integral_finsetSum, integral_div]
  · have h1 : ∀ i : Fin n, ∫ ω, (X (ω i) - mX ν X) ^ 2 ∂PP = s2 ν X := fun i =>
      eval_int ν (fun s => (X s - mX ν X) ^ 2) (by fun_prop) i
    simp_rw [h1]
    rw [sq_sum ν (fun s => X s - mX ν X) (by fun_prop) _ (centered_bound ν X hX C hC)
      (centered_mean ν X hX C hC) n]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    change (n * s2 ν X - n * s2 ν X / n) / ((n : ℝ) - 1) = s2 ν X
    field_simp
  · intro i _
    exact intF ν X hX C hC n (fun x => (x i - mX ν X) ^ 2) (by fun_prop)
  · exact intF ν X hX C hC n (fun x => ∑ i, (x i - mX ν X) ^ 2) (by fun_prop)
  · exact intF ν X hX C hC n (fun x => (∑ i, (x i - mX ν X)) ^ 2 / n) (by fun_prop)

lemma var_Z :
    Var[fun ω : ℕ → S => (X (ω 0) - mX ν X) ^ 2; PP] = m4 ν X - s2 ν X ^ 2 ∧
    ∫ ω, (X (ω 0) - mX ν X) ^ 2 ∂PP = s2 ν X := by
  have h2 : ∫ ω, (X (ω 0) - mX ν X) ^ 2 ∂PP = s2 ν X :=
    eval_int ν (fun s => (X s - mX ν X) ^ 2) (by fun_prop) 0
  refine ⟨?_, h2⟩
  rw [variance_eq_sub]
  · simp only [Pi.pow_apply]
    rw [h2, eval_int ν (fun s => ((X s - mX ν X) ^ 2) ^ 2) (by fun_prop) 0]
    simp only [m4, ← pow_mul]
  · obtain ⟨B, hB⟩ := (isCompact_Icc (a := -C) (b := C)).exists_bound_of_continuousOn
      (show Continuous (fun x : ℝ => (x - mX ν X) ^ 2) by fun_prop).continuousOn
    refine MemLp.of_bound (show Measurable (fun ω : ℕ → S => (X (ω 0) - mX ν X) ^ 2) by fun_prop).aestronglyMeasurable B (Eventually.of_forall fun ω => ?_)
    exact hB _ (abs_le.1 (hC _))

lemma v_nonneg : 0 ≤ m4 ν X - s2 ν X ^ 2 := by
  rw [← (var_Z ν X hX C hC).1]; exact variance_nonneg _ _

lemma clt : TendstoInDistribution
    (fun (n : ℕ) (ω : ℕ → S) => (√n)⁻¹ * (∑ k ∈ Finset.range n, (X (ω k) - mX ν X) ^ 2 - n * s2 ν X))
    atTop id (fun _ => PP) (gaussianReal 0 (m4 ν X - s2 ν X ^ 2).toNNReal) := by
  obtain ⟨hv, hm⟩ := var_Z ν X hX C hC
  have hZm : ∀ k, Measurable (fun ω : ℕ → S => (X (ω k) - mX ν X) ^ 2) := fun k => by fun_prop
  have hY : HasLaw (id : ℝ → ℝ) (gaussianReal 0 (Var[fun ω : ℕ → S => (X (ω 0) - mX ν X) ^ 2; PP]).toNNReal)
      (gaussianReal 0 (m4 ν X - s2 ν X ^ 2).toNNReal) := by
    rw [hv]; exact ⟨aemeasurable_id, Measure.map_id⟩
  have := tendstoInDistribution_inv_sqrt_mul_sum_sub (X := fun k (ω : ℕ → S) => (X (ω k) - mX ν X) ^ 2)
    hY ?_ ?_ ?_
  · simpa [hm] using this
  · obtain ⟨B, hB⟩ := (isCompact_Icc (a := -C) (b := C)).exists_bound_of_continuousOn
      (show Continuous (fun x : ℝ => (x - mX ν X) ^ 2) by fun_prop).continuousOn
    exact MemLp.of_bound (hZm 0).aestronglyMeasurable B (Eventually.of_forall fun ω => hB _ (abs_le.1 (hC _)))
  · exact iIndepFun_infinitePi (P := fun _ : ℕ => ν) (X := fun _ s => (X s - mX ν X) ^ 2) (fun _ => by fun_prop)
  · intro i
    refine ⟨(hZm i).aemeasurable, (hZm 0).aemeasurable, ?_⟩
    rw [map_eval ν (fun s => (X s - mX ν X) ^ 2) (by fun_prop) i,
      map_eval ν (fun s => (X s - mX ν X) ^ 2) (by fun_prop) 0]

omit hX hC in
lemma lim_aux (a b : ℝ) : Tendsto (fun n : ℕ => (a * √(n : ℝ) + b) / ((n : ℝ) - 1)) atTop (𝓝 0) := by
  have hu : Tendsto (fun n : ℕ => (√(n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hlim : Tendsto (fun n : ℕ => (a * (√(n : ℝ))⁻¹ + b * ((√(n : ℝ))⁻¹) ^ 2) /
      (1 - ((√(n : ℝ))⁻¹) ^ 2)) atTop (𝓝 0) := by
    have := ((tendsto_const_nhds (x := a)).mul hu).add ((tendsto_const_nhds (x := b)).mul (hu.pow 2))
    have h2 := (tendsto_const_nhds (x := (1:ℝ))).sub (hu.pow 2)
    have h3 := this.div h2 (by norm_num)
    rw [show (a * 0 + b * 0 ^ 2) / (1 - 0 ^ 2) = (0:ℝ) by ring] at h3
    exact h3
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn2 : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hr : (n : ℝ) = (√(n : ℝ)) ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg n)).symm
  have hpos : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  generalize √(n : ℝ) = r at hr hpos ⊢
  rw [hr] at hn1 ⊢
  have h1 : 1 - (r⁻¹) ^ 2 ≠ 0 := by
    rw [inv_pow, sub_ne_zero]; intro h
    apply hn1; field_simp at h; linarith
  field_simp

lemma W_sub_T : TendstoInMeasure PP
    ((fun (n : ℕ) (ω : ℕ → S) => √(n : ℝ) * (SVg n (fun i : Fin n => X (ω i)) - s2 ν X)) -
     (fun (n : ℕ) (ω : ℕ → S) => (√(n : ℝ))⁻¹ *
        (∑ k ∈ Finset.range n, (X (ω k) - mX ν X) ^ 2 - n * s2 ν X))) atTop 0 := by
  set m := mX ν X
  let g : ℕ → (ℕ → S) → ℝ := fun n ω =>
    (∑ i : Fin n, (X (ω i) - m) ^ 2 + (∑ i : Fin n, (X (ω i) - m)) ^ 2) / (√(n : ℝ) * ((n : ℝ) - 1))
  refine tim_of_L1 _ g (fun n => (2 * s2 ν X * √(n : ℝ) + 0) / ((n : ℝ) - 1)) ?_ ?_ ?_
    (lim_aux _ _) ?_
  · filter_upwards [eventually_ge_atTop 2] with n hn ω
    have hn0 : n ≠ 0 := by omega
    have hn2 : (2:ℝ) ≤ n := by exact_mod_cast hn
    simp only [Pi.sub_apply, g]
    rw [SVg_eq n hn0 _ m, ← Fin.sum_univ_eq_sum_range (fun k => (X (ω k) - m) ^ 2)]
    have hr : (n : ℝ) = (√(n : ℝ)) ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg n)).symm
    have hpos : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by linarith)
    have hA : 0 ≤ ∑ i : Fin n, (X (ω i) - m) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    generalize ∑ i : Fin n, (X (ω i) - m) ^ 2 = A at hA ⊢
    generalize ∑ i : Fin n, (X (ω i) - m) = B
    generalize √(n : ℝ) = r at hr hpos ⊢
    rw [hr] at hn2 ⊢
    have hd : 0 < r * (r ^ 2 - 1) := mul_pos hpos (by linarith)
    have hd1 : r ^ 2 - 1 ≠ 0 := by linarith
    have : r * ((A - B ^ 2 / r ^ 2) / (r ^ 2 - 1) - s2 ν X) - r⁻¹ * (A - r ^ 2 * s2 ν X) =
        (A - B ^ 2) / (r * (r ^ 2 - 1)) := by
      field_simp; ring
    rw [this, abs_div, abs_of_pos hd]
    gcongr
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg B]
  · intro n
    exact intF ν X hX C hC n (fun x => (∑ i, (x i - m) ^ 2 + (∑ i, (x i - m)) ^ 2) /
      (√(n : ℝ) * ((n : ℝ) - 1))) (by fun_prop)
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hn2 : (2:ℝ) ≤ n := by exact_mod_cast hn
    refine le_of_eq ?_
    simp only [g]
    rw [integral_div, integral_add, integral_finsetSum]
    · have h1 : ∀ i : Fin n, ∫ ω, (X (ω i) - m) ^ 2 ∂PP = s2 ν X := fun i =>
        eval_int ν (fun s => (X s - m) ^ 2) (by fun_prop) i
      simp_rw [h1]
      rw [sq_sum ν (fun s => X s - m) (by fun_prop) _ (centered_bound ν X hX C hC)
        (centered_mean ν X hX C hC) n]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      change (n * s2 ν X + n * s2 ν X) / (√(n : ℝ) * ((n : ℝ) - 1)) = _
      have hr : (n : ℝ) = (√(n : ℝ)) ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg n)).symm
      have hpos : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by linarith)
      generalize √(n : ℝ) = r at hr hpos ⊢
      rw [hr] at hn2 ⊢
      have : r ^ 2 - 1 ≠ 0 := by linarith
      field_simp
      ring
    · intro i _
      exact intF ν X hX C hC n (fun x => (x i - m) ^ 2) (by fun_prop)
    · exact intF ν X hX C hC n (fun x => ∑ i, (x i - m) ^ 2) (by fun_prop)
    · exact intF ν X hX C hC n (fun x => (∑ i, (x i - m)) ^ 2) (by fun_prop)
  · intro n
    refine Measurable.aestronglyMeasurable ?_
    have h1 : Measurable (fun ω : ℕ → S => SVg n (fun i : Fin n => X (ω i))) :=
      (SVg_cont n).measurable.comp (by fun_prop)
    simp only [Pi.sub_apply]
    exact (measurable_const.mul (h1.sub measurable_const)).sub
      (measurable_const.mul ((Finset.measurable_sum _ fun k _ => by fun_prop).sub measurable_const))

lemma W_tid : TendstoInDistribution
    (fun (n : ℕ) (ω : ℕ → S) => √(n : ℝ) * (SVg n (fun i : Fin n => X (ω i)) - s2 ν X))
    atTop id (fun _ => PP) (gaussianReal 0 (m4 ν X - s2 ν X ^ 2).toNNReal) := by
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ (clt ν X hX C hC) (W_sub_T ν X hX C hC) ?_
  intro n
  have h1 : Measurable (fun ω : ℕ → S => SVg n (fun i : Fin n => X (ω i))) :=
    (SVg_cont n).measurable.comp (by fun_prop)
  exact (measurable_const.mul (h1.sub measurable_const)).aemeasurable

omit hX hC in
lemma s2_nonneg : 0 ≤ s2 ν X := integral_nonneg fun _ => sq_nonneg _

omit hX hC in
lemma SV_bound (n : ℕ) (hn : 2 ≤ n) (A B σ2 : ℝ) (hσ : 0 ≤ σ2) :
    |(A - B ^ 2 / n) / ((n : ℝ) - 1) - σ2| ≤
      ((A - n * σ2) ^ 2 / √(n : ℝ) + √(n : ℝ) + σ2 + B ^ 2 / n) / ((n : ℝ) - 1) := by
  have hn2 : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hr : (n : ℝ) = (√(n : ℝ)) ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg n)).symm
  have hpos : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by linarith)
  generalize √(n : ℝ) = r at hr hpos ⊢
  rw [hr] at hn2 ⊢
  have hd : 0 < r ^ 2 - 1 := by linarith
  have : (A - B ^ 2 / r ^ 2) / (r ^ 2 - 1) - σ2 =
      ((A - r ^ 2 * σ2) + σ2 - B ^ 2 / r ^ 2) / (r ^ 2 - 1) := by
    field_simp; ring
  rw [this, abs_div, abs_of_pos hd]
  gcongr
  generalize A - r ^ 2 * σ2 = a
  have ha : |a| ≤ a ^ 2 / r + r := by
    rw [div_add' _ _ _ hpos.ne', le_div_iff₀ hpos]
    nlinarith [sq_abs a, sq_nonneg (|a| - r), abs_nonneg a]
  have hb : 0 ≤ B ^ 2 / r ^ 2 := by positivity
  have h3 : |a + σ2 - B ^ 2 / r ^ 2| ≤ |a| + σ2 + B ^ 2 / r ^ 2 := by
    rw [abs_le]; constructor <;> linarith [abs_nonneg a, neg_abs_le a, le_abs_self a]
  linarith

lemma SV_tim : TendstoInMeasure PP
    (fun (n : ℕ) (ω : ℕ → S) => SVg n (fun i : Fin n => X (ω i))) atTop (fun _ => s2 ν X) := by
  have hσ : 0 ≤ s2 ν X := s2_nonneg ν X
  let g : ℕ → (ℕ → S) → ℝ := fun n ω =>
    ((∑ i : Fin n, ((X (ω i) - mX ν X) ^ 2 - s2 ν X)) ^ 2 / √(n : ℝ) + √(n : ℝ) + s2 ν X +
      (∑ i : Fin n, (X (ω i) - mX ν X)) ^ 2 / n) / ((n : ℝ) - 1)
  have key := tim_of_L1 (P := PP) (fun n ω => SVg n (fun i : Fin n => X (ω i)) - s2 ν X) g
    (fun n => ((∫ s, ((X s - mX ν X) ^ 2 - s2 ν X) ^ 2 ∂ν + 1) * √(n : ℝ) + 2 * s2 ν X) / ((n : ℝ) - 1)) ?_ ?_ ?_
    (lim_aux (∫ s, ((X s - mX ν X) ^ 2 - s2 ν X) ^ 2 ∂ν + 1) (2 * s2 ν X)) ?_
  · rw [tendstoInMeasure_iff_norm] at key ⊢
    simpa using key
  · filter_upwards [eventually_ge_atTop 2] with n hn ω
    have hn0 : n ≠ 0 := by omega
    simp only [g]
    rw [SVg_eq n hn0 _ (mX ν X), Finset.sum_sub_distrib (f := fun i : Fin n => (X (ω i) - mX ν X) ^ 2)]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact SV_bound n hn _ _ (s2 ν X) hσ
  · intro n
    exact intF ν X hX C hC n (fun x => ((∑ i : Fin n, ((x i - mX ν X) ^ 2 - s2 ν X)) ^ 2 / √(n : ℝ) + √(n : ℝ) + s2 ν X +
      (∑ i : Fin n, (x i - mX ν X)) ^ 2 / n) / ((n : ℝ) - 1)) (by fun_prop)
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hn2 : (2:ℝ) ≤ n := by exact_mod_cast hn
    refine le_of_eq ?_
    simp only [g]
    have hb2 : ∀ s, |(X s - mX ν X) ^ 2 - s2 ν X| ≤ (C + |mX ν X|) ^ 2 + s2 ν X := by
      intro s
      have h1 := centered_bound ν X hX C hC s
      have h2 : (X s - mX ν X) ^ 2 ≤ (C + |mX ν X|) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg (X s - mX ν X)]
    have hmean2 : ∫ s, ((X s - mX ν X) ^ 2 - s2 ν X) ∂ν = 0 := by
      rw [integral_sub (intν ν X hX C hC (fun x => (x - mX ν X) ^ 2) (by fun_prop)) (integrable_const _)]
      simp [s2]
    have hI1 : Integrable (fun ω : ℕ → S => (∑ i : Fin n, ((X (ω i) - mX ν X) ^ 2 - s2 ν X)) ^ 2) PP :=
      intF ν X hX C hC n (fun x => (∑ i : Fin n, ((x i - mX ν X) ^ 2 - s2 ν X)) ^ 2) (by fun_prop)
    have hI2 : Integrable (fun ω : ℕ → S => (∑ i : Fin n, (X (ω i) - mX ν X)) ^ 2) PP :=
      intF ν X hX C hC n (fun x => (∑ i : Fin n, (x i - mX ν X)) ^ 2) (by fun_prop)
    rw [integral_div, integral_add, integral_add, integral_add, integral_div, integral_div,
      sq_sum ν (fun s => (X s - mX ν X) ^ 2 - s2 ν X) (by fun_prop) _ hb2 hmean2,
      sq_sum ν (fun s => X s - mX ν X) (by fun_prop) _ (centered_bound ν X hX C hC)
        (centered_mean ν X hX C hC) n]
    · simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
      change (n * _ / √(n : ℝ) + √(n : ℝ) + s2 ν X + n * s2 ν X / n) / ((n : ℝ) - 1) = _
      generalize (∫ s, ((X s - mX ν X) ^ 2 - s2 ν X) ^ 2 ∂ν) = V
      have hr : (n : ℝ) = (√(n : ℝ)) ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg n)).symm
      have hpos : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by linarith)
      generalize √(n : ℝ) = r at hr hpos ⊢
      rw [hr] at hn2 ⊢
      have : r ^ 2 - 1 ≠ 0 := by linarith
      field_simp
      ring
    all_goals first
      | exact integrable_const _
      | exact hI1.div_const _
      | exact hI2.div_const _
      | exact (hI1.div_const _).add (integrable_const _)
      | exact ((hI1.div_const _).add (integrable_const _)).add (integrable_const _)
  · intro n
    have h1 : Measurable (fun ω : ℕ → S => SVg n (fun i : Fin n => X (ω i))) :=
      (SVg_cont n).measurable.comp (by fun_prop)
    exact (h1.sub measurable_const).aestronglyMeasurable

lemma D_tid (hpos : 0 < s2 ν X) : TendstoInDistribution
    (fun (n : ℕ) (ω : ℕ → S) => (√(n : ℝ) * (SVg n (fun i : Fin n => X (ω i)) - s2 ν X)) /
      (√(SVg n (fun i : Fin n => X (ω i))) + √(s2 ν X)))
    atTop (fun y => y / (√(s2 ν X) + √(s2 ν X))) (fun _ => PP)
    (gaussianReal 0 (m4 ν X - s2 ν X ^ 2).toNNReal) := by
  have hσ : 0 < √(s2 ν X) := Real.sqrt_pos.2 hpos
  have hg : Continuous (fun p : ℝ × ℝ => p.1 / (√p.2 + √(s2 ν X))) := by
    refine Continuous.div (by fun_prop) (by fun_prop) fun p => ?_
    have := Real.sqrt_nonneg p.2
    linarith
  have := (W_tid ν X hX C hC).continuous_comp_prodMk_of_tendstoInMeasure_const hg
    (SV_tim ν X hX C hC) (fun n => ((SVg_cont n).measurable.comp (by fun_prop)).aemeasurable)
  exact this

omit [IsProbabilityMeasure ν] hX hC in
lemma laws [IsProbabilityMeasure ν] (F : ∀ n, (Fin n → S) → ℝ) (hF : ∀ n, Measurable (F n))
    (G : ℕ → (ℕ → S) → ℝ) (hFG : ∀ᶠ n in atTop, ∀ ω : ℕ → S, F n (fun i => ω i) = G n ω)
    (P' : Measure ℝ) [IsProbabilityMeasure P'] (Z : ℝ → ℝ)
    (h : TendstoInDistribution G atTop Z (fun _ => PP) P') :
    ∀ f : BoundedContinuousFunction ℝ ℝ, Tendsto
      (fun n => ∫ x, f x ∂((Measure.pi fun _ : Fin n => ν).map (F n))) atTop
      (𝓝 (∫ x, f x ∂(P'.map Z))) := by
  have := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 h.tendsto
  intro f
  refine (this f).congr' ?_
  filter_upwards [hFG] with n hn
  simp only [ProbabilityMeasure.coe_mk]
  rw [← map_restrict, Measure.map_map (hF n) (by fun_prop)]
  congr 2
  funext ω
  exact (hn ω).symm

end X7V

namespace QAlgorithms.Papers.Independent.Information100.P37

lemma X7V_gen_cont {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ) :
    Continuous (generated (conjSuperop U)) := by
  have h : ∀ p : ι → ℝ, generated (conjSuperop U) p = ∑ i, ∑ j, if i = j then 0 else
      Complex.normSq (∑ k, U i k * (p k : ℂ) * star (U j k)) := by
    intro p
    simp only [generated, coherence, conjSuperop, inputDensity, Matrix.mul_apply,
      Matrix.diagonal_apply, Matrix.conjTranspose_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    congr 2
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [Finset.sum_ite_eq', mul_ite]
  simp_rw [funext h]
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  split_ifs
  · exact continuous_const
  · exact Complex.continuous_normSq.comp (continuous_finset_sum _ fun k _ => by fun_prop)

instance X7V_probExp : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos

lemma X7V_exp_pos : ∀ᵐ x ∂(expMeasure 1), (0:ℝ) < x := by
  have hf : Measurable (gammaPDF 1 1) := (measurable_gammaPDFReal 1 1).ennreal_ofReal
  rw [expMeasure, gammaMeasure, ae_withDensity_iff hf]
  have hne : ∀ᵐ z ∂(volume : Measure ℝ), z ≠ 0 := by
    rw [ae_iff]; simp
  filter_upwards [hne] with x hx hpdf
  rcases lt_or_gt_of_ne hx with h | h
  · exact absurd (gammaPDF_of_neg h) hpdf
  · exact h

lemma X7V_pi_pos {ι : Type*} [Fintype ι] :
    ∀ᵐ z ∂(Measure.pi fun _ : ι => expMeasure 1), ∀ i, (0:ℝ) < z i :=
  eventually_all.2 fun _ => Measure.tendsto_eval_ae_ae.eventually X7V_exp_pos

lemma X7V_norm_meas {ι : Type*} [Fintype ι] :
    Measurable (normalizePopulation : (ι → ℝ) → (ι → ℝ)) := by
  unfold normalizePopulation
  refine Measurable.ite ?_ measurable_const ?_
  · exact measurableSet_eq_fun (by fun_prop) measurable_const
  · fun_prop

instance X7V_prob {ι : Type*} [Fintype ι] : IsProbabilityMeasure (simplexLaw ι) := by
  unfold simplexLaw
  exact Measure.isProbabilityMeasure_map X7V_norm_meas.aemeasurable

lemma X7V_ae_simplex {ι : Type*} [Fintype ι] :
    ∀ᵐ p ∂(simplexLaw ι), p ∈ Set.univ.pi (fun _ : ι => Set.Icc (0:ℝ) 1) := by
  unfold simplexLaw
  have hs : MeasurableSet {y : ι → ℝ | y ∈ Set.univ.pi (fun _ : ι => Set.Icc (0:ℝ) 1)} :=
    (isClosed_set_pi fun _ _ => isClosed_Icc).measurableSet
  refine (ae_map_iff X7V_norm_meas.aemeasurable hs).mpr ?_
  filter_upwards [X7V_pi_pos] with z hz
  intro i _
  have hcard : (1:ℝ) ≤ Fintype.card ι := by
    have := Fintype.card_pos_iff.mpr ⟨i⟩; exact_mod_cast this
  unfold normalizePopulation
  split_ifs with h0
  · exact ⟨by positivity, by rw [div_le_one (by linarith)]; exact hcard⟩
  · have hS : 0 < ∑ j, z j := Finset.sum_pos (fun j _ => hz j) ⟨i, Finset.mem_univ i⟩
    refine ⟨div_nonneg (hz i).le hS.le, (div_le_one hS).mpr ?_⟩
    exact Finset.single_le_sum (fun j _ => (hz j).le) (Finset.mem_univ i)

/-- A bounded measurable modification of a continuous function, equal to it a.e. under the simplex law. -/
lemma X7V_clip {ι : Type*} [Fintype ι] (G : (ι → ℝ) → ℝ) (hG : Continuous G) :
    ∃ X : (ι → ℝ) → ℝ, ∃ C : ℝ, Measurable X ∧ (∀ s, |X s| ≤ C) ∧ X =ᵐ[simplexLaw ι] G := by
  obtain ⟨C0, hC0⟩ := (isCompact_univ_pi fun _ : ι =>
    isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn hG.continuousOn
  set C1 := max C0 0
  refine ⟨fun s => max (-C1) (min C1 (G s)), C1, by fun_prop, fun s => ?_, ?_⟩
  · have : 0 ≤ C1 := le_max_right _ _
    rw [abs_le]; constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left _ _)
  · filter_upwards [X7V_ae_simplex] with p hp
    have h := hC0 p hp
    rw [Real.norm_eq_abs, abs_le] at h
    have h1 : G p ≤ C1 := h.2.trans (le_max_left _ _)
    have h2 : -C1 ≤ G p := le_trans (neg_le_neg (le_max_left _ _)) h.1
    show max (-C1) (min C1 (G p)) = G p
    rw [min_eq_right h1, max_eq_right h2]

end QAlgorithms.Papers.Independent.Information100.P37

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P37 MeasureTheory ProbabilityTheory Filter in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    let E := conjSuperop U
    let v := fourthCentral E - cgpd E ^ 4
    (∀ N : ℕ, 2 ≤ N → (∫ p, sampleVariance E p ∂sampleLaw ι N) = cgpd E ^ 2) ∧
    0 ≤ v ∧
    LawsConverge (fun N => Measure.map (fun p : Fin N → (ι → ℝ) =>
      Real.sqrt (N : ℝ) * (sampleVariance E p - cgpd E ^ 2)) (sampleLaw ι N))
      (gaussianReal 0 (Real.toNNReal v)) ∧
    (0 < cgpd E → LawsConverge (fun N => Measure.map (fun p : Fin N → (ι → ℝ) =>
      Real.sqrt (N : ℝ) * (Real.sqrt (sampleVariance E p) - cgpd E)) (sampleLaw ι N))
      (gaussianReal 0 (Real.toNNReal (v / (4 * cgpd E ^ 2))))) := by
  intro E v
  set G := generated E with hGdef
  have hGc : Continuous G := X7V_gen_cont U
  obtain ⟨X, C, hXm, hXC, hae⟩ := X7V_clip G hGc
  -- moments agree
  have hm : X7V.mX (simplexLaw ι) X = cgp E := by
    show ∫ s, X s ∂(simplexLaw ι) = ∫ p, generated E p ^ 1 ∂(simplexLaw ι)
    simp_rw [pow_one]
    exact integral_congr_ae hae
  have hs2 : X7V.s2 (simplexLaw ι) X = coherenceVariance E := by
    show ∫ s, (X s - X7V.mX (simplexLaw ι) X) ^ 2 ∂(simplexLaw ι) = ∫ p, (generated E p - cgp E) ^ 2 ∂(simplexLaw ι)
    rw [hm]
    exact integral_congr_ae (hae.mono fun s hs => by simp only [hs, G])
  have hm4 : X7V.m4 (simplexLaw ι) X = fourthCentral E := by
    show ∫ s, (X s - X7V.mX (simplexLaw ι) X) ^ 4 ∂(simplexLaw ι) = ∫ p, (generated E p - cgp E) ^ 4 ∂(simplexLaw ι)
    rw [hm]
    exact integral_congr_ae (hae.mono fun s hs => by simp only [hs, G])
  have hσ : 0 ≤ X7V.s2 (simplexLaw ι) X := X7V.s2_nonneg (simplexLaw ι) X
  have hcg : cgpd E = √(X7V.s2 (simplexLaw ι) X) := by rw [hs2]; rfl
  have hcg2 : cgpd E ^ 2 = X7V.s2 (simplexLaw ι) X := by rw [hcg, Real.sq_sqrt hσ]
  have hv : v = X7V.m4 (simplexLaw ι) X - X7V.s2 (simplexLaw ι) X ^ 2 := by
    simp only [v, hm4, show cgpd E ^ 4 = (cgpd E ^ 2) ^ 2 by ring, hcg2]
  -- sample variance is SVg of the sample, and a.e. equal to the clipped version
  have hSV : ∀ N (p : Fin N → (ι → ℝ)), sampleVariance E p = X7V.SVg N (fun i => G (p i)) :=
    fun N p => rfl
  have haeN : ∀ N : ℕ, ∀ᵐ p ∂(sampleLaw ι N), (fun i => G (p i)) = (fun i => X (p i)) := by
    intro N
    have : ∀ᵐ p ∂(Measure.pi fun _ : Fin N => (simplexLaw ι)), ∀ i, X (p i) = G (p i) :=
      eventually_all.2 fun i => (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin N => simplexLaw ι)
        (i := i)).eventually hae
    filter_upwards [this] with p hp
    funext i; exact (hp i).symm
  have hlaw : sampleLaw ι = fun N => Measure.pi fun _ : Fin N => (simplexLaw ι) := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro N hN
    rw [hcg2]
    have h1 : (∫ p, sampleVariance E p ∂sampleLaw ι N) =
        ∫ p, X7V.SVg N (fun i => X (p i)) ∂(Measure.pi fun _ : Fin N => (simplexLaw ι)) := by
      refine integral_congr_ae ((haeN N).mono fun p hp => ?_)
      simp only [hSV, hp]
    rw [h1, ← X7V.map_restrict (simplexLaw ι) N, integral_map (φ := fun (ω : ℕ → ι → ℝ) (i : Fin N) => ω i)
      (f := fun p : Fin N → ι → ℝ => X7V.SVg N (fun i => X (p i)))
      (measurable_pi_lambda _ fun i => measurable_pi_apply _).aemeasurable
      ((X7V.SVg_cont N).measurable.comp (by fun_prop)).aestronglyMeasurable]
    exact X7V.mean_SV (simplexLaw ι) X hXm C hXC N hN
  · rw [hv]; exact X7V.v_nonneg (simplexLaw ι) X hXm C hXC
  · intro f
    have hmap : ∀ N, Measure.map (fun p : Fin N → (ι → ℝ) =>
        Real.sqrt (N : ℝ) * (sampleVariance E p - cgpd E ^ 2)) (sampleLaw ι N) =
        (Measure.pi fun _ : Fin N => (simplexLaw ι)).map
          (fun p => √(N : ℝ) * (X7V.SVg N (fun i => X (p i)) - X7V.s2 (simplexLaw ι) X)) := by
      intro N
      refine Measure.map_congr ((haeN N).mono fun p hp => ?_)
      simp only [hSV, hp, hcg2]
    simp_rw [hmap]
    have := X7V.laws (simplexLaw ι) (fun N p => √(N : ℝ) * (X7V.SVg N (fun i => X (p i)) - X7V.s2 (simplexLaw ι) X))
      (fun N => measurable_const.mul
        (((X7V.SVg_cont N).measurable.comp (by fun_prop)).sub measurable_const))
      _ (Eventually.of_forall fun n ω => rfl) _ id (X7V.W_tid (simplexLaw ι) X hXm C hXC) f
    rw [Measure.map_id, ← hv] at this
    exact this
  · intro hpos f
    have hs2pos : 0 < X7V.s2 (simplexLaw ι) X := by rw [hcg] at hpos; exact Real.sqrt_pos.1 hpos
    have hmap : ∀ N, Measure.map (fun p : Fin N → (ι → ℝ) =>
        Real.sqrt (N : ℝ) * (Real.sqrt (sampleVariance E p) - cgpd E)) (sampleLaw ι N) =
        (Measure.pi fun _ : Fin N => (simplexLaw ι)).map
          (fun p => √(N : ℝ) * (√(X7V.SVg N (fun i => X (p i))) - √(X7V.s2 (simplexLaw ι) X))) := by
      intro N
      refine Measure.map_congr ((haeN N).mono fun p hp => ?_)
      simp only [hSV, hp, hcg]
    simp_rw [hmap]
    have := X7V.laws (simplexLaw ι) (fun N p => √(N : ℝ) * (√(X7V.SVg N (fun i => X (p i))) - √(X7V.s2 (simplexLaw ι) X)))
      (fun N => measurable_const.mul
        ((((X7V.SVg_cont N).measurable.comp (by fun_prop))).sqrt.sub measurable_const))
      _ ?_ _ _ (X7V.D_tid (simplexLaw ι) X hXm C hXC hs2pos) f
    · convert this using 3
      rw [gaussianReal_map_div_const]
      congr 1
      · simp
      · ext
        simp only [NNReal.coe_div, NNReal.coe_mk, Real.coe_toNNReal', hv]
        have h4 : 0 ≤ X7V.m4 (simplexLaw ι) X - X7V.s2 (simplexLaw ι) X ^ 2 := X7V.v_nonneg (simplexLaw ι) X hXm C hXC
        rw [max_eq_left h4, max_eq_left (div_nonneg h4 (by positivity)), hcg2]
        rw [show (√(X7V.s2 (simplexLaw ι) X) + √(X7V.s2 (simplexLaw ι) X)) ^ 2 = 4 * (√(X7V.s2 (simplexLaw ι) X)) ^ 2 by ring,
          Real.sq_sqrt hσ]
    · refine Eventually.of_forall fun n ω => ?_
      have hS := X7V.SVg_nonneg n (fun i : Fin n => X (ω i))
      have hq : 0 < √(X7V.s2 (simplexLaw ι) X) := Real.sqrt_pos.2 hs2pos
      have hden : 0 < √(X7V.SVg n (fun i : Fin n => X (ω i))) + √(X7V.s2 (simplexLaw ι) X) := by
        have := Real.sqrt_nonneg (X7V.SVg n (fun i : Fin n => X (ω i))); linarith
      field_simp
      have e1 := Real.sq_sqrt hS
      have e2 := Real.sq_sqrt hσ
      linear_combination (√(n : ℝ)) * (e1 - e2)
