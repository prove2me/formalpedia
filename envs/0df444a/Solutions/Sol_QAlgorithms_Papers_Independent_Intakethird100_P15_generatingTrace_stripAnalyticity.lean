-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P15.generatingTrace_stripAnalyticity
-- status  : ACCEPTED   (prove)
-- author  : @Yivy Yu
-- created : 2026-11-17T02:08:33.105164+00:00
-- url     : https://prove2.me/submissions/2dc5f5b5-beb8-4611-bd59-d8b2c7029e24

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P15

open MeasureTheory Filter
open QAlgorithms.Papers.Independent.Intakethird100.P15
open QAlgorithms.Papers.Independent.Information100.P37 (transition)
open scoped ENNReal Topology

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι : Type v} {Ω : Type w} [MeasurableSpace Ω]

omit [CompleteSpace E] in
private theorem born_column (b : HilbertBasis ι ℂ E) (U : E ≃ₗᵢ[ℂ] E) (a : ι) :
    HasSum (fun g => Complex.normSq (inner ℂ (b g) (U (b a)))) 1 := by
  let v := U (b a)
  have hterm (g : ι) : (inner ℂ v (b g) * inner ℂ (b g) v).re =
      Complex.normSq (inner ℂ (b g) v) := by
    rw [mul_comm, ← inner_conj_symm (𝕜 := ℂ) v (b g), Complex.mul_conj, Complex.ofReal_re]
  have hnorm : ‖v‖ = 1 := by
    rw [show ‖v‖ = ‖b a‖ from U.norm_map _, b.orthonormal.norm_eq_one a]
  have hre : (inner ℂ v v).re = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hnorm]
    simp
  simpa only [v, hterm, hre] using Complex.hasSum_re (b.hasSum_inner_mul_inner v v)

omit [CompleteSpace E] in
private theorem born_row (b : HilbertBasis ι ℂ E) (U : E ≃ₗᵢ[ℂ] E) (g : ι) :
    HasSum (fun a => Complex.normSq (inner ℂ (b g) (U (b a)))) 1 := by
  let v := U.symm (b g)
  have hterm (a : ι) :
      (inner ℂ v (b a) * inner ℂ (b a) v).re =
        Complex.normSq (inner ℂ (b g) (U (b a))) := by
    have hinner : inner ℂ (b g) (U (b a)) = inner ℂ v (b a) := by
      simpa only [v, U.apply_symm_apply] using U.inner_map_map v (b a)
    rw [hinner, ← inner_conj_symm (𝕜 := ℂ) (b a) v, Complex.mul_conj, Complex.ofReal_re]
  have hnorm : ‖v‖ = 1 := by
    rw [show ‖v‖ = ‖b g‖ from U.symm.norm_map _, b.orthonormal.norm_eq_one g]
  have hre : (inner ℂ v v).re = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hnorm]
    simp
  simpa only [hterm, hre] using Complex.hasSum_re (b.hasSum_inner_mul_inner v v)

private theorem weighted_transition {T : ι → ι → ℝ}
    (hn : ∀ a g, 0 ≤ T a g) (hT : ∀ a, HasSum (T a) 1)
    {w : ι → ℝ} (hw : ∀ a, 0 ≤ w a) (hs : Summable w) :
    HasSum (fun p : ι × ι => w p.1 * T p.1 p.2) (∑' a, w a) := by
  have hline (a : ι) : HasSum (fun g => w a * T a g) (w a) := by
    simpa only [mul_one] using (hT a).mul_left (w a)
  have heq : (fun a => ∑' g, w a * T a g) = w :=
    funext fun a => (hline a).tsum_eq
  have hsum : Summable (fun p : ι × ι => w p.1 * T p.1 p.2) :=
    (summable_prod_of_nonneg (fun p => mul_nonneg (hw p.1) (hn p.1 p.2))).2
      ⟨fun a => (hline a).summable, heq.symm ▸ hs⟩
  convert hsum.hasSum using 1
  rw [hsum.tsum_prod' (fun a => (hline a).summable), heq]

private theorem trace_term_norm (b : HilbertBasis ι ℂ E) (U : E ≃ₗᵢ[ℂ] E)
    (energy : ι → ℝ) (beta : ℝ) (z : ℂ) (p : ι × ι) :
    ‖qTerm b U energy beta z p‖ =
      Complex.normSq (inner ℂ (b p.2) (U (b p.1))) *
        Real.exp (z.re * (energy p.2 - energy p.1) - beta * energy p.1) := by
  unfold qTerm transition
  simp only [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _),
    abs_of_pos (Real.exp_pos _)]
  rw [show z.re * (energy p.2 - energy p.1) - beta * energy p.1 =
    z.re * (energy p.2 - energy p.1) + (-beta * energy p.1) by ring, Real.exp_add]
  ring

theorem solution [Countable ι] [Nonempty ι]
    (b : HilbertBasis ι ℂ E) (d : CyclicDrive (Ω := Ω) b)
    (energy : ι → ℝ) (beta : ℝ) (hbeta : 0 < beta)
    (henergy : IsInitialEnergyBasis b d energy) (hheat : HasFiniteHeatTraces energy) :
    DifferentiableOn ℂ (generatingTrace b d.evolution energy beta)
      {z : ℂ | -beta < z.re ∧ z.re < 0} ∧
    ContinuousOn (generatingTrace b d.evolution energy beta)
      {z : ℂ | -beta ≤ z.re ∧ z.re ≤ 0} ∧
    (∀ z : ℂ, -beta ≤ z.re → z.re ≤ 0 → Summable (qTerm b d.evolution energy beta z)) ∧
    (∀ z : ℂ, -beta < z.re → z.re < 0 →
      ‖generatingTrace b d.evolution energy beta z‖ ^ 2 ≤
        2 * heatTrace energy (2 * (z.re + beta)) * heatTrace energy (-2 * z.re)) := by
  let U := d.evolution
  let T (p : ι × ι) := Complex.normSq (inner ℂ (b p.2) (U (b p.1)))
  let leftWeight (t : ℝ) (p : ι × ι) := T p * Real.exp (-t * energy p.1)
  let rightWeight (t : ℝ) (p : ι × ι) := T p * Real.exp (-t * energy p.2)
  have hT (p : ι × ι) : 0 ≤ T p := Complex.normSq_nonneg _
  have hleft (t : ℝ) (ht : 0 < t) : HasSum (leftWeight t) (heatTrace energy t) := by
    simpa only [leftWeight, T, heatTrace, mul_comm] using
      (weighted_transition
        (T := fun a g => Complex.normSq (inner ℂ (b g) (U (b a))))
        (fun _ _ => Complex.normSq_nonneg _) (born_column b U)
        (fun _ => (Real.exp_pos _).le) (hheat t ht))
  have hright (t : ℝ) (ht : 0 < t) : HasSum (rightWeight t) (heatTrace energy t) := by
    have hrow := weighted_transition
      (T := fun g a => Complex.normSq (inner ℂ (b g) (U (b a))))
      (fun _ _ => Complex.normSq_nonneg _) (born_row b U)
      (fun _ => (Real.exp_pos _).le) (hheat t ht)
    have hswap := (Equiv.prodComm ι ι).hasSum_iff.mpr hrow
    change HasSum (fun p : ι × ι => Real.exp (-t * energy p.2) *
      Complex.normSq (inner ℂ (b p.2) (U (b p.1)))) _ at hswap
    simpa only [rightWeight, T, heatTrace, mul_comm] using hswap
  let majorant (p : ι × ι) := leftWeight beta p + rightWeight beta p
  have hmajorant : Summable majorant :=
    (hleft beta hbeta).summable.add (hright beta hbeta).summable
  have hbound (p : ι × ι) (z : ℂ) (hlo : -beta ≤ z.re) (hhi : z.re ≤ 0) :
      ‖qTerm b U energy beta z p‖ ≤ majorant p := by
    rw [trace_term_norm]
    change T p * Real.exp (z.re * (energy p.2 - energy p.1) - beta * energy p.1) ≤ _
    rcases le_total 0 (energy p.2 - energy p.1) with hgap | hgap
    · have hm := mul_nonpos_of_nonpos_of_nonneg hhi hgap
      calc
        _ ≤ leftWeight beta p := mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (by linarith)) (hT p)
        _ ≤ _ := le_add_of_nonneg_right (mul_nonneg (hT p) (Real.exp_pos _).le)
    · have hm := mul_le_mul_of_nonpos_right hlo hgap
      calc
        _ ≤ rightWeight beta p := mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (by nlinarith only [hm])) (hT p)
        _ ≤ _ := le_add_of_nonneg_left (mul_nonneg (hT p) (Real.exp_pos _).le)
  have hf (p : ι × ι) : Differentiable ℂ (fun z => qTerm b U energy beta z p) := by
    unfold qTerm
    fun_prop
  have hopen : IsOpen {z : ℂ | -beta < z.re ∧ z.re < 0} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Complex.differentiableOn_tsum_of_summable_norm hmajorant
      (fun p => (hf p).differentiableOn) hopen
      (fun p z hz => hbound p z hz.1.le hz.2.le)
  · exact continuousOn_tsum (fun p => (hf p).continuous.continuousOn)
      hmajorant (fun p z hz => hbound p z hz.1 hz.2)
  · intro z hlo hhi
    exact hmajorant.of_norm_bounded (fun p => hbound p z hlo hhi)
  · intro z hlo hhi
    let f (p : ι × ι) := ‖qTerm b U energy beta z p‖
    let A := leftWeight (2 * (z.re + beta))
    let G := rightWeight (-2 * z.re)
    have hA := hleft (2 * (z.re + beta)) (by linarith)
    have hG := hright (-2 * z.re) (by linarith)
    have hAn (p : ι × ι) : 0 ≤ A p := mul_nonneg (hT p) (Real.exp_pos _).le
    have hGn (p : ι × ι) : 0 ≤ G p := mul_nonneg (hT p) (Real.exp_pos _).le
    have hterm (p : ι × ι) : f p ^ 2 = A p * G p := by
      dsimp [f]
      rw [trace_term_norm]
      change (T p * Real.exp _) ^ 2 =
        (T p * Real.exp (-(2 * (z.re + beta)) * energy p.1)) *
          (T p * Real.exp (-(-2 * z.re) * energy p.2))
      rw [mul_pow, pow_two (Real.exp _), ← Real.exp_add, mul_mul_mul_comm, ← Real.exp_add]
      congr 2 <;> ring
    have hfs : Summable f := hmajorant.of_nonneg_of_le (fun p => norm_nonneg _)
      (fun p => hbound p z hlo.le hhi.le)
    have hfs_lim : Tendsto (fun s : Finset (ι × ι) => (∑ p ∈ s, f p) ^ 2)
        atTop (𝓝 ((∑' p, f p) ^ 2)) := hfs.hasSum.pow 2
    have hAG_lim : Tendsto (fun s : Finset (ι × ι) => (∑ p ∈ s, A p) * (∑ p ∈ s, G p))
        atTop (𝓝 (heatTrace energy (2 * (z.re + beta)) * heatTrace energy (-2 * z.re))) :=
      Tendsto.mul (show Tendsto _ atTop _ from hA) (show Tendsto _ atTop _ from hG)
    have hcs := le_of_tendsto_of_tendsto' hfs_lim hAG_lim (fun s =>
      Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s (fun p _ => hAn p) (fun p _ => hGn p)
        (fun p _ => (hterm p).le))
    have hnorm := norm_tsum_le_tsum_norm hfs
    change ‖∑' p, qTerm b U energy beta z p‖ ^ 2 ≤ _
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    have hnonneg (t : ℝ) : 0 ≤ heatTrace energy t :=
      tsum_nonneg fun _ => (Real.exp_pos _).le
    have hprod := mul_nonneg (hnonneg (2 * (z.re + beta))) (hnonneg (-2 * z.re))
    exact hsq.trans (hcs.trans (by linarith only [hprod]))
