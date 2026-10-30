-- Prove2me | solution 1 for TaoBR.opNorm_le_of_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T02:52:25.354747+00:00
-- url     : https://prove2.me/submissions/52728781-67b4-4190-aae5-3ac54acee93f

import Mathlib
import Definitions.Def_TaoBR

open scoped ENNReal FourierTransform ContDiff
open MeasureTheory Metric Function

namespace TaoBR
namespace OpNormBP

lemma kernelOp_congr_ae {n : ℕ} (K : E n → E n → ℂ) {f g : E n → ℂ} (h : f =ᵐ[volume] g) :
    kernelOp K f = kernelOp K g := by
  funext x
  unfold kernelOp
  exact integral_congr_ae (h.mono fun y hy => by simp [hy])

lemma eLpNorm_kernelOp_le {n : ℕ} (p q : ℝ≥0∞) (hp : p ≠ 0) (K : E n → E n → ℂ) (g : E n → ℂ)
    (hg : MemLp g p volume) :
    eLpNorm (kernelOp K g) q volume ≤ opNorm p q (kernelOp K) * eLpNorm g p volume := by
  by_cases h0 : eLpNorm g p volume = 0
  · have hg0 : g =ᵐ[volume] 0 := (eLpNorm_eq_zero_iff hg.1 hp).1 h0
    rw [kernelOp_congr_ae K hg0]
    have : kernelOp K (0 : E n → ℂ) = 0 := by
      funext x; simp [kernelOp]
    simp [this]
  have ht : eLpNorm g p volume ≠ ⊤ := hg.eLpNorm_lt_top.ne
  rw [← ENNReal.div_le_iff h0 ht]
  apply le_sInf
  intro C hC
  exact (ENNReal.div_le_iff h0 ht).2 (hC g hg)

lemma integrable_kernel_mul {n : ℕ} (p : ℝ≥0∞) (hp : 1 ≤ p) (K : E n → E n → ℂ)
    (Y : Set (E n)) (hY : IsCompact Y) (M : ℝ) (hKm : Measurable (uncurry K))
    (hKb : ∀ x y, ‖K x y‖ ≤ M) (hKs : ∀ x y, K x y ≠ 0 → y ∈ Y)
    (f : E n → ℂ) (hf : MemLp f p volume) (x : E n) :
    Integrable (fun y => K x y * f y) := by
  have hfY : IntegrableOn f Y volume := (hf.locallyIntegrable hp).integrableOn_isCompact hY
  have heq : (fun y => K x y * f y) = fun y => K x y * Y.indicator f y := by
    funext y
    by_cases hy : y ∈ Y
    · simp [hy]
    · have : K x y = 0 := by
        by_contra h; exact hy (hKs x y h)
      simp [this]
  rw [heq]
  refine (hfY.integrable_indicator hY.measurableSet).bdd_mul (c := M) ?_ ?_
  · exact (hKm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun y => hKb x y

lemma eLpNorm_le_tsum {n : ℕ} {ι : Type*} [Countable ι] (q : ℝ≥0∞) (hq : 1 ≤ q)
    (h : ι → E n → ℂ) (hm : ∀ k, AEStronglyMeasurable (h k) volume) (F : E n → ℂ)
    (hF : ∀ x, HasSum (fun k => h k x) (F x)) :
    eLpNorm F q volume ≤ ∑' k, eLpNorm (h k) q volume := by
  obtain ⟨u, hu⟩ := Filter.exists_seq_tendsto (Filter.atTop : Filter (Finset ι))
  have hlim : ∀ᵐ x ∂(volume : Measure (E n)),
      Filter.Tendsto (fun m => (∑ k ∈ u m, h k) x) Filter.atTop (nhds (F x)) := by
    refine Filter.Eventually.of_forall fun x => ?_
    have := (hF x).comp hu
    simpa [Finset.sum_apply, Function.comp_def] using this
  refine (Lp.eLpNorm_lim_le_liminf_eLpNorm (fun m => ?_) F hlim).trans ?_
  · exact Finset.aestronglyMeasurable_sum _ fun k _ => hm k
  refine Filter.liminf_le_of_le (by isBoundedDefault) fun b hb => ?_
  obtain ⟨m, hm'⟩ := hb.exists
  refine hm'.trans ((eLpNorm_sum_le (fun k _ => hm k) hq).trans ?_)
  exact ENNReal.sum_le_tsum _

lemma measurable_kernelOp {n : ℕ} (K : E n → E n → ℂ) (hKm : Measurable (uncurry K))
    (g : E n → ℂ) (hg : Measurable g) : AEStronglyMeasurable (kernelOp K g) volume := by
  have : StronglyMeasurable (uncurry fun x y => K x y * g y) :=
    (hKm.mul (hg.comp measurable_snd)).stronglyMeasurable
  exact (this.integral_prod_right (ν := volume)).aestronglyMeasurable

lemma opNorm_le_of_expansion {n : ℕ} {ι : Type*} [Countable ι] (p q : ℝ≥0∞) (hp : 1 ≤ p)
    (hq : 1 ≤ q) (K β : E n → E n → ℂ) (Y : Set (E n)) (hY : IsCompact Y) (M : ℝ)
    (hKm : Measurable (uncurry K)) (hKb : ∀ x y, ‖K x y‖ ≤ M)
    (hKs : ∀ x y, K x y ≠ 0 → y ∈ Y)
    (e c : ι → E n → ℂ) (a : ι → ℝ) (ha : Summable a)
    (he : ∀ k, Measurable (e k)) (he1 : ∀ k x, ‖e k x‖ ≤ 1)
    (hc : ∀ k, Measurable (c k)) (hca : ∀ k y, ‖c k y‖ ≤ a k)
    (hβ : ∀ x y, K x y ≠ 0 → HasSum (fun k => e k x * c k y) (β x y)) :
    opNorm p q (kernelOp fun x y => K x y * β x y) ≤
      ENNReal.ofReal (∑' k, a k) * opNorm p q (kernelOp K) := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  have ha0 : ∀ k, 0 ≤ a k := fun k => (norm_nonneg _).trans (hca k 0)
  apply sInf_le
  intro f hf
  obtain ⟨f', hf'm, hff'⟩ := hf.1
  have hf' : MemLp f' p volume := hf.ae_eq hff'
  rw [kernelOp_congr_ae _ hff', eLpNorm_congr_ae hff']
  have hf'meas : Measurable f' := hf'm.measurable
  set A := opNorm p q (kernelOp K)
  have hcf : ∀ k, MemLp (fun y => c k y * f' y) p volume := fun k =>
    hf'.of_le_mul (c := a k) ((hc k).mul hf'meas).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hca k y) (norm_nonneg _))
  have hcfn : ∀ k, eLpNorm (fun y => c k y * f' y) p volume ≤
      ENNReal.ofReal (a k) * eLpNorm f' p volume := fun k => by
    have := eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul (c := ⟨a k, ha0 k⟩)
      (f := fun y => c k y * f' y) (g := f') (μ := volume)
      (Filter.Eventually.of_forall fun y => by
        rw [nnnorm_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hca k y) (by positivity)) p
    refine this.trans (le_of_eq ?_)
    rw [ENNReal.ofReal, Real.toNNReal_of_nonneg (ha0 k)]; rfl
  set h : ι → E n → ℂ := fun k x => e k x * kernelOp K (fun y => c k y * f' y) x with hh
  have hsum : ∀ x, HasSum (fun k => h k x) (kernelOp (fun x y => K x y * β x y) f' x) := by
    intro x
    set F : ι → E n → ℂ := fun k y => e k x * (K x y * (c k y * f' y)) with hF
    have hFint : ∀ k, Integrable (F k) := fun k =>
      (integrable_kernel_mul p hp K Y hY M hKm hKb hKs _ (hcf k) x).const_mul (e k x)
    have hKf : Integrable (fun y => K x y * f' y) :=
      integrable_kernel_mul p hp K Y hY M hKm hKb hKs _ hf' x
    have hFle : ∀ k y, ‖F k y‖ ≤ a k * ‖K x y * f' y‖ := fun k y => by
      simp only [hF, norm_mul]
      have h1 := he1 k x
      have h2 := hca k y
      have : ‖e k x‖ * (‖K x y‖ * (‖c k y‖ * ‖f' y‖)) ≤ 1 * (‖K x y‖ * (a k * ‖f' y‖)) := by
        gcongr
      nlinarith [norm_nonneg (K x y), norm_nonneg (f' y)]
    have hFsum : Summable fun k => ∫ y, ‖F k y‖ := by
      refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun y => norm_nonneg _)
        (fun k => ?_) (ha.mul_right (∫ y, ‖K x y * f' y‖))
      rw [← integral_const_mul]
      exact integral_mono (hFint k).norm (hKf.norm.const_mul _) (fun y => hFle k y)
    have hpt : ∀ y, HasSum (fun k => F k y) (K x y * β x y * f' y) := by
      intro y
      by_cases hK0 : K x y = 0
      · simp [hF, hK0]
      · have := ((hβ x y hK0).mul_left (K x y)).mul_right (f' y)
        have hfun : (fun k => F k y) = fun k => K x y * (e k x * c k y) * f' y := by
          funext k; simp only [hF]; ring
        rw [hfun]; exact this
    have heqk : ∀ k, ∫ y, F k y = h k x := fun k => by
      simp only [hF, hh, kernelOp]; rw [integral_const_mul]
    have hs : Summable fun k => ∫ y, F k y :=
      Summable.of_norm_bounded hFsum fun k => norm_integral_le_integral_norm _
    have htsum := integral_tsum_of_summable_integral_norm hFint hFsum
    have : ∑' k, ∫ y, F k y = kernelOp (fun x y => K x y * β x y) f' x := by
      rw [htsum]; simp only [kernelOp]
      exact integral_congr_ae (Filter.Eventually.of_forall fun y => (hpt y).tsum_eq)
    rw [← this]
    simp_rw [← heqk]
    exact hs.hasSum
  have hhm : ∀ k, AEStronglyMeasurable (h k) volume := fun k =>
    (he k).aestronglyMeasurable.mul
      (measurable_kernelOp K hKm _ ((hc k).mul hf'meas))
  calc eLpNorm (kernelOp (fun x y => K x y * β x y) f') q volume
      ≤ ∑' k, eLpNorm (h k) q volume := eLpNorm_le_tsum q hq h hhm _ hsum
    _ ≤ ∑' k, A * (ENNReal.ofReal (a k) * eLpNorm f' p volume) := by
        refine ENNReal.tsum_le_tsum fun k => ?_
        calc eLpNorm (h k) q volume
            ≤ eLpNorm (kernelOp K (fun y => c k y * f' y)) q volume := by
              refine eLpNorm_mono fun x => ?_
              simp only [hh, norm_mul]
              have := he1 k x
              nlinarith [norm_nonneg (kernelOp K (fun y => c k y * f' y) x),
                norm_nonneg (e k x)]
          _ ≤ A * eLpNorm (fun y => c k y * f' y) p volume :=
              eLpNorm_kernelOp_le p q hp0 K _ (hcf k)
          _ ≤ A * (ENNReal.ofReal (a k) * eLpNorm f' p volume) := by gcongr; exact hcfn k
    _ = ENNReal.ofReal (∑' k, a k) * A * eLpNorm f' p volume := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right,
          ENNReal.ofReal_tsum_of_nonneg ha0 ha]
        ring


/-! ## Part 2 -/

noncomputable def freq (n : ℕ) (L : ℝ) (k : Fin n → ℤ) : E n :=
  L⁻¹ • WithLp.toLp 2 (fun i => (k i : ℝ))

noncomputable def expo (n : ℕ) (L : ℝ) (k : Fin n → ℤ) (x : E n) : ℂ :=
  (Real.fourierChar (inner ℝ x (freq n L k)) : ℂ)

lemma norm_expo (n : ℕ) (L : ℝ) (k : Fin n → ℤ) (x : E n) : ‖expo n L k x‖ = 1 := by
  simp [expo, Circle.norm_coe]

lemma continuous_expo (n : ℕ) (L : ℝ) (k : Fin n → ℤ) : Continuous (expo n L k) := by
  unfold expo
  fun_prop

lemma abs_apply_le (n : ℕ) (w : E n) (i : Fin n) : |w i| ≤ ‖w‖ := by
  have := PiLp.norm_apply_le w i
  simpa [Real.norm_eq_abs] using this

lemma summable_int_inv : Summable (fun j : ℤ => ((1 + |(j : ℝ)|) ^ 2)⁻¹) := by
  have h := (Real.summable_one_div_int_pow (p := 2)).2 (by norm_num)
  refine Summable.of_norm_bounded_eventually h ?_
  have : {j : ℤ | ¬ ‖((1 + |(j : ℝ)|) ^ 2)⁻¹‖ ≤ 1 / (j : ℝ) ^ 2} ⊆ {0} := by
    intro j hj
    by_contra h0
    apply hj
    have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast h0
    have hpos : 0 < (j : ℝ) ^ 2 := by positivity
    rw [Real.norm_of_nonneg (by positivity), one_div]
    apply inv_anti₀ hpos
    rw [← sq_abs (j : ℝ)]
    nlinarith [abs_nonneg (j : ℝ)]
  exact Set.Finite.subset (Set.finite_singleton 0) this

lemma summable_prod_inv (n : ℕ) :
    Summable (fun k : Fin n → ℤ => ∏ i, ((1 + |(k i : ℝ)|) ^ 2)⁻¹) := by
  set f : ℤ → ℝ := fun j => ((1 + |(j : ℝ)|) ^ 2)⁻¹ with hf
  have hf0 : ∀ j, 0 ≤ f j := fun j => by positivity
  refine summable_of_sum_le (c := (∑' j, f j) ^ n) (fun k => Finset.prod_nonneg fun i _ => hf0 _)
    fun s => ?_
  calc ∑ k ∈ s, ∏ i, f (k i)
      ≤ ∑ k ∈ Fintype.piFinset (fun i => s.image (fun k => k i)), ∏ i, f (k i) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ =>
          Finset.prod_nonneg fun i _ => hf0 _
        intro k hk
        rw [Fintype.mem_piFinset]
        intro i
        exact Finset.mem_image.2 ⟨k, hk, rfl⟩
    _ = ∏ i, ∑ j ∈ s.image (fun k => k i), f j := (Finset.prod_univ_sum _ _).symm
    _ ≤ ∏ _i : Fin n, ∑' j, f j := by
        refine Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun j _ => hf0 j) fun i _ => ?_
        exact summable_int_inv.sum_le_tsum _ fun j _ => hf0 j
    _ = (∑' j, f j) ^ n := by simp

lemma prod_le_freq (n : ℕ) (L : ℝ) (hL : 1 ≤ L) (k : Fin n → ℤ) :
    ∏ i, (1 + |(k i : ℝ)|) ^ 2 ≤ L ^ (2 * n) * (1 + ‖freq n L k‖) ^ (2 * n) := by
  have hL0 : 0 < L := by linarith
  have hi : ∀ i, (1 + |(k i : ℝ)|) ^ 2 ≤ (L * (1 + ‖freq n L k‖)) ^ 2 := by
    intro i
    have h1 := abs_apply_le n (freq n L k) i
    have h2 : freq n L k i = L⁻¹ * (k i : ℝ) := by simp [freq]
    rw [h2, abs_mul, abs_inv, abs_of_pos hL0] at h1
    have h3 : |(k i : ℝ)| ≤ L * ‖freq n L k‖ := by
      rw [inv_mul_le_iff₀ hL0] at h1; exact h1
    gcongr
    nlinarith
  calc ∏ i, (1 + |(k i : ℝ)|) ^ 2 ≤ ∏ _i : Fin n, (L * (1 + ‖freq n L k‖)) ^ 2 :=
        Finset.prod_le_prod (fun i _ => by positivity) fun i _ => hi i
    _ = L ^ (2 * n) * (1 + ‖freq n L k‖) ^ (2 * n) := by
        simp [Finset.prod_const, ← pow_mul, mul_pow, mul_comm]

lemma measurable_fourier_param {n : ℕ} (G : E n → E n → ℂ) (hG : Measurable (uncurry G))
    (w : E n) : Measurable (fun y => 𝓕 (fun x => G x y) w) := by
  simp_rw [Real.fourier_eq]
  have : StronglyMeasurable (uncurry fun x y => (Real.fourierChar (-inner ℝ x w) : ℂ) • G x y) := by
    refine Measurable.stronglyMeasurable ?_
    have h1 : Measurable fun p : E n × E n => (Real.fourierChar (-inner ℝ p.1 w) : ℂ) :=
      (by fun_prop : Continuous fun p : E n × E n => (Real.fourierChar (-inner ℝ p.1 w) : ℂ)).measurable
    exact h1.mul hG
  exact (this.integral_prod_left (μ := volume)).measurable


lemma fourier_decay (n : ℕ) (ρ : ℝ) (D : ℕ → ℝ) : ∃ C : ℝ, ∀ g : E n → ℂ,
    ContDiff ℝ ((2 * n : ℕ) : WithTop ℕ∞) g → (∀ x, g x ≠ 0 → ‖x‖ ≤ ρ) →
    (∀ j ≤ 2 * n, ∀ x, ‖iteratedFDeriv ℝ j g x‖ ≤ D j) →
    ∀ w, (1 + ‖w‖) ^ (2 * n) * ‖𝓕 g w‖ ≤ C := by
  set N := 2 * n with hN
  set V := (volume (closedBall (0 : E n) ρ)).toReal with hV
  set Cm : ℕ → ℝ := fun m => (2 * (0 : ℕ) + 2) ^ m *
    ∑ p ∈ Finset.range (0 + 1) ×ˢ Finset.range (m + 1), D p.2 * V with hCm
  refine ⟨2 ^ N * (Cm 0 + Cm N), fun g hg hsupp hD w => ?_⟩
  have hts : tsupport g ⊆ closedBall 0 ρ := by
    refine closure_minimal (fun x hx => ?_) isClosed_closedBall
    simpa using hsupp x hx
  have hcs : HasCompactSupport g := (isCompact_closedBall 0 ρ).of_isClosed_subset
    (isClosed_tsupport g) hts
  have hbound : ∀ m ≤ N, ‖w‖ ^ m * ‖𝓕 g w‖ ≤ Cm m := by
    intro m hm
    have hint : ∀ (k j : ℕ), (k : ℕ∞) ≤ (0 : ℕ∞) → (j : ℕ∞) ≤ ((N : ℕ) : ℕ∞) →
        Integrable (fun v => ‖v‖ ^ k * ‖iteratedFDeriv ℝ j g v‖) volume := by
      intro k j hk hj
      have hk0 : k = 0 := by exact_mod_cast nonpos_iff_eq_zero.1 hk
      subst hk0
      simp only [pow_zero, one_mul]
      have hjN : j ≤ N := by exact_mod_cast hj
      have hc : Continuous (iteratedFDeriv ℝ j g) :=
        hg.continuous_iteratedFDeriv (by exact_mod_cast hjN)
      exact (hc.integrable_of_hasCompactSupport (hcs.iteratedFDeriv j)).norm
    have := Real.pow_mul_norm_iteratedFDeriv_fourier_le (K := 0) (N := ((N : ℕ) : ℕ∞))
      (by exact_mod_cast hg) hint (k := 0) (n := m) le_rfl (by exact_mod_cast hm) w
    rw [norm_iteratedFDeriv_zero] at this
    refine this.trans ?_
    simp only [pow_zero, one_mul, hCm]
    gcongr with p hp
    simp only [Finset.mem_product, Finset.mem_range] at hp
    have hp1 : p.1 = 0 := by omega
    rw [hp1]
    simp only [pow_zero, one_mul]
    have hpN : p.2 ≤ N := by omega
    calc ∫ v, ‖iteratedFDeriv ℝ p.2 g v‖
        ≤ ∫ v, (closedBall (0 : E n) ρ).indicator (fun _ => D p.2) v := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun v => norm_nonneg _)
            ((integrable_indicator_iff measurableSet_closedBall).2
              (integrableOn_const (measure_closedBall_lt_top).ne)) ?_
          refine Filter.Eventually.of_forall fun v => ?_
          by_cases hv : v ∈ closedBall (0 : E n) ρ
          · rw [Set.indicator_of_mem hv]; exact hD p.2 hpN v
          · rw [Set.indicator_of_notMem hv]
            have : v ∉ tsupport g := fun h => hv (hts h)
            have h0 : iteratedFDeriv ℝ p.2 g v = 0 :=
              Function.notMem_support.1 fun h => this (support_iteratedFDeriv_subset _ h)
            simp [h0]
      _ = D p.2 * V := by
          rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul, mul_comm]
          simp [hV, Measure.real]
  have h0 := hbound 0 (Nat.zero_le _)
  have hNb := hbound N le_rfl
  simp only [pow_zero, one_mul] at h0
  have hw : (1 + ‖w‖) ^ N ≤ 2 ^ N * (1 + ‖w‖ ^ N) := by
    rcases le_total ‖w‖ 1 with h | h
    · calc (1 + ‖w‖) ^ N ≤ 2 ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
        _ ≤ 2 ^ N * (1 + ‖w‖ ^ N) := by
          have : 0 ≤ ‖w‖ ^ N := by positivity
          nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) N]
    · calc (1 + ‖w‖) ^ N ≤ (2 * ‖w‖) ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
        _ = 2 ^ N * ‖w‖ ^ N := mul_pow _ _ _
        _ ≤ 2 ^ N * (1 + ‖w‖ ^ N) := by
          nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) N]
  calc (1 + ‖w‖) ^ N * ‖𝓕 g w‖ ≤ 2 ^ N * (1 + ‖w‖ ^ N) * ‖𝓕 g w‖ := by gcongr
    _ = 2 ^ N * (‖𝓕 g w‖ + ‖w‖ ^ N * ‖𝓕 g w‖) := by ring
    _ ≤ 2 ^ N * (Cm 0 + Cm N) := by gcongr

/-- coordinatewise reduction to `[-1/2, 1/2)`. -/
noncomputable def red {n : ℕ} (s : Fin n → ℝ) : Fin n → ℝ := fun i => s i - round (s i)

/-- the periodic lift. -/
noncomputable def per {n : ℕ} (L : ℝ) (g : E n → ℂ) (s : Fin n → ℝ) : ℂ :=
  g (L • WithLp.toLp 2 (red s))

lemma per_periodic {n : ℕ} (L : ℝ) (g : E n → ℂ) (s t : Fin n → ℝ)
    (h : ∀ i, ((s i : ℝ) : UnitAddCircle) = (t i : UnitAddCircle)) : per L g s = per L g t := by
  have : red s = red t := by
    funext i
    have hi := QuotientAddGroup.eq.1 (h i)
    obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.1 hi
    have ht : t i = s i + m := by simp at hm; linarith
    simp only [red, ht, round_add_intCast]; push_cast; ring
  simp [per, this]

lemma per_continuous {n : ℕ} (L : ℝ) (hL : 0 < L) (g : E n → ℂ) (hg : Continuous g)
    (hsupp : ∀ x, g x ≠ 0 → ∀ i, |x i| ≤ L / 4) : Continuous (per L g) := by
  rw [continuous_iff_continuousAt]
  intro s
  by_cases hs : ∀ i, |s i - round (s i)| < 1 / 2
  · -- round is locally constant
    have hev : ∀ᶠ t in nhds s, red t = red s + (t - s) := by
      have : ∀ i, ∀ᶠ t in nhds s, round (t i) = round (s i) := by
        intro i
        set δ := 1 / 2 - |s i - round (s i)| with hδ
        have hδp : 0 < δ := by have := hs i; linarith
        have hc : Continuous fun t : Fin n → ℝ => t i := continuous_apply i
        filter_upwards [hc.continuousAt.eventually (Metric.ball_mem_nhds (s i) hδp)] with t ht
        rw [Real.dist_eq] at ht
        rw [round_eq, Int.floor_eq_iff]
        have h1 := abs_lt.1 ht
        have h4 := le_abs_self (s i - round (s i))
        have h5 := neg_abs_le (s i - round (s i))
        constructor <;> linarith
      filter_upwards [Filter.eventually_all.2 this] with t ht
      funext i; simp [red, ht i]
    have hcont : ContinuousAt (fun t => g (L • WithLp.toLp 2 (red s + (t - s)))) s := by
      fun_prop
    exact hcont.congr (by filter_upwards [hev] with t ht; simp [per, ht])
  · push Not at hs
    obtain ⟨i, hi⟩ := hs
    -- per vanishes near s
    have hev : ∀ᶠ t in nhds s, per L g t = 0 := by
      have hc : Continuous fun t : Fin n → ℝ => t i := continuous_apply i
      filter_upwards [hc.continuousAt.eventually (Metric.ball_mem_nhds (s i)
        (by norm_num : (0:ℝ) < 1 / 8))] with t ht
      rw [Real.dist_eq] at ht
      by_contra hne
      have := hsupp _ hne i
      have hti : (L • WithLp.toLp 2 (red t)) i = L * (t i - round (t i)) := by
        simp [red]
      rw [hti, abs_mul, abs_of_pos hL] at this
      have h1 : |t i - round (t i)| ≤ 1 / 4 := by
        have := (mul_le_mul_iff_right₀ hL).1 (by linarith : L * |t i - round (t i)| ≤ L * (1/4))
        exact this
      have h2 := round_le (s i) (round (t i))
      have h3 : |s i - round (t i)| ≤ |s i - t i| + |t i - round (t i)| := by
        have := abs_sub_le (s i) (t i) (round (t i)); linarith
      rw [abs_sub_comm] at ht
      linarith
    have h0 : per L g s = 0 := hev.self_of_nhds
    exact (continuousAt_const (y := (0 : ℂ))).congr (hev.mono fun t ht => ht.symm)


/-- the projection to the torus. -/
def proj {n : ℕ} (s : Fin n → ℝ) : UnitAddTorus (Fin n) := fun i => ((s i : ℝ) : UnitAddCircle)

lemma proj_quot (n : ℕ) : IsOpenQuotientMap (proj (n := n)) :=
  IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk

noncomputable def torusLift {n : ℕ} (L : ℝ) (g : E n → ℂ) (t : UnitAddTorus (Fin n)) : ℂ :=
  per L g (surjInv (proj_quot n).surjective t)

lemma torusLift_proj {n : ℕ} (L : ℝ) (g : E n → ℂ) (s : Fin n → ℝ) :
    torusLift L g (proj s) = per L g s := by
  unfold torusLift
  apply per_periodic
  intro i
  exact congrFun (surjInv_eq (proj_quot n).surjective (proj s)) i

lemma torusLift_continuous {n : ℕ} (L : ℝ) (hL : 0 < L) (g : E n → ℂ) (hg : Continuous g)
    (hsupp : ∀ x, g x ≠ 0 → ∀ i, |x i| ≤ L / 4) : Continuous (torusLift L g) := by
  rw [← (proj_quot n).continuous_comp_iff]
  have : torusLift L g ∘ proj = per L g := funext fun s => torusLift_proj L g s
  rw [this]
  exact per_continuous L hL g hg hsupp

lemma mFourier_proj {n : ℕ} (k : Fin n → ℤ) (s : Fin n → ℝ) :
    UnitAddTorus.mFourier k (proj s) =
      Complex.exp (2 * Real.pi * Complex.I * ∑ i, (k i : ℂ) * (s i : ℂ)) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, proj, fourier_coe_apply]
  rw [← Complex.exp_sum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast; ring

lemma inner_freq {n : ℕ} (L : ℝ) (hL : L ≠ 0) (k : Fin n → ℤ) (s : Fin n → ℝ) :
    inner ℝ (L • WithLp.toLp 2 s) (freq n L k) = ∑ i, (k i : ℝ) * s i := by
  simp only [freq, inner_smul_left, inner_smul_right, PiLp.inner_apply]
  simp only [RCLike.conj_to_real, real_inner_eq_re_inner, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp
  field_simp


lemma per_eq_on_cube {n : ℕ} (L : ℝ) (hL : 0 < L) (g : E n → ℂ)
    (hsupp : ∀ x, g x ≠ 0 → ∀ i, |x i| ≤ L / 4) (s : Fin n → ℝ)
    (hs : ∀ i, s i ∈ Set.Ioc (-(1/2) : ℝ) (-(1/2) + 1)) :
    per L g s = g (L • WithLp.toLp 2 s) := by
  by_cases h : ∀ i, round (s i) = 0
  · have : red s = s := funext fun i => by simp [red, h i]
    simp [per, this]
  push Not at h
  obtain ⟨i, hi⟩ := h
  have hsi : s i = 1 / 2 := by
    have h1 := hs i
    by_contra hne
    exact hi (round_eq_zero_iff.2 ⟨by linarith [h1.1], lt_of_le_of_ne (by linarith [h1.2]) hne⟩)
  have hr : round (s i) = 1 := by rw [hsi]; norm_num [round_eq]
  have hA : g (L • WithLp.toLp 2 s) = 0 := by
    by_contra hne
    have := hsupp _ hne i
    simp [hsi, abs_of_pos hL] at this
    linarith
  rw [hA]
  by_contra hne
  have := hsupp _ hne i
  simp [red, hsi, hr, abs_of_pos hL] at this
  norm_num [abs_of_pos hL] at this
  linarith

lemma g_zero_off_cube {n : ℕ} (L : ℝ) (hL : 0 < L) (g : E n → ℂ)
    (hsupp : ∀ x, g x ≠ 0 → ∀ i, |x i| ≤ L / 4) (s : Fin n → ℝ)
    (hs : ¬ ∀ i, s i ∈ Set.Ioc (-(1/2) : ℝ) (-(1/2) + 1)) :
    g (L • WithLp.toLp 2 s) = 0 := by
  by_contra hne
  apply hs
  intro i
  have := hsupp _ hne i
  simp [abs_mul, abs_of_pos hL] at this
  have h2 : |s i| ≤ 1 / 4 := by
    have := (mul_le_mul_iff_right₀ hL).1 (by linarith : L * |s i| ≤ L * (1/4)); exact this
  have := abs_le.1 h2
  constructor <;> linarith

lemma coeff_eq {n : ℕ} (L : ℝ) (hL : 0 < L) (g : E n → ℂ) (hg : Continuous g)
    (hsupp : ∀ x, g x ≠ 0 → ∀ i, |x i| ≤ L / 4) (k : Fin n → ℤ) :
    UnitAddTorus.mFourierCoeff (torusLift L g) k =
      ((L ^ n)⁻¹ : ℝ) * 𝓕 g (freq n L k) := by
  rw [UnitAddTorus.mFourierCoeff_eq_integral _ k (fun _ => -(1/2))]
  set H : (Fin n → ℝ) → ℂ := fun s =>
    (Real.fourierChar (-inner ℝ (L • WithLp.toLp 2 s) (freq n L k)) : ℂ) *
      g (L • WithLp.toLp 2 s) with hH
  have hreg : MeasurableSet {x : Fin n → ℝ | ∀ i, x i ∈ Set.Ioc (-(1/2) : ℝ) (-(1/2) + 1)} := by
    have : {x : Fin n → ℝ | ∀ i, x i ∈ Set.Ioc (-(1/2) : ℝ) (-(1/2) + 1)} =
        Set.univ.pi fun _ => Set.Ioc (-(1/2) : ℝ) (-(1/2) + 1) := by ext; simp
    rw [this]; exact MeasurableSet.univ_pi fun _ => measurableSet_Ioc
  have hpt : ∀ s : Fin n → ℝ, UnitAddTorus.mFourier (-k) (fun i => ((s i : ℝ) : UnitAddCircle)) *
      g (L • WithLp.toLp 2 s) = H s := by
    intro s
    have : UnitAddTorus.mFourier (-k) (fun i => ((s i : ℝ) : UnitAddCircle)) = _ :=
      mFourier_proj (-k) s
    rw [this]
    simp only [hH, Real.fourierChar_apply, inner_freq L hL.ne']
    congr 1; congr 1
    push_cast; simp only [Pi.neg_apply, Int.cast_neg, Complex.ofReal_neg, neg_mul,
      Finset.sum_neg_distrib, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_intCast]
    ring
  calc ∫ x in {x : Fin n → ℝ | ∀ i, x i ∈ Set.Ioc (-(1/2) : ℝ) (-(1/2) + 1)},
        UnitAddTorus.mFourier (-k) (fun i => ((x i : ℝ) : UnitAddCircle)) •
          torusLift L g (fun i => ((x i : ℝ) : UnitAddCircle))
      = ∫ x in {x : Fin n → ℝ | ∀ i, x i ∈ Set.Ioc (-(1/2) : ℝ) (-(1/2) + 1)}, H x := by
        refine setIntegral_congr_fun hreg fun s hs => ?_
        have h1 : torusLift L g (fun i => ((s i : ℝ) : UnitAddCircle)) = per L g s :=
          torusLift_proj L g s
        rw [smul_eq_mul, h1, per_eq_on_cube L hL g hsupp s hs, hpt]
    _ = ∫ x, H x := by
        refine setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs => ?_
        simp [hH, g_zero_off_cube L hL g hsupp s hs]
    _ = ∫ v : E n, (Real.fourierChar (-inner ℝ (L • v) (freq n L k)) : ℂ) * g (L • v) := by
        have := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n)).symm.integral_comp'
          (fun v : E n => (Real.fourierChar (-inner ℝ (L • v) (freq n L k)) : ℂ) * g (L • v))
        simpa [hH] using this
    _ = ((L ^ n)⁻¹ : ℝ) * 𝓕 g (freq n L k) := by
        rw [Measure.integral_comp_smul (μ := volume)
          (fun v : E n => (Real.fourierChar (-inner ℝ v (freq n L k)) : ℂ) * g v) L,
          Real.fourier_eq, finrank_euclideanSpace_fin, abs_of_pos (by positivity)]
        rw [Complex.real_smul]
        simp only [Complex.ofReal_inv, Complex.ofReal_pow, mul_eq_mul_left_iff, inv_eq_zero,
          pow_eq_zero_iff', Complex.ofReal_eq_zero]
        refine Or.inl (integral_congr_ae (Filter.Eventually.of_forall fun x => ?_))
        simp [Circle.smul_def]


lemma hasSum_fourier_cube (n : ℕ) (L : ℝ) (hL : 0 < L) (g : E n → ℂ) (hg : Continuous g)
    (hsupp : ∀ x, g x ≠ 0 → ∀ i, |x i| ≤ L / 4)
    (hsum : Summable (fun k => ‖𝓕 g (freq n L k)‖)) (x : E n) (hx : ∀ i, |x i| < L / 2) :
    HasSum (fun k => expo n L k x * ((L ^ n)⁻¹ * 𝓕 g (freq n L k))) (g x) := by
  set Φ : C(UnitAddTorus (Fin n), ℂ) := ⟨torusLift L g, torusLift_continuous L hL g hg hsupp⟩
  have hcoef : ∀ k, UnitAddTorus.mFourierCoeff Φ k = ((L ^ n)⁻¹ : ℝ) * 𝓕 g (freq n L k) :=
    fun k => coeff_eq L hL g hg hsupp k
  have hsumm : Summable (UnitAddTorus.mFourierCoeff Φ) := by
    refine Summable.of_norm ?_
    simp_rw [hcoef, norm_mul]
    refine (hsum.mul_left ‖(((L ^ n)⁻¹ : ℝ) : ℂ)‖).congr fun k => rfl
  set s : Fin n → ℝ := fun i => L⁻¹ * x i with hs
  have hxs : x = L • WithLp.toLp 2 s := by
    ext i; simp [hs]; field_simp
  have hred : red s = s := by
    funext i
    have : round (s i) = 0 := by
      rw [round_eq_zero_iff]
      have h1 := abs_lt.1 (hx i)
      simp only [hs, Set.mem_Ico]
      constructor
      · rw [le_inv_mul_iff₀ hL]; linarith
      · rw [inv_mul_lt_iff₀ hL]; linarith
    simp [red, this]
  have h := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hsumm (proj s)
  have hΦ : Φ (proj s) = g x := by
    show torusLift L g (proj s) = g x
    rw [torusLift_proj]; simp only [per, hred]; rw [← hxs]
  rw [hΦ] at h
  refine h.congr_fun ?_
  intro k
  rw [hcoef, smul_eq_mul, mul_comm]
  congr 1
  rw [mFourier_proj, expo, Real.fourierChar_apply, hxs, inner_freq L hL.ne']
  congr 1
  push_cast; ring


lemma expansion {ι : Type*} (n : ℕ) (ρ : ℝ) (G : ι → E n → E n → ℂ)
    (hGm : ∀ i, Measurable (uncurry (G i)))
    (hGs : ∀ i y, ContDiff ℝ ((2 * n : ℕ) : WithTop ℕ∞) (fun x => G i x y))
    (hsupp : ∀ i x y, G i x y ≠ 0 → ‖x‖ ≤ ρ)
    (hD : ∀ j, ∃ D, ∀ i x y, ‖iteratedFDeriv ℝ j (fun x => G i x y) x‖ ≤ D) :
    ∃ e : (Fin n → ℤ) → E n → ℂ, ∃ a : (Fin n → ℤ) → ℝ, Summable a ∧
      (∀ k, Measurable (e k)) ∧ (∀ k x, ‖e k x‖ ≤ 1) ∧
      ∀ i, ∃ c : (Fin n → ℤ) → E n → ℂ, (∀ k, Measurable (c k)) ∧ (∀ k y, ‖c k y‖ ≤ a k) ∧
        ∀ x y, ‖x‖ ≤ ρ → HasSum (fun k => e k x * c k y) (G i x y) := by
  choose D hD using hD
  obtain ⟨C, hC⟩ := fourier_decay n ρ D
  set C' := max C 0 with hC'
  set L : ℝ := 4 * (|ρ| + 1) with hL
  have hL1 : 1 ≤ L := by rw [hL]; linarith [abs_nonneg ρ]
  have hL0 : 0 < L := by linarith
  set a : (Fin n → ℤ) → ℝ := fun k =>
    (L ^ n)⁻¹ * (C' * L ^ (2 * n)) * ∏ i, ((1 + |(k i : ℝ)|) ^ 2)⁻¹ with ha
  have hgsupp : ∀ i y x, G i x y ≠ 0 → ∀ j, |x j| ≤ L / 4 := by
    intro i y x hx j
    have h1 := hsupp i x y hx
    have h2 := abs_apply_le n x j
    have : ρ ≤ |ρ| := le_abs_self ρ
    rw [hL]; linarith
  have hFbound : ∀ i y k, ‖𝓕 (fun x => G i x y) (freq n L k)‖ ≤
      C' * L ^ (2 * n) * ∏ j, ((1 + |(k j : ℝ)|) ^ 2)⁻¹ := by
    intro i y k
    have h1 := hC (fun x => G i x y) (hGs i y) (fun x hx => hsupp i x y hx)
      (fun j _ x => hD j i x y) (freq n L k)
    have h2 := prod_le_freq n L hL1 k
    set Q := (1 + ‖freq n L k‖) ^ (2 * n)
    set P := ∏ j, (1 + |(k j : ℝ)|) ^ 2
    have hQ : 0 < Q := by positivity
    have hP : 0 < P := Finset.prod_pos fun j _ => by positivity
    rw [Finset.prod_inv_distrib]
    change _ ≤ C' * L ^ (2 * n) * P⁻¹
    have h3 : ‖𝓕 (fun x => G i x y) (freq n L k)‖ ≤ C' / Q := by
      rw [le_div_iff₀ hQ, mul_comm]; exact h1.trans (le_max_left _ _)
    refine h3.trans ?_
    have hC0 : 0 ≤ C' := le_max_right _ _
    rw [div_le_iff₀ hQ]
    have : C' * L ^ (2 * n) * P⁻¹ * Q = C' * (L ^ (2 * n) * Q) / P := by field_simp
    rw [this, le_div_iff₀ hP]
    exact mul_le_mul_of_nonneg_left h2 hC0
  refine ⟨expo n L, a, ?_, fun k => (continuous_expo n L k).measurable,
    fun k x => (norm_expo n L k x).le, fun i => ?_⟩
  · exact (summable_prod_inv n).mul_left _
  refine ⟨fun k y => (L ^ n)⁻¹ * 𝓕 (fun x => G i x y) (freq n L k), fun k => ?_, fun k y => ?_,
    fun x y hx => ?_⟩
  · exact (measurable_fourier_param (G i) (hGm i) _).const_mul _
  · rw [norm_mul, ha]
    simp only
    rw [mul_assoc]
    refine mul_le_mul ?_ ((hFbound i y k).trans (le_of_eq (by ring))) (norm_nonneg _)
      (by positivity)
    simp [abs_of_pos hL0]
  · have hcont : Continuous fun x => G i x y := (hGs i y).continuous
    refine hasSum_fourier_cube n L hL0 (fun x => G i x y) hcont (hgsupp i y) ?_ x ?_
    · exact Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => hFbound i y k)
        ((summable_prod_inv n).mul_left _)
    · intro j
      have h2 := abs_apply_le n x j
      have : ρ ≤ |ρ| := le_abs_self ρ
      rw [hL]; linarith


/-- A smooth cutoff equal to `1` on a compact set, with compact support inside an open set. -/
lemma exists_cutoff {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (K U : Set P) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : P → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧
      ∀ z ∈ K, χ z = 1 := by
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  obtain ⟨f, hfs, hfd, hfr⟩ := (isOpen_thickening (δ := δ) (E := K)).exists_contDiff_support_eq
    (n := (⊤ : ℕ∞))
  obtain ⟨g, hgs, hgd, hgr⟩ := hK.isClosed.isOpen_compl.exists_contDiff_support_eq
    (n := (⊤ : ℕ∞))
  have hf0 : ∀ z, 0 ≤ f z := fun z => (hfr ⟨z, rfl⟩).1
  have hg0 : ∀ z, 0 ≤ g z := fun z => (hgr ⟨z, rfl⟩).1
  have hpos : ∀ z, 0 < f z + g z := by
    intro z
    by_cases hz : z ∈ thickening δ K
    · have : f z ≠ 0 := by rw [← mem_support, hfs]; exact hz
      have := lt_of_le_of_ne (hf0 z) (Ne.symm this)
      linarith [hg0 z]
    · have hzK : z ∉ K := fun h => hz (self_subset_thickening hδ K h)
      have : g z ≠ 0 := by rw [← mem_support, hgs]; exact hzK
      have := lt_of_le_of_ne (hg0 z) (Ne.symm this)
      linarith [hf0 z]
  have hsupp : support (fun z => f z / (f z + g z)) = thickening δ K := by
    rw [← hfs]; ext z; simp [(hpos z).ne']
  have hts : tsupport (fun z => f z / (f z + g z)) ⊆ cthickening δ K := by
    rw [tsupport, hsupp]; exact closure_thickening_subset_cthickening δ K
  refine ⟨fun z => f z / (f z + g z), ?_, ?_, hts.trans hδU, fun z hz => ?_⟩
  · exact hfd.div (hfd.add hgd) fun z => (hpos z).ne'
  · exact (hK.cthickening (r := δ)).of_isClosed_subset (isClosed_tsupport _) hts
  · have hg : g z = 0 := by
      by_contra h; have := (mem_support.2 h); rw [hgs] at this; exact this hz
    have hf : f z ≠ 0 := by rw [← mem_support, hfs]; exact self_subset_thickening hδ K hz
    simp [hg, hf]

lemma contDiff_cutoff_mul {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (U : Set P) (hU : IsOpen U) (χ : P → ℂ) (hχ : ContDiff ℝ ∞ χ) (htU : tsupport χ ⊆ U)
    (F : P → ℂ) (hF : ContDiffOn ℝ ∞ F U) : ContDiff ℝ ∞ (fun z => χ z * F z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ U
  · exact hχ.contDiffAt.mul (hF.contDiffAt (hU.mem_nhds hz))
  · have hz' : z ∉ tsupport χ := fun h => hz (htU h)
    have h0 : χ =ᶠ[nhds z] 0 := notMem_tsupport_iff_eventuallyEq.1 hz'
    refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [h0] with w hw
    simp [hw]

lemma norm_iteratedFDeriv_slice_le {n : ℕ} (H : E n × ℝ → ℂ) (hH : ContDiff ℝ ∞ H) (τ : ℝ)
    (j : ℕ) (x : E n) :
    ‖iteratedFDeriv ℝ j (fun x => H (x, τ)) x‖ ≤ ‖iteratedFDeriv ℝ j H (x, τ)‖ := by
  set T : E n × ℝ → ℂ := fun z => H (z + ((0 : E n), τ)) with hT
  have hTc : ContDiff ℝ ∞ T := hH.comp (contDiff_id.add contDiff_const)
  have heq : (fun x => H (x, τ)) = T ∘ (ContinuousLinearMap.inl ℝ (E n) ℝ) := by
    funext x; simp [hT]
  rw [heq, (ContinuousLinearMap.inl ℝ (E n) ℝ).iteratedFDeriv_comp_right hTc x
    (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have h1 : ∏ _i : Fin j, ‖ContinuousLinearMap.inl ℝ (E n) ℝ‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _)
      (fun _ _ => ContinuousLinearMap.norm_inl_le_one _ _ _)
  have h2 : iteratedFDeriv ℝ j T ((ContinuousLinearMap.inl ℝ (E n) ℝ) x) =
      iteratedFDeriv ℝ j H (x, τ) := by
    rw [hT, iteratedFDeriv_comp_add_right]; simp
  rw [h2]
  calc ‖iteratedFDeriv ℝ j H (x, τ)‖ * ∏ _i : Fin j, ‖ContinuousLinearMap.inl ℝ (E n) ℝ‖
      ≤ ‖iteratedFDeriv ℝ j H (x, τ)‖ * 1 := by gcongr
    _ = _ := mul_one _

/-- The prepared family `G_τ(x, y) = χ(x, τ) b(x, y, τ)` (for `y ∈ π₂(S)`, else `0`). -/
lemma prep (n : ℕ) (S : Set (E n × E n)) (hS : IsCompact S)
    (b : E n → E n → ℝ → ℂ) (hbm : ∀ τ, Measurable (Function.uncurry fun x y => b x y τ))
    (τ₀ : ℝ) (U : Set (E n × ℝ)) (hU : IsOpen U)
    (hSU : (Prod.fst '' S) ×ˢ Set.Icc 0 τ₀ ⊆ U)
    (hbsmooth : ∀ y ∈ Prod.snd '' S, ContDiffOn ℝ (⊤ : ℕ∞) (fun z : E n × ℝ => b z.1 y z.2) U)
    (hbder : ∀ k : ℕ, ∃ D : ℝ, ∀ y ∈ Prod.snd '' S, ∀ z ∈ U,
      ‖iteratedFDerivWithin ℝ k (fun z : E n × ℝ => b z.1 y z.2) U z‖ ≤ D) :
    ∃ ρ : ℝ, ∃ G : Set.Icc (0 : ℝ) τ₀ → E n → E n → ℂ,
      (∀ i, Measurable (uncurry (G i))) ∧
      (∀ i y, ContDiff ℝ ((2 * n : ℕ) : WithTop ℕ∞) (fun x => G i x y)) ∧
      (∀ i x y, G i x y ≠ 0 → ‖x‖ ≤ ρ) ∧
      (∀ j, ∃ D, ∀ i x y, ‖iteratedFDeriv ℝ j (fun x => G i x y) x‖ ≤ D) ∧
      (∀ i x y, (x, y) ∈ S → ‖x‖ ≤ ρ ∧ G i x y = b x y i) := by
  set X := Prod.fst '' S with hX
  set Y := Prod.snd '' S with hY
  have hXc : IsCompact X := hS.image continuous_fst
  have hYc : IsCompact Y := hS.image continuous_snd
  have hKc : IsCompact (X ×ˢ Set.Icc 0 τ₀) := hXc.prod isCompact_Icc
  obtain ⟨χr, hχd, hχcs, hχU, hχ1⟩ := exists_cutoff _ U hKc hU hSU
  set χ : E n × ℝ → ℂ := fun z => (χr z : ℂ) with hχdef
  have hχc : ContDiff ℝ ∞ χ := Complex.ofRealCLM.contDiff.comp hχd
  have hχsupp : support χ = support χr := by ext z; simp [hχdef]
  have hχts : tsupport χ = tsupport χr := by simp [tsupport, hχsupp]
  have hχcs' : HasCompactSupport χ := by
    unfold HasCompactSupport; rw [hχts]; exact hχcs
  obtain ⟨ρ, hρ⟩ := hχcs.isBounded.subset_closedBall (0 : E n × ℝ)
  set H : E n → E n × ℝ → ℂ := fun y z => χ z * b z.1 y z.2 with hH
  have hHc : ∀ y ∈ Y, ContDiff ℝ ∞ (H y) := fun y hy =>
    contDiff_cutoff_mul U hU χ hχc (hχts ▸ hχU) _ (hbsmooth y hy)
  -- derivative bounds for `H y`
  choose Db hDb using hbder
  have hχb : ∀ k, ∃ C, ∀ z, ‖iteratedFDeriv ℝ k χ z‖ ≤ C := fun k =>
    (hχc.continuous_iteratedFDeriv (by exact_mod_cast le_top)).bounded_above_of_compact_support
      (hχcs'.iteratedFDeriv k)
  choose Cχ hCχ using hχb
  set DH : ℕ → ℝ := fun k => ∑ i ∈ Finset.range (k + 1),
    (k.choose i : ℝ) * max (Cχ i) 0 * max (Db (k - i)) 0 with hDH
  have hDH0 : ∀ k, 0 ≤ DH k := fun k =>
    Finset.sum_nonneg fun i _ => by positivity
  have hHb : ∀ k, ∀ y ∈ Y, ∀ z, ‖iteratedFDeriv ℝ k (H y) z‖ ≤ DH k := by
    intro k y hy z
    by_cases hz : z ∈ U
    · rw [← iteratedFDerivWithin_of_isOpen k hU hz]
      refine (norm_iteratedFDerivWithin_mul_le hχc.contDiffOn (hbsmooth y hy)
        hU.uniqueDiffOn hz (n := k) (by exact_mod_cast le_top)).trans ?_
      refine Finset.sum_le_sum fun i _ => ?_
      have h1 : ‖iteratedFDerivWithin ℝ i χ U z‖ ≤ max (Cχ i) 0 := by
        rw [iteratedFDerivWithin_of_isOpen i hU hz]; exact (hCχ i z).trans (le_max_left _ _)
      have h2 : ‖iteratedFDerivWithin ℝ (k - i) (fun z : E n × ℝ => b z.1 y z.2) U z‖ ≤
          max (Db (k - i)) 0 := (hDb (k - i) y hy z hz).trans (le_max_left _ _)
      gcongr
    · have hz' : z ∉ tsupport (H y) := by
        intro h
        have : z ∈ tsupport χ := tsupport_mul_subset_left h
        rw [hχts] at this; exact hz (hχU this)
      have : iteratedFDeriv ℝ k (H y) z = 0 :=
        notMem_support.1 fun h => hz' (support_iteratedFDeriv_subset k h)
      rw [this, norm_zero]; exact hDH0 k
  classical
  refine ⟨ρ, fun i x y => if y ∈ Y then H y (x, i.1) else 0, fun i => ?_, fun i y => ?_,
    fun i x y hne => ?_, fun j => ⟨DH j, fun i x y => ?_⟩, fun i x y hxy => ?_⟩
  · -- measurability
    have hYm : MeasurableSet Y := hYc.isClosed.measurableSet
    have h1 : Measurable fun p : E n × E n => χ (p.1, i.1) :=
      (hχc.continuous.comp (continuous_fst.prodMk continuous_const)).measurable
    have h2 : Measurable fun p : E n × E n => H p.2 (p.1, i.1) := by
      simp only [hH]
      exact h1.mul (hbm i.1)
    exact Measurable.ite (measurableSet_preimage measurable_snd hYm) h2 measurable_const
  · by_cases hy : y ∈ Y
    · simp only [hy, if_true]
      exact ((hHc y hy).comp (contDiff_id.prodMk contDiff_const)).of_le
        (WithTop.coe_le_coe.2 le_top)
    · simp only [hy, if_false]; exact contDiff_const
  · by_cases hy : y ∈ Y
    · simp only [hy, if_true, hH] at hne
      have hχne : χ (x, i.1) ≠ 0 := left_ne_zero_of_mul hne
      have : (x, i.1) ∈ tsupport χr := by
        rw [← hχts]; exact subset_tsupport _ hχne
      have := hρ this
      rw [mem_closedBall, dist_zero_right] at this
      exact (norm_fst_le (x, i.1)).trans this
    · simp [hy] at hne
  · by_cases hy : y ∈ Y
    · simp only [hy, if_true]
      exact (norm_iteratedFDeriv_slice_le (H y) (hHc y hy) i.1 j x).trans (hHb j y hy _)
    · simp only [hy, if_false]
      rw [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]; exact hDH0 j
  · have hx : x ∈ X := ⟨(x, y), hxy, rfl⟩
    have hy : y ∈ Y := ⟨(x, y), hxy, rfl⟩
    have h1 : χr (x, i.1) = 1 := hχ1 _ ⟨hx, i.2⟩
    refine ⟨?_, ?_⟩
    · have hmem : (x, i.1) ∈ tsupport χr :=
        subset_tsupport _ (by rw [mem_support, h1]; norm_num)
      have := hρ hmem
      rw [mem_closedBall, dist_zero_right] at this
      exact (norm_fst_le (x, i.1)).trans this
    · simp [hy, hH, hχdef, h1]

/-! ## Assembly -/

theorem opNorm_le_of_contDiff_dev (n : ℕ) (p q : ℝ≥0∞) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (K : ℝ → E n → E n → ℂ) (S : Set (E n × E n)) (hS : IsCompact S) (M : ℝ)
    (hKm : ∀ R, Measurable (Function.uncurry (K R)))
    (hK : ∀ R x y, ‖K R x y‖ ≤ M ∧ (K R x y ≠ 0 → (x, y) ∈ S))
    (b : E n → E n → ℝ → ℂ) (hbm : ∀ τ, Measurable (Function.uncurry fun x y => b x y τ))
    (B : ℝ) (hb : ∀ x y τ, ‖b x y τ‖ ≤ B) (τ₀ : ℝ) (hτ₀ : 0 < τ₀)
    (U : Set (E n × ℝ)) (hU : IsOpen U) (hSU : (Prod.fst '' S) ×ˢ Set.Icc 0 τ₀ ⊆ U)
    (hbsmooth : ∀ y ∈ Prod.snd '' S, ContDiffOn ℝ (⊤ : ℕ∞) (fun z : E n × ℝ => b z.1 y z.2) U)
    (hbder : ∀ k : ℕ, ∃ D : ℝ, ∀ y ∈ Prod.snd '' S, ∀ z ∈ U,
      ‖iteratedFDerivWithin ℝ k (fun z : E n × ℝ => b z.1 y z.2) U z‖ ≤ D) :
    ∀ N : ℝ, 0 < N → ∃ C R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      opNorm p q (kernelOp fun x y => K R x y * b x y R⁻¹) ≤
        ENNReal.ofReal C * opNorm p q (kernelOp (K R)) + ENNReal.ofReal (C * R ^ (-N)) := by
  intro N _
  obtain ⟨ρ, G, hGm, hGs, hGsupp, hGD, hGS⟩ :=
    prep n S hS b hbm τ₀ U hU hSU hbsmooth hbder
  obtain ⟨e, a, ha, he, he1, hc⟩ := expansion n ρ G hGm hGs hGsupp hGD
  refine ⟨∑' k, a k, τ₀⁻¹, fun R hR => ?_⟩
  have hRpos : 0 < R := lt_of_lt_of_le (inv_pos.2 hτ₀) hR
  have hτ : R⁻¹ ∈ Set.Icc (0 : ℝ) τ₀ :=
    ⟨(inv_pos.2 hRpos).le, by
      rw [inv_le_comm₀ hRpos hτ₀]; exact hR⟩
  obtain ⟨c, hcm, hca, hsum⟩ := hc ⟨R⁻¹, hτ⟩
  have hY : IsCompact (Prod.snd '' S) := hS.image continuous_snd
  have key := opNorm_le_of_expansion p q hp hq (K R) (fun x y => b x y R⁻¹) (Prod.snd '' S) hY M
    (hKm R) (fun x y => (hK R x y).1)
    (fun x y h => ⟨(x, y), (hK R x y).2 h, rfl⟩) e c a ha he he1 hcm hca
    (fun x y h => by
      obtain ⟨hx, hG⟩ := hGS ⟨R⁻¹, hτ⟩ x y ((hK R x y).2 h)
      have := hsum x y hx
      rw [hG] at this
      exact this)
  exact key.trans le_self_add

end OpNormBP
end TaoBR

theorem solution : type_of% @TaoBR.OpNormBP.opNorm_le_of_contDiff_dev := @TaoBR.OpNormBP.opNorm_le_of_contDiff_dev
