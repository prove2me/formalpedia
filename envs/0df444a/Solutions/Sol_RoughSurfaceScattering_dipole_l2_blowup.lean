-- Prove2me | solution 1 for RoughSurfaceScattering.dipole_l2_blowup
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:31:58.029963+00:00
-- url     : https://prove2.me/submissions/b525a595-3009-4eaf-a039-c7ec0b7dfae5

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic
import Theorems.Thm_RoughSurfaceScattering_cone_below_interface

open MeasureTheory Metric
open scoped Pointwise
open RoughSurfaceScattering

/-- `∇ₓΦ₀(x,z)·ν = -(1/2π) (x-z)·ν / |x-z|²` for `x ≠ z`. -/
lemma dipole0_formula (z ν x : R2) (hx : x ≠ z) :
    dipoleSource 0 z ν x =
      ((-(1 / (2 * Real.pi)) * (@inner ℝ R2 _ (x - z) ν / ‖x - z‖ ^ 2) : ℝ) : ℂ) := by
  have hy : x - z ≠ 0 := sub_ne_zero.mpr hx
  have hn : ‖x - z‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hy)
  have hfun : (fun x' : R2 => Phi 0 x' z) =
      fun x' => (((-(1 / (4 * Real.pi))) * Real.log (‖x' - z‖ ^ 2) : ℝ) : ℂ) := by
    funext x'
    simp only [Phi, if_true, one_div, Real.log_inv, Real.log_pow]
    push_cast
    ring
  have hsq : HasFDerivAt (fun x' : R2 => ‖x' - z‖ ^ 2)
      (2 • (innerSL ℝ (x - z)).comp (ContinuousLinearMap.id ℝ R2)) x :=
    ((hasFDerivAt_id x).sub_const z).norm_sq
  have hlog := (hsq.log hn).const_mul (-(1 / (4 * Real.pi)))
  have hc := Complex.ofRealCLM.hasFDerivAt.comp x hlog
  unfold dipoleSource
  rw [hfun]
  rw [show (fun x' : R2 => (((-(1 / (4 * Real.pi))) * Real.log (‖x' - z‖ ^ 2) : ℝ) : ℂ)) =
      Complex.ofRealCLM ∘ (fun x' => (-(1 / (4 * Real.pi))) * Real.log (‖x' - z‖ ^ 2)) from rfl,
    hc.fderiv]
  simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
    ContinuousLinearMap.smul_apply, innerSL_apply_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
    nsmul_eq_mul]
  congr 1
  field_simp
  ring

lemma normal_norm (f : ℝ → ℝ) (s : ℝ) : ‖normal f s‖ = 1 := by
  have hpos : 0 < 1 + deriv f s ^ 2 := by positivity
  have hpt : ‖pt (deriv f s) (-1)‖ = Real.sqrt (1 + deriv f s ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    simp [pt, Fin.sum_univ_two]
    ring_nf
  rw [normal, norm_smul, hpt, arcDen, norm_inv, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact inv_mul_cancel₀ (Real.sqrt_pos.mpr hpos).ne'

/-- The `k`-th dyadic piece `(1/2)^k • A₀` of the cone. -/
lemma mem_dyadic (n : R2) (ρ : ℝ) (k : ℕ) (v : R2)
    (hv : v ∈ ((1 / 2 : ℝ) ^ k) • {w : R2 | w ≠ 0 ∧ ρ / 2 ≤ ‖w‖ ∧ ‖w‖ < ρ ∧
      ‖w‖ ≤ 2 * @inner ℝ R2 _ w n}) :
    v ≠ 0 ∧ ρ / 2 * (1 / 2) ^ k ≤ ‖v‖ ∧ ‖v‖ < ρ * (1 / 2) ^ k ∧
      ‖v‖ ≤ 2 * @inner ℝ R2 _ v n := by
  obtain ⟨w, ⟨hw0, hw1, hw2, hw3⟩, rfl⟩ := hv
  have hc : (0 : ℝ) < (1 / 2) ^ k := by positivity
  rw [norm_smul, Real.norm_of_nonneg hc.le, real_inner_smul_left]
  refine ⟨smul_ne_zero hc.ne' hw0, by nlinarith, by nlinarith, by nlinarith⟩

theorem solution (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f) (s0 δ : ℝ) (hδ : 0 < δ)
    (D0 : Set R2) (hD0 : Metric.ball (gpt f s0) (2 * δ) ∩ Dminus f ⊆ D0) :
    ∀ C : ℝ, ∃ j : ℕ, 1 ≤ j ∧ ENNReal.ofReal C <
      l2Norm D0 (dipoleSource 0 (gpt f s0 - (δ / (j : ℝ)) • normal f s0) (normal f s0)) := by
  intro C
  set n := normal f s0 with hn
  set x0 := gpt f s0 with hx0
  have hn1 : ‖n‖ = 1 := normal_norm f s0
  have hnn : @inner ℝ R2 _ n n = 1 := by rw [real_inner_self_eq_norm_sq, hn1]; norm_num
  obtain ⟨r, hr, hcone⟩ := cone_below_interface f s0 (hf.1 s0)
  set ρ := min r (2 * δ) with hρ
  have hρpos : 0 < ρ := lt_min hr (by linarith)
  set A0 : Set R2 := {w : R2 | w ≠ 0 ∧ ρ / 2 ≤ ‖w‖ ∧ ‖w‖ < ρ ∧ ‖w‖ ≤ 2 * @inner ℝ R2 _ w n}
    with hA0
  have hA0m : MeasurableSet A0 := by
    have h1 : Measurable fun w : R2 => 2 * @inner ℝ R2 _ w n := by fun_prop
    exact (measurableSet_singleton (0 : R2)).compl.inter
      ((measurableSet_le measurable_const measurable_norm).inter
        ((measurableSet_lt measurable_norm measurable_const).inter
          (measurableSet_le measurable_norm h1)))
  -- `A₀` has positive, finite measure
  have hA0pos : 0 < volume A0 := by
    refine lt_of_lt_of_le (measure_ball_pos volume ((3 * ρ / 4) • n) (by positivity : 0 < ρ / 8))
      (measure_mono ?_)
    intro w hw
    rw [mem_ball, dist_eq_norm] at hw
    have hstar : ‖(3 * ρ / 4) • n‖ = 3 * ρ / 4 := by
      rw [norm_smul, hn1, Real.norm_of_nonneg (by positivity)]; ring
    have hup : ‖w‖ ≤ ‖w - (3 * ρ / 4) • n‖ + 3 * ρ / 4 := by
      have := norm_sub_norm_le w ((3 * ρ / 4) • n)
      rw [hstar] at this
      linarith
    have hlow : 3 * ρ / 4 ≤ ‖w‖ + ‖w - (3 * ρ / 4) • n‖ := by
      have := norm_sub_norm_le ((3 * ρ / 4) • n) w
      rw [hstar, norm_sub_rev] at this
      linarith
    have hin : @inner ℝ R2 _ w n = 3 * ρ / 4 + @inner ℝ R2 _ (w - (3 * ρ / 4) • n) n := by
      rw [inner_sub_left, real_inner_smul_left, hnn]; ring
    have hcs : |@inner ℝ R2 _ (w - (3 * ρ / 4) • n) n| ≤ ‖w - (3 * ρ / 4) • n‖ := by
      have := abs_real_inner_le_norm (w - (3 * ρ / 4) • n) n
      rwa [hn1, mul_one] at this
    have hw0 : w ≠ 0 := by
      rintro rfl
      simp at hlow hw
      linarith
    refine ⟨hw0, by linarith, by linarith, ?_⟩
    rw [hin]
    have := (abs_le.mp hcs).1
    linarith
  have hA0fin : volume A0 ≠ ⊤ := by
    refine ne_top_of_le_ne_top (measure_ball_lt_top (x := (0 : R2)) (r := ρ)).ne (measure_mono ?_)
    intro w hw
    simpa using hw.2.2.1
  -- the dyadic pieces, translated to `x₀`
  let A : ℕ → Set R2 := fun k => ((1 / 2 : ℝ) ^ k) • A0
  let B : ℕ → Set R2 := fun k => (fun x => x - x0) ⁻¹' A k
  have hAm : ∀ k, MeasurableSet (A k) := fun k =>
    hA0m.const_smul₀ _
  have hBm : ∀ k, MeasurableSet (B k) := fun k =>
    (hAm k).preimage (measurable_id.sub_const x0)
  have hBvol : ∀ k, volume (B k) = ENNReal.ofReal (((1 / 2 : ℝ) ^ k) ^ 2) * volume A0 := by
    intro k
    rw [(measurePreserving_sub_right volume x0).measure_preimage (hAm k).nullMeasurableSet]
    simp only [A]
    rw [Measure.addHaar_smul, finrank_euclideanSpace_fin, abs_of_nonneg (by positivity)]
  have hBsub : ∀ k, B k ⊆ D0 := by
    intro k x hx
    obtain ⟨hv0, -, hv2, hv3⟩ := mem_dyadic n ρ k (x - x0) hx
    have hk : ρ * (1 / 2 : ℝ) ^ k ≤ ρ := by
      have : (1 / 2 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      nlinarith
    have hvr : ‖x - x0‖ < r := lt_of_lt_of_le hv2 (hk.trans (min_le_left _ _))
    have hvd : ‖x - x0‖ < 2 * δ := lt_of_lt_of_le hv2 (hk.trans (min_le_right _ _))
    apply hD0
    refine ⟨by rwa [mem_ball, dist_eq_norm], ?_⟩
    have := hcone (x - x0) hv0 hvr hv3
    rwa [add_sub_cancel] at this
  have hBdisj : ∀ N : ℕ, Pairwise (Function.onFun Disjoint fun k : Fin N => B k) := by
    intro N k l hkl
    rw [Function.onFun, Set.disjoint_left]
    intro x hxk hxl
    obtain ⟨-, hk1, hk2, -⟩ := mem_dyadic n ρ k (x - x0) hxk
    obtain ⟨-, hl1, hl2, -⟩ := mem_dyadic n ρ l (x - x0) hxl
    have e1 : (1 / 2 : ℝ) ^ ((k : ℕ) + 1) < (1 / 2) ^ (l : ℕ) := by
      rw [pow_succ]; nlinarith
    have e2 : (1 / 2 : ℝ) ^ ((l : ℕ) + 1) < (1 / 2) ^ (k : ℕ) := by
      rw [pow_succ]; nlinarith
    rw [pow_lt_pow_iff_right_of_lt_one₀ (by norm_num) (by norm_num)] at e1 e2
    exact hkl (Fin.ext (by omega))
  -- the constant gained from each dyadic piece
  set κ : ENNReal := ENNReal.ofReal (1 / (64 * Real.pi ^ 2 * ρ ^ 2)) * volume A0 with hκ
  have hκ0 : κ ≠ 0 := by
    rw [hκ]
    exact mul_ne_zero (by simp; positivity) hA0pos.ne'
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_mul_gt hκ0
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 2) ENNReal.ofReal_ne_top :
      ENNReal.ofReal C ^ (2 : ℝ) ≠ ⊤)
  -- the source index
  set j : ℕ := ⌈δ * 2 ^ (N + 1) / ρ⌉₊ + 1 with hj
  have hj1 : 1 ≤ j := by omega
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj1
  have ht : δ / (j : ℝ) ≤ ρ / 2 ^ (N + 1) := by
    have hge : δ * 2 ^ (N + 1) / ρ ≤ j := by
      have := Nat.le_ceil (δ * 2 ^ (N + 1) / ρ)
      have h2 : ((⌈δ * 2 ^ (N + 1) / ρ⌉₊ : ℕ) : ℝ) ≤ j := by
        rw [hj]; push_cast; linarith
      linarith
    rw [div_le_iff₀ hρpos] at hge
    rw [div_le_div_iff₀ hjpos (by positivity)]
    linarith
  refine ⟨j, hj1, ?_⟩
  set t := δ / (j : ℝ) with htdef
  have htpos : 0 < t := by positivity
  -- pointwise lower bound on the `k`-th piece
  have hpt : ∀ k : ℕ, k < N → ∀ x ∈ B k,
      ENNReal.ofReal (1 / (64 * Real.pi ^ 2 * ρ ^ 2 * ((1 / 2 : ℝ) ^ k) ^ 2)) ≤
        ‖dipoleSource 0 (x0 - t • n) n x‖ₑ ^ (2 : ℝ) := by
    intro k hk x hx
    obtain ⟨hv0, hv1, hv2, hv3⟩ := mem_dyadic n ρ k (x - x0) hx
    have hc : (0 : ℝ) < (1 / 2) ^ k := by positivity
    have htk : t ≤ ρ / 2 * (1 / 2) ^ k := by
      have hNk : (1 / 2 : ℝ) ^ N ≤ (1 / 2) ^ k :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hk.le
      have : ρ / 2 ^ (N + 1) = ρ / 2 * (1 / 2) ^ N := by
        rw [pow_succ, one_div_pow]; field_simp
      rw [this] at ht
      nlinarith
    set y := x - (x0 - t • n) with hy
    have hyv : y = (x - x0) + t • n := by rw [hy]; abel
    have hiy : @inner ℝ R2 _ y n = @inner ℝ R2 _ (x - x0) n + t := by
      rw [hyv, inner_add_left, real_inner_smul_left, hnn, mul_one]
    have hny : ‖y‖ ≤ ‖x - x0‖ + t := by
      rw [hyv]
      calc ‖(x - x0) + t • n‖ ≤ ‖x - x0‖ + ‖t • n‖ := norm_add_le _ _
        _ = ‖x - x0‖ + t := by rw [norm_smul, hn1, Real.norm_of_nonneg htpos.le, mul_one]
    have hvpos : 0 < ‖x - x0‖ := norm_pos_iff.mpr hv0
    have hiypos : ‖y‖ / 2 ≤ @inner ℝ R2 _ y n := by rw [hiy]; linarith
    have hypos : 0 < ‖y‖ := by
      rcases eq_or_lt_of_le (norm_nonneg y) with h | h
      · exfalso
        have : y = 0 := norm_eq_zero.mp h.symm
        rw [this, inner_zero_left] at hiy
        linarith
      · exact h
    have hxne : x ≠ x0 - t • n := by
      intro h; rw [hy, h, sub_self, norm_zero] at hypos; exact lt_irrefl _ hypos
    have hy2 : ‖y‖ ≤ 2 * ‖x - x0‖ := by linarith
    rw [dipole0_formula _ _ _ hxne, ← hy]
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    rw [Complex.norm_real, Real.norm_eq_abs, Real.rpow_two, sq_abs]
    have hpi : 0 < Real.pi := Real.pi_pos
    have hlow : 1 / (8 * Real.pi * (ρ * (1 / 2) ^ k)) ≤
        1 / (2 * Real.pi) * (@inner ℝ R2 _ y n / ‖y‖ ^ 2) := by
      have h1 : 1 / (4 * Real.pi * ‖y‖) ≤ 1 / (2 * Real.pi) * (@inner ℝ R2 _ y n / ‖y‖ ^ 2) := by
        rw [div_le_iff₀ (by positivity)]
        have : 1 / (2 * Real.pi) * (@inner ℝ R2 _ y n / ‖y‖ ^ 2) * (4 * Real.pi * ‖y‖) =
            2 * @inner ℝ R2 _ y n / ‖y‖ := by field_simp; ring
        rw [this, le_div_iff₀ hypos]
        linarith
      refine le_trans ?_ h1
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    have hlowpos : 0 ≤ 1 / (8 * Real.pi * (ρ * (1 / 2) ^ k)) := by positivity
    calc 1 / (64 * Real.pi ^ 2 * ρ ^ 2 * ((1 / 2 : ℝ) ^ k) ^ 2)
        = (1 / (8 * Real.pi * (ρ * (1 / 2) ^ k))) ^ 2 := by field_simp; ring
      _ ≤ (1 / (2 * Real.pi) * (@inner ℝ R2 _ y n / ‖y‖ ^ 2)) ^ 2 :=
          pow_le_pow_left₀ hlowpos hlow 2
      _ = (-(1 / (2 * Real.pi)) * (@inner ℝ R2 _ y n / ‖y‖ ^ 2)) ^ 2 := by ring
  -- integral over each piece
  have hpiece : ∀ k : ℕ, k < N →
      κ ≤ ∫⁻ x in B k, ‖dipoleSource 0 (x0 - t • n) n x‖ₑ ^ (2 : ℝ) := by
    intro k hk
    calc κ = ENNReal.ofReal (1 / (64 * Real.pi ^ 2 * ρ ^ 2 * ((1 / 2 : ℝ) ^ k) ^ 2)) *
          volume (B k) := by
          rw [hBvol, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), hκ]
          congr 2
          have : ((1 / 2 : ℝ) ^ k) ^ 2 ≠ 0 := by positivity
          field_simp
      _ = ∫⁻ x in B k, ENNReal.ofReal (1 / (64 * Real.pi ^ 2 * ρ ^ 2 * ((1 / 2 : ℝ) ^ k) ^ 2)) :=
          (setLIntegral_const _ _).symm
      _ ≤ _ := setLIntegral_mono' (hBm k) (hpt k hk)
  -- sum over the pieces
  have hsum : (N : ENNReal) * κ ≤
      ∫⁻ x in D0, ‖dipoleSource 0 (x0 - t • n) n x‖ₑ ^ (2 : ℝ) := by
    calc (N : ENNReal) * κ = ∑ k : Fin N, κ := by simp
      _ ≤ ∑ k : Fin N, ∫⁻ x in B k, ‖dipoleSource 0 (x0 - t • n) n x‖ₑ ^ (2 : ℝ) :=
          Finset.sum_le_sum fun k _ => hpiece k k.isLt
      _ = ∫⁻ x in ⋃ k : Fin N, B k, ‖dipoleSource 0 (x0 - t • n) n x‖ₑ ^ (2 : ℝ) := by
          rw [lintegral_iUnion (s := fun k : Fin N => B k) (fun k => hBm k) (hBdisj N),
            tsum_fintype]
      _ ≤ _ := lintegral_mono_set (Set.iUnion_subset fun k => hBsub k)
  -- conclusion
  unfold l2Norm
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  calc ENNReal.ofReal C = (ENNReal.ofReal C ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
        rw [one_div, ENNReal.rpow_rpow_inv (by norm_num)]
    _ < (∫⁻ x in D0, ‖dipoleSource 0 (x0 - t • n) n x‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
        ENNReal.rpow_lt_rpow (hN.trans_le hsum) (by norm_num)
