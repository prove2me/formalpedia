-- Prove2me | solution 1 for QuantileSPQO.Rate.lemma_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T20:26:03.448981+00:00
-- url     : https://prove2.me/submissions/dcc489b6-9d27-4599-be57-4becc4966de4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_QuantileSPQO_Rate_Setting
import Theorems.Thm_QuantileSPQO_Rate_lemma_1

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal RealInnerProductSpace

namespace SPQOL2Aux
open QuantileSPQO.Rate

lemma rem_bound {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (F : V → ℝ) (p y : V)
    (δ K : ℝ) (hy : ‖y‖ < δ) (hK : ∀ x ∈ Metric.ball p δ, ‖iteratedFDeriv ℝ 3 F x‖ ≤ K) :
    ‖∫ t in (0:ℝ)..1, (1 - t) ^ 2 • iteratedFDeriv ℝ (2 + 1) F (p + t • y) (fun _ => y)‖
      ≤ K * ‖y‖ ^ 3 := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1)
    (C := K * ‖y‖ ^ 3)
    (f := fun t => (1 - t) ^ 2 • iteratedFDeriv ℝ (2 + 1) F (p + t • y) (fun _ => y)) (by
      intro t ht
      rw [Set.uIoc_of_le zero_le_one] at ht
      have hmem : p + t • y ∈ Metric.ball p δ := by
        rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_pos ht.1]
        nlinarith [norm_nonneg y, ht.2]
      have h1 := hK _ hmem
      have h2 := (iteratedFDeriv ℝ (2 + 1) F (p + t • y)).le_opNorm (fun _ => y)
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h2
      have hK0 : 0 ≤ K := (norm_nonneg _).trans h1
      have h3 : ‖iteratedFDeriv ℝ (2 + 1) F (p + t • y) (fun _ => y)‖ ≤ K * ‖y‖ ^ 3 :=
        h2.trans (mul_le_mul_of_nonneg_right h1 (by positivity))
      have h4 : |1 - t| ^ 2 ≤ 1 := by
        rw [abs_of_nonneg (by linarith [ht.2])]
        nlinarith [ht.1, ht.2]
      rw [norm_smul, norm_pow, Real.norm_eq_abs]
      calc |1 - t| ^ 2 * ‖iteratedFDeriv ℝ (2 + 1) F (p + t • y) (fun _ => y)‖
          ≤ 1 * (K * ‖y‖ ^ 3) := mul_le_mul h4 h3 (norm_nonneg _) zero_le_one
        _ = K * ‖y‖ ^ 3 := one_mul _)
  simpa using this

lemma taylor3 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (F : V → ℝ) (p h : V)
    (δ K : ℝ) (hh : ‖h‖ < δ) (hC : ContDiffOn ℝ 3 F (Metric.ball p δ))
    (hK : ∀ x ∈ Metric.ball p δ, ‖iteratedFDeriv ℝ 3 F x‖ ≤ K) :
    |F (p + h) - F (p - h) - 2 * fderiv ℝ F p h| ≤ K * ‖h‖ ^ 3 := by
  have hUo : IsOpen (Metric.ball p δ) := Metric.isOpen_ball
  have hcd : ∀ y : V, ‖y‖ < δ → ∀ t ∈ Set.Icc (0:ℝ) 1, ContDiffAt ℝ (2 + 1) F (p + t • y) := by
    intro y hy t ht
    have hmem : p + t • y ∈ Metric.ball p δ := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg ht.1]
      nlinarith [norm_nonneg y, ht.2]
    exact (hC.contDiffAt (hUo.mem_nhds hmem))
  have hneg : ‖-h‖ < δ := by rwa [norm_neg]
  have TP := map_add_eq_sum_add_integral_iteratedFDeriv (n := 2) (hcd h hh)
  have TM := map_add_eq_sum_add_integral_iteratedFDeriv (n := 2) (hcd (-h) hneg)
  have RP := rem_bound F p h δ K hh hK
  have RM := rem_bound F p (-h) δ K hneg hK
  rw [norm_neg] at RM
  set IP := ∫ t in (0:ℝ)..1, (1 - t) ^ 2 • iteratedFDeriv ℝ (2 + 1) F (p + t • h) (fun _ => h)
  set IM := ∫ t in (0:ℝ)..1, (1 - t) ^ 2 • iteratedFDeriv ℝ (2 + 1) F (p + t • (-h)) (fun _ => -h)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.factorial,
    Nat.cast_one, inv_one, one_smul, iteratedFDeriv_zero_apply, iteratedFDeriv_one_apply,
    smul_eq_mul] at TP TM
  have e2 : iteratedFDeriv ℝ 2 F p (fun _ => -h) = iteratedFDeriv ℝ 2 F p (fun _ => h) := by
    rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
    simp
  rw [e2, ← sub_eq_add_neg] at TM
  have e1 : fderiv ℝ F p (-h) = -fderiv ℝ F p h := map_neg _ _
  rw [e1] at TM
  have : F (p + h) - F (p - h) - 2 * fderiv ℝ F p h = (IP - IM) / 2 := by
    rw [TP, TM]; push_cast; ring
  rw [this, abs_div, abs_two]
  have hIP : |IP| ≤ K * ‖h‖ ^ 3 := by rw [← Real.norm_eq_abs]; exact RP
  have hIM : |IM| ≤ K * ‖h‖ ^ 3 := by rw [← Real.norm_eq_abs]; exact RM
  have := abs_sub IP IM
  linarith

lemma L_split {d : ℕ} (M : Model d)
    (hdens : ∀ y θ, HasDerivAt (fun y' => cdf M y' θ) (M.dens y θ) y) (q : ℝ) (θ : E d)
    (hF : DifferentiableAt ℝ (cdfU M) (q, θ)) (a : ℝ) (v : E d) :
    fderiv ℝ (cdfU M) (q, θ) (a, v) = a * M.dens q θ + ⟪gradθ M q θ, v⟫ := by
  set L := fderiv ℝ (cdfU M) (q, θ) with hL
  have hFd : HasFDerivAt (cdfU M) L (q, θ) := hF.hasFDerivAt
  have hy : HasFDerivAt (fun y => cdfU M (y, θ)) (L.comp (ContinuousLinearMap.inl ℝ ℝ (E d))) q :=
    HasFDerivAt.comp (g := cdfU M) (f := fun y => (y, θ)) q hFd
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) q θ)
  have hy' : HasDerivAt (fun y => cdfU M (y, θ)) (M.dens q θ) q := hdens q θ
  have hd1 : L (1, 0) = M.dens q θ := by
    have := hy'.hasFDerivAt.unique hy
    have h2 := congrArg (fun T : ℝ →L[ℝ] ℝ => T 1) this
    simp at h2
    exact h2.symm
  have hθ : HasFDerivAt (fun θ' => cdf M q θ') (L.comp (ContinuousLinearMap.inr ℝ ℝ (E d))) θ :=
    HasFDerivAt.comp (g := cdfU M) (f := fun θ' => (q, θ')) θ hFd
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) q θ)
  have hg : ⟪gradθ M q θ, v⟫ = L (0, v) := by
    simp only [gradθ, gradient, hθ.fderiv, InnerProductSpace.toDual_symm_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
  have hsplit : ((a, v) : ℝ × E d) = a • ((1 : ℝ), (0 : E d)) + ((0 : ℝ), v) := by
    ext <;> simp
  rw [hsplit, map_add, map_smul, smul_eq_mul, hd1, hg]

lemma sgn_sum {d : ℕ} (i j : Fin d) :
    ∑ b : Fin d → Bool, (if b j then (1:ℝ) else -1) * (if b i then (1:ℝ) else -1)
      = if j = i then (2 : ℝ) ^ d else 0 := by
  split_ifs with hji
  · subst hji
    have : ∀ b : Fin d → Bool, (if b j then (1:ℝ) else -1) * (if b j then (1:ℝ) else -1) = 1 := by
      intro b; split_ifs <;> norm_num
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    push_cast; ring
  · set f : (Fin d → Bool) → ℝ :=
      fun b => (if b j then (1:ℝ) else -1) * (if b i then (1:ℝ) else -1) with hf
    have hinv : Function.Involutive (fun b : Fin d → Bool => Function.update b j (!(b j))) := by
      intro b
      funext m
      by_cases hm : m = j
      · subst hm; simp
      · simp [Function.update_of_ne hm]
    have hflip : ∀ b, f (Function.update b j (!(b j))) = -f b := by
      intro b
      have hij : i ≠ j := fun h => hji h.symm
      simp only [hf, Function.update_self, Function.update_of_ne hij]
      cases b j <;> cases b i <;> simp
    have hS := Equiv.sum_comp hinv.toPerm f
    simp only [Function.Involutive.coe_toPerm, hflip, Finset.sum_neg_distrib] at hS
    show ∑ b, f b = 0
    linarith

lemma sum_sign {d : ℕ} (v : E d) :
    ∑ b : Fin d → Bool, ⟪v, signVec b⟫ • signVec b = ((2 : ℝ) ^ d) • v := by
  ext i
  simp only [PiLp.smul_apply, smul_eq_mul, signVec, PiLp.toLp_apply, WithLp.ofLp_sum,
    Finset.sum_apply, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have : ∀ j : Fin d, ∑ b : Fin d → Bool,
      (if b j then (1:ℝ) else -1) * v j * (if b i then (1:ℝ) else -1)
        = v j * (if j = i then (2 : ℝ) ^ d else 0) := by
    intro j
    rw [← sgn_sum i j, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro b _; ring
  rw [Finset.sum_congr rfl (fun j _ => this j)]
  simp [mul_comm]

lemma norm_signVec {d : ℕ} (b : Fin d → Bool) : ‖signVec b‖ = Real.sqrt d := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp only [signVec, PiLp.toLp_apply, Real.norm_eq_abs]
  have : ∀ i, |(if b i then (1:ℝ) else -1)| ^ 2 = 1 := by
    intro i; split_ifs <;> norm_num
  simp [this]

lemma bias_bound {d : ℕ} (hd : 0 < d) (M : Model d)
    (hdens : ∀ y θ, HasDerivAt (fun y' => cdf M y' θ) (M.dens y θ) y) (c : ℕ → ℝ) (k : ℕ)
    (q : ℝ) (D θ : E d) (δ K : ℝ) (hck : 0 < c k) (hsmall : c k * d < δ)
    (hC3 : ContDiffOn ℝ 3 (cdfU M) (Metric.ball (q, θ) δ))
    (hK : ∀ x ∈ Metric.ball (q, θ) δ, ‖iteratedFDeriv ℝ 3 (cdfU M) x‖ ≤ K) :
    ‖bias M c k q D θ‖ ≤ mfac D * (K * (d : ℝ) ^ 3 * Real.sqrt d) * c k ^ 2 := by
  set m := mfac D with hm
  have hm1 : 1 ≤ m := le_max_left _ _
  have hm0 : 0 < m := by linarith
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd0 : 0 < Real.sqrt d := Real.sqrt_pos.2 (by linarith)
  have hsd1 : Real.sqrt d ≤ d := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hsdsq : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt (by linarith)
  have hmD : ‖D‖ ≤ m * Real.sqrt d := by
    have : ‖D‖ / Real.sqrt d ≤ m := le_max_right _ _
    rwa [div_le_iff₀ hsd0] at this
  set cb := cbar c k D with hcb
  have hcbeq : cb = c k / m := rfl
  have hcb0 : 0 < cb := by rw [hcbeq]; positivity
  have hmcb : m * cb = c k := by rw [hcbeq]; field_simp
  set p : ℝ × E d := (q, θ) with hp
  have hpball : p ∈ Metric.ball p δ := by
    have : 0 ≤ c k * d := by positivity
    exact Metric.mem_ball_self (by linarith)
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK p hpball)
  have hdiff : DifferentiableAt ℝ (cdfU M) p :=
    (hC3.differentiableOn (by norm_num)).differentiableAt (Metric.isOpen_ball.mem_nhds hpball)
  set s : (Fin d → Bool) → E d := fun b => signVec b with hs
  set hv : (Fin d → Bool) → ℝ × E d := fun b => (cb * ⟪D, s b⟫, cb • s b) with hhv
  have hnorm_h : ∀ b, ‖hv b‖ ≤ c k * d := by
    intro b
    have hsb : ‖s b‖ = Real.sqrt d := norm_signVec b
    rw [hhv, Prod.norm_mk]
    apply max_le
    · rw [Real.norm_eq_abs, abs_mul, abs_of_pos hcb0]
      have h1 : |⟪D, s b⟫| ≤ ‖D‖ * ‖s b‖ := abs_real_inner_le_norm _ _
      rw [hsb] at h1
      calc cb * |⟪D, s b⟫| ≤ cb * (‖D‖ * Real.sqrt d) := mul_le_mul_of_nonneg_left h1 hcb0.le
        _ ≤ cb * (m * Real.sqrt d * Real.sqrt d) := by
            gcongr
        _ = c k * d := by rw [mul_assoc m, hsdsq, ← mul_assoc, mul_comm cb m, hmcb]
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hcb0, hsb]
      have : cb ≤ c k := by
        rw [hcbeq]; exact div_le_self hck.le hm1
      exact mul_le_mul this hsd1 hsd0.le hck.le
  set w : E d := M.dens q θ • D + gradθ M q θ with hw
  set rem : (Fin d → Bool) → ℝ := fun b =>
    cdfU M (p + hv b) - cdfU M (p - hv b) - 2 * fderiv ℝ (cdfU M) p (hv b) with hrem
  have hremb : ∀ b, |rem b| ≤ K * (c k * d) ^ 3 := by
    intro b
    have h1 := taylor3 (cdfU M) p (hv b) δ K (lt_of_le_of_lt (hnorm_h b) hsmall) hC3 hK
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ hK0)
    exact pow_le_pow_left₀ (norm_nonneg _) (hnorm_h b) 3
  have hLh : ∀ b, fderiv ℝ (cdfU M) p (hv b) = cb * ⟪w, s b⟫ := by
    intro b
    rw [hhv, hp, L_split M hdens q θ hdiff, hw, inner_add_left, real_inner_smul_left,
      real_inner_smul_right]
    ring
  have hterm : ∀ b, (-cdf M (q + cbar c k D * ⟪D, signVec b⟫) (θ + cbar c k D • signVec b) +
        cdf M (q - cbar c k D * ⟪D, signVec b⟫) (θ - cbar c k D • signVec b)) • signVec b
      = (-(2 * cb)) • (⟪w, s b⟫ • s b) - rem b • s b := by
    intro b
    have e1 : cdf M (q + cbar c k D * ⟪D, signVec b⟫) (θ + cbar c k D • signVec b)
        = cdfU M (p + hv b) := rfl
    have e2 : cdf M (q - cbar c k D * ⟪D, signVec b⟫) (θ - cbar c k D • signVec b)
        = cdfU M (p - hv b) := rfl
    rw [e1, e2, smul_smul, ← sub_smul]
    congr 1
    simp only [hrem, hLh b]
    ring
  set R : E d := ∑ b, rem b • s b with hR
  have hsum : ∑ b : Fin d → Bool, (-cdf M (q + cbar c k D * ⟪D, signVec b⟫)
        (θ + cbar c k D • signVec b) +
        cdf M (q - cbar c k D * ⟪D, signVec b⟫) (θ - cbar c k D • signVec b)) • signVec b
      = (-(2 * cb)) • (((2 : ℝ) ^ d) • w) - R := by
    rw [Finset.sum_congr rfl (fun b _ => hterm b), Finset.sum_sub_distrib, ← Finset.smul_sum]
    congr 2
    exact sum_sign w
  have key : bias M c k q D θ =
      (m / (2 * c k) * ((2 ^ d : ℝ)⁻¹ * (-(2 * cb)) * 2 ^ d) + 1) • w
        - (m / (2 * c k) * (2 ^ d : ℝ)⁻¹) • R := by
    simp only [bias]
    rw [hsum]
    module
  have hcoef : m / (2 * c k) * ((2 ^ d : ℝ)⁻¹ * (-(2 * cb)) * 2 ^ d) + 1 = 0 := by
    rw [hcbeq]; field_simp; ring
  rw [key, hcoef, zero_smul, zero_sub, norm_neg, norm_smul]
  have hRn : ‖R‖ ≤ (2 : ℝ) ^ d * (K * (c k * d) ^ 3 * Real.sqrt d) := by
    calc ‖R‖ ≤ ∑ b, ‖rem b • s b‖ := norm_sum_le _ _
      _ ≤ ∑ _b : Fin d → Bool, K * (c k * d) ^ 3 * Real.sqrt d := by
          apply Finset.sum_le_sum
          intro b _
          rw [norm_smul, Real.norm_eq_abs, norm_signVec]
          exact mul_le_mul_of_nonneg_right (hremb b) hsd0.le
      _ = (2 : ℝ) ^ d * (K * (c k * d) ^ 3 * Real.sqrt d) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
            Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
  have hcoefn : ‖m / (2 * c k) * (2 ^ d : ℝ)⁻¹‖ = m / (2 * c k) * (2 ^ d : ℝ)⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [hcoefn]
  calc m / (2 * c k) * (2 ^ d : ℝ)⁻¹ * ‖R‖
      ≤ m / (2 * c k) * (2 ^ d : ℝ)⁻¹ * ((2 : ℝ) ^ d * (K * (c k * d) ^ 3 * Real.sqrt d)) :=
        mul_le_mul_of_nonneg_left hRn (by positivity)
    _ = m * (K * (d : ℝ) ^ 3 * Real.sqrt d) * c k ^ 2 / 2 := by
        field_simp
    _ ≤ m * (K * (d : ℝ) ^ 3 * Real.sqrt d) * c k ^ 2 := by
        have : 0 ≤ m * (K * (d : ℝ) ^ 3 * Real.sqrt d) * c k ^ 2 := by positivity
        linarith

lemma enorm_le_of_sq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ℝ≥0∞) (t : ℝ) (ht : 0 < t)
    (h : ∫⁻ ω, f ω ^ 2 ∂P ≤ ENNReal.ofReal (t ^ 2)) :
    ∫⁻ ω, f ω ∂P ≤ ENNReal.ofReal t := by
  have hpt : ∀ x : ℝ≥0∞, x ≤ x ^ 2 * ENNReal.ofReal (1 / (2 * t)) + ENNReal.ofReal (t / 2) := by
    intro x
    by_cases hx : x = ⊤
    · subst hx
      have : ENNReal.ofReal (1 / (2 * t)) ≠ 0 := by
        rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
      rw [ENNReal.top_pow two_ne_zero, ENNReal.top_mul this, top_add]
    · have hx' : x = ENNReal.ofReal x.toReal := (ENNReal.ofReal_toReal hx).symm
      set r := x.toReal
      have hr : 0 ≤ r := ENNReal.toReal_nonneg
      rw [hx', ← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have : r ^ 2 * (1 / (2 * t)) + t / 2 - r = (r - t) ^ 2 / (2 * t) := by
        field_simp; ring
      have : 0 ≤ (r - t) ^ 2 / (2 * t) := by positivity
      linarith
  calc ∫⁻ ω, f ω ∂P ≤ ∫⁻ ω, (f ω ^ 2 * ENNReal.ofReal (1 / (2 * t)) + ENNReal.ofReal (t / 2)) ∂P :=
        lintegral_mono (fun ω => hpt (f ω))
    _ = (∫⁻ ω, f ω ^ 2 ∂P) * ENNReal.ofReal (1 / (2 * t)) + ENNReal.ofReal (t / 2) := by
        rw [lintegral_add_right _ measurable_const, lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
        simp
    _ ≤ ENNReal.ofReal (t ^ 2) * ENNReal.ofReal (1 / (2 * t)) + ENNReal.ofReal (t / 2) := by
        gcongr
    _ = ENNReal.ofReal t := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; field_simp; ring

end SPQOL2Aux

open QuantileSPQO.Rate SPQOL2Aux

theorem solution {Ω : Type*} [m0 : MeasurableSpace Ω] {d : ℕ} (hd : 0 < d)
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (M : Model d) (Θ : Set (E d)) (Proj : E d → E d) (I : Set ℝ) (Pq : ℝ → ℝ)
    (α β γ c : ℕ → ℝ) (R : Run Ω d)
    (hΘ : IsConstraintSet Θ) (hM : IsQuantileModel M Θ)
    (hProj : SpectralProjGrad.Shared.IsProjOnto Θ Proj)
    (hrun : IsSPQORun P ℱ M Θ Proj I Pq α β γ c R)
    (hA1 : A1 P M R) (hA2 : A2 P ℱ R) (hA3a : A3a β c) :
    (∀ᵐ ω ∂P, ∃ C : ℝ, ∀ᶠ k in atTop,
      ‖bias M c k (R.q k ω) (R.D k ω) (R.θ k ω)‖ ≤ C * c k ^ 2) ∧
    (∃ C : ℝ, ∀ᶠ k in atTop,
      ∫⁻ ω, ‖bias M c k (R.q k ω) (R.D k ω) (R.θ k ω)‖ₑ ∂P ≤ ENNReal.ofReal (C * c k ^ 2)) := by
  obtain ⟨hsup, hbdd⟩ := lemma_1 hd P ℱ M Θ Proj I Pq α β γ c R hΘ hM hProj hrun hA1 hA2 hA3a
  obtain ⟨δ, hδ, K, ε, hε, hA1ae⟩ := hA1
  have hc0 : ∀ k, 0 < c k := fun k => (hA3a.1 k).2
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd0 : 0 < Real.sqrt d := Real.sqrt_pos.2 (by linarith)
  have hsmall : ∀ᶠ k in atTop, c k * d < δ := by
    have := hA3a.2.1.mul_const (d : ℝ)
    rw [zero_mul] at this
    exact this.eventually (gt_mem_nhds hδ)
  set K' := max K 0 with hK'
  set Kp := K' * (d : ℝ) ^ 3 * Real.sqrt d with hKp
  have hKp0 : 0 ≤ Kp := by positivity
  have hpt : ∀ᵐ ω ∂P, ∀ k, c k * d < δ →
      ‖bias M c k (R.q k ω) (R.D k ω) (R.θ k ω)‖ ≤ mfac (R.D k ω) * Kp * c k ^ 2 := by
    filter_upwards [hA1ae] with ω hω k hk
    exact bias_bound hd M hM.hasDens c k _ _ _ δ K' (hc0 k) hk (hω k).1
      (fun x hx => ((hω k).2 x hx).2.1.trans (le_max_left _ _))
  refine ⟨?_, ?_⟩
  · filter_upwards [hpt, hbdd] with ω h1 hB
    obtain ⟨B, hB⟩ := hB
    refine ⟨max 1 (B / Real.sqrt d) * Kp, ?_⟩
    filter_upwards [hsmall] with k hk
    refine (h1 k hk).trans ?_
    have hDk : ‖R.D k ω‖ ≤ B := hB ⟨k, rfl⟩
    have hm : mfac (R.D k ω) ≤ max 1 (B / Real.sqrt d) :=
      max_le_max le_rfl (div_le_div_of_nonneg_right hDk hsd0.le)
    have := sq_nonneg (c k)
    nlinarith [mul_le_mul_of_nonneg_right hm hKp0]
  · set S := ⨆ k, ∫⁻ ω, ‖R.D k ω‖ₑ ^ 2 ∂P with hS
    set t := S.toReal + 1 with ht
    have ht0 : 0 < t := by positivity
    have hDint : ∀ k, ∫⁻ ω, ‖R.D k ω‖ₑ ∂P ≤ ENNReal.ofReal t := by
      intro k
      apply enorm_le_of_sq P _ t ht0
      calc ∫⁻ ω, ‖R.D k ω‖ₑ ^ 2 ∂P ≤ S := le_iSup (fun k => ∫⁻ ω, ‖R.D k ω‖ₑ ^ 2 ∂P) k
        _ = ENNReal.ofReal S.toReal := (ENNReal.ofReal_toReal hsup.ne).symm
        _ ≤ ENNReal.ofReal (t ^ 2) := by
            apply ENNReal.ofReal_le_ofReal
            have : 0 ≤ S.toReal := ENNReal.toReal_nonneg
            nlinarith
    refine ⟨Kp * (1 + t / Real.sqrt d), ?_⟩
    filter_upwards [hsmall] with k hk
    have hck2 : 0 ≤ Kp * c k ^ 2 := by positivity
    calc ∫⁻ ω, ‖bias M c k (R.q k ω) (R.D k ω) (R.θ k ω)‖ₑ ∂P
        ≤ ∫⁻ ω, ENNReal.ofReal (Kp * c k ^ 2) *
            (1 + ENNReal.ofReal (1 / Real.sqrt d) * ‖R.D k ω‖ₑ) ∂P := by
          apply lintegral_mono_ae
          filter_upwards [hpt] with ω hω
          have h1 := hω k hk
          have hm : mfac (R.D k ω) ≤ 1 + ‖R.D k ω‖ * (1 / Real.sqrt d) := by
            apply max_le
            · have : 0 ≤ ‖R.D k ω‖ * (1 / Real.sqrt d) := by positivity
              linarith
            · rw [div_eq_mul_one_div]; linarith
          rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (by positivity),
            ← ENNReal.ofReal_mul hck2]
          apply ENNReal.ofReal_le_ofReal
          calc ‖bias M c k (R.q k ω) (R.D k ω) (R.θ k ω)‖ ≤ mfac (R.D k ω) * Kp * c k ^ 2 := h1
            _ = Kp * c k ^ 2 * mfac (R.D k ω) := by ring
            _ ≤ Kp * c k ^ 2 * (1 + 1 / Real.sqrt d * ‖R.D k ω‖) := by
                apply mul_le_mul_of_nonneg_left _ hck2
                linarith
      _ = ENNReal.ofReal (Kp * c k ^ 2) *
            (1 + ENNReal.ofReal (1 / Real.sqrt d) * ∫⁻ ω, ‖R.D k ω‖ₑ ∂P) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_add_left measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          simp
      _ ≤ ENNReal.ofReal (Kp * c k ^ 2) * (1 + ENNReal.ofReal (1 / Real.sqrt d) * ENNReal.ofReal t) := by
          gcongr
          exact hDint k
      _ = ENNReal.ofReal (Kp * (1 + t / Real.sqrt d) * c k ^ 2) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_one,
            ← ENNReal.ofReal_add zero_le_one (by positivity), ← ENNReal.ofReal_mul hck2]
          congr 1
          ring
