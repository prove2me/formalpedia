-- Prove2me | solution 1 for QuantileSPQO.Rate.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T20:10:29.934198+00:00
-- url     : https://prove2.me/submissions/85ea0227-51ca-4a3e-85b1-9a2cb0112ebb

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_QuantileSPQO_Rate_Setting
import Theorems.Thm_QuantileSPQO_Rate_eq_4
import Theorems.Thm_QuantileSPQO_Rate_lemma_3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal RealInnerProductSpace

/-! ### Part 1: Deterministic calculus, geometry, and bias/gradient-identity bounds -/

namespace SPQOCommon
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
    Nat.cast_one, inv_one, iteratedFDeriv_zero_apply, iteratedFDeriv_one_apply,
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

lemma abs_dens_le_fderiv {d : ℕ} (M : Model d)
    (hdens : ∀ y θ, HasDerivAt (fun y' => cdf M y' θ) (M.dens y θ) y) (q : ℝ) (θ : E d)
    (hF : DifferentiableAt ℝ (cdfU M) (q, θ)) :
    |M.dens q θ| ≤ ‖fderiv ℝ (cdfU M) (q, θ)‖ := by
  have h1 := L_split M hdens q θ hF 1 0
  simp only [one_mul, inner_zero_right, add_zero] at h1
  rw [← h1, ← Real.norm_eq_abs]
  have h2 := (fderiv ℝ (cdfU M) (q, θ)).le_opNorm ((1 : ℝ), (0 : E d))
  have h3 : ‖((1 : ℝ), (0 : E d))‖ = 1 := by
    rw [Prod.norm_mk, Real.norm_eq_abs, abs_one, norm_zero, max_eq_left zero_le_one]
  rwa [h3, mul_one] at h2

lemma norm_gradθ_le_fderiv {d : ℕ} (M : Model d)
    (hdens : ∀ y θ, HasDerivAt (fun y' => cdf M y' θ) (M.dens y θ) y) (q : ℝ) (θ : E d)
    (hF : DifferentiableAt ℝ (cdfU M) (q, θ)) :
    ‖gradθ M q θ‖ ≤ ‖fderiv ℝ (cdfU M) (q, θ)‖ := by
  set v := gradθ M q θ with hvdef
  by_cases hv : v = 0
  · rw [hv, norm_zero]; exact norm_nonneg _
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
  have h1 := L_split M hdens q θ hF 0 v
  simp only [zero_mul, zero_add] at h1
  rw [← hvdef, real_inner_self_eq_norm_sq] at h1
  have h2 := (fderiv ℝ (cdfU M) (q, θ)).le_opNorm ((0 : ℝ), v)
  have h3 : ‖((0 : ℝ), v)‖ = ‖v‖ := by
    rw [Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg v)]
  rw [h3, h1, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖v‖)] at h2
  nlinarith

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
      intro b; funext m
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
  simp only [PiLp.smul_apply, smul_eq_mul, signVec, WithLp.ofLp_sum,
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

lemma norm_pert_le {d : ℕ} (hd : 0 < d) (c : ℕ → ℝ) (k : ℕ) (hck : 0 < c k)
    (D : E d) (b : Fin d → Bool) :
    ‖(cbar c k D * ⟪D, signVec b⟫, cbar c k D • signVec b)‖ ≤ c k * d := by
  set m := mfac D with hm
  have hm1 : 1 ≤ m := le_max_left _ _
  have hm0 : 0 < m := by linarith
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd0 : 0 < Real.sqrt d := Real.sqrt_pos.2 (by linarith)
  have hsd1 : Real.sqrt d ≤ d := by rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hsdsq : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt (by linarith)
  have hmD : ‖D‖ ≤ m * Real.sqrt d := by
    have : ‖D‖ / Real.sqrt d ≤ m := le_max_right _ _
    rwa [div_le_iff₀ hsd0] at this
  set cb := cbar c k D with hcb
  have hcbeq : cb = c k / m := rfl
  have hcb0 : 0 < cb := by rw [hcbeq]; positivity
  have hmcb : m * cb = c k := by rw [hcbeq]; field_simp
  have hsb : ‖signVec b‖ = Real.sqrt d := norm_signVec b
  rw [Prod.norm_mk]
  apply max_le
  · rw [Real.norm_eq_abs, abs_mul, abs_of_pos hcb0]
    have h1 : |⟪D, signVec b⟫| ≤ ‖D‖ * ‖signVec b‖ := abs_real_inner_le_norm _ _
    rw [hsb] at h1
    calc cb * |⟪D, signVec b⟫| ≤ cb * (‖D‖ * Real.sqrt d) := mul_le_mul_of_nonneg_left h1 hcb0.le
      _ ≤ cb * (m * Real.sqrt d * Real.sqrt d) := by gcongr
      _ = c k * d := by rw [mul_assoc m, hsdsq, ← mul_assoc, mul_comm cb m, hmcb]
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hcb0, hsb]
    have : cb ≤ c k := by rw [hcbeq]; exact div_le_self hck.le hm1
    exact mul_le_mul this hsd1 hsd0.le hck.le

lemma abs_cbar_inner_le {d : ℕ} (hd : 0 < d) (c : ℕ → ℝ) (k : ℕ) (hck : 0 < c k)
    (D : E d) (b : Fin d → Bool) :
    |cbar c k D * ⟪D, signVec b⟫| ≤ c k * d := by
  have h := norm_pert_le hd c k hck D b
  rw [Prod.norm_mk, Real.norm_eq_abs] at h
  exact (le_max_left _ _).trans h

lemma mfac_sq_le {d : ℕ} (hd : 0 < d) (D : E d) :
    mfac D ^ 2 ≤ 1 + ‖D‖ ^ 2 / d := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hsd0 : 0 < Real.sqrt d := Real.sqrt_pos.2 hd0
  unfold mfac
  rcases max_choice 1 (‖D‖ / Real.sqrt d) with h | h
  · rw [h, one_pow]; exact le_add_of_nonneg_right (by positivity)
  · rw [h, div_pow, Real.sq_sqrt hd0.le]; linarith

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
  set cb := cbar c k D with hcb
  have hcbeq : cb = c k / m := rfl
  set p : ℝ × E d := (q, θ) with hp
  have hpball : p ∈ Metric.ball p δ := by
    have : 0 ≤ c k * d := by positivity
    exact Metric.mem_ball_self (by linarith)
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK p hpball)
  have hdiff : DifferentiableAt ℝ (cdfU M) p :=
    (hC3.differentiableOn (by norm_num)).differentiableAt (Metric.isOpen_ball.mem_nhds hpball)
  set s : (Fin d → Bool) → E d := fun b => signVec b with hs
  set hv : (Fin d → Bool) → ℝ × E d := fun b => (cb * ⟪D, s b⟫, cb • s b) with hhv
  have hnorm_h : ∀ b, ‖hv b‖ ≤ c k * d := fun b => norm_pert_le hd c k hck D b
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
    congr 1; simp only [hrem, hLh b]; ring
  set R : E d := ∑ b, rem b • s b with hR
  have hsum : ∑ b : Fin d → Bool, (-cdf M (q + cbar c k D * ⟪D, signVec b⟫)
        (θ + cbar c k D • signVec b) +
        cdf M (q - cbar c k D * ⟪D, signVec b⟫) (θ - cbar c k D • signVec b)) • signVec b
      = (-(2 * cb)) • (((2 : ℝ) ^ d) • w) - R := by
    rw [Finset.sum_congr rfl (fun b _ => hterm b), Finset.sum_sub_distrib, ← Finset.smul_sum]
    congr 2; exact sum_sign w
  have key : bias M c k q D θ =
      (m / (2 * c k) * ((2 ^ d : ℝ)⁻¹ * (-(2 * cb)) * 2 ^ d) + 1) • w
        - (m / (2 * c k) * (2 ^ d : ℝ)⁻¹) • R := by
    simp only [bias]; rw [hsum]; module
  have hcoef : m / (2 * c k) * ((2 ^ d : ℝ)⁻¹ * (-(2 * cb)) * 2 ^ d) + 1 = 0 := by
    rw [hcbeq]; field_simp; ring
  rw [key, hcoef, zero_smul, zero_sub, norm_neg, norm_smul]
  have hRn : ‖R‖ ≤ (2 : ℝ) ^ d * (K * (c k * d) ^ 3 * Real.sqrt d) := by
    calc ‖R‖ ≤ ∑ b, ‖rem b • s b‖ := norm_sum_le _ _
      _ ≤ ∑ _b : Fin d → Bool, K * (c k * d) ^ 3 * Real.sqrt d := by
          apply Finset.sum_le_sum; intro b _
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
    _ = m * (K * (d : ℝ) ^ 3 * Real.sqrt d) * c k ^ 2 / 2 := by field_simp
    _ ≤ m * (K * (d : ℝ) ^ 3 * Real.sqrt d) * c k ^ 2 := by
        have : 0 ≤ m * (K * (d : ℝ) ^ 3 * Real.sqrt d) * c k ^ 2 := by positivity
        linarith

lemma proj1d {I : Set ℝ} {Pq : ℝ → ℝ} (h : IsIntervalProj I Pq) {z : ℝ} (hz : z ∈ I) (x : ℝ) :
    |Pq x - z| ≤ |x - z| := by
  obtain ⟨hp, hmin⟩ := h.proj x
  have hmz := hmin z hz
  rcases le_total z x with hzx | hxz
  · rcases le_or_gt z (Pq x) with h1 | h1
    · by_cases h2 : Pq x ≤ x
      · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
      · push Not at h2
        have hx : x ∈ I := h.ordConnected.out hz hp ⟨hzx, h2.le⟩
        have h3 : |x - Pq x| = 0 := le_antisymm (by simpa using hmin x hx) (abs_nonneg _)
        rw [abs_eq_zero] at h3; linarith
    · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ x - z)] at hmz ⊢
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ x - Pq x)] at hmz
      rw [abs_of_neg (by linarith : Pq x - z < 0)]; linarith
  · rcases le_or_gt (Pq x) z with h1 | h1
    · by_cases h2 : x ≤ Pq x
      · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
      · push Not at h2
        have hx : x ∈ I := h.ordConnected.out hp hz ⟨h2.le, hxz⟩
        have h3 : |x - Pq x| = 0 := le_antisymm (by simpa using hmin x hx) (abs_nonneg _)
        rw [abs_eq_zero] at h3; linarith
    · rw [abs_of_nonpos (by linarith : x - z ≤ 0)] at hmz ⊢
      rw [abs_of_nonpos (by linarith : x - Pq x ≤ 0)] at hmz
      rw [abs_of_pos (by linarith : 0 < Pq x - z)]; linarith

lemma proj_nonexp {d : ℕ} {Θ : Set (E d)} {Proj : E d → E d} (hc : Convex ℝ Θ)
    (hProj : SpectralProjGrad.Shared.IsProjOnto Θ Proj) {z : E d} (hz : z ∈ Θ) (x : E d) :
    ‖Proj x - z‖ ≤ ‖x - z‖ := by
  obtain ⟨hp, hmin⟩ := hProj x
  set p := Proj x
  have hvi : ⟪x - p, z - p⟫ ≤ 0 := by
    by_contra hpos
    push Not at hpos
    set δ := ⟪x - p, z - p⟫
    set t := min 1 (δ / (‖z - p‖ ^ 2 + 1))
    have ht0 : 0 < t := lt_min one_pos (by positivity)
    have ht1 : t ≤ 1 := min_le_left _ _
    have htδ : t ≤ δ / (‖z - p‖ ^ 2 + 1) := min_le_right _ _
    have hmem : p + t • (z - p) ∈ Θ := by
      have := hc hp hz (by linarith : (0:ℝ) ≤ 1 - t) ht0.le (by ring)
      convert this using 1
      simp only [smul_sub, sub_smul, one_smul]; abel
    have hle := hmin _ hmem
    have hsq : ‖x - p‖ ^ 2 ≤ ‖x - (p + t • (z - p))‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hle 2
    have e : x - (p + t • (z - p)) = (x - p) - t • (z - p) := by abel
    have e2 : ‖(x - p) - t • (z - p)‖ ^ 2 = ‖x - p‖ ^ 2 - 2 * t * δ + t ^ 2 * ‖z - p‖ ^ 2 := by
      rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      ring
    rw [e, e2] at hsq
    have h1 : t * ‖z - p‖ ^ 2 < δ := by
      have hpos' : (0:ℝ) < ‖z - p‖ ^ 2 + 1 := by positivity
      have := mul_le_mul_of_nonneg_right htδ (by positivity : (0:ℝ) ≤ ‖z - p‖ ^ 2 + 1)
      rw [div_mul_cancel₀ _ hpos'.ne'] at this
      nlinarith [sq_nonneg ‖z - p‖]
    nlinarith [mul_pos ht0 hpos]
  have h1 : ‖x - z‖ ^ 2 = ‖x - p‖ ^ 2 - 2 * ⟪x - p, z - p⟫ + ‖z - p‖ ^ 2 := by
    have : x - z = (x - p) - (z - p) := by abel
    rw [this, norm_sub_sq_real]
  have h2 : ‖p - z‖ = ‖z - p‖ := norm_sub_rev _ _
  have h3 : ‖p - z‖ ^ 2 ≤ ‖x - z‖ ^ 2 := by rw [h1, h2]; nlinarith [sq_nonneg ‖x - p‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h3

lemma q_lip {d : ℕ} {Θ : Set (E d)} {q : E d → ℝ} (hc : Convex ℝ Θ) (hK : IsCompact Θ)
    (hq2 : ∃ U : Set (E d), IsOpen U ∧ Θ ⊆ U ∧ ContDiffOn ℝ 2 q U) :
    ∃ L : ℝ, 0 < L ∧ ∀ x ∈ Θ, ∀ y ∈ Θ, |q x - q y| ≤ L * ‖x - y‖ := by
  obtain ⟨U, hU, hΘU, hq⟩ := hq2
  have hcont : ContinuousOn (fun x => fderiv ℝ q x) U :=
    hq.continuousOn_fderiv_of_isOpen hU (by norm_num)
  have hdiff : ∀ x ∈ Θ, DifferentiableAt ℝ q x := fun x hx =>
    (hq.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds (hΘU hx))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (f := fun x => fderiv ℝ q x) (hcont.mono hΘU)
  refine ⟨max C 1, by positivity, fun x hx y hy => ?_⟩
  have hb : ∀ z ∈ Θ, ‖fderiv ℝ q z‖ ≤ max C 1 := fun z hz => (hC z hz).trans (le_max_left _ _)
  have := hc.norm_image_sub_le_of_norm_fderiv_le hdiff hb hy hx
  rwa [Real.norm_eq_abs] at this

lemma grad_lip {d : ℕ} {Θ : Set (E d)} {q : E d → ℝ} (hc : Convex ℝ Θ) (hK : IsCompact Θ)
    (hq2 : ∃ U : Set (E d), IsOpen U ∧ Θ ⊆ U ∧ ContDiffOn ℝ 2 q U) :
    ∃ L : ℝ, 0 < L ∧ ∀ x ∈ Θ, ∀ y ∈ Θ, ‖gradient q x - gradient q y‖ ≤ L * ‖x - y‖ := by
  obtain ⟨U, hU, hΘU, hq⟩ := hq2
  have h1 : ContDiffOn ℝ 1 (fun y => fderiv ℝ q y) U := hq.fderiv_of_isOpen hU (by norm_num)
  have hcont : ContinuousOn (fun x => fderiv ℝ (fun y => fderiv ℝ q y) x) U :=
    h1.continuousOn_fderiv_of_isOpen hU le_rfl
  have hdiff : ∀ x ∈ Θ, DifferentiableAt ℝ (fun y => fderiv ℝ q y) x := fun x hx =>
    (h1.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds (hΘU hx))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (f := fun x => fderiv ℝ (fun y => fderiv ℝ q y) x) (hcont.mono hΘU)
  refine ⟨max C 1, by positivity, fun x hx y hy => ?_⟩
  have hb : ∀ z ∈ Θ, ‖fderiv ℝ (fun y => fderiv ℝ q y) z‖ ≤ max C 1 :=
    fun z hz => (hC z hz).trans (le_max_left _ _)
  have key := hc.norm_image_sub_le_of_norm_fderiv_le hdiff hb hy hx
  have e : gradient q x - gradient q y =
      (InnerProductSpace.toDual ℝ (E d)).symm (fderiv ℝ q x - fderiv ℝ q y) := by
    simp only [gradient, map_sub]
  rw [e, LinearIsometryEquiv.norm_map]
  exact key

lemma grad_contOn {d : ℕ} {Θ : Set (E d)} {q : E d → ℝ}
    (hq2 : ∃ U : Set (E d), IsOpen U ∧ Θ ⊆ U ∧ ContDiffOn ℝ 2 q U) :
    ContinuousOn (gradient q) Θ := by
  obtain ⟨U, hU, hΘU, hq⟩ := hq2
  have hcont : ContinuousOn (fun x => fderiv ℝ q x) U :=
    hq.continuousOn_fderiv_of_isOpen hU (by norm_num)
  have : gradient q = fun x => (InnerProductSpace.toDual ℝ (E d)).symm (fderiv ℝ q x) := rfl
  rw [this]
  exact (InnerProductSpace.toDual ℝ (E d)).symm.continuous.comp_continuousOn (hcont.mono hΘU)

lemma meas_comp_on {Ω : Type*} {m : MeasurableSpace Ω} {d : ℕ} {V : Type*}
    [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    {Θ : Set (E d)} {g : E d → V}
    (hg : ContinuousOn g Θ) {θ : Ω → E d} (hθ : StronglyMeasurable[m] θ) (hmem : ∀ ω, θ ω ∈ Θ) :
    StronglyMeasurable[m] (fun ω => g (θ ω)) := by
  have h1 : Measurable[m] (fun ω => (⟨θ ω, hmem ω⟩ : Θ)) := hθ.measurable.subtype_mk
  have h2 : Measurable (Θ.domRestrict g) := hg.domRestrict.measurable
  exact (h2.comp h1).stronglyMeasurable

lemma mvt_cdf {d : ℕ} (M : Model d)
    (hdens : ∀ y θ, HasDerivAt (fun y' => cdf M y' θ) (M.dens y θ) y) (θ : E d) (y1 y2 : ℝ) :
    ∃ ξ ∈ Set.uIcc y1 y2, cdf M y2 θ - cdf M y1 θ = M.dens ξ θ * (y2 - y1) := by
  have hc : Continuous (fun y => cdf M y θ) :=
    continuous_iff_continuousAt.2 fun y => (hdens y θ).continuousAt
  rcases lt_trichotomy y1 y2 with h | h | h
  · obtain ⟨ξ, hξ, he⟩ := exists_hasDerivAt_eq_slope (fun y => cdf M y θ) (fun y => M.dens y θ)
      h hc.continuousOn (fun x _ => hdens x θ)
    refine ⟨ξ, ?_, ?_⟩
    · rw [Set.uIcc_of_le h.le]; exact Set.Ioo_subset_Icc_self hξ
    · rw [he]; field_simp [sub_ne_zero.2 h.ne']
  · subst h; exact ⟨y1, Set.left_mem_uIcc, by ring⟩
  · obtain ⟨ξ, hξ, he⟩ := exists_hasDerivAt_eq_slope (fun y => cdf M y θ) (fun y => M.dens y θ)
      h hc.continuousOn (fun x _ => hdens x θ)
    refine ⟨ξ, ?_, ?_⟩
    · rw [Set.uIcc_of_ge h.le]; exact Set.Ioo_subset_Icc_self hξ
    · rw [he]; field_simp [sub_ne_zero.2 h.ne']; ring

lemma cdf_nonneg {d : ℕ} (M : Model d) (y : ℝ) (θ : E d) : 0 ≤ cdf M y θ := ENNReal.toReal_nonneg

lemma cdf_le_one {d : ℕ} (M : Model d) (hprob : ∀ θ, IsProbabilityMeasure (M.law θ)) (y : ℝ)
    (θ : E d) : cdf M y θ ≤ 1 := by
  unfold QuantileSPQO.Rate.cdf
  have := hprob θ
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)

/-- Pointwise bound on `f(q;θ) ∇q(θ) + ∇_θ F(q;θ)` in terms of `|q − q(θ)|`, combining
`eq_4` + B2 (when `|q − q(θ)| < δ`) and the `A1` derivative bound (when `|q − q(θ)| ≥ δ`). -/
lemma grad_residual_bound {d : ℕ} (M : Model d) (Θ : Set (E d))
    (hM : IsQuantileModel M Θ) (Lf LF Mg δ K ε : ℝ)
    (hLf : 0 < Lf) (_hLF : 0 < LF) (hMg0 : 0 ≤ Mg) (hδ : 0 < δ) (hK0 : 0 ≤ K) (hε : 0 < ε)
    (hLip : ∀ θ ∈ Θ, ∀ y₁ y₂ : ℝ,
      |M.dens y₁ θ - M.dens y₂ θ| ≤ Lf * |y₁ - y₂| ∧
      ‖gradθ M y₁ θ - gradθ M y₂ θ‖ ≤ LF * |y₁ - y₂|)
    (hMg : ∀ θ ∈ Θ, ‖gradient M.qf θ‖ ≤ Mg)
    (hqdiff : ∀ θ ∈ Θ, DifferentiableAt ℝ M.qf θ)
    (q : ℝ) (θ : E d) (hθ : θ ∈ Θ)
    (hC3 : ContDiffOn ℝ 3 (cdfU M) (Metric.ball (q, θ) δ))
    (hball : ∀ p ∈ Metric.ball (q, θ) δ, ‖fderiv ℝ (cdfU M) p‖ ≤ K ∧ ε ≤ M.dens p.1 p.2) :
    ‖M.dens q θ • gradient M.qf θ + gradθ M q θ‖
      ≤ max (Lf * Mg + LF) (K * (Mg + 1) / δ) * |q - M.qf θ| := by
  set Lr := max (Lf * Mg + LF) (K * (Mg + 1) / δ) with hLr
  by_cases hnear : |q - M.qf θ| < δ
  · have hmem : (M.qf θ, θ) ∈ Metric.ball (q, θ) δ := by
      rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, dist_self, abs_sub_comm,
        max_eq_left (abs_nonneg _)]
      exact hnear
    have hFdiff : DifferentiableAt ℝ (cdfU M) (M.qf θ, θ) :=
      (hC3.differentiableOn (by norm_num)).differentiableAt (Metric.isOpen_ball.mem_nhds hmem)
    have hfpos : ε ≤ M.dens (M.qf θ) θ := (hball _ hmem).2
    have hfne : M.dens (M.qf θ) θ ≠ 0 := by linarith
    have heq4 := eq_4 M Θ hM θ (hqdiff θ hθ) hFdiff hfne
    have hzero : M.dens (M.qf θ) θ • gradient M.qf θ + gradθ M (M.qf θ) θ = 0 := by
      rw [heq4, smul_smul, mul_neg, mul_inv_cancel₀ hfne, neg_one_smul, neg_add_cancel]
    have hsplit : M.dens q θ • gradient M.qf θ + gradθ M q θ =
        (M.dens q θ - M.dens (M.qf θ) θ) • gradient M.qf θ +
        (gradθ M q θ - gradθ M (M.qf θ) θ) := by
      rw [sub_smul]
      have : (M.dens q θ • gradient M.qf θ - M.dens (M.qf θ) θ • gradient M.qf θ) +
          (gradθ M q θ - gradθ M (M.qf θ) θ)
          = (M.dens q θ • gradient M.qf θ + gradθ M q θ) -
            (M.dens (M.qf θ) θ • gradient M.qf θ + gradθ M (M.qf θ) θ) := by abel
      rw [this, hzero, sub_zero]
    rw [hsplit]
    obtain ⟨h1, h2⟩ := hLip θ hθ q (M.qf θ)
    have h3 : ‖(M.dens q θ - M.dens (M.qf θ) θ) • gradient M.qf θ‖
        ≤ Lf * Mg * |q - M.qf θ| := by
      rw [norm_smul, Real.norm_eq_abs]
      calc |M.dens q θ - M.dens (M.qf θ) θ| * ‖gradient M.qf θ‖
          ≤ (Lf * |q - M.qf θ|) * Mg := mul_le_mul h1 (hMg θ hθ) (norm_nonneg _) (by positivity)
        _ = Lf * Mg * |q - M.qf θ| := by ring
    calc ‖(M.dens q θ - M.dens (M.qf θ) θ) • gradient M.qf θ +
            (gradθ M q θ - gradθ M (M.qf θ) θ)‖
        ≤ ‖(M.dens q θ - M.dens (M.qf θ) θ) • gradient M.qf θ‖ +
            ‖gradθ M q θ - gradθ M (M.qf θ) θ‖ := norm_add_le _ _
      _ ≤ Lf * Mg * |q - M.qf θ| + LF * |q - M.qf θ| := add_le_add h3 h2
      _ = (Lf * Mg + LF) * |q - M.qf θ| := by ring
      _ ≤ Lr * |q - M.qf θ| :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)
  · push Not at hnear
    have hmem : (q, θ) ∈ Metric.ball (q, θ) δ := Metric.mem_ball_self hδ
    have hFdiff : DifferentiableAt ℝ (cdfU M) (q, θ) :=
      (hC3.differentiableOn (by norm_num)).differentiableAt (Metric.isOpen_ball.mem_nhds hmem)
    have hfK : ‖fderiv ℝ (cdfU M) (q, θ)‖ ≤ K := (hball _ hmem).1
    have hdK : |M.dens q θ| ≤ K := (abs_dens_le_fderiv M hM.hasDens q θ hFdiff).trans hfK
    have hgK : ‖gradθ M q θ‖ ≤ K := (norm_gradθ_le_fderiv M hM.hasDens q θ hFdiff).trans hfK
    have h1 : ‖M.dens q θ • gradient M.qf θ + gradθ M q θ‖ ≤ K * (Mg + 1) := by
      calc ‖M.dens q θ • gradient M.qf θ + gradθ M q θ‖
          ≤ ‖M.dens q θ • gradient M.qf θ‖ + ‖gradθ M q θ‖ := norm_add_le _ _
        _ = |M.dens q θ| * ‖gradient M.qf θ‖ + ‖gradθ M q θ‖ := by
            rw [norm_smul, Real.norm_eq_abs]
        _ ≤ K * Mg + K := add_le_add (mul_le_mul hdK (hMg θ hθ) (norm_nonneg _) hK0) hgK
        _ = K * (Mg + 1) := by ring
    have h1le : 1 ≤ |q - M.qf θ| / δ := (one_le_div hδ).2 hnear
    calc ‖M.dens q θ • gradient M.qf θ + gradθ M q θ‖
        ≤ K * (Mg + 1) * 1 := by linarith
      _ ≤ K * (Mg + 1) * (|q - M.qf θ| / δ) :=
          mul_le_mul_of_nonneg_left h1le (by positivity)
      _ = (K * (Mg + 1) / δ) * |q - M.qf θ| := by ring
      _ ≤ Lr * |q - M.qf θ| :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _)

end SPQOCommon

/-! ### Part 2: Rademacher measure, conditional expectation of the SP estimator, and `goodEvent` -/

namespace SPQOCond
open QuantileSPQO.Rate SPQOCommon

lemma signVec_injective {d : ℕ} : Function.Injective (signVec (d := d)) := by
  intro b₁ b₂ h
  funext i
  have hi := congrArg (fun v : E d => v i) h
  simp only [signVec, PiLp.toLp_apply] at hi
  cases hb1 : b₁ i <;> cases hb2 : b₂ i <;> simp [hb1, hb2] at hi ⊢ <;> norm_num at hi

lemma rademacher_singleton {d : ℕ} (b : Fin d → Bool) :
    rademacher d {signVec b} = ((2 : ℝ≥0∞) ^ d)⁻¹ := by
  unfold rademacher
  set μ : Measure ℝ := (2⁻¹ : ℝ≥0∞) • (Measure.dirac (1 : ℝ) + Measure.dirac (-1 : ℝ)) with hμ
  have : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    simp only [hμ, Measure.smul_apply, Measure.add_apply, Measure.dirac_apply' _ MeasurableSet.univ,
      Set.indicator_univ, Pi.one_apply, smul_eq_mul]
    rw [show (1 : ℝ≥0∞) + 1 = 2 by norm_num, ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]
    exact ENNReal.one_lt_top
  rw [Measure.map_apply (WithLp.measurable_toLp 2 (Fin d → ℝ)) (MeasurableSet.singleton _)]
  have hpre : WithLp.toLp 2 ⁻¹' ({signVec b} : Set (E d))
      = Set.univ.pi (fun i => {if b i then (1 : ℝ) else -1}) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ_pi, signVec]
    constructor
    · intro h i
      have hi := congrArg (fun v : E d => v i) h
      simpa using hi
    · intro h
      ext i
      simpa using h i
  rw [hpre, Measure.pi_pi]
  have hcoord : ∀ i : Fin d, μ {if b i then (1 : ℝ) else -1} = (2 : ℝ≥0∞)⁻¹ := by
    intro i
    simp only [hμ, Measure.smul_apply, Measure.add_apply,
      Measure.dirac_apply' _ (MeasurableSet.singleton _), Set.indicator_apply,
      Set.mem_singleton_iff, Pi.one_apply, smul_eq_mul]
    cases b i
    · have hne : (1 : ℝ) ≠ -1 := by norm_num
      simp [hne]
    · have hne : (-1 : ℝ) ≠ 1 := by norm_num
      simp [hne]
  simp only [hcoord, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.inv_pow]

lemma rademacher_range {d : ℕ} : rademacher d (Set.range (signVec (d := d))) = 1 := by
  have hU : Set.range (signVec (d := d)) = ⋃ b : Fin d → Bool, {signVec b} := by
    ext x; simp [eq_comm]
  rw [hU, measure_iUnion (fun b₁ b₂ hne => Set.disjoint_singleton.2 (fun h => hne (signVec_injective h)))
    (fun _ => MeasurableSet.singleton _)]
  simp only [rademacher_singleton, tsum_fintype, Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
  have hcast : (((2 ^ d : ℕ) : ℝ≥0∞)) = (2 : ℝ≥0∞) ^ d := by push_cast; rfl
  rw [hcast, ENNReal.mul_inv_cancel (by positivity) (ENNReal.pow_ne_top (by norm_num))]

lemma prob_Delta_eq {Ω : Type*} [m0 : MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (Δ : Ω → E d) (hΔm : Measurable Δ) (hlaw : P.map Δ = rademacher d)
    (b : Fin d → Bool) :
    P {ω | Δ ω = signVec b} = ((2 : ℝ≥0∞) ^ d)⁻¹ := by
  have h1 := rademacher_singleton b
  rw [← hlaw, Measure.map_apply hΔm (MeasurableSet.singleton _)] at h1
  simpa [Set.preimage] using h1

lemma ae_Delta_mem_range {Ω : Type*} [m0 : MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (Δ : Ω → E d) (hΔm : Measurable Δ)
    (hlaw : P.map Δ = rademacher d) :
    ∀ᵐ ω ∂P, Δ ω ∈ Set.range (signVec (d := d)) := by
  have hm : MeasurableSet (Set.range (signVec (d := d))) := (Set.finite_range _).measurableSet
  have h1 := rademacher_range (d := d)
  rw [← hlaw, Measure.map_apply hΔm hm] at h1
  rw [ae_iff]
  have hcomp : P (Δ ⁻¹' Set.range (signVec (d := d)))ᶜ = 0 := by
    rw [prob_compl_eq_zero_iff (hΔm hm)]
    exact h1
  simpa [Set.compl_def] using hcomp

lemma integral_ind_Delta_eq {Ω : Type*} [m0 : MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (Δ : Ω → E d) (hΔm : Measurable Δ) (hlaw : P.map Δ = rademacher d)
    (b : Fin d → Bool) :
    ∫ ω, (if Δ ω = signVec b then (1 : ℝ) else 0) ∂P = ((2 : ℝ) ^ d)⁻¹ := by
  have hs : MeasurableSet {ω | Δ ω = signVec b} := hΔm (MeasurableSet.singleton _)
  have hind : (fun ω => if Δ ω = signVec b then (1 : ℝ) else 0)
      = ({ω | Δ ω = signVec b}).indicator 1 := by
    funext ω; simp [Set.indicator_apply]
  rw [hind, integral_indicator_one hs, Measure.real, prob_Delta_eq P Δ hΔm hlaw b,
    ENNReal.toReal_inv, ENNReal.toReal_pow]
  norm_num

lemma cond_fixed {Ω : Type*} {m m0 : MeasurableSpace Ω} (hm : m ≤ m0) (P : Measure Ω)
    [IsProbabilityMeasure P] (X H Φ : Ω → ℝ) (hX : Integrable X P) (hH : StronglyMeasurable[m] H)
    (Hb : ℝ) (hHb : ∀ ω, |H ω| ≤ Hb) (hce : P[X | m] =ᵐ[P] Φ) :
    ∫ ω, H ω * X ω ∂P = ∫ ω, H ω * Φ ω ∂P := by
  have hHX : Integrable (H * X) P :=
    hX.bdd_mul (c := Hb) (hH.mono hm).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hHb ω)
  calc ∫ ω, H ω * X ω ∂P = ∫ ω, (P[H * X | m]) ω ∂P := (integral_condExp hm).symm
    _ = ∫ ω, (H * P[X | m]) ω ∂P :=
        integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hH hHX hX)
    _ = ∫ ω, H ω * Φ ω ∂P := integral_congr_ae (hce.mono fun ω h => by simp [h])

lemma cond_threshold {Ω : Type*} {m m0 : MeasurableSpace Ω} (hm : m ≤ m0) (P : Measure Ω)
    [IsProbabilityMeasure P] {d : ℕ} (M : Model d) (hprob : ∀ θ, IsProbabilityMeasure (M.law θ))
    (hcont : ∀ θ, Continuous (fun y => cdf M y θ))
    (Y : Ω → ℝ) (hY : Measurable[m0] Y) (θ : Ω → E d) (q G : Ω → ℝ)
    (hq : StronglyMeasurable[m] q) (hG : StronglyMeasurable[m] G) (Qb Gb : ℝ)
    (hqb : ∀ ω, |q ω| ≤ Qb) (hGb : ∀ ω, |G ω| ≤ Gb)
    (hs : ∀ v : ℝ, P[fun ω => (Set.Iic v).indicator (fun _ => (1:ℝ)) (Y ω) | m] =ᵐ[P]
      fun ω => cdf M v (θ ω)) :
    AEStronglyMeasurable (fun ω => cdf M (q ω) (θ ω)) P ∧
    ∫ ω, G ω * (if Y ω ≤ q ω then 1 else 0) ∂P = ∫ ω, G ω * cdf M (q ω) (θ ω) ∂P := by
  have hcdfv : ∀ v : ℝ, AEStronglyMeasurable (fun ω => cdf M v (θ ω)) P := fun v =>
    ((stronglyMeasurable_condExp (m := m) (μ := P)).mono hm).aestronglyMeasurable.congr (hs v)
  have hind : ∀ v : ℝ, (fun ω => (Set.Iic v).indicator (fun _ => (1:ℝ)) (Y ω))
      = fun ω => if Y ω ≤ v then (1:ℝ) else 0 := by
    intro v; funext ω; by_cases h : Y ω ≤ v <;> simp [h]
  have hindI : ∀ v : ℝ, Integrable (fun ω => if Y ω ≤ v then (1:ℝ) else 0) P := by
    intro v; rw [← hind v]
    have : (fun ω => (Set.Iic v).indicator (fun _ => (1:ℝ)) (Y ω))
        = (Y ⁻¹' Set.Iic v).indicator (fun _ => (1:ℝ)) := by
      funext ω; by_cases h : Y ω ≤ v <;> simp [h]
    rw [this]
    exact (integrable_const (1:ℝ)).indicator (hY measurableSet_Iic)
  have hfix : ∀ (v : ℝ) (H : Ω → ℝ), StronglyMeasurable[m] H → (∀ ω, |H ω| ≤ Gb) →
      ∫ ω, H ω * (if Y ω ≤ v then 1 else 0) ∂P = ∫ ω, H ω * cdf M v (θ ω) ∂P := by
    intro v H hH hHb
    have hsv := hs v; rw [hind v] at hsv
    exact cond_fixed hm P (fun ω => if Y ω ≤ v then (1:ℝ) else 0) H (fun ω => cdf M v (θ ω))
      (hindI v) hH Gb hHb hsv
  set s : ℕ → ℝ := fun n => (2:ℝ) ^ n with hsdef
  have hs0 : ∀ n, 0 < s n := fun n => by positivity
  set qn : ℕ → Ω → ℝ := fun n ω => (⌈q ω * s n⌉ : ℝ) / s n with hqn
  have hqn_ge : ∀ n ω, q ω ≤ qn n ω := by
    intro n ω; simp only [hqn]; rw [le_div_iff₀ (hs0 n)]; exact Int.le_ceil _
  have hqn_lt : ∀ n ω, qn n ω < q ω + 1 / s n := by
    intro n ω; simp only [hqn]
    rw [div_lt_iff₀ (hs0 n), add_mul, div_mul_cancel₀ _ (hs0 n).ne']
    exact Int.ceil_lt_add_one _
  have hceil_meas : ∀ n, Measurable[m] (fun ω => ⌈q ω * s n⌉) := fun n =>
    Int.measurable_ceil.comp (hq.measurable.mul_const _)
  set N : ℕ → ℤ := fun n => ⌈Qb * s n⌉ + 1 with hN
  have hmemJ : ∀ n ω, ⌈q ω * s n⌉ ∈ Finset.Icc (-N n) (N n) := by
    intro n ω; rw [Finset.mem_Icc]
    have h1 := hqb ω; have hsn := hs0 n
    constructor
    · have : -(Qb * s n) ≤ q ω * s n := by have := neg_abs_le (q ω); nlinarith
      have h2 : (-(N n) : ℝ) ≤ ⌈q ω * s n⌉ := by
        simp only [hN]; push_cast
        have := Int.le_ceil (Qb * s n); have := Int.le_ceil (q ω * s n); linarith
      exact_mod_cast h2
    · simp only [hN]
      have : q ω * s n ≤ Qb * s n := by have := le_abs_self (q ω); nlinarith
      have := Int.ceil_mono this; omega
  have hrep : ∀ (n : ℕ) (Φ : ℝ → ℝ) (ω : Ω), Φ (qn n ω) =
      ∑ j ∈ Finset.Icc (-N n) (N n), (if ⌈q ω * s n⌉ = j then (1:ℝ) else 0) * Φ ((j : ℝ) / s n) := by
    intro n Φ ω
    rw [Finset.sum_eq_single_of_mem (⌈q ω * s n⌉) (hmemJ n ω)]
    · simp [hqn]
    · intro j _ hj; simp [Ne.symm hj]
  have hHj : ∀ (n : ℕ) (j : ℤ), StronglyMeasurable[m]
      (fun ω => G ω * (if ⌈q ω * s n⌉ = j then (1:ℝ) else 0)) := fun n j =>
    hG.mul (Measurable.ite ((hceil_meas n) (measurableSet_singleton j))
      measurable_const measurable_const).stronglyMeasurable
  have hHjb : ∀ (n : ℕ) (j : ℤ) (ω : Ω),
      |G ω * (if ⌈q ω * s n⌉ = j then (1:ℝ) else 0)| ≤ Gb := by
    intro n j ω; split_ifs
    · simpa using hGb ω
    · simpa using (abs_nonneg _).trans (hGb ω)
  have hcdfqn : ∀ n, AEStronglyMeasurable (fun ω => cdf M (qn n ω) (θ ω)) P := by
    intro n
    have : (fun ω => cdf M (qn n ω) (θ ω)) = fun ω => ∑ j ∈ Finset.Icc (-N n) (N n),
        (if ⌈q ω * s n⌉ = j then (1:ℝ) else 0) * cdf M ((j : ℝ) / s n) (θ ω) := by
      funext ω; exact hrep n (fun y => cdf M y (θ ω)) ω
    rw [this]
    refine Finset.aestronglyMeasurable_fun_sum _ (fun j _ => AEStronglyMeasurable.mul ?_ (hcdfv _))
    exact ((Measurable.ite ((hceil_meas n) (measurableSet_singleton j)) measurable_const
      measurable_const).mono hm le_rfl).aestronglyMeasurable
  have hGaesm : AEStronglyMeasurable G P := (hG.mono hm).aestronglyMeasurable
  have hYle : ∀ v : ℝ, Measurable[m0] (fun ω => if Y ω ≤ v then (1:ℝ) else 0) := fun v =>
    Measurable.ite (hY measurableSet_Iic) measurable_const measurable_const
  have hlevel : ∀ n, ∫ ω, G ω * (if Y ω ≤ qn n ω then 1 else 0) ∂P
      = ∫ ω, G ω * cdf M (qn n ω) (θ ω) ∂P := by
    intro n
    have e1 : (fun ω => G ω * (if Y ω ≤ qn n ω then (1:ℝ) else 0)) = fun ω =>
        ∑ j ∈ Finset.Icc (-N n) (N n), (G ω * (if ⌈q ω * s n⌉ = j then (1:ℝ) else 0)) *
          (if Y ω ≤ (j : ℝ) / s n then 1 else 0) := by
      funext ω; rw [hrep n (fun y => if Y ω ≤ y then (1:ℝ) else 0) ω, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _; ring
    have e2 : (fun ω => G ω * cdf M (qn n ω) (θ ω)) = fun ω =>
        ∑ j ∈ Finset.Icc (-N n) (N n), (G ω * (if ⌈q ω * s n⌉ = j then (1:ℝ) else 0)) *
          cdf M ((j : ℝ) / s n) (θ ω) := by
      funext ω; rw [hrep n (fun y => cdf M y (θ ω)) ω, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _; ring
    rw [e1, e2, integral_finsetSum, integral_finsetSum]
    · exact Finset.sum_congr rfl fun j _ => hfix _ _ (hHj n j) (hHjb n j)
    · intro j _
      refine Integrable.of_bound (((hHj n j).mono hm).aestronglyMeasurable.mul (hcdfv _)) Gb
        (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      have := hHjb n j ω
      have h0 := cdf_nonneg M ((j : ℝ) / s n) (θ ω)
      have h1 := cdf_le_one M hprob ((j : ℝ) / s n) (θ ω)
      rw [abs_of_nonneg h0]
      nlinarith [abs_nonneg (G ω * (if ⌈q ω * s n⌉ = j then (1:ℝ) else 0))]
    · intro j _
      refine Integrable.of_bound (((hHj n j).mono hm).aestronglyMeasurable.mul
        (hYle _).aestronglyMeasurable) Gb (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      have := hHjb n j ω
      have h1 : |(if Y ω ≤ (j:ℝ) / s n then (1:ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
      nlinarith [abs_nonneg (G ω * (if ⌈q ω * s n⌉ = j then (1:ℝ) else 0)),
        abs_nonneg (if Y ω ≤ (j:ℝ) / s n then (1:ℝ) else 0)]
  have hqn_t : ∀ ω, Tendsto (fun n => qn n ω) atTop (𝓝 (q ω)) := by
    intro ω
    have hinv : Tendsto (fun n : ℕ => 1 / s n) atTop (𝓝 0) := by
      simp only [hsdef, one_div]
      exact tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
    have hup : Tendsto (fun n => q ω + 1 / s n) atTop (𝓝 (q ω)) := by
      simpa using hinv.const_add (q ω)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun n => hqn_ge n ω) (fun n => (hqn_lt n ω).le)
  have hcdf_lim : AEStronglyMeasurable (fun ω => cdf M (q ω) (θ ω)) P :=
    aestronglyMeasurable_of_tendsto_ae atTop hcdfqn
      (Eventually.of_forall fun ω => ((hcont (θ ω)).tendsto _).comp (hqn_t ω))
  refine ⟨hcdf_lim, ?_⟩
  have hL : Tendsto (fun n => ∫ ω, G ω * (if Y ω ≤ qn n ω then 1 else 0) ∂P) atTop
      (𝓝 (∫ ω, G ω * (if Y ω ≤ q ω then 1 else 0) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => Gb) (fun n => ?_)
      (integrable_const Gb) (fun n => Eventually.of_forall fun ω => ?_)
      (Eventually.of_forall fun ω => ?_)
    · refine hGaesm.mul ?_
      have : Measurable[m0] (fun ω => if Y ω ≤ qn n ω then (1:ℝ) else 0) := by
        refine Measurable.ite ?_ measurable_const measurable_const
        have hc : Measurable[m0] (fun ω => ((⌈q ω * s n⌉ : ℤ) : ℝ)) :=
          measurable_from_top.comp ((hceil_meas n).mono hm le_rfl)
        exact measurableSet_le hY (hc.div_const _)
      exact this.aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul]
      have h1 : |(if Y ω ≤ qn n ω then (1:ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
      nlinarith [hGb ω, abs_nonneg (G ω), abs_nonneg (if Y ω ≤ qn n ω then (1:ℝ) else 0)]
    · by_cases hyq : Y ω ≤ q ω
      · have : ∀ n, (if Y ω ≤ qn n ω then (1:ℝ) else 0) = 1 := fun n =>
          if_pos (hyq.trans (hqn_ge n ω))
        simp only [this, if_pos hyq]; exact tendsto_const_nhds
      · push Not at hyq
        have hev : ∀ᶠ n in atTop, (if Y ω ≤ qn n ω then (1:ℝ) else 0) = 0 := by
          have := (hqn_t ω).eventually (gt_mem_nhds hyq)
          filter_upwards [this] with n hn; exact if_neg (not_le.2 hn)
        rw [if_neg (not_le.2 hyq), mul_zero]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hev] with n hn; rw [hn, mul_zero]
  have hR : Tendsto (fun n => ∫ ω, G ω * cdf M (qn n ω) (θ ω) ∂P) atTop
      (𝓝 (∫ ω, G ω * cdf M (q ω) (θ ω) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => Gb)
      (fun n => hGaesm.mul (hcdfqn n))
      (integrable_const Gb) (fun n => Eventually.of_forall fun ω => ?_)
      (Eventually.of_forall fun ω => ?_)
    · rw [Real.norm_eq_abs, abs_mul]
      have h0 := cdf_nonneg M (qn n ω) (θ ω)
      have h1 := cdf_le_one M hprob (qn n ω) (θ ω)
      rw [abs_of_nonneg h0]; nlinarith [hGb ω, abs_nonneg (G ω)]
    · exact (((hcont (θ ω)).tendsto _).comp (hqn_t ω)).const_mul (G ω)
  exact tendsto_nhds_unique (hL.congr hlevel) hR

/-- The largest open set on which `cdfU M` is continuous. -/
def cdfOpen {d : ℕ} (M : Model d) : Set (ℝ × E d) :=
  ⋃₀ {B : Set (ℝ × E d) | IsOpen B ∧ ContinuousOn (cdfU M) B}

lemma isOpen_cdfOpen {d : ℕ} (M : Model d) : IsOpen (cdfOpen M) :=
  isOpen_sUnion fun _ hB => hB.1

lemma continuousOn_cdfOpen {d : ℕ} (M : Model d) : ContinuousOn (cdfU M) (cdfOpen M) := by
  intro x hx
  rcases hx with ⟨B, ⟨hBo, hBc⟩, hxB⟩
  exact (hBc.continuousAt (hBo.mem_nhds hxB)).continuousWithinAt

/-- Borel-measurable modification of `cdfU M` agreeing with `cdfU M` on every open set where
`cdfU M` is continuous. -/
noncomputable def cdfReg {d : ℕ} (M : Model d) : ℝ × E d → ℝ :=
  (cdfOpen M).indicator (cdfU M)

lemma measurable_cdfReg {d : ℕ} (M : Model d) : Measurable (cdfReg M) := by
  classical
  have hopen := isOpen_cdfOpen M
  have hcont := continuousOn_cdfOpen M
  refine measurable_of_isOpen fun U hU => ?_
  have heq : cdfReg M ⁻¹' U =
      (cdfOpen M ∩ cdfU M ⁻¹' U) ∪ ((cdfOpen M)ᶜ ∩ if (0 : ℝ) ∈ U then Set.univ else ∅) := by
    ext p
    by_cases hp : p ∈ cdfOpen M
    · simp [cdfReg, hp]
    · simp [cdfReg, hp]
  rw [heq]
  apply MeasurableSet.union
  · have hopen1 : IsOpen (cdfOpen M ∩ cdfU M ⁻¹' U) := by
      rw [isOpen_iff_mem_nhds]
      intro p ⟨hp1, hp2⟩
      have hc : ContinuousAt (cdfU M) p := (hcont.continuousAt (hopen.mem_nhds hp1))
      have h1 : cdfU M ⁻¹' U ∈ 𝓝 p := hc.preimage_mem_nhds (hU.mem_nhds hp2)
      exact Filter.inter_mem (hopen.mem_nhds hp1) h1
    exact hopen1.measurableSet
  · refine hopen.measurableSet.compl.inter ?_
    split_ifs <;> simp

lemma cdfReg_eq_of_ball {d : ℕ} (M : Model d) {p p' : ℝ × E d} {δ : ℝ}
    (hC3 : ContDiffOn ℝ 3 (cdfU M) (Metric.ball p δ)) (hp' : p' ∈ Metric.ball p δ) :
    cdfReg M p' = cdfU M p' := by
  have hmem : p' ∈ cdfOpen M := ⟨Metric.ball p δ, ⟨Metric.isOpen_ball, hC3.continuousOn⟩, hp'⟩
  exact Set.indicator_of_mem hmem _

/-- The SP stochastic gradient step vector `g_k` in (21). -/
noncomputable def spGrad {Ω : Type*} {d : ℕ} (c : ℕ → ℝ) (R : Run Ω d) (k : ℕ) (ω : Ω) : E d :=
  WithLp.toLp 2 (fun i : Fin d =>
    (-Ip c R k ω + Im c R k ω) / (2 * cbar c k (R.D k ω) * R.Δ k ω i))

/-- The conditional expectation of `spGrad` over `Δ_k` and `(Y^+, Y^-)`. -/
noncomputable def spAvg {d : ℕ} (M : Model d) (c : ℕ → ℝ) (k : ℕ) (q : ℝ) (D θ : E d) : E d :=
  (mfac D / (2 * c k)) • ((2 ^ d : ℝ)⁻¹ • ∑ b : Fin d → Bool,
      (-cdf M (q + cbar c k D * ⟪D, signVec b⟫) (θ + cbar c k D • signVec b) +
        cdf M (q - cbar c k D * ⟪D, signVec b⟫) (θ - cbar c k D • signVec b)) • signVec b)

lemma D_succ_eq {Ω : Type*} [m0 : MeasurableSpace Ω] {d : ℕ}
    {P : Measure Ω} {ℱ : Filtration ℕ m0} {M : Model d} {Θ : Set (E d)} {Proj : E d → E d}
    {I : Set ℝ} {Pq : ℝ → ℝ} {α β γ c : ℕ → ℝ} {R : Run Ω d}
    (hrun : IsSPQORun P ℱ M Θ Proj I Pq α β γ c R) (k : ℕ) (ω : Ω) :
    R.D (k + 1) ω = R.D k ω + β k • spGrad c R k ω := by
  ext i
  simpa [spGrad] using hrun.eq21 k ω i

lemma spAvg_eq {d : ℕ} (M : Model d) (c : ℕ → ℝ) (k : ℕ) (q : ℝ) (D θ : E d) :
    spAvg M c k q D θ = -M.dens q θ • D - gradθ M q θ + bias M c k q D θ := by
  unfold spAvg bias
  rw [neg_smul]
  abel

lemma spGrad_on_signVec {Ω : Type*} {d : ℕ} (c : ℕ → ℝ) (R : Run Ω d) (k : ℕ) (ω : Ω)
    (b : Fin d → Bool) (hΔ : R.Δ k ω = signVec b) :
    spGrad c R k ω = (mfac (R.D k ω) / (2 * c k) * (-Ip c R k ω + Im c R k ω)) • signVec b := by
  have hm0 : mfac (R.D k ω) ≠ 0 := by
    have : (1 : ℝ) ≤ mfac (R.D k ω) := le_max_left _ _
    linarith
  ext i
  simp only [spGrad, PiLp.smul_apply, smul_eq_mul, PiLp.toLp_apply, hΔ, signVec, cbar]
  cases b i <;> simp <;> field_simp

lemma abs_neg_Ip_add_Im_le {Ω : Type*} {d : ℕ} (c : ℕ → ℝ) (R : Run Ω d) (k : ℕ) (ω : Ω) :
    |-Ip c R k ω + Im c R k ω| ≤ 1 := by
  unfold Ip Im
  split_ifs <;> norm_num

lemma norm_spGrad_sq_le {Ω : Type*} {d : ℕ} (hd : 0 < d) (c : ℕ → ℝ) (R : Run Ω d) (k : ℕ)
    (ω : Ω) (hck : 0 < c k) (b : Fin d → Bool) (hΔ : R.Δ k ω = signVec b) :
    ‖spGrad c R k ω‖ ^ 2 ≤ (d + ‖R.D k ω‖ ^ 2) / (4 * c k ^ 2) := by
  rw [spGrad_on_signVec c R k ω b hΔ, norm_smul, Real.norm_eq_abs, norm_signVec, mul_pow,
    sq_abs, mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  have h1 : (-Ip c R k ω + Im c R k ω) ^ 2 ≤ 1 := by
    rw [← sq_abs]; nlinarith [abs_neg_Ip_add_Im_le c R k ω, abs_nonneg (-Ip c R k ω + Im c R k ω)]
  have hm2 := mfac_sq_le hd (R.D k ω)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have h2 : (mfac (R.D k ω) / (2 * c k)) ^ 2 * (-Ip c R k ω + Im c R k ω) ^ 2 * (d : ℝ)
      ≤ (mfac (R.D k ω) / (2 * c k)) ^ 2 * 1 * (d : ℝ) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (sq_nonneg _)) hd0.le
  calc (mfac (R.D k ω) / (2 * c k)) ^ 2 * (-Ip c R k ω + Im c R k ω) ^ 2 * (d : ℝ)
      ≤ (mfac (R.D k ω) / (2 * c k)) ^ 2 * 1 * (d : ℝ) := h2
    _ = mfac (R.D k ω) ^ 2 * d / (4 * c k ^ 2) := by ring
    _ ≤ (1 + ‖R.D k ω‖ ^ 2 / d) * d / (4 * c k ^ 2) := by gcongr
    _ = (d + ‖R.D k ω‖ ^ 2) / (4 * c k ^ 2) := by field_simp

lemma norm_spGrad_le {Ω : Type*} {d : ℕ} (hd : 0 < d) (c : ℕ → ℝ) (R : Run Ω d) (k : ℕ)
    (ω : Ω) (hck : 0 < c k) (b : Fin d → Bool) (hΔ : R.Δ k ω = signVec b) :
    ‖spGrad c R k ω‖ ≤ (Real.sqrt d + ‖R.D k ω‖) / (2 * c k) := by
  rw [spGrad_on_signVec c R k ω b hΔ, norm_smul, Real.norm_eq_abs, norm_signVec, abs_mul]
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hsd0 : 0 < Real.sqrt d := Real.sqrt_pos.2 hd0
  have hm0 : 0 ≤ mfac (R.D k ω) / (2 * c k) := by
    have : (1 : ℝ) ≤ mfac (R.D k ω) := le_max_left _ _; positivity
  rw [abs_of_nonneg hm0]
  have hmle : mfac (R.D k ω) ≤ 1 + ‖R.D k ω‖ / Real.sqrt d := by
    unfold mfac; apply max_le <;> linarith [div_nonneg (norm_nonneg (R.D k ω)) hsd0.le]
  have hI := abs_neg_Ip_add_Im_le c R k ω
  calc mfac (R.D k ω) / (2 * c k) * |-Ip c R k ω + Im c R k ω| * Real.sqrt d
      ≤ mfac (R.D k ω) / (2 * c k) * 1 * Real.sqrt d := by
        gcongr
    _ ≤ (1 + ‖R.D k ω‖ / Real.sqrt d) / (2 * c k) * 1 * Real.sqrt d := by gcongr
    _ = (Real.sqrt d + ‖R.D k ω‖) / (2 * c k) := by field_simp

/-- The `ℱ_k`-measurable full-measure event on which `Δ_j ∈ {±1}^d` for all `j < k`. -/
def goodEvent {Ω : Type*} {d : ℕ} (R : Run Ω d) (k : ℕ) : Set Ω :=
  ⋂ j ∈ Finset.range k, {ω | R.Δ j ω ∈ Set.range (signVec (d := d))}

lemma goodEvent_meas {Ω : Type*} [m0 : MeasurableSpace Ω] {d : ℕ}
    {P : Measure Ω} {ℱ : Filtration ℕ m0} {M : Model d} {Θ : Set (E d)} {Proj : E d → E d}
    {I : Set ℝ} {Pq : ℝ → ℝ} {α β γ c : ℕ → ℝ} {R : Run Ω d}
    (hrun : IsSPQORun P ℱ M Θ Proj I Pq α β γ c R) (k : ℕ) :
    MeasurableSet[ℱ k] (goodEvent R k) := by
  unfold goodEvent
  refine Finset.measurableSet_biInter _ fun j hj => ?_
  rw [Finset.mem_range] at hj
  have hΔj : Measurable[ℱ k] (R.Δ j) :=
    ((hrun.meas_Δ j).mono (ℱ.mono (by omega : j + 1 ≤ k))).measurable
  exact hΔj (Set.finite_range _).measurableSet

lemma goodEvent_ae {Ω : Type*} [m0 : MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (M : Model d) (Θ : Set (E d)) (Proj : E d → E d) (I : Set ℝ) (Pq : ℝ → ℝ)
    (α β γ c : ℕ → ℝ) (R : Run Ω d)
    (hrun : IsSPQORun P ℱ M Θ Proj I Pq α β γ c R) (hA2 : A2 P ℱ R) (k : ℕ) :
    ∀ᵐ ω ∂P, ω ∈ goodEvent R k := by
  induction k with
  | zero =>
    refine Eventually.of_forall fun ω => ?_
    simp [goodEvent]
  | succ k ih =>
    have hnext := ae_Delta_mem_range P (R.Δ k)
      (((hrun.meas_Δ k).mono (ℱ.le (k + 1))).measurable) (hA2 k).1
    filter_upwards [ih, hnext] with ω h1 h2
    simp only [goodEvent, Set.mem_iInter, Finset.mem_range] at h1 ⊢
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hlt | rfl
    · exact h1 j hlt
    · exact h2

lemma goodEvent_succ_subset {Ω : Type*} {d : ℕ} (R : Run Ω d) (k : ℕ) :
    goodEvent R (k + 1) ⊆ goodEvent R k := by
  intro ω hω
  simp only [goodEvent, Set.mem_iInter, Finset.mem_range] at hω ⊢
  intro j hj; exact hω j (by omega)

lemma goodEvent_succ_mem_Delta {Ω : Type*} {d : ℕ} (R : Run Ω d) (k : ℕ) {ω : Ω}
    (hω : ω ∈ goodEvent R (k + 1)) : ∃ b : Fin d → Bool, R.Δ k ω = signVec b := by
  simp only [goodEvent, Set.mem_iInter, Finset.mem_range] at hω
  obtain ⟨b, hb⟩ := hω k (Nat.lt_succ_self k)
  exact ⟨b, hb.symm⟩

/-- Deterministic bound `B_k` on `‖D_k(ω)‖` valid everywhere on `goodEvent R k`. -/
noncomputable def Dbound {d : ℕ} (β c : ℕ → ℝ) (D₀ : E d) : ℕ → ℝ
  | 0 => ‖D₀‖
  | k + 1 => Dbound β c D₀ k + β k * (Real.sqrt d + Dbound β c D₀ k) / (2 * c k)

lemma Dbound_nonneg {d : ℕ} (β c : ℕ → ℝ) (D₀ : E d)
    (hβ : ∀ k, 0 < β k) (hc : ∀ k, 0 < c k) (k : ℕ) : 0 ≤ Dbound β c D₀ k := by
  induction k with
  | zero => exact norm_nonneg _
  | succ k ih =>
    simp only [Dbound]
    have := hβ k; have := hc k; positivity

lemma norm_D_le_Dbound {Ω : Type*} [m0 : MeasurableSpace Ω] {d : ℕ} (hd : 0 < d)
    {P : Measure Ω} {ℱ : Filtration ℕ m0} {M : Model d} {Θ : Set (E d)} {Proj : E d → E d}
    {I : Set ℝ} {Pq : ℝ → ℝ} {α β γ c : ℕ → ℝ} {R : Run Ω d}
    (hrun : IsSPQORun P ℱ M Θ Proj I Pq α β γ c R)
    (hβ : ∀ k, 0 < β k) (hc : ∀ k, 0 < c k)
    {D₀ : E d} (hD₀ : ∀ ω, R.D 0 ω = D₀) :
    ∀ k ω, ω ∈ goodEvent R k → ‖R.D k ω‖ ≤ Dbound β c D₀ k := by
  intro k
  induction k with
  | zero => intro ω _; rw [hD₀ ω]; exact le_rfl
  | succ k ih =>
    intro ω hω
    have hk : ω ∈ goodEvent R k := goodEvent_succ_subset R k hω
    obtain ⟨b, hb⟩ := goodEvent_succ_mem_Delta R k hω
    have h1 := ih ω hk
    have h2 := norm_spGrad_le hd c R k ω (hc k) b hb
    rw [D_succ_eq hrun k ω]
    calc ‖R.D k ω + β k • spGrad c R k ω‖
        ≤ ‖R.D k ω‖ + ‖β k • spGrad c R k ω‖ := norm_add_le _ _
      _ = ‖R.D k ω‖ + β k * ‖spGrad c R k ω‖ := by
          rw [norm_smul, Real.norm_of_nonneg (hβ k).le]
      _ ≤ Dbound β c D₀ k + β k * ((Real.sqrt d + ‖R.D k ω‖) / (2 * c k)) := by
          have := (hβ k).le; gcongr
      _ ≤ Dbound β c D₀ k + β k * ((Real.sqrt d + Dbound β c D₀ k) / (2 * c k)) := by
          have := (hβ k).le; have := (hc k).le; gcongr
      _ = Dbound β c D₀ (k + 1) := by simp only [Dbound]; ring

lemma spGrad_meas {Ω : Type*} [m0 : MeasurableSpace Ω] {d : ℕ}
    {P : Measure Ω} {ℱ : Filtration ℕ m0} {M : Model d} {Θ : Set (E d)} {Proj : E d → E d}
    {I : Set ℝ} {Pq : ℝ → ℝ} {α β γ c : ℕ → ℝ} {R : Run Ω d}
    (hrun : IsSPQORun P ℱ M Θ Proj I Pq α β γ c R) (hβ : ∀ k, 0 < β k) (k : ℕ) :
    StronglyMeasurable (spGrad c R k) := by
  have heq : spGrad c R k = fun ω => (β k)⁻¹ • (R.D (k + 1) ω - R.D k ω) := by
    funext ω; rw [D_succ_eq hrun k ω, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ (hβ k).ne',
      one_smul]
  rw [heq]
  exact (((hrun.adapted_D (k + 1)).mono (ℱ.le (k + 1))).sub
    ((hrun.adapted_D k).mono (ℱ.le k))).const_smul (β k)⁻¹

lemma mfac_stronglyMeasurable {Ω : Type*} {m : MeasurableSpace Ω} {d : ℕ} {D : Ω → E d}
    (hD : StronglyMeasurable[m] D) : StronglyMeasurable[m] (fun ω => mfac (D ω)) := by
  unfold mfac
  exact (measurable_const.sup (hD.measurable.norm.div_const _)).stronglyMeasurable

lemma cbar_stronglyMeasurable {Ω : Type*} {m : MeasurableSpace Ω} {d : ℕ} (c : ℕ → ℝ) (k : ℕ)
    {D : Ω → E d} (hD : StronglyMeasurable[m] D) :
    StronglyMeasurable[m] (fun ω => cbar c k (D ω)) := by
  unfold cbar
  exact (measurable_const.div (mfac_stronglyMeasurable hD).measurable).stronglyMeasurable

/-- Main conditional-expectation identity for the SP estimator `spGrad`:
for any bounded `ℱ_k`-measurable `H` supported on `goodEvent R k`,
`E[⟪H, spGrad c R k⟫] = E[⟪H, spAvg M c k (q_k, D_k, θ_k)⟫]` whenever `c_k * d < δ`. -/
lemma cond_sp {Ω : Type*} [m0 : MeasurableSpace Ω] {d : ℕ} (hd : 0 < d)
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (M : Model d) (Θ : Set (E d)) (Proj : E d → E d) (I : Set ℝ) (Pq : ℝ → ℝ)
    (α β γ c : ℕ → ℝ) (R : Run Ω d)
    (hM : IsQuantileModel M Θ)
    (hrun : IsSPQORun P ℱ M Θ Proj I Pq α β γ c R)
    (hA2 : A2 P ℱ R) (hβ : ∀ k, 0 < β k) (hc : ∀ k, 0 < c k)
    (k : ℕ) (δ Qk Bk Hb : ℝ) (hQk : 0 ≤ Qk) (hBk : 0 ≤ Bk) (hHb : 0 ≤ Hb)
    (hsmall : c k * d < δ)
    (hqb : ∀ ω, |R.q k ω| ≤ Qk)
    (hDb : ∀ ω, ω ∈ goodEvent R k → ‖R.D k ω‖ ≤ Bk)
    (hA1k : ∀ᵐ ω ∂P, ContDiffOn ℝ 3 (cdfU M) (Metric.ball (R.q k ω, R.θ k ω) δ))
    (H : Ω → E d) (hHm : StronglyMeasurable[ℱ k] H)
    (hHnorm : ∀ ω, ‖H ω‖ ≤ Hb) (hHsupp : ∀ ω, ω ∉ goodEvent R k → H ω = 0) :
    Integrable (fun ω => ⟪H ω, spGrad c R k ω⟫) P ∧
    Integrable (fun ω => ⟪H ω, spAvg M c k (R.q k ω) (R.D k ω) (R.θ k ω)⟫) P ∧
    ∫ ω, ⟪H ω, spGrad c R k ω⟫ ∂P =
      ∫ ω, ⟪H ω, spAvg M c k (R.q k ω) (R.D k ω) (R.θ k ω)⟫ ∂P := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hsd0 : 0 < Real.sqrt d := Real.sqrt_pos.2 hd0
  have hck := hc k
  have hcontcdf : ∀ θ, Continuous (fun y => cdf M y θ) := fun θ =>
    continuous_iff_continuousAt.2 fun y => (hM.hasDens y θ).continuousAt
  have hΔm0 : Measurable[m0] (R.Δ k) := ((hrun.meas_Δ k).mono (ℱ.le (k + 1))).measurable
  have hmle : ℱ k ⊔ MeasurableSpace.comap (R.Δ k) inferInstance ≤ m0 :=
    sup_le (ℱ.le k) hΔm0.comap_le
  have hDmk : StronglyMeasurable[ℱ k] (R.D k) := hrun.adapted_D k
  have hqmk : StronglyMeasurable[ℱ k] (R.q k) := hrun.adapted_q k
  have hθmk : StronglyMeasurable[ℱ k] (R.θ k) := hrun.adapted_θ k
  have hconst_r : ∀ x : ℝ, StronglyMeasurable[ℱ k] (fun _ : Ω => x) :=
    fun _ => stronglyMeasurable_const
  have hconst_sm : ∀ v : E d, StronglyMeasurable[ℱ k] (fun _ : Ω => v) :=
    fun _ => stronglyMeasurable_const
  have hmfac_meas : StronglyMeasurable[ℱ k] (fun ω => mfac (R.D k ω)) :=
    mfac_stronglyMeasurable hDmk
  have hcbar_meas : StronglyMeasurable[ℱ k] (fun ω => cbar c k (R.D k ω)) :=
    cbar_stronglyMeasurable c k hDmk
  set mB := max 1 (Bk / Real.sqrt d) with hmB
  have hmB0 : 0 ≤ mB := le_trans zero_le_one (le_max_left _ _)
  set Mb := mB / (2 * c k) * (Hb * Real.sqrt d) with hMb
  have hMb0 : 0 ≤ Mb := by positivity
  -- Helper per sign vector b
  set Hb_fn : (Fin d → Bool) → Ω → ℝ :=
    fun b ω => mfac (R.D k ω) / (2 * c k) * ⟪H ω, signVec b⟫ with hHbfn
  have hHbm : ∀ b, StronglyMeasurable[ℱ k] (Hb_fn b) := fun b =>
    (hmfac_meas.div (hconst_r (2 * c k))).mul (hHm.inner (hconst_sm (signVec b)))
  have hHb_bd : ∀ b ω, |Hb_fn b ω| ≤ Mb := by
    intro b ω
    by_cases hω : ω ∈ goodEvent R k
    · have hmle' : mfac (R.D k ω) ≤ mB :=
        max_le_max le_rfl (div_le_div_of_nonneg_right (hDb ω hω) hsd0.le)
      have hmpos : 0 ≤ mfac (R.D k ω) / (2 * c k) := by
        have : (1 : ℝ) ≤ mfac (R.D k ω) := le_max_left _ _; positivity
      simp only [hHbfn, abs_mul, abs_of_nonneg hmpos]
      have h1 : |⟪H ω, signVec b⟫| ≤ Hb * Real.sqrt d := by
        calc |⟪H ω, signVec b⟫| ≤ ‖H ω‖ * ‖signVec b‖ := abs_real_inner_le_norm _ _
          _ ≤ Hb * Real.sqrt d := by rw [norm_signVec]; gcongr; exact hHnorm ω
      calc mfac (R.D k ω) / (2 * c k) * |⟪H ω, signVec b⟫|
          ≤ mB / (2 * c k) * (Hb * Real.sqrt d) :=
            mul_le_mul (div_le_div_of_nonneg_right hmle' (by positivity)) h1 (abs_nonneg _)
              (by positivity)
        _ = Mb := rfl
    · simp [hHbfn, hHsupp ω hω, hMb0]
  set Xb : (Fin d → Bool) → Ω → ℝ := fun b ω => if R.Δ k ω = signVec b then 1 else 0 with hXb
  have hXbm_comap : ∀ b, Measurable[MeasurableSpace.comap (R.Δ k) inferInstance] (Xb b) := by
    intro b
    refine Measurable.ite ?_ measurable_const measurable_const
    exact ⟨{signVec b}, MeasurableSet.singleton _, rfl⟩
  have hXbm_m : ∀ b, StronglyMeasurable[ℱ k ⊔ MeasurableSpace.comap (R.Δ k) inferInstance] (Xb b) :=
    fun b => ((hXbm_comap b).mono (@le_sup_right _ _ (ℱ k) _) le_rfl).stronglyMeasurable
  set Gb : (Fin d → Bool) → Ω → ℝ := fun b ω => Xb b ω * Hb_fn b ω with hGb
  have hGbm : ∀ b, StronglyMeasurable[ℱ k ⊔ MeasurableSpace.comap (R.Δ k) inferInstance] (Gb b) :=
    fun b => (hXbm_m b).mul ((hHbm b).mono le_sup_left)
  have hGb_bd : ∀ b ω, |Gb b ω| ≤ Mb := by
    intro b ω
    simp only [hGb, hXb]
    split_ifs
    · rw [one_mul]; exact hHb_bd b ω
    · rw [zero_mul, abs_zero]; exact hMb0
  set Tpb : (Fin d → Bool) → Ω → ℝ :=
    fun b ω => R.q k ω + cbar c k (R.D k ω) * ⟪R.D k ω, signVec b⟫ with hTpb
  set Tmb : (Fin d → Bool) → Ω → ℝ :=
    fun b ω => R.q k ω - cbar c k (R.D k ω) * ⟪R.D k ω, signVec b⟫ with hTmb
  have hTpbm : ∀ b, StronglyMeasurable[ℱ k] (Tpb b) := fun b =>
    hqmk.add (hcbar_meas.mul (hDmk.inner stronglyMeasurable_const))
  have hTmbm : ∀ b, StronglyMeasurable[ℱ k] (Tmb b) := fun b =>
    hqmk.sub (hcbar_meas.mul (hDmk.inner stronglyMeasurable_const))
  have hTpb_bd : ∀ b ω, |Tpb b ω| ≤ Qk + c k * d := fun b ω =>
    (abs_add_le _ _).trans (add_le_add (hqb ω) (abs_cbar_inner_le hd c k hck (R.D k ω) b))
  have hTmb_bd : ∀ b ω, |Tmb b ω| ≤ Qk + c k * d := fun b ω =>
    (abs_sub _ _).trans (add_le_add (hqb ω) (abs_cbar_inner_le hd c k hck (R.D k ω) b))
  set θpb : (Fin d → Bool) → Ω → E d :=
    fun b ω => R.θ k ω + cbar c k (R.D k ω) • signVec b with hθpb
  set θmb : (Fin d → Bool) → Ω → E d :=
    fun b ω => R.θ k ω - cbar c k (R.D k ω) • signVec b with hθmb
  have hθpbm : ∀ b, StronglyMeasurable[ℱ k] (θpb b) := fun b =>
    hθmk.add (hcbar_meas.smul stronglyMeasurable_const)
  have hθmbm : ∀ b, StronglyMeasurable[ℱ k] (θmb b) := fun b =>
    hθmk.sub (hcbar_meas.smul stronglyMeasurable_const)
  -- Per-sign-vector integral identities for Ip and Im
  have hYp_meas : Measurable (R.Yp k) := ((hrun.meas_Yp k).mono (ℱ.le (k + 1))).measurable
  have hYm_meas : Measurable (R.Ym k) := ((hrun.meas_Ym k).mono (ℱ.le (k + 1))).measurable
  have hper_b : ∀ b : Fin d → Bool,
      Integrable (fun ω => Gb b ω * (-Ip c R k ω + Im c R k ω)) P ∧
      Integrable (fun ω => Hb_fn b ω *
        (-cdf M (Tpb b ω) (θpb b ω) + cdf M (Tmb b ω) (θmb b ω))) P ∧
      ∫ ω, Gb b ω * (-Ip c R k ω + Im c R k ω) ∂P =
        ((2 : ℝ) ^ d)⁻¹ * ∫ ω, Hb_fn b ω *
          (-cdf M (Tpb b ω) (θpb b ω) + cdf M (Tmb b ω) (θmb b ω)) ∂P := by
    intro b
    have hcp := cond_threshold hmle P M hM.isProb hcontcdf (R.Yp k) hYp_meas
      (fun ω => R.θ k ω + cbar c k (R.D k ω) • R.Δ k ω) (Tpb b) (Gb b)
      ((hTpbm b).mono le_sup_left) (hGbm b) (Qk + c k * d) Mb (hTpb_bd b) (hGb_bd b)
      (fun v => hrun.sampleP k (Set.Iic v) measurableSet_Iic)
    have hcm := cond_threshold hmle P M hM.isProb hcontcdf (R.Ym k) hYm_meas
      (fun ω => R.θ k ω - cbar c k (R.D k ω) • R.Δ k ω) (Tmb b) (Gb b)
      ((hTmbm b).mono le_sup_left) (hGbm b) (Qk + c k * d) Mb (hTmb_bd b) (hGb_bd b)
      (fun v => hrun.sampleM k (Set.Iic v) measurableSet_Iic)
    -- Pointwise agreement of Ip/Im with fixed-b threshold on {Δ_k = s_b}
    have hIpeq : (fun ω => Gb b ω * Ip c R k ω) =
        fun ω => Gb b ω * (if R.Yp k ω ≤ Tpb b ω then (1 : ℝ) else 0) := by
      funext ω; by_cases h1 : R.Δ k ω = signVec b <;> simp [hGb, hXb, Ip, hTpb, h1]
    have hImeq : (fun ω => Gb b ω * Im c R k ω) =
        fun ω => Gb b ω * (if R.Ym k ω ≤ Tmb b ω then (1 : ℝ) else 0) := by
      funext ω; by_cases h1 : R.Δ k ω = signVec b <;> simp [hGb, hXb, Im, hTmb, h1]
    have hFpeq : (fun ω => Gb b ω * cdf M (Tpb b ω) (R.θ k ω + cbar c k (R.D k ω) • R.Δ k ω)) =
        fun ω => Xb b ω * (Hb_fn b ω * cdf M (Tpb b ω) (θpb b ω)) := by
      funext ω; by_cases h1 : R.Δ k ω = signVec b <;> simp [hGb, hXb, hθpb, h1]
    have hFmeq : (fun ω => Gb b ω * cdf M (Tmb b ω) (R.θ k ω - cbar c k (R.D k ω) • R.Δ k ω)) =
        fun ω => Xb b ω * (Hb_fn b ω * cdf M (Tmb b ω) (θmb b ω)) := by
      funext ω; by_cases h1 : R.Δ k ω = signVec b <;> simp [hGb, hXb, hθmb, h1]
    -- a.e. agreement of cdf with Borel-measurable cdfReg
    have hregp_ae : ∀ᵐ ω ∂P, cdf M (Tpb b ω) (θpb b ω) = cdfReg M (Tpb b ω, θpb b ω) := by
      filter_upwards [hA1k] with ω hω
      have hmem : (Tpb b ω, θpb b ω) ∈ Metric.ball (R.q k ω, R.θ k ω) δ := by
        rw [Metric.mem_ball, dist_eq_norm]
        have heq : (Tpb b ω, θpb b ω) - (R.q k ω, R.θ k ω)
            = (cbar c k (R.D k ω) * ⟪R.D k ω, signVec b⟫, cbar c k (R.D k ω) • signVec b) := by
          ext <;> simp [hTpb, hθpb]
        rw [heq]
        exact (norm_pert_le hd c k hck (R.D k ω) b).trans_lt hsmall
      exact (cdfReg_eq_of_ball M hω hmem).symm
    have hregm_ae : ∀ᵐ ω ∂P, cdf M (Tmb b ω) (θmb b ω) = cdfReg M (Tmb b ω, θmb b ω) := by
      filter_upwards [hA1k] with ω hω
      have hmem : (Tmb b ω, θmb b ω) ∈ Metric.ball (R.q k ω, R.θ k ω) δ := by
        rw [Metric.mem_ball, dist_eq_norm]
        have heq : (Tmb b ω, θmb b ω) - (R.q k ω, R.θ k ω)
            = -((cbar c k (R.D k ω) * ⟪R.D k ω, signVec b⟫, cbar c k (R.D k ω) • signVec b)) := by
          ext <;> simp [hTmb, hθmb, sub_eq_add_neg]
        rw [heq, norm_neg]
        exact (norm_pert_le hd c k hck (R.D k ω) b).trans_lt hsmall
      exact (cdfReg_eq_of_ball M hω hmem).symm
    -- ℱ_k-measurability of regularized terms
    set Zp : Ω → ℝ := fun ω => Hb_fn b ω * cdfReg M (Tpb b ω, θpb b ω) with hZp
    set Zm : Ω → ℝ := fun ω => Hb_fn b ω * cdfReg M (Tmb b ω, θmb b ω) with hZm
    have hZpm : Measurable[ℱ k] Zp :=
      (hHbm b).measurable.mul
        ((measurable_cdfReg M).comp ((hTpbm b).measurable.prodMk (hθpbm b).measurable))
    have hZmm : Measurable[ℱ k] Zm :=
      (hHbm b).measurable.mul
        ((measurable_cdfReg M).comp ((hTmbm b).measurable.prodMk (hθmbm b).measurable))
    -- Independence via A2
    have hind_p : IndepFun (Xb b) Zp P :=
      indep_of_indep_of_le (hA2 k).2 (hXbm_comap b).comap_le hZpm.comap_le
    have hind_m : IndepFun (Xb b) Zm P :=
      indep_of_indep_of_le (hA2 k).2 (hXbm_comap b).comap_le hZmm.comap_le
    have hXaesm : AEStronglyMeasurable (Xb b) P :=
      ((hXbm_comap b).mono hΔm0.comap_le le_rfl).aestronglyMeasurable
    have hZpaesm : AEStronglyMeasurable Zp P := (hZpm.mono (ℱ.le k) le_rfl).aestronglyMeasurable
    have hZmaesm : AEStronglyMeasurable Zm P := (hZmm.mono (ℱ.le k) le_rfl).aestronglyMeasurable
    have hEX : ∫ ω, Xb b ω ∂P = ((2 : ℝ) ^ d)⁻¹ :=
      integral_ind_Delta_eq P (R.Δ k) hΔm0 (hA2 k).1 b
    -- Integrability of Ip and Im terms
    have hIp_int : Integrable (fun ω => Gb b ω * Ip c R k ω) P := by
      rw [hIpeq]
      have hm1 : Measurable (fun ω => if R.Yp k ω ≤ Tpb b ω then (1 : ℝ) else 0) :=
        Measurable.ite (measurableSet_le hYp_meas ((hTpbm b).mono (ℱ.le k)).measurable)
          measurable_const measurable_const
      refine Integrable.of_bound (((hGbm b).mono hmle).aestronglyMeasurable.mul
        hm1.aestronglyMeasurable) Mb (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      have h1 : |(if R.Yp k ω ≤ Tpb b ω then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
      nlinarith [hGb_bd b ω, abs_nonneg (Gb b ω),
        abs_nonneg (if R.Yp k ω ≤ Tpb b ω then (1 : ℝ) else 0)]
    have hIm_int : Integrable (fun ω => Gb b ω * Im c R k ω) P := by
      rw [hImeq]
      have hm1 : Measurable (fun ω => if R.Ym k ω ≤ Tmb b ω then (1 : ℝ) else 0) :=
        Measurable.ite (measurableSet_le hYm_meas ((hTmbm b).mono (ℱ.le k)).measurable)
          measurable_const measurable_const
      refine Integrable.of_bound (((hGbm b).mono hmle).aestronglyMeasurable.mul
        hm1.aestronglyMeasurable) Mb (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      have h1 : |(if R.Ym k ω ≤ Tmb b ω then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
      nlinarith [hGb_bd b ω, abs_nonneg (Gb b ω),
        abs_nonneg (if R.Ym k ω ≤ Tmb b ω then (1 : ℝ) else 0)]
    have hFp_int : Integrable (fun ω => Hb_fn b ω * cdf M (Tpb b ω) (θpb b ω)) P := by
      have haesm : AEStronglyMeasurable (fun ω => Hb_fn b ω * cdf M (Tpb b ω) (θpb b ω)) P :=
        hZpaesm.congr (hregp_ae.mono fun ω h => by simp [hZp, h])
      refine Integrable.of_bound haesm Mb (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      have h0 := cdf_nonneg M (Tpb b ω) (θpb b ω)
      have h1 := cdf_le_one M hM.isProb (Tpb b ω) (θpb b ω)
      rw [abs_of_nonneg h0]; nlinarith [hHb_bd b ω, abs_nonneg (Hb_fn b ω)]
    have hFm_int : Integrable (fun ω => Hb_fn b ω * cdf M (Tmb b ω) (θmb b ω)) P := by
      have haesm : AEStronglyMeasurable (fun ω => Hb_fn b ω * cdf M (Tmb b ω) (θmb b ω)) P :=
        hZmaesm.congr (hregm_ae.mono fun ω h => by simp [hZm, h])
      refine Integrable.of_bound haesm Mb (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      have h0 := cdf_nonneg M (Tmb b ω) (θmb b ω)
      have h1 := cdf_le_one M hM.isProb (Tmb b ω) (θmb b ω)
      rw [abs_of_nonneg h0]; nlinarith [hHb_bd b ω, abs_nonneg (Hb_fn b ω)]
    -- Compute Ip integral
    have hint_p : ∫ ω, Gb b ω * Ip c R k ω ∂P
        = ((2 : ℝ) ^ d)⁻¹ * ∫ ω, Hb_fn b ω * cdf M (Tpb b ω) (θpb b ω) ∂P := by
      calc ∫ ω, Gb b ω * Ip c R k ω ∂P
          = ∫ ω, Gb b ω * (if R.Yp k ω ≤ Tpb b ω then 1 else 0) ∂P := by rw [hIpeq]
        _ = ∫ ω, Gb b ω * cdf M (Tpb b ω) (R.θ k ω + cbar c k (R.D k ω) • R.Δ k ω) ∂P := hcp.2
        _ = ∫ ω, Xb b ω * (Hb_fn b ω * cdf M (Tpb b ω) (θpb b ω)) ∂P := by rw [hFpeq]
        _ = ∫ ω, Xb b ω * Zp ω ∂P :=
            integral_congr_ae (hregp_ae.mono fun ω h => by simp [hZp, h])
        _ = (∫ ω, Xb b ω ∂P) * (∫ ω, Zp ω ∂P) :=
            hind_p.integral_fun_mul_eq_mul_integral hXaesm hZpaesm
        _ = ((2 : ℝ) ^ d)⁻¹ * ∫ ω, Hb_fn b ω * cdf M (Tpb b ω) (θpb b ω) ∂P := by
            rw [hEX]; congr 1
            exact integral_congr_ae (hregp_ae.mono fun ω h => by simp [hZp, h])
    -- Compute Im integral
    have hint_m : ∫ ω, Gb b ω * Im c R k ω ∂P
        = ((2 : ℝ) ^ d)⁻¹ * ∫ ω, Hb_fn b ω * cdf M (Tmb b ω) (θmb b ω) ∂P := by
      calc ∫ ω, Gb b ω * Im c R k ω ∂P
          = ∫ ω, Gb b ω * (if R.Ym k ω ≤ Tmb b ω then 1 else 0) ∂P := by rw [hImeq]
        _ = ∫ ω, Gb b ω * cdf M (Tmb b ω) (R.θ k ω - cbar c k (R.D k ω) • R.Δ k ω) ∂P := hcm.2
        _ = ∫ ω, Xb b ω * (Hb_fn b ω * cdf M (Tmb b ω) (θmb b ω)) ∂P := by rw [hFmeq]
        _ = ∫ ω, Xb b ω * Zm ω ∂P :=
            integral_congr_ae (hregm_ae.mono fun ω h => by simp [hZm, h])
        _ = (∫ ω, Xb b ω ∂P) * (∫ ω, Zm ω ∂P) :=
            hind_m.integral_fun_mul_eq_mul_integral hXaesm hZmaesm
        _ = ((2 : ℝ) ^ d)⁻¹ * ∫ ω, Hb_fn b ω * cdf M (Tmb b ω) (θmb b ω) ∂P := by
            rw [hEX]; congr 1
            exact integral_congr_ae (hregm_ae.mono fun ω h => by simp [hZm, h])
    have eL : (fun ω => Gb b ω * (-Ip c R k ω + Im c R k ω))
        = fun ω => Gb b ω * Im c R k ω - Gb b ω * Ip c R k ω := by funext ω; ring
    have eR : (fun ω => Hb_fn b ω * (-cdf M (Tpb b ω) (θpb b ω) + cdf M (Tmb b ω) (θmb b ω)))
        = fun ω => Hb_fn b ω * cdf M (Tmb b ω) (θmb b ω) -
          Hb_fn b ω * cdf M (Tpb b ω) (θpb b ω) := by funext ω; ring
    refine ⟨?_, ?_, ?_⟩
    · rw [eL]; exact hIm_int.sub hIp_int
    · rw [eR]; exact hFm_int.sub hFp_int
    · rw [eL, eR, integral_sub hIm_int hIp_int, integral_sub hFm_int hFp_int, hint_p, hint_m]
      ring
  -- Sum over all b : Fin d → Bool
  have hae_rad := ae_Delta_mem_range P (R.Δ k) hΔm0 (hA2 k).1
  have hsumL_ae : (fun ω => ⟪H ω, spGrad c R k ω⟫) =ᵐ[P]
      fun ω => ∑ b : Fin d → Bool, Gb b ω * (-Ip c R k ω + Im c R k ω) := by
    filter_upwards [hae_rad] with ω hω
    rcases hω with ⟨b₀, hb₀⟩
    rw [Finset.sum_eq_single_of_mem b₀ (Finset.mem_univ _)]
    · rw [spGrad_on_signVec c R k ω b₀ hb₀.symm, real_inner_smul_right]
      simp only [hGb, hXb, hHbfn, hb₀.symm, if_true, one_mul]; ring
    · intro b _ hne
      have : R.Δ k ω ≠ signVec b := fun h => hne (signVec_injective (h.symm.trans hb₀.symm))
      simp [hGb, hXb, this]
  have hsumR_eq : (fun ω => ⟪H ω, spAvg M c k (R.q k ω) (R.D k ω) (R.θ k ω)⟫) =
      fun ω => ∑ b : Fin d → Bool, ((2 : ℝ) ^ d)⁻¹ * (Hb_fn b ω *
        (-cdf M (Tpb b ω) (θpb b ω) + cdf M (Tmb b ω) (θmb b ω))) := by
    funext ω
    simp only [spAvg, real_inner_smul_right, inner_sum, hHbfn, hTpb, hTmb, hθpb, hθmb,
      Finset.mul_sum]
    apply Finset.sum_congr rfl; intro b _; ring
  have hIntL : Integrable (fun ω => ⟪H ω, spGrad c R k ω⟫) P :=
    (integrable_finsetSum _ fun b _ => (hper_b b).1).congr hsumL_ae.symm
  have hIntR : Integrable (fun ω => ⟪H ω, spAvg M c k (R.q k ω) (R.D k ω) (R.θ k ω)⟫) P := by
    rw [hsumR_eq]
    exact integrable_finsetSum _ fun b _ => (hper_b b).2.1.const_mul _
  refine ⟨hIntL, hIntR, ?_⟩
  rw [integral_congr_ae hsumL_ae, hsumR_eq,
    integral_finsetSum _ (fun b _ => (hper_b b).1),
    integral_finsetSum _ (fun b _ => (hper_b b).2.1.const_mul _)]
  apply Finset.sum_congr rfl; intro b _
  rw [integral_const_mul, (hper_b b).2.2]

end SPQOCond

/-! ### Part 3: Polynomial-step exponent utilities and weighted-sum unrolling -/

namespace SPQOSeq
open QuantileSPQO.Rate

noncomputable def Ssum (u w : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 k, (∏ j ∈ Finset.Ioc i k, (1 - u j)) * u i * w i

lemma Ssum_succ (u w : ℕ → ℝ) (k : ℕ) :
    Ssum u w (k + 1) = (1 - u (k + 1)) * Ssum u w k + u (k + 1) * w (k + 1) := by
  unfold Ssum
  rw [Finset.sum_Icc_succ_top (by omega), Finset.mul_sum]
  simp only [Finset.Ioc_self, Finset.prod_empty, one_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_Icc] at hi
  rw [Finset.prod_Ioc_succ_top (by omega)]
  ring

lemma Ssum_nonneg (u w : ℕ → ℝ) (hu0 : ∀ j, 1 ≤ j → 0 ≤ u j) (hu1 : ∀ j, 1 ≤ j → u j ≤ 1)
    (hw0 : ∀ j, 1 ≤ j → 0 ≤ w j) (k : ℕ) : 0 ≤ Ssum u w k := by
  unfold Ssum
  apply Finset.sum_nonneg
  intro i hi
  rw [Finset.mem_Icc] at hi
  refine mul_nonneg (mul_nonneg (Finset.prod_nonneg fun j hj => ?_) (hu0 i hi.1)) (hw0 i hi.1)
  rw [Finset.mem_Ioc] at hj
  linarith [hu1 j (by omega)]

lemma Ssum_add (u w₁ w₂ : ℕ → ℝ) (k : ℕ) :
    Ssum u (fun i => w₁ i + w₂ i) k = Ssum u w₁ k + Ssum u w₂ k := by
  unfold Ssum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _; ring

lemma cmp (u w x : ℕ → ℝ) (N : ℕ) (hu0 : ∀ j, 1 ≤ j → 0 ≤ u j) (hu1 : ∀ j, 1 ≤ j → u j ≤ 1)
    (hw0 : ∀ j, 1 ≤ j → 0 ≤ w j) (hbase : x (N + 1) ≤ u (N + 1) * w (N + 1))
    (hstep : ∀ k, N + 1 ≤ k → x (k + 1) ≤ (1 - u (k + 1)) * x k + u (k + 1) * w (k + 1)) :
    ∀ k, N + 1 ≤ k → x k ≤ Ssum u w k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    rw [Ssum_succ]
    have h1 := Ssum_nonneg u w hu0 hu1 hw0 N
    have h2 : 0 ≤ 1 - u (N + 1) := by linarith [hu1 (N + 1) (by omega)]
    nlinarith
  | succ k hk ih =>
    rw [Ssum_succ]
    have h2 : 0 ≤ 1 - u (k + 1) := by linarith [hu1 (k + 1) (by omega)]
    calc x (k + 1) ≤ (1 - u (k + 1)) * x k + u (k + 1) * w (k + 1) := hstep k hk
      _ ≤ _ := by gcongr

lemma rp_div (A B p q X : ℝ) (hX : 0 < X) (hB : B ≠ 0) :
    (A / X ^ p) / (B / X ^ q) = A / B * X ^ (-(p - q)) := by
  rw [Real.rpow_neg hX.le, Real.rpow_sub hX]
  have h1 : 0 < X ^ p := Real.rpow_pos_of_pos hX p
  have h2 : 0 < X ^ q := Real.rpow_pos_of_pos hX q
  field_simp

lemma rp_pow_sq (X z : ℝ) (hX : 0 < X) : (X ^ z) ^ 2 = X ^ (2 * z) := by
  rw [mul_comm, Real.rpow_mul hX.le, Real.rpow_two]

lemma exp_neg_of_tendsto (f : ℕ → ℝ) (A e : ℝ) (hA : 0 < A)
    (hf : ∀ k : ℕ, f k = A * ((k : ℝ) + 1) ^ e) (ht : Tendsto f atTop (𝓝 0)) : e < 0 := by
  by_contra h; push Not at h
  have hge : ∀ k : ℕ, A ≤ f k := by
    intro k; rw [hf k]
    have : 1 ≤ ((k : ℝ) + 1) ^ e := Real.one_le_rpow (by linarith [k.cast_nonneg (α := ℝ)]) h
    nlinarith
  have := ge_of_tendsto' ht hge
  linarith

lemma exp_lt_of_summable (A e : ℝ) (hA : 0 < A)
    (hs : Summable (fun k : ℕ => A * ((k : ℝ) + 1) ^ e)) : e < -1 := by
  have h1 : Summable (fun k : ℕ => ((k : ℝ) + 1) ^ e) := by
    have := hs.mul_left A⁻¹
    refine this.congr (fun k => ?_); field_simp
  have h2 : Summable (fun k : ℕ => (((k + 1 : ℕ) : ℝ)) ^ e) :=
    h1.congr fun k => by push_cast; rfl
  have h3 : Summable (fun n : ℕ => (n : ℝ) ^ e) :=
    (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ e) 1).1 h2
  exact Real.summable_nat_rpow.1 h3

lemma kpow_le (k : ℕ) (hk : 1 ≤ k) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (k : ℝ) ^ (-s) ≤ 2 * ((k : ℝ) + 1) ^ (-s) := by
  have hk0 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hX : (0 : ℝ) < k := by linarith
  rw [Real.rpow_neg hX.le, Real.rpow_neg (by linarith)]
  have h1 : 0 < (k : ℝ) ^ s := Real.rpow_pos_of_pos hX s
  have h2 : ((k : ℝ) + 1) ^ s ≤ 2 * (k : ℝ) ^ s := by
    calc ((k : ℝ) + 1) ^ s ≤ (2 * (k : ℝ)) ^ s :=
          Real.rpow_le_rpow (by linarith) (by linarith) hs0
      _ = 2 ^ s * (k : ℝ) ^ s := Real.mul_rpow (by norm_num) hX.le
      _ ≤ 2 * (k : ℝ) ^ s := by
          gcongr
          calc (2:ℝ) ^ s ≤ 2 ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs1
            _ = 2 := Real.rpow_one 2
  have h3 : 0 < ((k : ℝ) + 1) ^ s := Real.rpow_pos_of_pos (by linarith) s
  rw [inv_le_iff_one_le_mul₀ h1]
  calc (1 : ℝ) = ((k : ℝ) + 1) ^ s * (((k : ℝ) + 1) ^ s)⁻¹ := by field_simp
    _ ≤ (2 * (k : ℝ) ^ s) * (((k : ℝ) + 1) ^ s)⁻¹ := by gcongr
    _ = _ := by ring

/-- Unroll a 3-term linear recursion starting at `N₀` when `s₃ ∈ (0, 1)` and `s₁, s₂ > 0`. -/
lemma det_rate_3 (Y : ℕ → ℝ) (hY0 : ∀ k, 0 ≤ Y k) (a p s1 s2 s3 : ℝ)
    (ha : 0 < a) (ha1 : a ≤ 1 / 2) (hp0 : 0 < p) (hp1 : p < 1)
    (hs1 : 0 < s1) (hs2 : 0 < s2) (hs30 : 0 < s3) (hs31 : s3 < 1)
    (K1 K2 K3 : ℝ) (hK1 : 0 < K1) (hK2 : 0 < K2) (hK3 : 0 < K3) (N₀ : ℕ)
    (hrec : ∀ k : ℕ, N₀ ≤ k →
      Y (k + 1) ≤ (1 - a * ((k : ℝ) + 1) ^ (-p)) * Y k
        + a * ((k : ℝ) + 1) ^ (-p) * (K1 * ((k : ℝ) + 1) ^ (-s1)
          + K2 * ((k : ℝ) + 1) ^ (-s2) + K3 * ((k : ℝ) + 1) ^ (-s3))) :
    ∃ A1 A2 A3 : ℝ, 0 ≤ A1 ∧ 0 ≤ A2 ∧ 0 ≤ A3 ∧ ∀ᶠ k : ℕ in atTop,
      Y k ≤ A1 * ((k : ℝ) + 1) ^ (-s1) + A2 * ((k : ℝ) + 1) ^ (-s2)
        + A3 * ((k : ℝ) + 1) ^ (-s3) := by
  have hX : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 1 := fun k => by positivity
  have hX1 : ∀ k : ℕ, (1 : ℝ) ≤ (k : ℝ) + 1 := fun k => by
    have := (k.cast_nonneg : (0 : ℝ) ≤ k); linarith
  set s1' := min s1 s3 with hs1'
  set s2' := min s2 s3 with hs2'
  have hs1'0 : 0 < s1' := lt_min hs1 hs30
  have hs1'1 : s1' < 1 := lt_of_le_of_lt (min_le_right _ _) hs31
  have hs2'0 : 0 < s2' := lt_min hs2 hs30
  have hs2'1 : s2' < 1 := lt_of_le_of_lt (min_le_right _ _) hs31
  set u : ℕ → ℝ := fun j => a / (j : ℝ) ^ p with hudef
  have hu_eq : ∀ k : ℕ, u (k + 1) = a * ((k : ℝ) + 1) ^ (-p) := by
    intro k; simp only [hudef]; push_cast
    rw [Real.rpow_neg (hX k).le, div_eq_mul_inv]
  have hupos : ∀ j, 1 ≤ j → 0 < u j := fun j hj => by
    have : (0 : ℝ) < j := by exact_mod_cast hj
    simp only [hudef]; exact div_pos ha (Real.rpow_pos_of_pos this _)
  have hu0 : ∀ j, 1 ≤ j → 0 ≤ u j := fun j hj => (hupos j hj).le
  have hu1 : ∀ j, 1 ≤ j → u j ≤ 1 := fun j hj => by
    have : (1 : ℝ) ≤ j := by exact_mod_cast hj
    simp only [hudef]
    calc a / (j : ℝ) ^ p ≤ a := div_le_self ha.le (Real.one_le_rpow this hp0.le)
      _ ≤ 1 := by linarith
  set bump : ℕ → ℝ := fun j => if j = N₀ + 1 then Y N₀ / u (N₀ + 1) else 0 with hbump
  have hbump0 : ∀ j, 0 ≤ bump j := by
    intro j; simp only [hbump]; split_ifs
    · exact div_nonneg (hY0 N₀) (hu0 _ (by omega))
    · exact le_rfl
  set w1 : ℕ → ℝ := fun j => K1 * (j : ℝ) ^ (-s1') with hw1
  set w2 : ℕ → ℝ := fun j => K2 * (j : ℝ) ^ (-s2') with hw2
  set w3 : ℕ → ℝ := fun j => K3 * (j : ℝ) ^ (-s3) + bump j with hw3
  set w : ℕ → ℝ := fun j => (w1 j + w2 j) + w3 j with hw
  have hW : ∀ k : ℕ, K1 * ((k : ℝ) + 1) ^ (-s1) + K2 * ((k : ℝ) + 1) ^ (-s2)
      + K3 * ((k : ℝ) + 1) ^ (-s3) + bump (k + 1) ≤ w (k + 1) := by
    intro k
    simp only [hw, hw1, hw2, hw3]; push_cast
    have h1 : ((k : ℝ) + 1) ^ (-s1) ≤ ((k : ℝ) + 1) ^ (-s1') :=
      Real.rpow_le_rpow_of_exponent_le (hX1 k) (by have := min_le_left s1 s3; linarith)
    have h2 : ((k : ℝ) + 1) ^ (-s2) ≤ ((k : ℝ) + 1) ^ (-s2') :=
      Real.rpow_le_rpow_of_exponent_le (hX1 k) (by have := min_le_left s2 s3; linarith)
    nlinarith
  have hw0 : ∀ j, 1 ≤ j → 0 ≤ w j := fun j hj => by
    have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
    simp only [hw, hw1, hw2, hw3]
    have := hbump0 j
    have := Real.rpow_pos_of_pos hj0 (-s1')
    have := Real.rpow_pos_of_pos hj0 (-s2')
    have := Real.rpow_pos_of_pos hj0 (-s3)
    positivity
  have hcmp := cmp u w Y N₀ hu0 hu1 hw0 (by
      have h1 := hrec N₀ le_rfl
      have h2 := hW N₀
      rw [← hu_eq N₀] at h1
      have hb : bump (N₀ + 1) = Y N₀ / u (N₀ + 1) := by simp [hbump]
      rw [hb] at h2
      have hup := hupos (N₀ + 1) (by omega)
      have e : u (N₀ + 1) * (Y N₀ / u (N₀ + 1)) = Y N₀ := mul_div_cancel₀ _ hup.ne'
      have h3 := mul_le_mul_of_nonneg_left h2 hup.le
      have h4 : 0 ≤ u (N₀ + 1) * Y N₀ := mul_nonneg hup.le (hY0 N₀)
      have h5 : u (N₀ + 1) * (K1 * ((N₀ : ℝ) + 1) ^ (-s1) + K2 * ((N₀ : ℝ) + 1) ^ (-s2)
            + K3 * ((N₀ : ℝ) + 1) ^ (-s3) + Y N₀ / u (N₀ + 1))
          = u (N₀ + 1) * (K1 * ((N₀ : ℝ) + 1) ^ (-s1) + K2 * ((N₀ : ℝ) + 1) ^ (-s2)
            + K3 * ((N₀ : ℝ) + 1) ^ (-s3)) + Y N₀ := by
        rw [mul_add, e]
      nlinarith)
    (by
      intro k hk
      have h1 := hrec k (by omega)
      rw [← hu_eq k] at h1
      have h2 := hW k
      have h3 := mul_le_mul_of_nonneg_left
        (show K1 * ((k : ℝ) + 1) ^ (-s1) + K2 * ((k : ℝ) + 1) ^ (-s2)
            + K3 * ((k : ℝ) + 1) ^ (-s3) ≤ w (k + 1) by linarith [hbump0 (k + 1)])
        (hu0 (k + 1) (by omega))
      linarith)
  have hpow_eq : ∀ (K s : ℝ) (i : ℕ), 1 ≤ i → K * (i : ℝ) ^ (-s) = K / (i : ℝ) ^ s := by
    intro K s i hi
    have : (0 : ℝ) < i := by exact_mod_cast hi
    rw [Real.rpow_neg this.le, div_eq_mul_inv]
  obtain ⟨C1, hC1⟩ := lemma_3 a p s1' ha ⟨hp0, hp1⟩ ⟨hs1'0, hs1'1⟩ w1
    (fun i hi => by
      have hi0 : (0 : ℝ) < i := by exact_mod_cast hi
      have := Real.rpow_pos_of_pos hi0 (-s1'); simp only [hw1]; positivity)
    ⟨K1, by filter_upwards [eventually_ge_atTop 1] with i hi; simp only [hw1]; rw [hpow_eq _ _ _ hi]⟩
  obtain ⟨C2, hC2⟩ := lemma_3 a p s2' ha ⟨hp0, hp1⟩ ⟨hs2'0, hs2'1⟩ w2
    (fun i hi => by
      have hi0 : (0 : ℝ) < i := by exact_mod_cast hi
      have := Real.rpow_pos_of_pos hi0 (-s2'); simp only [hw2]; positivity)
    ⟨K2, by filter_upwards [eventually_ge_atTop 1] with i hi; simp only [hw2]; rw [hpow_eq _ _ _ hi]⟩
  obtain ⟨C3, hC3⟩ := lemma_3 a p s3 ha ⟨hp0, hp1⟩ ⟨hs30, hs31⟩ w3
    (fun i hi => by
      have hi0 : (0 : ℝ) < i := by exact_mod_cast hi
      have := hbump0 i; have := Real.rpow_pos_of_pos hi0 (-s3); simp only [hw3]; positivity)
    ⟨K3, by
      filter_upwards [eventually_ge_atTop (N₀ + 2)] with i hi
      have hb : bump i = 0 := by simp only [hbump]; rw [if_neg (by omega)]
      simp only [hw3, hb, add_zero]; rw [hpow_eq _ _ _ (by omega)]⟩
  refine ⟨2 * max C1 0, 2 * max C2 0, 2 * (max C1 0 + max C2 0 + max C3 0),
    by positivity, by positivity, by positivity, ?_⟩
  filter_upwards [hC1, hC2, hC3, eventually_ge_atTop (N₀ + 1)] with k h1 h2 h3 hk
  have hxk := hcmp k hk
  have hsplit : Ssum u w k = Ssum u w1 k + Ssum u w2 k + Ssum u w3 k := by
    simp only [hw]; rw [Ssum_add u (fun i => w1 i + w2 i) w3, Ssum_add u w1 w2]
  have hkp : ∀ s : ℝ, 0 ≤ (k : ℝ) ^ s := fun s => Real.rpow_nonneg (Nat.cast_nonneg k) s
  have m : ∀ (C s : ℝ), 0 ≤ s → s ≤ 1 →
      C * (k : ℝ) ^ (-s) ≤ max C 0 * (2 * ((k : ℝ) + 1) ^ (-s)) :=
    fun C s hs0 hs1 => (mul_le_mul_of_nonneg_right (le_max_left _ _) (hkp _)).trans
      (mul_le_mul_of_nonneg_left (kpow_le k (by omega) s hs0 hs1) (le_max_right _ _))
  have m1 := m C1 s1' hs1'0.le hs1'1.le
  have m2 := m C2 s2' hs2'0.le hs2'1.le
  have m3 := m C3 s3 hs30.le hs31.le
  have hXs1' : ((k : ℝ) + 1) ^ (-s1') ≤ ((k : ℝ) + 1) ^ (-s1) + ((k : ℝ) + 1) ^ (-s3) := by
    have := Real.rpow_nonneg (hX k).le (-s1)
    have := Real.rpow_nonneg (hX k).le (-s3)
    rcases min_choice s1 s3 with h | h <;> (rw [hs1', h]; linarith)
  have hXs2' : ((k : ℝ) + 1) ^ (-s2') ≤ ((k : ℝ) + 1) ^ (-s2) + ((k : ℝ) + 1) ^ (-s3) := by
    have := Real.rpow_nonneg (hX k).le (-s2)
    have := Real.rpow_nonneg (hX k).le (-s3)
    rcases min_choice s2 s3 with h | h <;> (rw [hs2', h]; linarith)
  have p1 := le_max_right C1 0
  have p2 := le_max_right C2 0
  have p3 := le_max_right C3 0
  have n1 := mul_le_mul_of_nonneg_left hXs1' p1
  have n2 := mul_le_mul_of_nonneg_left hXs2' p2
  have h1' : Ssum u w1 k ≤ C1 * (k : ℝ) ^ (-s1') := h1
  have h2' : Ssum u w2 k ≤ C2 * (k : ℝ) ^ (-s2') := h2
  have h3' : Ssum u w3 k ≤ C3 * (k : ℝ) ^ (-s3) := h3
  nlinarith

end SPQOSeq

/-! ### Part 4: Uniform second-moment bound `sup_k E‖D_k‖² < ∞` (Lemma 1(i) under PolySteps) -/

namespace SPQODBound
open QuantileSPQO.Rate SPQOCommon SPQOCond SPQOSeq

lemma D_drift_pt {d : ℕ} (v g b : E d) (f ε K' Kp ck sd : ℝ)
    (hε : 0 < ε) (hf : ε ≤ f) (_hK' : 0 ≤ K') (hKp : 0 ≤ Kp) (hck : 0 < ck) (hck1 : ck ≤ 1)
    (_hsd : 0 < sd) (hKpε : Kp * ck ^ 2 / sd ≤ ε / 4)
    (hg : ‖g‖ ≤ K') (hb : ‖b‖ ≤ (1 + ‖v‖ / sd) * Kp * ck ^ 2) :
    ⟪v, -f • v - g + b⟫ ≤ -(ε / 2) * ‖v‖ ^ 2 + (K' + Kp) ^ 2 / ε := by
  rw [inner_add_right, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  have h2 : -⟪v, g⟫ ≤ K' * ‖v‖ := by
    have h2a := neg_le_abs (⟪v, g⟫)
    have h2b := abs_real_inner_le_norm v g
    have h2c := mul_le_mul_of_nonneg_left hg (norm_nonneg v)
    linarith
  have h3 : ⟪v, b⟫ ≤ (Kp * ck ^ 2) * ‖v‖ + (Kp * ck ^ 2 / sd) * ‖v‖ ^ 2 := by
    have h3a := real_inner_le_norm v b
    have h3b := mul_le_mul_of_nonneg_left hb (norm_nonneg v)
    linarith [show ‖v‖ * ((1 + ‖v‖ / sd) * Kp * ck ^ 2)
        = (Kp * ck ^ 2) * ‖v‖ + (Kp * ck ^ 2 / sd) * ‖v‖ ^ 2 by ring]
  have hck2 : ck ^ 2 ≤ 1 := by nlinarith
  have hKp_ck : Kp * ck ^ 2 * ‖v‖ ≤ Kp * ‖v‖ := by
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hck2 hKp) (norm_nonneg v)
    simpa using this
  have hKp_v2 : (Kp * ck ^ 2 / sd) * ‖v‖ ^ 2 ≤ (ε / 4) * ‖v‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hKpε (sq_nonneg _)
  have hfv2 : -f * ‖v‖ ^ 2 ≤ -ε * ‖v‖ ^ 2 := by nlinarith [sq_nonneg ‖v‖]
  have h4 : (K' + Kp) * ‖v‖ ≤ (ε / 4) * ‖v‖ ^ 2 + (K' + Kp) ^ 2 / ε := by
    have hsq : 0 ≤ (ε / 2 * ‖v‖ - (K' + Kp)) ^ 2 / ε := by positivity
    have : (ε / 2 * ‖v‖ - (K' + Kp)) ^ 2 / ε
        = (ε / 4) * ‖v‖ ^ 2 - (K' + Kp) * ‖v‖ + (K' + Kp) ^ 2 / ε := by field_simp; ring
    linarith
  linarith

lemma D_sq_bdd {Ω : Type*} [m0 : MeasurableSpace Ω] {d : ℕ} (hd : 0 < d)
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (M : Model d) (Θ : Set (E d)) (Proj : E d → E d) (I : Set ℝ) (Pq : ℝ → ℝ)
    (α β γ c : ℕ → ℝ) (R : Run Ω d)
    (hM : IsQuantileModel M Θ)
    (hrun : IsSPQORun P ℱ M Θ Proj I Pq α β γ c R)
    (hA1 : A1 P M R) (hA2 : A2 P ℱ R) (hA3a : A3a β c) (hA3b : A3b γ)
    (hpoly : PolySteps α β γ c) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ k,
      Integrable (fun ω => ‖R.D k ω‖ ^ 2) P ∧
      ∫ ω, ‖R.D k ω‖ ^ 2 ∂P ≤ S ∧
      ∫⁻ ω, ‖R.D k ω‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal S := by
  obtain ⟨δ, hδ, K, ε, hε, hA1ae⟩ := hA1
  obtain ⟨a, b, r, c₀, eα, eβ, eγ, τ, ha, hb, hr, hc0, ⟨heα0, heα1⟩, ⟨heβ0, heβ1⟩,
    ⟨heγ0, heγ1⟩, ⟨hτ0, hτ1⟩, hsteps⟩ := hpoly
  obtain ⟨θ₀, _, q₀, hq₀, D₀, hinit⟩ := hrun.init
  have hβpos : ∀ k, 0 < β k := fun k => (hA3a.1 k).1
  have hcpos : ∀ k, 0 < c k := fun k => (hA3a.1 k).2
  have hγpos : ∀ k, 0 < γ k := hA3b.1
  have hX : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 1 := fun k => by positivity
  -- Show eβ - 2*τ > 0 from summability of β²/c²
  have hβc2_eq : ∀ k : ℕ, β k ^ 2 / c k ^ 2 = (b / c₀) ^ 2 * ((k : ℝ) + 1) ^ (-(2 * (eβ - τ))) := by
    intro k
    have h1 := (hsteps k).2.1
    have h2 := (hsteps k).2.2.2
    rw [h1, h2, ← div_pow, rp_div b c₀ eβ τ _ (hX k) hc0.ne', mul_pow, rp_pow_sq _ _ (hX k)]
    congr 1; ring_nf
  have heβτ : 1 / 2 < eβ - τ := by
    have hs : Summable (fun k : ℕ => (b / c₀) ^ 2 * ((k : ℝ) + 1) ^ (-(2 * (eβ - τ)))) :=
      hA3a.2.2.2.congr hβc2_eq
    have := exp_lt_of_summable ((b / c₀) ^ 2) (-(2 * (eβ - τ))) (by positivity) hs
    linarith
  have heβ2τ : 0 < eβ - 2 * τ := by linarith
  -- Hence β_k / c_k² → 0 and β_k → 0
  have hβc_tend : Tendsto (fun k => β k / c k ^ 2) atTop (𝓝 0) := by
    have heq : (fun k : ℕ => β k / c k ^ 2) =
        fun k : ℕ => (b / c₀ ^ 2) * ((k : ℝ) + 1) ^ (-(eβ - 2 * τ)) := by
      funext k
      have h1 := (hsteps k).2.1
      have h2 := (hsteps k).2.2.2
      rw [h1, h2, div_pow, rp_pow_sq _ _ (hX k), rp_div b (c₀ ^ 2) eβ (2 * τ) _ (hX k) (by positivity)]
    rw [heq]
    have h1 : Tendsto (fun k : ℕ => ((k : ℝ) + 1) ^ (-(eβ - 2 * τ))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop heβ2τ).comp
        (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    simpa using h1.const_mul (b / c₀ ^ 2)
  have hβ_tend : Tendsto β atTop (𝓝 0) := by
    have heq : β = fun k : ℕ => b * ((k : ℝ) + 1) ^ (-eβ) := by
      funext k; rw [(hsteps k).2.1, Real.rpow_neg (hX k).le, div_eq_mul_inv]
    rw [heq]
    have h1 : Tendsto (fun k : ℕ => ((k : ℝ) + 1) ^ (-eβ)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop heβ0).comp
        (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    simpa using h1.const_mul b
  -- Deterministic bounds on q_k and D_k (on goodEvent R k)
  have hqI : ∀ k ω, R.q k ω ∈ I := by
    intro k ω; induction k with
    | zero => rw [(hinit ω).2.1]; exact hq₀
    | succ k _ => rw [hrun.eq20]; exact (hrun.pqProj.proj _).1
  have hind01 : ∀ (P' : Prop) [Decidable P'], |M.φ - (if P' then (1 : ℝ) else 0)| ≤ 1 := by
    intro P' _; have := hM.φ_pos; have := hM.φ_lt_one
    split_ifs
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [sub_zero, abs_of_pos hM.φ_pos]; linarith
  set Qk : ℕ → ℝ := fun k => |q₀| + ∑ i ∈ Finset.range k, γ i with hQk
  have hQk0 : ∀ k, 0 ≤ Qk k := fun k => by
    simp only [hQk]; exact add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun i _ => (hγpos i).le)
  have hqb : ∀ k ω, |R.q k ω| ≤ Qk k := by
    intro k ω; induction k with
    | zero => rw [(hinit ω).2.1]; simp [hQk]
    | succ k ih =>
      have h1 : |R.q (k + 1) ω - R.q k ω| ≤ γ k := by
        rw [hrun.eq20]
        refine (proj1d hrun.pqProj (hqI k ω) _).trans ?_
        rw [add_sub_cancel_left, abs_mul, abs_of_pos (hγpos k)]
        have := hind01 (R.Y0 k ω ≤ R.q k ω); nlinarith [hγpos k]
      simp only [hQk, Finset.sum_range_succ] at ih ⊢
      linarith [abs_sub_abs_le_abs_sub (R.q (k + 1) ω) (R.q k ω)]
  set Bk : ℕ → ℝ := Dbound β c D₀ with hBk
  have hBk0 : ∀ k, 0 ≤ Bk k := Dbound_nonneg β c D₀ hβpos hcpos
  have hDb : ∀ k ω, ω ∈ goodEvent R k → ‖R.D k ω‖ ≤ Bk k :=
    norm_D_le_Dbound hd hrun hβpos hcpos (fun ω => (hinit ω).2.2)
  have hDint : ∀ k, Integrable (fun ω => ‖R.D k ω‖ ^ 2) P := by
    intro k
    refine Integrable.of_bound (((hrun.adapted_D k).mono (ℱ.le k)).norm.pow 2).aestronglyMeasurable
      (Bk k ^ 2) ?_
    filter_upwards [goodEvent_ae P ℱ M Θ Proj I Pq α β γ c R hrun hA2 k] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hDb k ω hω) 2
  have hgint : ∀ k, Integrable (fun ω => ‖spGrad c R k ω‖ ^ 2) P := by
    intro k
    refine Integrable.of_bound ((spGrad_meas hrun hβpos k).norm.pow 2).aestronglyMeasurable
      ((d + Bk k ^ 2) / (4 * c k ^ 2)) ?_
    filter_upwards [goodEvent_ae P ℱ M Θ Proj I Pq α β γ c R hrun hA2 (k + 1)] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    obtain ⟨b, hb⟩ := goodEvent_succ_mem_Delta R k hω
    have h1 := norm_spGrad_sq_le hd c R k ω (hcpos k) b hb
    have h2 := hDb k ω (goodEvent_succ_subset R k hω)
    calc ‖spGrad c R k ω‖ ^ 2 ≤ (d + ‖R.D k ω‖ ^ 2) / (4 * c k ^ 2) := h1
      _ ≤ (d + Bk k ^ 2) / (4 * c k ^ 2) := by
          gcongr
  -- Choose N₁ large enough for all asymptotic inequalities
  set K' := max K 0 with hK'
  have hK'0 : 0 ≤ K' := le_max_right _ _
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hsd0 : 0 < Real.sqrt d := Real.sqrt_pos.2 hd0
  set Kp := K' * (d : ℝ) ^ 3 * Real.sqrt d with hKp
  have hKp0 : 0 ≤ Kp := by positivity
  have hev_all : ∀ᶠ k in atTop,
      c k * d < δ ∧ c k ≤ 1 ∧ Kp * c k ^ 2 / Real.sqrt d ≤ ε / 4 ∧
      β k / c k ^ 2 ≤ ε ∧ β k * ε ≤ 1 := by
    have h1 : ∀ᶠ k in atTop, c k * d < δ := by
      have := hA3a.2.1.mul_const (d : ℝ); rw [zero_mul] at this
      exact this.eventually (gt_mem_nhds hδ)
    have h2 : ∀ᶠ k in atTop, c k ≤ 1 :=
      (hA3a.2.1.eventually (gt_mem_nhds one_pos)).mono fun _ h => h.le
    have h3 : ∀ᶠ k in atTop, Kp * c k ^ 2 / Real.sqrt d ≤ ε / 4 := by
      have ht : Tendsto (fun k => Kp * c k ^ 2 / Real.sqrt d) atTop (𝓝 0) := by
        have := ((hA3a.2.1.pow 2).const_mul Kp).div_const (Real.sqrt d)
        simpa using this
      exact (ht.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 4))).mono fun _ h => h.le
    have h4 : ∀ᶠ k in atTop, β k / c k ^ 2 ≤ ε :=
      (hβc_tend.eventually (gt_mem_nhds hε)).mono fun _ h => h.le
    have h5 : ∀ᶠ k in atTop, β k * ε ≤ 1 := by
      have := hβ_tend.mul_const ε; rw [zero_mul] at this
      exact (this.eventually (gt_mem_nhds one_pos)).mono fun _ h => h.le
    filter_upwards [h1, h2, h3, h4, h5] with k h1 h2 h3 h4 h5 using ⟨h1, h2, h3, h4, h5⟩
  rw [Filter.eventually_atTop] at hev_all
  obtain ⟨N₁, hN₁⟩ := hev_all
  set X : ℕ → ℝ := fun k => ∫ ω, ‖R.D k ω‖ ^ 2 ∂P with hXdef
  set Mstar : ℝ := 4 * (K' + Kp) ^ 2 / ε ^ 2 + d / 2 with hMstar
  have hMstar0 : 0 ≤ Mstar := by positivity
  -- One-step contraction of X_k for k ≥ N₁
  have hrecX : ∀ k, N₁ ≤ k →
      X (k + 1) ≤ (1 - β k * ε / 2) * X k + (β k * ε / 2) * Mstar := by
    intro k hk
    obtain ⟨hsmall, hc1, hKpε, hβcε, hβε1⟩ := hN₁ k hk
    set H : Ω → E d := (goodEvent R k).indicator (R.D k) with hHdef
    have hHm : StronglyMeasurable[ℱ k] H := (hrun.adapted_D k).indicator (goodEvent_meas hrun k)
    have hHnorm : ∀ ω, ‖H ω‖ ≤ Bk k := by
      intro ω; rw [hHdef]
      by_cases hω : ω ∈ goodEvent R k
      · rw [Set.indicator_of_mem hω]; exact hDb k ω hω
      · rw [Set.indicator_of_notMem hω, norm_zero]; exact hBk0 k
    have hHsupp : ∀ ω, ω ∉ goodEvent R k → H ω = 0 := fun ω hω =>
      Set.indicator_of_notMem hω _
    have hHae : ∀ᵐ ω ∂P, H ω = R.D k ω :=
      (goodEvent_ae P ℱ M Θ Proj I Pq α β γ c R hrun hA2 k).mono fun ω hω =>
        Set.indicator_of_mem hω _
    obtain ⟨hIntL, hIntR, hcond⟩ := cond_sp hd P ℱ M Θ Proj I Pq α β γ c R hM hrun hA2
      hβpos hcpos k δ (Qk k) (Bk k) (Bk k) (hQk0 k) (hBk0 k) (hBk0 k) hsmall (hqb k) (hDb k)
      (hA1ae.mono fun ω hω => (hω k).1) H hHm hHnorm hHsupp
    -- Expand X (k + 1)
    have hexp_ae : (fun ω => ‖R.D (k + 1) ω‖ ^ 2) =ᵐ[P]
        fun ω => ‖R.D k ω‖ ^ 2 + 2 * β k * ⟪H ω, spGrad c R k ω⟫ +
          β k ^ 2 * ‖spGrad c R k ω‖ ^ 2 := by
      filter_upwards [hHae] with ω hω
      rw [D_succ_eq hrun k ω, norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow,
        Real.norm_of_nonneg (hβpos k).le, hω]
      ring
    have hXeq : X (k + 1) = X k + 2 * β k * ∫ ω, ⟪H ω, spAvg M c k (R.q k ω) (R.D k ω) (R.θ k ω)⟫ ∂P
        + β k ^ 2 * ∫ ω, ‖spGrad c R k ω‖ ^ 2 ∂P := by
      simp only [hXdef]
      have hi12 : Integrable (fun ω => ‖R.D k ω‖ ^ 2 + 2 * β k * ⟪H ω, spGrad c R k ω⟫) P :=
        (hDint k).add (hIntL.const_mul (2 * β k))
      rw [integral_congr_ae hexp_ae,
        integral_add hi12 ((hgint k).const_mul _),
        integral_add (hDint k) (hIntL.const_mul _),
        integral_const_mul, integral_const_mul, hcond]
    -- Bound the drift integral
    have hdrift_pt : ∀ᵐ ω ∂P, ⟪H ω, spAvg M c k (R.q k ω) (R.D k ω) (R.θ k ω)⟫ ≤
        -(ε / 2) * ‖R.D k ω‖ ^ 2 + (K' + Kp) ^ 2 / ε := by
      filter_upwards [hHae, hA1ae] with ω hHω hA1ω
      rw [hHω, spAvg_eq]
      obtain ⟨hC3, hball⟩ := hA1ω k
      have hpball : (R.q k ω, R.θ k ω) ∈ Metric.ball (R.q k ω, R.θ k ω) δ :=
        Metric.mem_ball_self hδ
      have hdiff : DifferentiableAt ℝ (cdfU M) (R.q k ω, R.θ k ω) :=
        (hC3.differentiableOn (by norm_num)).differentiableAt (Metric.isOpen_ball.mem_nhds hpball)
      have hfε : ε ≤ M.dens (R.q k ω) (R.θ k ω) := (hball _ hpball).2.2
      have hgK : ‖gradθ M (R.q k ω) (R.θ k ω)‖ ≤ K' :=
        (norm_gradθ_le_fderiv M hM.hasDens _ _ hdiff).trans
          ((hball _ hpball).1.trans (le_max_left _ _))
      have hbias : ‖bias M c k (R.q k ω) (R.D k ω) (R.θ k ω)‖ ≤
          mfac (R.D k ω) * Kp * c k ^ 2 :=
        bias_bound hd M hM.hasDens c k _ _ _ δ K' (hcpos k) hsmall hC3
          (fun x hx => (hball x hx).2.1.trans (le_max_left _ _))
      have hmle : mfac (R.D k ω) ≤ 1 + ‖R.D k ω‖ / Real.sqrt d := by
        unfold mfac; apply max_le <;> linarith [div_nonneg (norm_nonneg (R.D k ω)) hsd0.le]
      have hbias' : ‖bias M c k (R.q k ω) (R.D k ω) (R.θ k ω)‖ ≤
          (1 + ‖R.D k ω‖ / Real.sqrt d) * Kp * c k ^ 2 := by
        refine hbias.trans ?_
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmle hKp0) (sq_nonneg _)
      exact D_drift_pt (R.D k ω) (gradθ M (R.q k ω) (R.θ k ω))
        (bias M c k (R.q k ω) (R.D k ω) (R.θ k ω)) (M.dens (R.q k ω) (R.θ k ω))
        ε K' Kp (c k) (Real.sqrt d) hε hfε hK'0 hKp0 (hcpos k) hc1 hsd0 hKpε hgK hbias'
    have hdrift : ∫ ω, ⟪H ω, spAvg M c k (R.q k ω) (R.D k ω) (R.θ k ω)⟫ ∂P
        ≤ -(ε / 2) * X k + (K' + Kp) ^ 2 / ε := by
      have hi := ((hDint k).const_mul (-(ε / 2))).add (integrable_const ((K' + Kp) ^ 2 / ε))
      have hm := integral_mono_ae hIntR hi hdrift_pt
      rw [integral_add' ((hDint k).const_mul _) (integrable_const _)] at hm
      rw [integral_const_mul, integral_const, probReal_univ, smul_eq_mul, one_mul] at hm
      exact hm
    -- Bound the noise integral
    have hnoise_pt : ∀ᵐ ω ∂P, ‖spGrad c R k ω‖ ^ 2 ≤ (d + ‖R.D k ω‖ ^ 2) / (4 * c k ^ 2) := by
      filter_upwards [goodEvent_ae P ℱ M Θ Proj I Pq α β γ c R hrun hA2 (k + 1)] with ω hω
      obtain ⟨b, hb⟩ := goodEvent_succ_mem_Delta R k hω
      exact norm_spGrad_sq_le hd c R k ω (hcpos k) b hb
    have hnoise : ∫ ω, ‖spGrad c R k ω‖ ^ 2 ∂P ≤ ((d : ℝ) + X k) / (4 * c k ^ 2) := by
      have hi : Integrable (fun ω => (d + ‖R.D k ω‖ ^ 2) / (4 * c k ^ 2)) P :=
        ((integrable_const (d : ℝ)).add (hDint k)).div_const _
      have hm := integral_mono_ae (hgint k) hi hnoise_pt
      rw [integral_div, integral_add (integrable_const _) (hDint k), integral_const,
        probReal_univ, smul_eq_mul, one_mul] at hm
      exact hm
    -- Combine drift and noise
    have hX0 : 0 ≤ X k := integral_nonneg fun ω => sq_nonneg _
    have hβ0 := hβpos k
    have hnt : β k ^ 2 * (((d : ℝ) + X k) / (4 * c k ^ 2))
        ≤ (β k * ε / 4) * ((d : ℝ) + X k) := by
      have e : β k ^ 2 * (((d : ℝ) + X k) / (4 * c k ^ 2))
          = (β k * (β k / c k ^ 2) / 4) * ((d : ℝ) + X k) := by ring
      rw [e]
      have h1 : β k * (β k / c k ^ 2) / 4 ≤ β k * ε / 4 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hβcε hβ0.le) (by norm_num)
      exact mul_le_mul_of_nonneg_right h1 (by positivity)
    have h1 := mul_le_mul_of_nonneg_left hdrift (by positivity : (0 : ℝ) ≤ 2 * β k)
    have h2 := mul_le_mul_of_nonneg_left hnoise (sq_nonneg (β k))
    have eM : (β k * ε / 2) * Mstar = 2 * β k * ((K' + Kp) ^ 2 / ε) + (β k * ε / 4) * d := by
      simp only [hMstar]; field_simp; ring
    have hX4 : 0 ≤ (β k * ε / 4) * X k := by positivity
    linarith only [hXeq, h1, h2, hnt, eM, hX4]
  -- Uniform bound S from N₁ and finite prefix
  set S_pre : ℝ := ∑ j ∈ Finset.range (N₁ + 1), X j with hSpre
  have hXnn : ∀ j, 0 ≤ X j := fun j => integral_nonneg fun ω => sq_nonneg _
  have hXle_pre : ∀ j, j ≤ N₁ → X j ≤ S_pre := fun j hj =>
    Finset.single_le_sum (fun i _ => hXnn i) (Finset.mem_range.2 (by omega))
  set S : ℝ := max S_pre Mstar with hSdef
  have hS0 : 0 ≤ S := le_trans hMstar0 (le_max_right _ _)
  have hXS : ∀ k, X k ≤ S := by
    intro k
    by_cases hk : k ≤ N₁
    · exact (hXle_pre k hk).trans (le_max_left _ _)
    · push Not at hk
      have hle : N₁ ≤ k := Nat.le_of_lt hk
      clear hk
      induction k, hle using Nat.le_induction with
      | base => exact (hXle_pre N₁ le_rfl).trans (le_max_left _ _)
      | succ k hge ih =>
        have hstep := hrecX k hge
        have hβε1 := (hN₁ k hge).2.2.2.2
        have hu0 : 0 ≤ β k * ε / 2 := by have := hβpos k; positivity
        have hu1 : 0 ≤ 1 - β k * ε / 2 := by linarith
        have hMleS : Mstar ≤ S := le_max_right _ _
        have m1 := mul_le_mul_of_nonneg_left ih hu1
        have m2 := mul_le_mul_of_nonneg_left hMleS hu0
        linarith only [hstep, m1, m2]
  refine ⟨S, hS0, fun k => ⟨hDint k, hXS k, ?_⟩⟩
  have heq : ∫⁻ ω, ‖R.D k ω‖ₑ ^ 2 ∂P = ∫⁻ ω, ENNReal.ofReal (‖R.D k ω‖ ^ 2) ∂P := by
    congr 1; funext ω; rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  rw [heq, ← ofReal_integral_eq_lintegral_ofReal (hDint k)
    (Eventually.of_forall fun ω => by simp only [Pi.zero_apply]; positivity)]
  exact ENNReal.ofReal_le_ofReal (hXS k)

end SPQODBound

/-! ### Part 5: Quantile tracker rate `E[(q_k − q(θ_k))²] = O(α_k²/γ_k²) + O(γ_k)` (Lemma 4) -/

namespace SPQOL4
open QuantileSPQO.Rate SPQOCommon SPQOCond SPQOSeq

lemma pathwise (z z' δq e Δ γ ε : ℝ) (hγ : 0 < γ) (hε : 0 < ε)
    (hz : |z'| ≤ |z + δq + γ * e|) (hδ : |δq| ≤ Δ) (he : |e| ≤ 1) :
    z' ^ 2 ≤ (1 + γ * ε) * z ^ 2 + (1 + 1 / (γ * ε)) * Δ ^ 2 + γ ^ 2 + 2 * γ * (z * e)
      + 2 * γ * Δ := by
  have hΔ0 : 0 ≤ Δ := le_trans (abs_nonneg _) hδ
  have hge : 0 < γ * ε := by positivity
  have hsq : z' ^ 2 ≤ (z + δq + γ * e) ^ 2 := by
    rw [← sq_abs z', ← sq_abs (z + δq + γ * e)]
    exact pow_le_pow_left₀ (abs_nonneg _) hz 2
  have amgm : 2 * |z| * Δ ≤ γ * ε * z ^ 2 + Δ ^ 2 / (γ * ε) := by
    have h0 : 0 ≤ (γ * ε * |z| - Δ) ^ 2 / (γ * ε) := by positivity
    have e2 : (γ * ε * |z| - Δ) ^ 2 / (γ * ε)
        = γ * ε * |z| ^ 2 - 2 * |z| * Δ + Δ ^ 2 / (γ * ε) := by field_simp; ring
    rw [e2, sq_abs] at h0; linarith
  have t1 : 2 * z * δq ≤ 2 * |z| * Δ := by
    have h2 : z * δq ≤ |z| * |δq| := by rw [← abs_mul]; exact le_abs_self _
    have h3 : |z| * |δq| ≤ |z| * Δ := mul_le_mul_of_nonneg_left hδ (abs_nonneg _)
    linarith
  have t2 : δq ^ 2 ≤ Δ ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hδ 2
  have t3 : δq * e ≤ Δ := by
    calc δq * e ≤ |δq * e| := le_abs_self _
      _ = |δq| * |e| := abs_mul _ _
      _ ≤ Δ * 1 := mul_le_mul hδ he (abs_nonneg _) hΔ0
      _ = Δ := mul_one _
  have t4 : e ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg e]
  have hexp : (z + δq + γ * e) ^ 2 = z ^ 2 + δq ^ 2 + γ ^ 2 * e ^ 2 + 2 * z * δq
      + 2 * γ * (z * e) + 2 * γ * (δq * e) := by ring
  have hfin : Δ ^ 2 / (γ * ε) + Δ ^ 2 = (1 + 1 / (γ * ε)) * Δ ^ 2 := by field_simp; ring
  have t5 : γ ^ 2 * e ^ 2 ≤ γ ^ 2 := by nlinarith [sq_nonneg γ]
  have t6 : 2 * γ * (δq * e) ≤ 2 * γ * Δ := by nlinarith
  nlinarith

lemma onestep {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (z z' ind F Dn : Ω → ℝ) (γ ε α L φ : ℝ) (hγ : 0 < γ) (_hε : 0 < ε)
    (iz : Integrable (fun ω => z ω ^ 2) P) (iz1 : Integrable z P)
    (iz' : Integrable (fun ω => z' ω ^ 2) P)
    (izI : Integrable (fun ω => z ω * ind ω) P) (izF : Integrable (fun ω => z ω * F ω) P)
    (iD2 : Integrable (fun ω => Dn ω ^ 2) P) (iD : Integrable Dn P)
    (hcond : ∫ ω, z ω * ind ω ∂P = ∫ ω, z ω * F ω ∂P)
    (P1 : ∀ ω, z' ω ^ 2 ≤ (1 + γ * ε) * z ω ^ 2 + (1 + 1 / (γ * ε)) * (L * α) ^ 2 * Dn ω ^ 2
      + γ ^ 2 + 2 * γ * (φ * z ω - z ω * ind ω) + 2 * γ * (L * α) * Dn ω)
    (P2 : ∀ᵐ ω ∂P, φ * z ω - z ω * F ω ≤ -ε * z ω ^ 2) :
    ∫ ω, z' ω ^ 2 ∂P ≤ (1 - γ * ε) * ∫ ω, z ω ^ 2 ∂P
      + (1 + 1 / (γ * ε)) * (L * α) ^ 2 * ∫ ω, Dn ω ^ 2 ∂P + γ ^ 2
      + 2 * γ * (L * α) * ∫ ω, Dn ω ∂P := by
  set c1 := 1 + γ * ε
  set c2 := (1 + 1 / (γ * ε)) * (L * α) ^ 2
  set c3 := 2 * γ * (L * α)
  have i1 : Integrable (fun ω => c1 * z ω ^ 2) P := iz.const_mul c1
  have i2 : Integrable (fun ω => c2 * Dn ω ^ 2) P := iD2.const_mul c2
  have i3 : Integrable (fun _ : Ω => γ ^ 2) P := integrable_const _
  have i4 : Integrable (fun ω => 2 * γ * (φ * z ω - z ω * ind ω)) P :=
    ((iz1.const_mul φ).sub izI).const_mul (2 * γ)
  have i5 : Integrable (fun ω => c3 * Dn ω) P := iD.const_mul c3
  have hmono := integral_mono iz' ((((i1.add i2).add i3).add i4).add i5) P1
  rw [integral_add' (((i1.add i2).add i3).add i4) i5, integral_add' ((i1.add i2).add i3) i4,
    integral_add' (i1.add i2) i3, integral_add' i1 i2] at hmono
  rw [integral_const_mul, integral_const_mul,
    integral_const, integral_const_mul, integral_sub (iz1.const_mul φ) izI, integral_const_mul,
    integral_const_mul, hcond] at hmono
  simp only [probReal_univ, smul_eq_mul, one_mul] at hmono
  have hP2 : φ * ∫ ω, z ω ∂P - ∫ ω, z ω * F ω ∂P ≤ -ε * ∫ ω, z ω ^ 2 ∂P := by
    rw [← integral_const_mul, ← integral_sub (iz1.const_mul φ) izF, ← integral_const_mul]
    exact integral_mono_ae ((iz1.const_mul φ).sub izF) (iz.const_mul _) P2
  have : 2 * γ * (φ * ∫ ω, z ω ∂P - ∫ ω, z ω * F ω ∂P) ≤ 2 * γ * (-ε * ∫ ω, z ω ^ 2 ∂P) :=
    mul_le_mul_of_nonneg_left hP2 (by positivity)
  nlinarith

lemma coef_ineq (α γ a r ε Lq Sr t : ℝ) (hα : 0 < α) (hγ : 0 < γ) (hγr : γ ≤ r) (ha : 0 < a)
    (hr : 0 < r) (hε : 0 < ε) (hLq : 0 < Lq) (hSr : 0 ≤ Sr) (ht : 0 < t) :
    (1 + 1 / (γ * ε)) * (Lq * α) ^ 2 * Sr + γ ^ 2 + 2 * γ * (Lq * α) * t ≤
      γ * ε * ((Lq ^ 2 * Sr * (r / ε + 1 / ε ^ 2) * (a / r) ^ 2 + 1) * ((r / a) ^ 2 * (α / γ) ^ 2)
        + r / ε * (γ / r) + (2 * Lq * t * a / ε + 1) * (α / a)) := by
  have e1 : γ * ε * ((Lq ^ 2 * Sr * (r / ε + 1 / ε ^ 2) * (a / r) ^ 2 + 1) * ((r / a) ^ 2 * (α / γ) ^ 2))
      = Lq ^ 2 * Sr * (r * α ^ 2 / γ) + Lq ^ 2 * Sr * (α ^ 2 / (γ * ε))
        + γ * ε * ((r / a) ^ 2 * (α / γ) ^ 2) := by field_simp
  have e2 : γ * ε * (r / ε * (γ / r)) = γ ^ 2 := by field_simp
  have e3 : γ * ε * ((2 * Lq * t * a / ε + 1) * (α / a)) = 2 * γ * (Lq * α) * t + γ * ε * (α / a) := by
    field_simp
  have e4 : (1 + 1 / (γ * ε)) * (Lq * α) ^ 2 * Sr = Lq ^ 2 * Sr * α ^ 2 + Lq ^ 2 * Sr * (α ^ 2 / (γ * ε)) := by
    field_simp
  have h1 : α ^ 2 ≤ r * α ^ 2 / γ := by rw [le_div_iff₀ hγ]; nlinarith [sq_nonneg α]
  have h2 : Lq ^ 2 * Sr * α ^ 2 ≤ Lq ^ 2 * Sr * (r * α ^ 2 / γ) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h3 : 0 ≤ γ * ε * ((r / a) ^ 2 * (α / γ) ^ 2) := by positivity
  have h4 : 0 ≤ γ * ε * (α / a) := by positivity
  rw [mul_add, mul_add, e1, e2, e3, e4]
  linarith

lemma quantile_rate {Ω : Type*} [m0 : MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (M : Model d) (Θ : Set (E d)) (Proj : E d → E d) (I : Set ℝ) (Pq : ℝ → ℝ)
    (α β γ c : ℕ → ℝ) (R : Run Ω d)
    (hΘ : IsConstraintSet Θ) (hM : IsQuantileModel M Θ)
    (hProj : SpectralProjGrad.Shared.IsProjOnto Θ Proj)
    (hrun : IsSPQORun P ℱ M Θ Proj I Pq α β γ c R)
    (hA3d : A3d α β γ) (hB1 : B1 P M R)
    (hpoly : PolySteps α β γ c)
    (hq2 : ∃ U : Set (E d), IsOpen U ∧ Θ ⊆ U ∧ ContDiffOn ℝ 2 M.qf U)
    (Sr : ℝ) (hSr0 : 0 ≤ Sr)
    (hDint : ∀ k, Integrable (fun ω => ‖R.D k ω‖ ^ 2) P ∧ ∫ ω, ‖R.D k ω‖ ^ 2 ∂P ≤ Sr) :
    (∀ k, Integrable (fun ω => (R.q k ω - M.qf (R.θ k ω)) ^ 2) P) ∧
    ∃ A1 A2 : ℝ, 0 ≤ A1 ∧ 0 ≤ A2 ∧ ∀ᶠ k in atTop,
      ∫ ω, (R.q k ω - M.qf (R.θ k ω)) ^ 2 ∂P
        ≤ A1 * (α k / γ k) ^ 2 + A2 * γ k := by
  obtain ⟨ε0, Cf, hε0, hCf, hB1ae⟩ := hB1
  obtain ⟨a, b, r, c₀, eα, eβ, eγ, τ, ha, hb, hr, hc0, ⟨heα0, heα1⟩, ⟨heβ0, heβ1⟩,
    ⟨heγ0, heγ1⟩, ⟨hτ0, hτ1⟩, hsteps⟩ := hpoly
  have hX : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 1 := fun k => by positivity
  have hX1 : ∀ k : ℕ, (1 : ℝ) ≤ (k : ℝ) + 1 := fun k => by
    have := (k.cast_nonneg : (0 : ℝ) ≤ k); linarith
  have hαk : ∀ k, α k = a / ((k : ℝ) + 1) ^ eα := fun k => (hsteps k).1
  have hγk : ∀ k, γ k = r / ((k : ℝ) + 1) ^ eγ := fun k => (hsteps k).2.2.1
  have hαpos : ∀ k, 0 < α k := fun k => by rw [hαk]; exact div_pos ha (Real.rpow_pos_of_pos (hX k) _)
  have hγpos : ∀ k, 0 < γ k := fun k => by rw [hγk]; exact div_pos hr (Real.rpow_pos_of_pos (hX k) _)
  have hγle : ∀ k, γ k ≤ r := fun k => by
    rw [hγk]; exact div_le_self hr.le (Real.one_le_rpow (hX1 k) heγ0.le)
  have iαγ : ∀ k : ℕ, α k / γ k = a / r * ((k : ℝ) + 1) ^ (-(eα - eγ)) := fun k => by
    rw [hαk, hγk]; exact rp_div _ _ _ _ _ (hX k) hr.ne'
  have iα : ∀ k : ℕ, α k = a * ((k : ℝ) + 1) ^ (-eα) := fun k => by
    rw [hαk, Real.rpow_neg (hX k).le, div_eq_mul_inv]
  have iγ : ∀ k : ℕ, γ k = r * ((k : ℝ) + 1) ^ (-eγ) := fun k => by
    rw [hγk, Real.rpow_neg (hX k).le, div_eq_mul_inv]
  have hs1 : eγ < eα := by
    have := exp_neg_of_tendsto (fun k => α k / γ k) (a / r) (-(eα - eγ)) (by positivity) iαγ hA3d.1
    linarith
  obtain ⟨θ₀, hθ₀, q₀, hq₀, D₀, hinit⟩ := hrun.init
  have hθΘ : ∀ k ω, R.θ k ω ∈ Θ := by
    intro k ω; induction k with
    | zero => rw [(hinit ω).1]; exact hθ₀
    | succ k _ => rw [hrun.eq22]; exact (hProj _).1
  have hqI : ∀ k ω, R.q k ω ∈ I := by
    intro k ω; induction k with
    | zero => rw [(hinit ω).2.1]; exact hq₀
    | succ k _ => rw [hrun.eq20]; exact (hrun.pqProj.proj _).1
  have hqfI : ∀ k ω, M.qf (R.θ k ω) ∈ I := fun k ω => hrun.quantiles_mem ⟨_, hθΘ k ω, rfl⟩
  obtain ⟨Lq, hLq, hLip⟩ := q_lip hΘ.convex hΘ.isCompact hq2
  obtain ⟨U, hU, hΘU, hqC⟩ := hq2
  have hqcont : ContinuousOn M.qf Θ := hqC.continuousOn.mono hΘU
  obtain ⟨Qθ, hQθ⟩ := hΘ.isCompact.exists_bound_of_continuousOn hqcont
  have hind01 : ∀ (P' : Prop) [Decidable P'], |M.φ - (if P' then (1 : ℝ) else 0)| ≤ 1 := by
    intro P' _; have := hM.φ_pos; have := hM.φ_lt_one
    split_ifs
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [sub_zero, abs_of_pos hM.φ_pos]; linarith
  set Qk : ℕ → ℝ := fun k => |q₀| + ∑ i ∈ Finset.range k, γ i with hQk
  have hqb : ∀ k ω, |R.q k ω| ≤ Qk k := by
    intro k ω; induction k with
    | zero => rw [(hinit ω).2.1]; simp [hQk]
    | succ k ih =>
      have h1 : |R.q (k + 1) ω - R.q k ω| ≤ γ k := by
        rw [hrun.eq20]
        refine (proj1d hrun.pqProj (hqI k ω) _).trans ?_
        rw [add_sub_cancel_left, abs_mul, abs_of_pos (hγpos k)]
        have := hind01 (R.Y0 k ω ≤ R.q k ω); nlinarith [hγpos k]
      simp only [hQk, Finset.sum_range_succ] at ih ⊢
      linarith [abs_sub_abs_le_abs_sub (R.q (k + 1) ω) (R.q k ω)]
  have hθstep : ∀ k ω, ‖R.θ (k + 1) ω - R.θ k ω‖ ≤ α k * ‖R.D k ω‖ := by
    intro k ω; rw [hrun.eq22]
    have := proj_nonexp hΘ.convex hProj (hθΘ k ω) (R.θ k ω - α k • R.D k ω)
    rw [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_of_nonneg (hαpos k).le] at this
    exact this
  have hmqf : ∀ k, StronglyMeasurable[ℱ k] (fun ω => M.qf (R.θ k ω)) := fun k =>
    meas_comp_on hqcont (hrun.adapted_θ k) (hθΘ k)
  set ζ : ℕ → Ω → ℝ := fun k ω => R.q k ω - M.qf (R.θ k ω) with hζ
  have hζm : ∀ k, StronglyMeasurable[ℱ k] (ζ k) := fun k => (hrun.adapted_q k).sub (hmqf k)
  have hζm0 : ∀ k, StronglyMeasurable (ζ k) := fun k => (hζm k).mono (ℱ.le k)
  have hζb : ∀ k ω, |ζ k ω| ≤ Qk k + Qθ := by
    intro k ω; have h1 := hqb k ω; have h2 := hQθ _ (hθΘ k ω); rw [Real.norm_eq_abs] at h2
    exact (abs_sub _ _).trans (by linarith)
  have hζ2int : ∀ k, Integrable (fun ω => ζ k ω ^ 2) P := fun k =>
    Integrable.of_bound ((hζm0 k).aestronglyMeasurable.pow 2) ((Qk k + Qθ) ^ 2)
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hζb k ω) 2)
  have hζint : ∀ k, Integrable (ζ k) P := fun k =>
    Integrable.of_bound (hζm0 k).aestronglyMeasurable (Qk k + Qθ)
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hζb k ω)
  refine ⟨hζ2int, ?_⟩
  -- First moment of ‖D_k‖ from second moment
  set t := Sr + 1 with ht
  have ht0 : 0 < t := by positivity
  have hD1 : ∀ k, Integrable (fun ω => ‖R.D k ω‖) P ∧ ∫ ω, ‖R.D k ω‖ ∂P ≤ t := by
    intro k
    have hpt : ∀ ω, ‖R.D k ω‖ ≤ ‖R.D k ω‖ ^ 2 + 1 := fun ω => by
      nlinarith [sq_nonneg (‖R.D k ω‖ - 1), norm_nonneg (R.D k ω)]
    have i1 : Integrable (fun ω => ‖R.D k ω‖) P :=
      Integrable.mono' ((hDint k).1.add (integrable_const 1))
        (((hrun.adapted_D k).mono (ℱ.le k)).norm.aestronglyMeasurable)
        (Eventually.of_forall fun ω => by simp only [Pi.add_apply, Real.norm_eq_abs, abs_norm]; exact hpt ω)
    refine ⟨i1, ?_⟩
    have hm := integral_mono i1 ((hDint k).1.add (integrable_const 1)) (fun ω => hpt ω)
    rw [integral_add' (hDint k).1 (integrable_const 1), integral_const, probReal_univ,
      smul_eq_mul, one_mul] at hm
    linarith [(hDint k).2]
  set ε := min ε0 (1 / (2 * r)) with hεdef
  have hε : 0 < ε := lt_min hε0 (by positivity)
  have hεle : ε ≤ ε0 := min_le_left _ _
  have hrε : r * ε ≤ 1 / 2 := by
    have : ε ≤ 1 / (2 * r) := min_le_right _ _
    calc r * ε ≤ r * (1 / (2 * r)) := mul_le_mul_of_nonneg_left this hr.le
      _ = 1 / 2 := by field_simp
  set Z : ℕ → ℝ := fun k => ∫ ω, ζ k ω ^ 2 ∂P with hZ
  have hcontcdf : ∀ θ, Continuous (fun y => cdf M y θ) := fun θ =>
    continuous_iff_continuousAt.2 fun y => (hM.hasDens y θ).continuousAt
  have hrecZ : ∀ k, Z (k + 1) ≤ (1 - γ k * ε) * Z k
      + (1 + 1 / (γ k * ε)) * (Lq * α k) ^ 2 * Sr + γ k ^ 2 + 2 * γ k * (Lq * α k) * t := by
    intro k
    have hY : Measurable (R.Y0 k) := ((hrun.meas_Y0 k).mono (ℱ.le (k + 1))).measurable
    obtain ⟨hFm, hcond⟩ := cond_threshold (ℱ.le k) P M hM.isProb hcontcdf (R.Y0 k) hY
      (R.θ k) (R.q k) (ζ k) (hrun.adapted_q k) (hζm k) (Qk k) (Qk k + Qθ) (hqb k) (hζb k)
      (fun v => hrun.sample0 k (Set.Iic v) measurableSet_Iic)
    have hindm : Measurable (fun ω => if R.Y0 k ω ≤ R.q k ω then (1 : ℝ) else 0) :=
      Measurable.ite (measurableSet_le hY ((hrun.adapted_q k).mono (ℱ.le k)).measurable)
        measurable_const measurable_const
    have izI : Integrable (fun ω => ζ k ω * (if R.Y0 k ω ≤ R.q k ω then (1 : ℝ) else 0)) P :=
      Integrable.of_bound ((hζm0 k).aestronglyMeasurable.mul hindm.aestronglyMeasurable)
        (Qk k + Qθ) (Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_mul]
          have h1 : |(if R.Y0 k ω ≤ R.q k ω then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
          nlinarith [hζb k ω, abs_nonneg (ζ k ω),
            abs_nonneg (if R.Y0 k ω ≤ R.q k ω then (1 : ℝ) else 0)])
    have izF : Integrable (fun ω => ζ k ω * cdf M (R.q k ω) (R.θ k ω)) P :=
      Integrable.of_bound ((hζm0 k).aestronglyMeasurable.mul hFm) (Qk k + Qθ)
        (Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_mul]
          have h0 := cdf_nonneg M (R.q k ω) (R.θ k ω)
          have h1 := cdf_le_one M hM.isProb (R.q k ω) (R.θ k ω)
          rw [abs_of_nonneg h0]; nlinarith [hζb k ω, abs_nonneg (ζ k ω)])
    have hP1 : ∀ ω, ζ (k + 1) ω ^ 2 ≤ (1 + γ k * ε) * ζ k ω ^ 2
        + (1 + 1 / (γ k * ε)) * (Lq * α k) ^ 2 * ‖R.D k ω‖ ^ 2 + γ k ^ 2
        + 2 * γ k * (M.φ * ζ k ω - ζ k ω * (if R.Y0 k ω ≤ R.q k ω then (1 : ℝ) else 0))
        + 2 * γ k * (Lq * α k) * ‖R.D k ω‖ := by
      intro ω
      set e := M.φ - (if R.Y0 k ω ≤ R.q k ω then (1 : ℝ) else 0) with he
      set δq := M.qf (R.θ k ω) - M.qf (R.θ (k + 1) ω) with hδq
      have hδ : |δq| ≤ Lq * α k * ‖R.D k ω‖ := by
        have := hLip _ (hθΘ k ω) _ (hθΘ (k + 1) ω); rw [norm_sub_rev] at this
        calc |δq| ≤ Lq * ‖R.θ (k + 1) ω - R.θ k ω‖ := this
          _ ≤ Lq * (α k * ‖R.D k ω‖) := mul_le_mul_of_nonneg_left (hθstep k ω) hLq.le
          _ = _ := by ring
      have hz1 : |ζ (k + 1) ω| ≤ |ζ k ω + δq + γ k * e| := by
        simp only [hζ]; rw [hrun.eq20]
        refine (proj1d hrun.pqProj (hqfI (k + 1) ω) _).trans (le_of_eq ?_)
        congr 1; simp only [hδq, he]; ring
      have hpw := pathwise (ζ k ω) (ζ (k + 1) ω) δq e (Lq * α k * ‖R.D k ω‖) (γ k) ε
        (hγpos k) hε hz1 hδ (hind01 _)
      have e1 : (Lq * α k * ‖R.D k ω‖) ^ 2 = (Lq * α k) ^ 2 * ‖R.D k ω‖ ^ 2 := by ring
      have e2 : ζ k ω * e = M.φ * ζ k ω - ζ k ω *
          (if R.Y0 k ω ≤ R.q k ω then (1 : ℝ) else 0) := by rw [he]; ring
      rw [e1, e2] at hpw; linarith
    have hP2 : ∀ᵐ ω ∂P, M.φ * ζ k ω - ζ k ω * cdf M (R.q k ω) (R.θ k ω) ≤ -ε * ζ k ω ^ 2 := by
      filter_upwards [hB1ae] with ω hω
      obtain ⟨ξ, hξ, hmvt⟩ := mvt_cdf M hM.hasDens (R.θ k ω) (R.q k ω) (M.qf (R.θ k ω))
      have hfξ := ((hω k) ξ hξ).1
      have hφq : cdf M (M.qf (R.θ k ω)) (R.θ k ω) = M.φ := hM.quantile _
      have e : M.φ * ζ k ω - ζ k ω * cdf M (R.q k ω) (R.θ k ω)
          = -(M.dens ξ (R.θ k ω)) * ζ k ω ^ 2 := by
        rw [← hφq]
        have : ζ k ω = R.q k ω - M.qf (R.θ k ω) := rfl
        rw [this]; linear_combination (R.q k ω - M.qf (R.θ k ω)) * hmvt
      rw [e]; nlinarith [sq_nonneg (ζ k ω)]
    have hos := onestep P (ζ k) (ζ (k + 1)) (fun ω => if R.Y0 k ω ≤ R.q k ω then (1 : ℝ) else 0)
      (fun ω => cdf M (R.q k ω) (R.θ k ω)) (fun ω => ‖R.D k ω‖) (γ k) ε (α k) Lq M.φ
      (hγpos k) hε (hζ2int k) (hζint k) (hζ2int (k + 1)) izI izF (hDint k).1 (hD1 k).1 hcond
      hP1 hP2
    have c1 : 0 ≤ (1 + 1 / (γ k * ε)) * (Lq * α k) ^ 2 := by have := hγpos k; positivity
    have c2 : 0 ≤ 2 * γ k * (Lq * α k) := by have := hγpos k; have := hαpos k; positivity
    have := mul_le_mul_of_nonneg_left (hDint k).2 c1
    have := mul_le_mul_of_nonneg_left (hD1 k).2 c2
    linarith
  have hZ0 : ∀ k, 0 ≤ Z k := fun k => integral_nonneg fun ω => sq_nonneg _
  set K1 := Lq ^ 2 * Sr * (r / ε + 1 / ε ^ 2) * (a / r) ^ 2 + 1 with hK1
  set K2 := 2 * Lq * t * a / ε + 1 with hK2
  set K3 := r / ε with hK3
  have hX2 : ∀ k : ℕ, ((k : ℝ) + 1) ^ (-(2 * (eα - eγ))) = (r / a) ^ 2 * (α k / γ k) ^ 2 := by
    intro k; rw [iαγ k, mul_pow, rp_pow_sq _ _ (hX k)]; field_simp
  have hXg : ∀ k : ℕ, ((k : ℝ) + 1) ^ (-eγ) = γ k / r := fun k => by rw [iγ k]; field_simp
  have hXa : ∀ k : ℕ, ((k : ℝ) + 1) ^ (-eα) = α k / a := fun k => by rw [iα k]; field_simp
  obtain ⟨B1, B2, B3, hB1', hB2', hB3', hev⟩ := det_rate_3 Z hZ0 (r * ε) eγ
    (2 * (eα - eγ)) eα eγ (by positivity) hrε heγ0 heγ1 (by linarith) heα0 heγ0 heγ1
    K1 K2 K3 (by positivity) (by positivity) (by positivity) 0 (by
      intro k _
      rw [hX2 k, hXa k, hXg k]
      have hci := coef_ineq (α k) (γ k) a r ε Lq Sr t (hαpos k) (hγpos k) (hγle k) ha hr hε hLq
        hSr0 ht0
      have hre : r * ε * (γ k / r) = γ k * ε := by field_simp
      rw [hre]; linarith [hrecZ k])
  refine ⟨B1 * (r / a) ^ 2, (B2 + B3) / r, by positivity, by positivity, ?_⟩
  filter_upwards [hev] with k hk
  have hXeα : ((k : ℝ) + 1) ^ (-eα) ≤ ((k : ℝ) + 1) ^ (-eγ) :=
    Real.rpow_le_rpow_of_exponent_le (hX1 k) (by linarith)
  have hk' : Z k ≤ B1 * ((k : ℝ) + 1) ^ (-(2 * (eα - eγ)))
      + (B2 + B3) * ((k : ℝ) + 1) ^ (-eγ) := by
    nlinarith [mul_le_mul_of_nonneg_left hXeα hB2']
  rw [hX2 k, hXg k] at hk'
  linarith [show B1 * ((r / a) ^ 2 * (α k / γ k) ^ 2) + (B2 + B3) * (γ k / r)
      = B1 * (r / a) ^ 2 * (α k / γ k) ^ 2 + (B2 + B3) / r * γ k by ring]

end SPQOL4

/-! ### Part 6: Pointwise & algebraic helpers for Lemma 5 and main theorem -/

namespace SPQOL5
open QuantileSPQO.Rate

lemma eta_onestep_pt {d : ℕ} (η₀ η₁ δG g : E d) (Dn β ε Lg α : ℝ)
    (hβ : 0 < β) (hε : 0 < ε) (_hLg : 0 < Lg) (_hα : 0 < α) (_hDn : 0 ≤ Dn)
    (hsucc : η₁ = η₀ + δG + β • g) (hδG : ‖δG‖ ≤ Lg * α * Dn) :
    ‖η₁‖ ^ 2 ≤ (1 + β * ε / 2) * ‖η₀‖ ^ 2 + (2 + 2 / (β * ε)) * (Lg * α) ^ 2 * Dn ^ 2
      + 2 * β ^ 2 * ‖g‖ ^ 2 + 2 * β * ⟪η₀, g⟫ := by
  have hδG_sq : ‖δG‖ ^ 2 ≤ (Lg * α) ^ 2 * Dn ^ 2 := by
    have : (Lg * α * Dn) ^ 2 = (Lg * α) ^ 2 * Dn ^ 2 := by ring
    rw [← this]; exact pow_le_pow_left₀ (norm_nonneg _) hδG 2
  have hexp : ‖η₁‖ ^ 2 = ‖η₀‖ ^ 2 + ‖δG‖ ^ 2 + β ^ 2 * ‖g‖ ^ 2
      + 2 * ⟪η₀, δG⟫ + 2 * β * ⟪δG, g⟫ + 2 * β * ⟪η₀, g⟫ := by
    rw [hsucc, norm_add_sq_real, norm_add_sq_real, inner_add_left,
      real_inner_smul_right, real_inner_smul_right, norm_smul, mul_pow,
      Real.norm_of_nonneg hβ.le]
    ring
  have hy1 : 2 * ⟪η₀, δG⟫ ≤ (β * ε / 2) * ‖η₀‖ ^ 2 + (2 / (β * ε)) * ‖δG‖ ^ 2 := by
    have h1 : ⟪η₀, δG⟫ ≤ ‖η₀‖ * ‖δG‖ := real_inner_le_norm _ _
    have h2 : 0 ≤ (β * ε * ‖η₀‖ - 2 * ‖δG‖) ^ 2 / (2 * (β * ε)) := by positivity
    have e : (β * ε * ‖η₀‖ - 2 * ‖δG‖) ^ 2 / (2 * (β * ε))
        = (β * ε / 2) * ‖η₀‖ ^ 2 - 2 * ‖η₀‖ * ‖δG‖ + (2 / (β * ε)) * ‖δG‖ ^ 2 := by
      field_simp; ring
    linarith
  have hy2 : 2 * β * ⟪δG, g⟫ ≤ ‖δG‖ ^ 2 + β ^ 2 * ‖g‖ ^ 2 := by
    have h1 : ⟪δG, g⟫ ≤ ‖δG‖ * ‖g‖ := real_inner_le_norm _ _
    nlinarith [sq_nonneg (‖δG‖ - β * ‖g‖)]
  have hcoef : 0 ≤ 2 + 2 / (β * ε) := by positivity
  have h3 := mul_le_mul_of_nonneg_left hδG_sq hcoef
  rw [hexp]; linarith

lemma drift_onestep_pt {d : ℕ} (η res b : E d) (f qd m2 ε Lr Kp c : ℝ)
    (hε : 0 < ε) (hf : ε ≤ f) (hLr : 0 ≤ Lr) (hKp : 0 ≤ Kp)
    (hres : ‖res‖ ≤ Lr * |qd|) (hbias : ‖b‖ ^ 2 ≤ Kp ^ 2 * m2 * c ^ 4) :
    ⟪η, -f • η - res + b⟫ ≤
      -(ε / 2) * ‖η‖ ^ 2 + (Lr ^ 2 / ε) * qd ^ 2 + (Kp ^ 2 / ε) * m2 * c ^ 4 := by
  rw [inner_add_right, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  have hy_res : -⟪η, res⟫ ≤ (ε / 4) * ‖η‖ ^ 2 + (1 / ε) * ‖res‖ ^ 2 := by
    have h1 : -⟪η, res⟫ ≤ ‖η‖ * ‖res‖ := by
      have := neg_le_abs (⟪η, res⟫); linarith [abs_real_inner_le_norm η res]
    have h2 : 0 ≤ (ε / 2 * ‖η‖ - ‖res‖) ^ 2 / ε := by positivity
    have e : (ε / 2 * ‖η‖ - ‖res‖) ^ 2 / ε
        = (ε / 4) * ‖η‖ ^ 2 - ‖η‖ * ‖res‖ + (1 / ε) * ‖res‖ ^ 2 := by field_simp; ring
    linarith
  have hy_b : ⟪η, b⟫ ≤ (ε / 4) * ‖η‖ ^ 2 + (1 / ε) * ‖b‖ ^ 2 := by
    have h1 : ⟪η, b⟫ ≤ ‖η‖ * ‖b‖ := real_inner_le_norm _ _
    have h2 : 0 ≤ (ε / 2 * ‖η‖ - ‖b‖) ^ 2 / ε := by positivity
    have e : (ε / 2 * ‖η‖ - ‖b‖) ^ 2 / ε
        = (ε / 4) * ‖η‖ ^ 2 - ‖η‖ * ‖b‖ + (1 / ε) * ‖b‖ ^ 2 := by field_simp; ring
    linarith
  have hres_sq : ‖res‖ ^ 2 ≤ Lr ^ 2 * qd ^ 2 := by
    have h1 := pow_le_pow_left₀ (norm_nonneg _) hres 2
    rwa [mul_pow, sq_abs] at h1
  have h1e : 0 ≤ 1 / ε := by positivity
  have hm1 := mul_le_mul_of_nonneg_left hres_sq h1e
  have hm2 := mul_le_mul_of_nonneg_left hbias h1e
  have hfn : -f * ‖η‖ ^ 2 ≤ -ε * ‖η‖ ^ 2 := by nlinarith [sq_nonneg ‖η‖]
  linarith [show (1 / ε) * (Lr ^ 2 * qd ^ 2) = (Lr ^ 2 / ε) * qd ^ 2 by ring,
    show (1 / ε) * (Kp ^ 2 * m2 * c ^ 4) = (Kp ^ 2 / ε) * m2 * c ^ 4 by ring]

lemma forcing_combine (Y0 Y1 α β γ c a b r c₀ ε Lg Sr Lr Kp d A4₁ A4₂ X1 X2 X3 : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hc : 0 < c)
    (_ha : 0 < a) (hb : 0 < b) (_hr : 0 < r) (_hc0 : 0 < c₀)
    (hε : 0 < ε) (hLg : 0 < Lg) (hSr : 0 ≤ Sr) (_hLr : 0 ≤ Lr) (_hKp : 0 ≤ Kp) (hd : 0 < d)
    (_hA4₁ : 0 ≤ A4₁) (hA4₂ : 0 ≤ A4₂) (hX1 : 0 ≤ X1) (hX2 : 0 ≤ X2) (hX3 : 0 ≤ X3)
    (hβb : β ≤ b) (hαβ : α / β ≤ (r / b) * (α / γ)) (hγ3 : γ ≤ r * X3)
    (hR1 : (α / γ) ^ 2 = (a / r) ^ 2 * X1)
    (hR2 : c ^ 4 = c₀ ^ 4 * X2)
    (hR3 : β / c ^ 2 = (b / c₀ ^ 2) * X3)
    (hstep : Y1 ≤ (1 - β * ε / 2) * Y0
      + (2 + 2 / (β * ε)) * (Lg * α) ^ 2 * Sr
      + 2 * β ^ 2 * ((d + Sr) / (4 * c ^ 2))
      + 2 * β * (Lr ^ 2 / ε) * (A4₁ * (α / γ) ^ 2 + A4₂ * γ)
      + 2 * β * ((Kp ^ 2 / ε) * (1 + Sr / d) * c ^ 4)) :
    Y1 ≤ (1 - β * ε / 2) * Y0 + (β * ε / 2) * (
      ((4 * b / ε + 4 / ε ^ 2) * Lg ^ 2 * Sr * (r / b) ^ 2 * (a / r) ^ 2
        + (4 * Lr ^ 2 / ε ^ 2) * A4₁ * (a / r) ^ 2 + 1) * X1
      + ((4 * Kp ^ 2 / ε ^ 2) * (1 + Sr / d) * c₀ ^ 4 + 1) * X2
      + ((d + Sr) / ε * (b / c₀ ^ 2) + (4 * Lr ^ 2 / ε ^ 2) * A4₂ * r + 1) * X3) := by
  have hbe : 0 ≤ β * ε / 2 := by positivity
  have hF1 : (2 + 2 / (β * ε)) * (Lg * α) ^ 2 * Sr
      ≤ (β * ε / 2) * ((4 * b / ε + 4 / ε ^ 2) * Lg ^ 2 * Sr * (r / b) ^ 2 * (a / r) ^ 2 * X1) := by
    have h1R : (4 * b / ε + 4 / ε ^ 2) * Lg ^ 2 * Sr * (r / b) ^ 2 * (a / r) ^ 2 * X1
        = (4 * b / ε + 4 / ε ^ 2) * Lg ^ 2 * Sr * (r / b) ^ 2 * ((a / r) ^ 2 * X1) := by ring
    rw [h1R, ← hR1]
    have hαβ2 : (α / β) ^ 2 ≤ (r / b) ^ 2 * (α / γ) ^ 2 := by
      have h1 := pow_le_pow_left₀ (div_nonneg hα.le hβ.le) hαβ 2; rwa [mul_pow] at h1
    have h1 : 2 + 2 / (β * ε) ≤ (2 * b + 2 / ε) / β := by
      rw [le_div_iff₀ hβ]
      have e : (2 + 2 / (β * ε)) * β = 2 * β + 2 / ε := by field_simp
      linarith
    have h2 : (2 + 2 / (β * ε)) * (Lg * α) ^ 2 * Sr
        ≤ (β * ε / 2) * ((4 * b / ε + 4 / ε ^ 2) * Lg ^ 2 * Sr * (α / β) ^ 2) := by
      have e : (β * ε / 2) * ((4 * b / ε + 4 / ε ^ 2) * Lg ^ 2 * Sr * (α / β) ^ 2)
          = ((2 * b + 2 / ε) / β) * (Lg * α) ^ 2 * Sr := by field_simp; ring
      rw [e]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (sq_nonneg _)) hSr
    refine h2.trans ?_
    have h3 : (4 * b / ε + 4 / ε ^ 2) * Lg ^ 2 * Sr * (α / β) ^ 2
        ≤ (4 * b / ε + 4 / ε ^ 2) * Lg ^ 2 * Sr * ((r / b) ^ 2 * (α / γ) ^ 2) :=
      mul_le_mul_of_nonneg_left hαβ2 (by positivity)
    have h4 := mul_le_mul_of_nonneg_left h3 hbe
    linarith
  have hF2 : 2 * β ^ 2 * ((d + Sr) / (4 * c ^ 2))
      = (β * ε / 2) * ((d + Sr) / ε * (b / c₀ ^ 2) * X3) := by
    have h2R : (d + Sr) / ε * (b / c₀ ^ 2) * X3 = (d + Sr) / ε * (b / c₀ ^ 2 * X3) := by ring
    rw [h2R, ← hR3]; field_simp; ring
  have hF3 : 2 * β * (Lr ^ 2 / ε) * (A4₁ * (α / γ) ^ 2 + A4₂ * γ)
      ≤ (β * ε / 2) * ((4 * Lr ^ 2 / ε ^ 2) * A4₁ * (a / r) ^ 2 * X1
          + (4 * Lr ^ 2 / ε ^ 2) * A4₂ * r * X3) := by
    have e : 2 * β * (Lr ^ 2 / ε) * (A4₁ * (α / γ) ^ 2 + A4₂ * γ)
        = (β * ε / 2) * ((4 * Lr ^ 2 / ε ^ 2) * A4₁ * (α / γ) ^ 2
            + (4 * Lr ^ 2 / ε ^ 2) * A4₂ * γ) := by field_simp; ring
    rw [e, hR1]
    have h1 : (4 * Lr ^ 2 / ε ^ 2) * A4₂ * γ ≤ (4 * Lr ^ 2 / ε ^ 2) * A4₂ * (r * X3) :=
      mul_le_mul_of_nonneg_left hγ3 (by positivity)
    exact mul_le_mul_of_nonneg_left (by linarith) hbe
  have hF4 : 2 * β * ((Kp ^ 2 / ε) * (1 + Sr / d) * c ^ 4)
      = (β * ε / 2) * ((4 * Kp ^ 2 / ε ^ 2) * (1 + Sr / d) * c₀ ^ 4 * X2) := by
    have h4R : 4 * Kp ^ 2 / ε ^ 2 * (1 + Sr / d) * c₀ ^ 4 * X2
        = 4 * Kp ^ 2 / ε ^ 2 * (1 + Sr / d) * (c₀ ^ 4 * X2) := by ring
    rw [h4R, ← hR2]; field_simp; ring
  have hExtra : 0 ≤ (β * ε / 2) * (X1 + X2 + X3) := by positivity
  linarith

lemma final_sq_bound (Yk A1 A2 A3 r a c₀ b T1 T2 T3 : ℝ)
    (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2) (hA3 : 0 ≤ A3)
    (hr : 0 < r) (ha : 0 < a) (hc0 : 0 < c₀) (hb : 0 < b)
    (hT1 : 0 ≤ T1) (hT2 : 0 ≤ T2) (hT3 : 0 ≤ T3)
    (hk : Yk ≤ A1 * ((r / a) ^ 2 * T1 ^ 2) + A2 * (T2 ^ 2 / c₀ ^ 4)
      + A3 * ((c₀ ^ 2 / b) * T3 ^ 2)) :
    Yk ≤ (Real.sqrt (A1 * (r / a) ^ 2 + A2 / c₀ ^ 4 + A3 * (c₀ ^ 2 / b))
      * (T1 + T2 + T3)) ^ 2 := by
  set B1 := A1 * (r / a) ^ 2
  set B2 := A2 / c₀ ^ 4
  set B3 := A3 * (c₀ ^ 2 / b)
  have hB1 : 0 ≤ B1 := by positivity
  have hB2 : 0 ≤ B2 := by positivity
  have hB3 : 0 ≤ B3 := by positivity
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hsq1 : T1 ^ 2 ≤ (T1 + T2 + T3) ^ 2 := by nlinarith
  have hsq2 : T2 ^ 2 ≤ (T1 + T2 + T3) ^ 2 := by nlinarith
  have hsq3 : T3 ^ 2 ≤ (T1 + T2 + T3) ^ 2 := by nlinarith
  have m1 := mul_le_mul_of_nonneg_left hsq1 hB1
  have m2 := mul_le_mul_of_nonneg_left hsq2 hB2
  have m3 := mul_le_mul_of_nonneg_left hsq3 hB3
  have hrew : A1 * ((r / a) ^ 2 * T1 ^ 2) + A2 * (T2 ^ 2 / c₀ ^ 4)
      + A3 * ((c₀ ^ 2 / b) * T3 ^ 2) = B1 * T1 ^ 2 + B2 * T2 ^ 2 + B3 * T3 ^ 2 := by
    simp only [B1, B2, B3]; ring
  linarith

end SPQOL5

open QuantileSPQO.Rate SPQOCommon SPQOCond SPQOSeq SPQODBound SPQOL4 SPQOL5

theorem solution {Ω : Type*} [m0 : MeasurableSpace Ω] {d : ℕ} (hd : 0 < d)
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (M : Model d) (Θ : Set (E d)) (Proj : E d → E d) (I : Set ℝ) (Pq : ℝ → ℝ)
    (α β γ c : ℕ → ℝ) (R : Run Ω d)
    (hΘ : IsConstraintSet Θ) (hM : IsQuantileModel M Θ)
    (hProj : SpectralProjGrad.Shared.IsProjOnto Θ Proj)
    (hrun : IsSPQORun P ℱ M Θ Proj I Pq α β γ c R)
    (hA1 : A1 P M R) (hA2 : A2 P ℱ R) (hA3a : A3a β c)
    (hA3b : A3b γ) (hA3c : A3c α) (hA3d : A3d α β γ)
    (hB1 : B1 P M R)
    (hB2 : B2 M Θ)
    (hpoly : PolySteps α β γ c)
    (hq2 : ∃ U : Set (E d), IsOpen U ∧ Θ ⊆ U ∧ ContDiffOn ℝ 2 M.qf U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop,
      ∫⁻ ω, ‖R.D k ω - gradient M.qf (R.θ k ω)‖ₑ ^ 2 ∂P
        ≤ ENNReal.ofReal ((C * (α k / γ k + c k ^ 2 + Real.sqrt (β k) / c k)) ^ 2) := by
  -- Step 1: Uniform bound on E‖D_k‖² and quantile tracker rate (Lemma 4)
  obtain ⟨Sr, hSr0, hDmom⟩ := D_sq_bdd hd P ℱ M Θ Proj I Pq α β γ c R hM hrun hA1 hA2 hA3a hA3b hpoly
  obtain ⟨hζ2int, A4₁, A4₂, hA4₁, hA4₂, hL4ev⟩ := quantile_rate P ℱ M Θ Proj I Pq α β γ c R
    hΘ hM hProj hrun hA3d hB1 hpoly hq2 Sr hSr0 (fun k => ⟨(hDmom k).1, (hDmom k).2.1⟩)
  -- Step 2: Unpack step-size exponents and assumptions
  obtain ⟨a, b, r, c₀, eα, eβ, eγ, τ, ha, hb, hr, hc0, ⟨heα0, heα1⟩, ⟨heβ0, heβ1⟩,
    ⟨heγ0, heγ1⟩, ⟨hτ0, hτ1⟩, hsteps⟩ := hpoly
  obtain ⟨δ, hδ, K, ε0, hε0, hA1ae⟩ := hA1
  obtain ⟨-, Lf, LF, hLf, hLF, hB2lip⟩ := hB2
  obtain ⟨θ₀, hθ₀, q₀, hq₀, D₀, hinit⟩ := hrun.init
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hsd0 : 0 < Real.sqrt d := Real.sqrt_pos.2 hd0
  have hX : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 1 := fun k => by positivity
  have hX1 : ∀ k : ℕ, (1 : ℝ) ≤ (k : ℝ) + 1 := fun k => by
    have := (k.cast_nonneg : (0 : ℝ) ≤ k); linarith
  have hαk : ∀ k, α k = a / ((k : ℝ) + 1) ^ eα := fun k => (hsteps k).1
  have hβk : ∀ k, β k = b / ((k : ℝ) + 1) ^ eβ := fun k => (hsteps k).2.1
  have hγk : ∀ k, γ k = r / ((k : ℝ) + 1) ^ eγ := fun k => (hsteps k).2.2.1
  have hck : ∀ k, c k = c₀ / ((k : ℝ) + 1) ^ τ := fun k => (hsteps k).2.2.2
  have hαpos : ∀ k, 0 < α k := hA3c.1
  have hβpos : ∀ k, 0 < β k := fun k => (hA3a.1 k).1
  have hγpos : ∀ k, 0 < γ k := hA3b.1
  have hcpos : ∀ k, 0 < c k := fun k => (hA3a.1 k).2
  have hβle : ∀ k, β k ≤ b := fun k => by
    rw [hβk]; exact div_le_self hb.le (Real.one_le_rpow (hX1 k) heβ0.le)
  have iαγ : ∀ k : ℕ, α k / γ k = a / r * ((k : ℝ) + 1) ^ (-(eα - eγ)) := fun k => by
    rw [hαk, hγk]; exact rp_div _ _ _ _ _ (hX k) hr.ne'
  have iγβ : ∀ k : ℕ, γ k / β k = r / b * ((k : ℝ) + 1) ^ (-(eγ - eβ)) := fun k => by
    rw [hγk, hβk]; exact rp_div _ _ _ _ _ (hX k) hb.ne'
  have hβc2_eq : ∀ k : ℕ, β k ^ 2 / c k ^ 2 = (b / c₀) ^ 2 * ((k : ℝ) + 1) ^ (-(2 * (eβ - τ))) := by
    intro k; rw [hβk, hck, ← div_pow, rp_div b c₀ eβ τ _ (hX k) hc0.ne', mul_pow, rp_pow_sq _ _ (hX k)]
    congr 1; ring_nf
  have heγ_lt_eα : eγ < eα := by
    have := exp_neg_of_tendsto (fun k => α k / γ k) (a / r) (-(eα - eγ)) (by positivity) iαγ hA3d.1
    linarith
  have heβ_lt_eγ : eβ < eγ := by
    have := exp_neg_of_tendsto (fun k => γ k / β k) (r / b) (-(eγ - eβ)) (by positivity) iγβ hA3d.2
    linarith
  have heβτ : 1 / 2 < eβ - τ := by
    have hs : Summable (fun k : ℕ => (b / c₀) ^ 2 * ((k : ℝ) + 1) ^ (-(2 * (eβ - τ)))) :=
      hA3a.2.2.2.congr hβc2_eq
    have := exp_lt_of_summable ((b / c₀) ^ 2) (-(2 * (eβ - τ))) (by positivity) hs
    linarith
  have hs30 : 0 < eβ - 2 * τ := by linarith
  have hs31 : eβ - 2 * τ < 1 := by linarith
  -- Power representations of the three rate terms
  have hR1 : ∀ k : ℕ, (α k / γ k) ^ 2 = (a / r) ^ 2 * ((k : ℝ) + 1) ^ (-(2 * (eα - eγ))) := by
    intro k; rw [iαγ k, mul_pow, rp_pow_sq _ _ (hX k)]; ring_nf
  have hR2 : ∀ k : ℕ, c k ^ 4 = c₀ ^ 4 * ((k : ℝ) + 1) ^ (-(4 * τ)) := by
    intro k
    have hc2 : c k ^ 2 = c₀ ^ 2 * ((k : ℝ) + 1) ^ (-(2 * τ)) := by
      rw [hck, div_pow, rp_pow_sq _ _ (hX k), Real.rpow_neg (hX k).le, div_eq_mul_inv]
    calc c k ^ 4 = (c k ^ 2) ^ 2 := by ring
      _ = (c₀ ^ 2) ^ 2 * (((k : ℝ) + 1) ^ (-(2 * τ))) ^ 2 := by rw [hc2, mul_pow]
      _ = c₀ ^ 4 * ((k : ℝ) + 1) ^ (-(4 * τ)) := by rw [rp_pow_sq _ _ (hX k)]; ring_nf
  have hR3 : ∀ k : ℕ, β k / c k ^ 2 = (b / c₀ ^ 2) * ((k : ℝ) + 1) ^ (-(eβ - 2 * τ)) := by
    intro k
    rw [hβk, hck, div_pow, rp_pow_sq _ _ (hX k),
      rp_div b (c₀ ^ 2) eβ (2 * τ) _ (hX k) (by positivity)]
  have hβ_eq : ∀ k : ℕ, β k = b * ((k : ℝ) + 1) ^ (-eβ) := fun k => by
    rw [hβk, Real.rpow_neg (hX k).le, div_eq_mul_inv]
  have hγ_le_β : ∀ k : ℕ, γ k / r ≤ β k / b := by
    intro k
    rw [hγk, hβk]
    have h1 : ((k : ℝ) + 1) ^ eβ ≤ ((k : ℝ) + 1) ^ eγ :=
      Real.rpow_le_rpow_of_exponent_le (hX1 k) heβ_lt_eγ.le
    have h2 : 0 < ((k : ℝ) + 1) ^ eβ := Real.rpow_pos_of_pos (hX k) _
    have h3 : 0 < ((k : ℝ) + 1) ^ eγ := Real.rpow_pos_of_pos (hX k) _
    rw [div_div_cancel_left' hr.ne', div_div_cancel_left' hb.ne']
    exact inv_anti₀ h2 h1
  have hαβ_le : ∀ k : ℕ, α k / β k ≤ (r / b) * (α k / γ k) := by
    intro k
    have h1 := hγ_le_β k
    have hγp := hγpos k; have hβp := hβpos k; have hαp := hαpos k
    have h2 : γ k / β k ≤ r / b := by
      rw [div_le_div_iff₀ hβp hb]; rw [div_le_div_iff₀ hr hb] at h1; linarith
    have e : α k / β k = (γ k / β k) * (α k / γ k) := by field_simp
    rw [e]; exact mul_le_mul_of_nonneg_right h2 (by positivity)
  have hγ_le_R3 : ∀ k : ℕ, γ k ≤ r * ((k : ℝ) + 1) ^ (-(eβ - 2 * τ)) := by
    intro k
    rw [hγk, div_eq_mul_inv, Real.rpow_neg (hX k).le]
    exact mul_le_mul_of_nonneg_left
      (inv_anti₀ (Real.rpow_pos_of_pos (hX k) _)
        (Real.rpow_le_rpow_of_exponent_le (hX1 k) (by linarith))) hr.le
  -- Step 3: Geometry of Θ and regularity of ∇q
  have hθΘ : ∀ k ω, R.θ k ω ∈ Θ := by
    intro k ω; induction k with
    | zero => rw [(hinit ω).1]; exact hθ₀
    | succ k _ => rw [hrun.eq22]; exact (hProj _).1
  have hqI : ∀ k ω, R.q k ω ∈ I := by
    intro k ω; induction k with
    | zero => rw [(hinit ω).2.1]; exact hq₀
    | succ k _ => rw [hrun.eq20]; exact (hrun.pqProj.proj _).1
  have hθstep : ∀ k ω, ‖R.θ (k + 1) ω - R.θ k ω‖ ≤ α k * ‖R.D k ω‖ := by
    intro k ω; rw [hrun.eq22]
    have := proj_nonexp hΘ.convex hProj (hθΘ k ω) (R.θ k ω - α k • R.D k ω)
    rw [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_of_nonneg (hαpos k).le] at this
    exact this
  obtain ⟨Lg, hLg, hgradLip⟩ := grad_lip hΘ.convex hΘ.isCompact hq2
  have hgcont : ContinuousOn (gradient M.qf) Θ := grad_contOn hq2
  obtain ⟨Mg0, hMg0'⟩ := hΘ.isCompact.exists_bound_of_continuousOn hgcont
  set Mg := max Mg0 0 with hMgdef
  have hMg0 : 0 ≤ Mg := le_max_right _ _
  have hMg : ∀ θ ∈ Θ, ‖gradient M.qf θ‖ ≤ Mg := fun θ hθ => (hMg0' θ hθ).trans (le_max_left _ _)
  obtain ⟨U, hU, hΘU, hqC⟩ := hq2
  have hqdiff : ∀ θ ∈ Θ, DifferentiableAt ℝ M.qf θ := fun θ hθ =>
    (hqC.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds (hΘU hθ))
  -- Deterministic bounds on q_k and D_k (on goodEvent)
  have hind01 : ∀ (P' : Prop) [Decidable P'], |M.φ - (if P' then (1 : ℝ) else 0)| ≤ 1 := by
    intro P' _; have := hM.φ_pos; have := hM.φ_lt_one
    split_ifs
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [sub_zero, abs_of_pos hM.φ_pos]; linarith
  set Qk : ℕ → ℝ := fun k => |q₀| + ∑ i ∈ Finset.range k, γ i with hQk
  have hQk0 : ∀ k, 0 ≤ Qk k := fun k => by
    simp only [hQk]; exact add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun i _ => (hγpos i).le)
  have hqb : ∀ k ω, |R.q k ω| ≤ Qk k := by
    intro k ω; induction k with
    | zero => rw [(hinit ω).2.1]; simp [hQk]
    | succ k ih =>
      have h1 : |R.q (k + 1) ω - R.q k ω| ≤ γ k := by
        rw [hrun.eq20]
        refine (proj1d hrun.pqProj (hqI k ω) _).trans ?_
        rw [add_sub_cancel_left, abs_mul, abs_of_pos (hγpos k)]
        have := hind01 (R.Y0 k ω ≤ R.q k ω); nlinarith [hγpos k]
      simp only [hQk, Finset.sum_range_succ] at ih ⊢
      linarith [abs_sub_abs_le_abs_sub (R.q (k + 1) ω) (R.q k ω)]
  set Bk : ℕ → ℝ := Dbound β c D₀ with hBk
  have hBk0 : ∀ k, 0 ≤ Bk k := Dbound_nonneg β c D₀ hβpos hcpos
  have hDb : ∀ k ω, ω ∈ goodEvent R k → ‖R.D k ω‖ ≤ Bk k :=
    norm_D_le_Dbound hd hrun hβpos hcpos (fun ω => (hinit ω).2.2)
  -- Tracking error η_k = D_k − ∇q(θ_k)
  set η : ℕ → Ω → E d := fun k ω => R.D k ω - gradient M.qf (R.θ k ω) with hηdef
  have hgm : ∀ k, StronglyMeasurable[ℱ k] (fun ω => gradient M.qf (R.θ k ω)) := fun k =>
    meas_comp_on hgcont (hrun.adapted_θ k) (hθΘ k)
  have hηm : ∀ k, StronglyMeasurable[ℱ k] (η k) := fun k => (hrun.adapted_D k).sub (hgm k)
  have hηm0 : ∀ k, StronglyMeasurable (η k) := fun k => (hηm k).mono (ℱ.le k)
  have hηb : ∀ k ω, ω ∈ goodEvent R k → ‖η k ω‖ ≤ Bk k + Mg := fun k ω hω =>
    (norm_sub_le _ _).trans (add_le_add (hDb k ω hω) (hMg _ (hθΘ k ω)))
  have hη2int : ∀ k, Integrable (fun ω => ‖η k ω‖ ^ 2) P := by
    intro k
    refine Integrable.of_bound ((hηm0 k).norm.pow 2).aestronglyMeasurable ((Bk k + Mg) ^ 2) ?_
    filter_upwards [goodEvent_ae P ℱ M Θ Proj I Pq α β γ c R hrun hA2 k] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hηb k ω hω) 2
  have hgint : ∀ k, Integrable (fun ω => ‖spGrad c R k ω‖ ^ 2) P := by
    intro k
    refine Integrable.of_bound ((spGrad_meas hrun hβpos k).norm.pow 2).aestronglyMeasurable
      ((d + Bk k ^ 2) / (4 * c k ^ 2)) ?_
    filter_upwards [goodEvent_ae P ℱ M Θ Proj I Pq α β γ c R hrun hA2 (k + 1)] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    obtain ⟨b, hb⟩ := goodEvent_succ_mem_Delta R k hω
    have h1 := norm_spGrad_sq_le hd c R k ω (hcpos k) b hb
    have h2 := hDb k ω (goodEvent_succ_subset R k hω)
    calc ‖spGrad c R k ω‖ ^ 2 ≤ (d + ‖R.D k ω‖ ^ 2) / (4 * c k ^ 2) := h1
      _ ≤ (d + Bk k ^ 2) / (4 * c k ^ 2) := by gcongr
  -- Step 4: One-step recursion for Y_k = E‖η_k‖²
  set ε := min ε0 (1 / b) with hεdef
  have hε : 0 < ε := lt_min hε0 (by positivity)
  have hεle : ε ≤ ε0 := min_le_left _ _
  have hbε : b * ε / 2 ≤ 1 / 2 := by
    have : ε ≤ 1 / b := min_le_right _ _
    have h1 : b * ε ≤ 1 := by
      calc b * ε ≤ b * (1 / b) := mul_le_mul_of_nonneg_left this hb.le
        _ = 1 := by field_simp
    linarith
  set K' := max K 0 with hK'
  have hK'0 : 0 ≤ K' := le_max_right _ _
  set Kp := K' * (d : ℝ) ^ 3 * Real.sqrt d with hKp
  have hKp0 : 0 ≤ Kp := by positivity
  set Lr := max (Lf * Mg + LF) (K' * (Mg + 1) / δ) with hLr
  have hLr0 : 0 ≤ Lr := le_trans (by positivity) (le_max_left _ _)
  set Y : ℕ → ℝ := fun k => ∫ ω, ‖η k ω‖ ^ 2 ∂P with hYdef
  have hY0 : ∀ k, 0 ≤ Y k := fun k => integral_nonneg fun ω => sq_nonneg _
  -- Threshold N₀ where c_k * d < δ and Lemma 4 holds
  have hevN0 : ∀ᶠ k in atTop,
      c k * d < δ ∧
      ∫ ω, (R.q k ω - M.qf (R.θ k ω)) ^ 2 ∂P ≤ A4₁ * (α k / γ k) ^ 2 + A4₂ * γ k := by
    have hsmall : ∀ᶠ k in atTop, c k * d < δ := by
      have := hA3a.2.1.mul_const (d : ℝ); rw [zero_mul] at this
      exact this.eventually (gt_mem_nhds hδ)
    filter_upwards [hsmall, hL4ev] with k h1 h2 using ⟨h1, h2⟩
  rw [Filter.eventually_atTop] at hevN0
  obtain ⟨N₀, hN₀⟩ := hevN0
  -- Explicit forcing constants
  set K1 : ℝ := (4 * b / ε + 4 / ε ^ 2) * Lg ^ 2 * Sr * (r / b) ^ 2 * (a / r) ^ 2
      + (4 * Lr ^ 2 / ε ^ 2) * A4₁ * (a / r) ^ 2 + 1 with hK1
  set K2 : ℝ := (4 * Kp ^ 2 / ε ^ 2) * (1 + Sr / d) * c₀ ^ 4 + 1 with hK2
  set K3 : ℝ := ((d : ℝ) + Sr) / ε * (b / c₀ ^ 2) + (4 * Lr ^ 2 / ε ^ 2) * A4₂ * r + 1 with hK3
  have hK1pos : 0 < K1 := by positivity
  have hK2pos : 0 < K2 := by positivity
  have hK3pos : 0 < K3 := by positivity
  have hrecY : ∀ k, N₀ ≤ k →
      Y (k + 1) ≤ (1 - (b * ε / 2) * ((k : ℝ) + 1) ^ (-eβ)) * Y k
        + (b * ε / 2) * ((k : ℝ) + 1) ^ (-eβ) *
          (K1 * ((k : ℝ) + 1) ^ (-(2 * (eα - eγ)))
            + K2 * ((k : ℝ) + 1) ^ (-(4 * τ))
            + K3 * ((k : ℝ) + 1) ^ (-(eβ - 2 * τ))) := by
    intro k hk
    obtain ⟨hsmall, hL4k⟩ := hN₀ k hk
    set H : Ω → E d := (goodEvent R k).indicator (η k) with hHdef
    have hHm : StronglyMeasurable[ℱ k] H := (hηm k).indicator (goodEvent_meas hrun k)
    have hHnorm : ∀ ω, ‖H ω‖ ≤ Bk k + Mg := by
      intro ω; rw [hHdef]
      by_cases hω : ω ∈ goodEvent R k
      · rw [Set.indicator_of_mem hω]; exact hηb k ω hω
      · rw [Set.indicator_of_notMem hω, norm_zero]; linarith [hBk0 k]
    have hHsupp : ∀ ω, ω ∉ goodEvent R k → H ω = 0 := fun ω hω =>
      Set.indicator_of_notMem hω _
    have hHae : ∀ᵐ ω ∂P, H ω = η k ω :=
      (goodEvent_ae P ℱ M Θ Proj I Pq α β γ c R hrun hA2 k).mono fun ω hω =>
        Set.indicator_of_mem hω _
    obtain ⟨hIntL, hIntR, hcond⟩ := cond_sp hd P ℱ M Θ Proj I Pq α β γ c R hM hrun hA2
      hβpos hcpos k δ (Qk k) (Bk k) (Bk k + Mg) (hQk0 k) (hBk0 k) (by linarith [hBk0 k])
      hsmall (hqb k) (hDb k) (hA1ae.mono fun ω hω => (hω k).1) H hHm hHnorm hHsupp
    -- Pointwise a.e. expansion of ‖η_{k+1}‖²
    have hβk0 := hβpos k
    have hP1 : ∀ᵐ ω ∂P, ‖η (k + 1) ω‖ ^ 2 ≤
        (1 + β k * ε / 2) * ‖η k ω‖ ^ 2 +
        (2 + 2 / (β k * ε)) * (Lg * α k) ^ 2 * ‖R.D k ω‖ ^ 2 +
        2 * β k ^ 2 * ‖spGrad c R k ω‖ ^ 2 +
        2 * β k * ⟪H ω, spGrad c R k ω⟫ := by
      filter_upwards [hHae] with ω hHω
      rw [hHω]
      set δG := gradient M.qf (R.θ k ω) - gradient M.qf (R.θ (k + 1) ω) with hδG
      have hη_succ : η (k + 1) ω = η k ω + δG + β k • spGrad c R k ω := by
        simp only [hηdef, hδG, D_succ_eq hrun k ω]; abel
      have hδG_bd : ‖δG‖ ≤ Lg * α k * ‖R.D k ω‖ := by
        have h1 := hgradLip _ (hθΘ k ω) _ (hθΘ (k + 1) ω)
        rw [norm_sub_rev (R.θ k ω) (R.θ (k + 1) ω)] at h1
        calc ‖δG‖ ≤ Lg * ‖R.θ (k + 1) ω - R.θ k ω‖ := h1
          _ ≤ Lg * (α k * ‖R.D k ω‖) := mul_le_mul_of_nonneg_left (hθstep k ω) hLg.le
          _ = Lg * α k * ‖R.D k ω‖ := by ring
      exact eta_onestep_pt (η k ω) (η (k + 1) ω) δG (spGrad c R k ω) ‖R.D k ω‖ (β k) ε Lg (α k)
        hβk0 hε hLg (hαpos k) (norm_nonneg _) hη_succ hδG_bd
    -- Pointwise a.e. bound on the drift integrand ⟪H, spAvg⟫
    have hP2 : ∀ᵐ ω ∂P, ⟪H ω, spAvg M c k (R.q k ω) (R.D k ω) (R.θ k ω)⟫ ≤
        -(ε / 2) * ‖η k ω‖ ^ 2
        + (Lr ^ 2 / ε) * (R.q k ω - M.qf (R.θ k ω)) ^ 2
        + (Kp ^ 2 / ε) * (1 + ‖R.D k ω‖ ^ 2 / d) * c k ^ 4 := by
      filter_upwards [hHae, hA1ae] with ω hHω hA1ω
      rw [hHω, spAvg_eq]
      obtain ⟨hC3, hball⟩ := hA1ω k
      have hpball : (R.q k ω, R.θ k ω) ∈ Metric.ball (R.q k ω, R.θ k ω) δ :=
        Metric.mem_ball_self hδ
      have hfε : ε ≤ M.dens (R.q k ω) (R.θ k ω) := hεle.trans (hball _ hpball).2.2
      set res : E d := M.dens (R.q k ω) (R.θ k ω) • gradient M.qf (R.θ k ω)
          + gradθ M (R.q k ω) (R.θ k ω) with hres
      have hres_bd : ‖res‖ ≤ Lr * |R.q k ω - M.qf (R.θ k ω)| :=
        grad_residual_bound M Θ hM Lf LF Mg δ K' ε0 hLf hLF hMg0 hδ hK'0 hε0 hB2lip hMg hqdiff
          (R.q k ω) (R.θ k ω) (hθΘ k ω) hC3
          (fun p hp => ⟨(hball p hp).1.trans (le_max_left _ _), (hball p hp).2.2⟩)
      have hbias_bd : ‖bias M c k (R.q k ω) (R.D k ω) (R.θ k ω)‖ ≤
          mfac (R.D k ω) * Kp * c k ^ 2 :=
        bias_bound hd M hM.hasDens c k _ _ _ δ K' (hcpos k) hsmall hC3
          (fun x hx => (hball x hx).2.1.trans (le_max_left _ _))
      have hbias_sq : ‖bias M c k (R.q k ω) (R.D k ω) (R.θ k ω)‖ ^ 2
          ≤ Kp ^ 2 * (1 + ‖R.D k ω‖ ^ 2 / d) * c k ^ 4 := by
        have h1 := pow_le_pow_left₀ (norm_nonneg _) hbias_bd 2
        have h2 := mfac_sq_le hd (R.D k ω)
        have h3 : (mfac (R.D k ω) * Kp * c k ^ 2) ^ 2 = Kp ^ 2 * mfac (R.D k ω) ^ 2 * c k ^ 4 := by
          ring
        rw [h3] at h1
        exact h1.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h2 (sq_nonneg _)) (by positivity))
      have hrewrite : -M.dens (R.q k ω) (R.θ k ω) • R.D k ω - gradθ M (R.q k ω) (R.θ k ω)
            + bias M c k (R.q k ω) (R.D k ω) (R.θ k ω)
          = -M.dens (R.q k ω) (R.θ k ω) • η k ω - res
            + bias M c k (R.q k ω) (R.D k ω) (R.θ k ω) := by
        simp only [hηdef, hres, neg_smul, smul_sub]; abel
      rw [hrewrite]
      exact drift_onestep_pt (η k ω) res (bias M c k (R.q k ω) (R.D k ω) (R.θ k ω))
        (M.dens (R.q k ω) (R.θ k ω)) (R.q k ω - M.qf (R.θ k ω))
        (1 + ‖R.D k ω‖ ^ 2 / d) ε Lr Kp (c k) hε hfε hLr0 hKp0 hres_bd hbias_sq
    -- Integrate hP1 and hP2 and combine
    have hi1 := (hη2int k).const_mul (1 + β k * ε / 2)
    have hi2 := (hDmom k).1.const_mul ((2 + 2 / (β k * ε)) * (Lg * α k) ^ 2)
    have hi3 := (hgint k).const_mul (2 * β k ^ 2)
    have hi4 := hIntL.const_mul (2 * β k)
    have hI1 := integral_mono_ae (hη2int (k + 1)) (((hi1.add hi2).add hi3).add hi4) hP1
    rw [integral_add' ((hi1.add hi2).add hi3) hi4, integral_add' (hi1.add hi2) hi3,
      integral_add' hi1 hi2] at hI1
    rw [integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul, hcond] at hI1
    have hj1 := (hη2int k).const_mul (-(ε / 2))
    have hj2 := (hζ2int k).const_mul (Lr ^ 2 / ε)
    have hj3 : Integrable (fun ω => (Kp ^ 2 / ε) * (1 + ‖R.D k ω‖ ^ 2 / d) * c k ^ 4) P := by
      have : (fun ω => (Kp ^ 2 / ε) * (1 + ‖R.D k ω‖ ^ 2 / d) * c k ^ 4)
          = fun ω => ((Kp ^ 2 / ε) * c k ^ 4) * (1 + ‖R.D k ω‖ ^ 2 / d) := by funext ω; ring
      rw [this]
      exact ((integrable_const (1 : ℝ)).add ((hDmom k).1.div_const (d : ℝ))).const_mul _
    have hI2 := integral_mono_ae hIntR ((hj1.add hj2).add hj3) hP2
    rw [integral_add' (hj1.add hj2) hj3, integral_add' hj1 hj2] at hI2
    rw [integral_const_mul, integral_const_mul] at hI2
    have hI3 : ∫ ω, (Kp ^ 2 / ε) * (1 + ‖R.D k ω‖ ^ 2 / d) * c k ^ 4 ∂P
        ≤ (Kp ^ 2 / ε) * (1 + Sr / d) * c k ^ 4 := by
      have e : (fun ω => (Kp ^ 2 / ε) * (1 + ‖R.D k ω‖ ^ 2 / d) * c k ^ 4)
          = fun ω => ((Kp ^ 2 / ε) * c k ^ 4) * (1 + ‖R.D k ω‖ ^ 2 / d) := by funext ω; ring
      rw [e, integral_const_mul, integral_add (integrable_const _) ((hDmom k).1.div_const _),
        integral_const, probReal_univ, smul_eq_mul, one_mul, integral_div]
      have hle : (∫ ω, ‖R.D k ω‖ ^ 2 ∂P) / (d : ℝ) ≤ Sr / d :=
        div_le_div_of_nonneg_right (hDmom k).2.1 hd0.le
      calc (Kp ^ 2 / ε) * c k ^ 4 * (1 + (∫ ω, ‖R.D k ω‖ ^ 2 ∂P) / (d : ℝ))
          ≤ (Kp ^ 2 / ε) * c k ^ 4 * (1 + Sr / d) :=
            mul_le_mul_of_nonneg_left (by linarith only [hle]) (by positivity)
        _ = (Kp ^ 2 / ε) * (1 + Sr / d) * c k ^ 4 := by ring
    have hnoise_pt : ∀ᵐ ω ∂P, ‖spGrad c R k ω‖ ^ 2 ≤ (d + ‖R.D k ω‖ ^ 2) / (4 * c k ^ 2) := by
      filter_upwards [goodEvent_ae P ℱ M Θ Proj I Pq α β γ c R hrun hA2 (k + 1)] with ω hω
      obtain ⟨b, hb⟩ := goodEvent_succ_mem_Delta R k hω
      exact norm_spGrad_sq_le hd c R k ω (hcpos k) b hb
    have hnoise : ∫ ω, ‖spGrad c R k ω‖ ^ 2 ∂P ≤ ((d : ℝ) + Sr) / (4 * c k ^ 2) := by
      have hi : Integrable (fun ω => (d + ‖R.D k ω‖ ^ 2) / (4 * c k ^ 2)) P :=
        ((integrable_const (d : ℝ)).add (hDmom k).1).div_const _
      have hm := integral_mono_ae (hgint k) hi hnoise_pt
      rw [integral_div, integral_add (integrable_const _) (hDmom k).1, integral_const,
        probReal_univ, smul_eq_mul, one_mul] at hm
      exact hm.trans (div_le_div_of_nonneg_right (by linarith only [(hDmom k).2.1]) (by positivity))
    have hstep1 : Y (k + 1) ≤ (1 - β k * ε / 2) * Y k
        + (2 + 2 / (β k * ε)) * (Lg * α k) ^ 2 * Sr
        + 2 * β k ^ 2 * (((d : ℝ) + Sr) / (4 * c k ^ 2))
        + 2 * β k * (Lr ^ 2 / ε) * (A4₁ * (α k / γ k) ^ 2 + A4₂ * γ k)
        + 2 * β k * ((Kp ^ 2 / ε) * (1 + Sr / d) * c k ^ 4) := by
      have cD : 0 ≤ (2 + 2 / (β k * ε)) * (Lg * α k) ^ 2 := by positivity
      have cN : 0 ≤ 2 * β k ^ 2 := by positivity
      have cβ : 0 ≤ 2 * β k := by positivity
      have cQ : 0 ≤ 2 * β k * (Lr ^ 2 / ε) := by positivity
      change Y (k + 1) ≤ (1 + β k * ε / 2) * Y k + _ + _ + _ at hI1
      change ∫ ω, ⟪H ω, spAvg M c k (R.q k ω) (R.D k ω) (R.θ k ω)⟫ ∂P ≤ -(ε / 2) * Y k + _ + _ at hI2
      have m1 := mul_le_mul_of_nonneg_left (hDmom k).2.1 cD
      have m2 := mul_le_mul_of_nonneg_left hnoise cN
      have m3 := mul_le_mul_of_nonneg_left hI2 cβ
      have m4 := mul_le_mul_of_nonneg_left hL4k cQ
      have m5 := mul_le_mul_of_nonneg_left hI3 cβ
      linarith only [hI1, m1, m2, m3, m4, m5]
    have hbe_eq : β k * ε / 2 = (b * ε / 2) * ((k : ℝ) + 1) ^ (-eβ) := by
      rw [hβ_eq k]; ring
    rw [← hbe_eq]
    exact forcing_combine (Y k) (Y (k + 1)) (α k) (β k) (γ k) (c k) a b r c₀ ε Lg Sr Lr Kp d
      A4₁ A4₂ (((k : ℝ) + 1) ^ (-(2 * (eα - eγ)))) (((k : ℝ) + 1) ^ (-(4 * τ)))
      (((k : ℝ) + 1) ^ (-(eβ - 2 * τ)))
      (hαpos k) hβk0 (hγpos k) (hcpos k) ha hb hr hc0 hε hLg hSr0 hLr0 hKp0 hd0 hA4₁ hA4₂
      (Real.rpow_nonneg (hX k).le _) (Real.rpow_nonneg (hX k).le _) (Real.rpow_nonneg (hX k).le _)
      (hβle k) (hαβ_le k) (hγ_le_R3 k) (hR1 k) (hR2 k) (hR3 k) hstep1
  -- Step 5: Unroll with det_rate_3 (which calls Lemma 3 three times)
  obtain ⟨A1, A2, A3, hA1', hA2', hA3', hevY⟩ := det_rate_3 Y hY0 (b * ε / 2) eβ
    (2 * (eα - eγ)) (4 * τ) (eβ - 2 * τ) (by positivity) hbε heβ0 heβ1
    (by linarith) (by positivity) hs30 hs31 K1 K2 K3 hK1pos hK2pos hK3pos N₀ hrecY
  -- Step 6: Convert back to (C * (α_k/γ_k + c_k² + √β_k/c_k))² and lintegral
  set C := Real.sqrt (A1 * (r / a) ^ 2 + A2 / c₀ ^ 4 + A3 * (c₀ ^ 2 / b)) with hCdef
  refine ⟨C, Real.sqrt_nonneg _, ?_⟩
  filter_upwards [hevY] with k hk
  have h1 : ((k : ℝ) + 1) ^ (-(2 * (eα - eγ))) = (r / a) ^ 2 * (α k / γ k) ^ 2 := by
    rw [hR1 k]; field_simp
  have h2 : ((k : ℝ) + 1) ^ (-(4 * τ)) = (c k ^ 2) ^ 2 / c₀ ^ 4 := by
    rw [show (c k ^ 2) ^ 2 = c k ^ 4 by ring, hR2 k]; field_simp
  have h3 : ((k : ℝ) + 1) ^ (-(eβ - 2 * τ)) = (c₀ ^ 2 / b) * (Real.sqrt (β k) / c k) ^ 2 := by
    rw [div_pow, Real.sq_sqrt (hβpos k).le, hR3 k]; field_simp
  rw [h1, h2, h3] at hk
  have hYle := final_sq_bound (Y k) A1 A2 A3 r a c₀ b (α k / γ k) (c k ^ 2)
    (Real.sqrt (β k) / c k) hA1' hA2' hA3' hr ha hc0 hb
    (div_nonneg (hαpos k).le (hγpos k).le) (sq_nonneg _)
    (div_nonneg (Real.sqrt_nonneg _) (hcpos k).le) hk
  have hlin : ∫⁻ ω, ‖R.D k ω - gradient M.qf (R.θ k ω)‖ₑ ^ 2 ∂P = ENNReal.ofReal (Y k) := by
    have heq : ∫⁻ ω, ‖R.D k ω - gradient M.qf (R.θ k ω)‖ₑ ^ 2 ∂P
        = ∫⁻ ω, ENNReal.ofReal (‖η k ω‖ ^ 2) ∂P := by
      congr 1; funext ω; rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [heq, ← ofReal_integral_eq_lintegral_ofReal (hη2int k)
      (Eventually.of_forall fun ω => by simp only [Pi.zero_apply]; positivity)]
  rw [hlin]
  exact ENNReal.ofReal_le_ofReal hYle
