-- Prove2me | solution 1 for VolunteerEngage.Thresholds.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T23:37:01.724322+00:00
-- url     : https://prove2.me/submissions/f1e4abe7-1499-493f-bb5e-70b0effa7f76

import Mathlib
import Definitions.Def_VolunteerEngage_Thresholds_Setting

set_option autoImplicit false
open VolunteerEngage.Thresholds

lemma vet_theta_succ (M : Model) (l : ℕ) : M.θ (l + 1) = M.θ l + M.η (l + 1) := by
  simp [Model.θ, Finset.sum_Icc_succ_top]
  ring

lemma vet_theta_step (M : Model) (hM : M.Standing) (l : ℕ) (hl : l + 1 ≤ M.L) :
    M.θ l ≤ M.θ (l + 1) := by
  rw [vet_theta_succ]
  have := hM.2.2.1 (l + 1) (Finset.mem_Icc.mpr ⟨by omega, hl⟩)
  linarith

lemma vet_theta_mono (M : Model) (hM : M.Standing) (k l : ℕ) (hkl : k ≤ l) (hl : l ≤ M.L) :
    M.θ k ≤ M.θ l := by
  induction l, hkl using Nat.le_induction with
  | base => exact le_refl _
  | succ n hn ih => exact (ih (by omega)).trans (vet_theta_step M hM n hl)

lemma vet_c_mono (M : Model) (hM : M.Standing) (k l : ℕ) (hk : 1 ≤ k) (hkl : k ≤ l)
    (hl : l ≤ M.L) : M.c k ≤ M.c l := by
  induction l, hkl using Nat.le_induction with
  | base => exact le_refl _
  | succ n hn ih =>
    have := hM.2.2.2.2.1 n (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
    exact (ih (by omega)).trans this.le

/-- one summand of the cost -/
noncomputable def vetA (M : Model) (l : ℕ) (x : ℝ) : ℝ :=
  min (M.θ l) (max (M.θ (l - 1)) x) - M.θ (l - 1)

lemma vet_tele (M : Model) (hM : M.Standing) (x : ℝ) :
    ∀ n, n ≤ M.L → ∑ l ∈ Finset.Icc 1 n, vetA M l x = min (M.θ n) (max (M.θ 0) x) - M.θ 0 := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    rw [Finset.sum_Icc_succ_top (by omega), ih (by omega)]
    unfold vetA
    have h1 := vet_theta_step M hM n hn
    have h2 := vet_theta_mono M hM 0 n (by omega) (by omega)
    simp only [Nat.add_sub_cancel]
    simp only [min_def, max_def]
    split_ifs <;> linarith

lemma vet_cost_eq (M : Model) (x : ℝ) :
    cost M x = ∑ l ∈ Finset.Icc 1 M.L, M.c l * vetA M l x := rfl

lemma vet_g_eq (M : Model) (hM : M.Standing) (y x : ℝ) (hx : x ∈ Set.Icc M.θ0 (M.θ M.L)) :
    y * x - cost M x = y * M.θ0 + ∑ l ∈ Finset.Icc 1 M.L, (y - M.c l) * vetA M l x := by
  have ht := vet_tele M hM x M.L le_rfl
  have h0 : M.θ 0 = M.θ0 := by simp [Model.θ]
  rw [h0] at ht
  have hm : min (M.θ M.L) (max M.θ0 x) = x := by
    rw [max_eq_right hx.1, min_eq_right hx.2]
  rw [hm] at ht
  have : ∑ l ∈ Finset.Icc 1 M.L, (y - M.c l) * vetA M l x
      = y * (x - M.θ0) - cost M x := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ht, vet_cost_eq]
  rw [this]; ring

lemma vet_E9_core (M : Model) (hM : M.Standing) (y : ℝ) (k : ℕ) (hk : k ≤ M.L)
    (h1 : ∀ l ∈ Finset.Icc 1 M.L, l ≤ k → M.c l ≤ y)
    (h2 : ∀ l ∈ Finset.Icc 1 M.L, k < l → y ≤ M.c l) :
    phi M y = y * M.θ k - cost M (M.θ k) := by
  have h0 : M.θ 0 = M.θ0 := by simp [Model.θ]
  have hkm : M.θ k ∈ Set.Icc M.θ0 (M.θ M.L) :=
    ⟨h0 ▸ vet_theta_mono M hM 0 k (by omega) hk, vet_theta_mono M hM k M.L hk le_rfl⟩
  unfold phi
  apply IsGreatest.csSup_eq
  refine ⟨⟨M.θ k, hkm, rfl⟩, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  simp only
  rw [vet_g_eq M hM y x hx, vet_g_eq M hM y _ hkm]
  apply add_le_add_right (Finset.sum_le_sum ?_)
  intro l hl
  obtain ⟨hl1, hlL⟩ := Finset.mem_Icc.mp hl
  obtain ⟨j, rfl⟩ : ∃ j, l = j + 1 := ⟨l - 1, by omega⟩
  have hjθ := vet_theta_step M hM j hlL
  unfold vetA
  simp only [Nat.add_sub_cancel]
  rcases le_or_gt (j + 1) k with hlk | hlk
  · have hy := h1 (j + 1) hl hlk
    have hθk : M.θ (j + 1) ≤ M.θ k := vet_theta_mono M hM _ _ hlk hk
    have : min (M.θ (j + 1)) (max (M.θ j) (M.θ k)) = M.θ (j + 1) := by
      rw [max_eq_right (hjθ.trans hθk), min_eq_left hθk]
    rw [this]
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    have : min (M.θ (j + 1)) (max (M.θ j) x) ≤ M.θ (j + 1) := min_le_left _ _
    linarith
  · have hy := h2 (j + 1) hl hlk
    have hθk : M.θ k ≤ M.θ j := vet_theta_mono M hM _ _ (by omega) (by omega)
    have : min (M.θ (j + 1)) (max (M.θ j) (M.θ k)) = M.θ j := by
      rw [max_eq_left hθk, min_eq_right hjθ]
    rw [this]
    have hnn : 0 ≤ min (M.θ (j + 1)) (max (M.θ j) x) - M.θ j := by
      have : M.θ j ≤ min (M.θ (j + 1)) (max (M.θ j) x) :=
        le_min hjθ (le_max_left _ _)
      linarith
    have : (y - M.c (j + 1)) * (min (M.θ (j + 1)) (max (M.θ j) x) - M.θ j) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hnn
    simp only [sub_self, mul_zero]
    exact this

lemma vet_cost_theta0 (M : Model) (hM : M.Standing) : cost M (M.θ 0) = 0 := by
  unfold cost
  apply Finset.sum_eq_zero
  intro l hl
  obtain ⟨hl1, hlL⟩ := Finset.mem_Icc.mp hl
  obtain ⟨j, rfl⟩ : ∃ j, l = j + 1 := ⟨l - 1, by omega⟩
  have h1 := vet_theta_step M hM j hlL
  have h2 := vet_theta_mono M hM 0 j (by omega) (by omega)
  simp only [Nat.add_sub_cancel]
  rw [max_eq_left h2, min_eq_right h1]
  simp

theorem vet_E9 (M : Model) (hM : M.Standing) :
    (∀ y : ℝ, y ≤ M.c 1 → phi M y = M.θ 0 * y) ∧
    (∀ m ∈ Finset.Icc 2 M.L, ∀ y : ℝ, M.c (m - 1) < y → y ≤ M.c m →
      phi M y = M.θ (m - 1) * y - cost M (M.θ (m - 1))) ∧
    (∀ y : ℝ, M.c M.L < y → phi M y = M.θ M.L * y - cost M (M.θ M.L)) := by
  have hL : 1 ≤ M.L := hM.1
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    have := vet_E9_core M hM y 0 (by omega)
      (fun l hl h => by have := (Finset.mem_Icc.mp hl).1; omega)
      (fun l hl _ => hy.trans (vet_c_mono M hM 1 l le_rfl (Finset.mem_Icc.mp hl).1 (Finset.mem_Icc.mp hl).2))
    rw [this, vet_cost_theta0 M hM]; ring
  · intro m hm y hy1 hy2
    obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
    have := vet_E9_core M hM y (m - 1) (by omega)
      (fun l hl h => (vet_c_mono M hM l (m - 1) (Finset.mem_Icc.mp hl).1 h (by omega)).trans hy1.le)
      (fun l hl h => hy2.trans (vet_c_mono M hM m l (by omega) (by omega) (Finset.mem_Icc.mp hl).2))
    rw [this]; ring
  · intro y hy
    have := vet_E9_core M hM y M.L le_rfl
      (fun l hl h => (vet_c_mono M hM l M.L (Finset.mem_Icc.mp hl).1 (Finset.mem_Icc.mp hl).2 le_rfl).trans hy.le)
      (fun l hl h => by have := (Finset.mem_Icc.mp hl).2; omega)
    rw [this]; ring
open MeasureTheory ProbabilityTheory

lemma vet_Phi_sub_of_le (a b : ℝ) (hab : a ≤ b) :
    Cohen2019.Robust.Phi b - Cohen2019.Robust.Phi a =
      ∫ w in a..b, gaussianPDFReal 0 1 w := by
  have h := (cdf (gaussianReal 0 1)).measure_Ioc a b
  rw [measure_cdf] at h
  rw [gaussianReal_apply_eq_integral 0 one_ne_zero] at h
  have h1 : 0 ≤ ∫ w in Set.Ioc a b, gaussianPDFReal 0 1 w :=
    setIntegral_nonneg measurableSet_Ioc (fun w _ => gaussianPDFReal_nonneg _ _ _)
  have h2 : 0 ≤ Cohen2019.Robust.Phi b - Cohen2019.Robust.Phi a :=
    sub_nonneg.mpr ((monotone_cdf _) hab)
  have h3 := (ENNReal.ofReal_eq_ofReal_iff h1 h2).mp h
  rw [intervalIntegral.integral_of_le hab]
  unfold Cohen2019.Robust.Phi
  exact h3.symm

lemma vet_Phi_sub (a b : ℝ) :
    Cohen2019.Robust.Phi b - Cohen2019.Robust.Phi a =
      ∫ w in a..b, gaussianPDFReal 0 1 w := by
  rcases le_total a b with h | h
  · exact vet_Phi_sub_of_le a b h
  · rw [intervalIntegral.integral_symm, ← vet_Phi_sub_of_le b a h]; ring

lemma vet_gauss_int (a b : ℝ) :
    ∫ w in a..b, Real.exp (-w ^ 2 / 2) =
      Real.sqrt (2 * Real.pi) * (Cohen2019.Robust.Phi b - Cohen2019.Robust.Phi a) := by
  rw [vet_Phi_sub]
  have : ∀ w : ℝ, gaussianPDFReal 0 1 w = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-w ^ 2 / 2) := by
    intro w
    simp [gaussianPDFReal]
  simp_rw [this]
  rw [intervalIntegral.integral_const_mul]
  have : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  field_simp


lemma vet_Phi_deriv (t : ℝ) :
    HasDerivAt Cohen2019.Robust.Phi ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-t ^ 2 / 2)) t := by
  have hpdf : ∀ w : ℝ, gaussianPDFReal 0 1 w = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-w ^ 2 / 2) := by
    intro w; simp [gaussianPDFReal]
  have hcont : Continuous (fun w : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-w ^ 2 / 2)) := by
    fun_prop
  have heq : Cohen2019.Robust.Phi = fun x => Cohen2019.Robust.Phi 0 +
      ∫ w in (0:ℝ)..x, (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-w ^ 2 / 2) := by
    funext x
    have := vet_Phi_sub 0 x
    simp_rw [hpdf] at this
    linarith
  rw [heq]
  have := intervalIntegral.integral_hasDerivAt_right (a := 0) (b := t)
    (hcont.intervalIntegrable 0 t) (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt
  exact this.const_add _

lemma vet_const_alg (κ σ b : ℝ) (hκ : 0 < κ) (hσ : 0 < σ) :
    2 * b * Real.sqrt Real.pi / (σ * Real.sqrt κ) *
      ((Real.sqrt (2 * Real.pi))⁻¹ * (κ / (σ * Real.sqrt (κ / 2)))) = 2 * b / σ ^ 2 := by
  obtain ⟨s, hs, rfl⟩ : ∃ s : ℝ, 0 < s ∧ κ = s ^ 2 :=
    ⟨Real.sqrt κ, Real.sqrt_pos.2 hκ, (Real.sq_sqrt hκ.le).symm⟩
  rw [Real.sqrt_sq hs.le, Real.sqrt_div (by positivity) 2, Real.sqrt_sq hs.le,
    Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  have hq : 0 < Real.sqrt 2 := by positivity
  have hr : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  field_simp

lemma vet_z_alg (κ σ θ x : ℝ) (hκ : 0 < κ) (hσ : 0 < σ) :
    ((κ * x - θ) / (σ * Real.sqrt (κ / 2))) ^ 2 / 2 = (κ * x - θ) ^ 2 / (κ * σ ^ 2) := by
  have h : Real.sqrt (κ / 2) ^ 2 = κ / 2 := Real.sq_sqrt (by positivity)
  have : 0 < Real.sqrt (κ / 2) := Real.sqrt_pos.2 (by positivity)
  rw [div_pow, mul_pow, h]
  field_simp

/-- the explicit function `u_l` with abstract parameters -/
noncomputable def vetU (p ch θ κ σ b T x : ℝ) : ℝ :=
  p - ch * Real.exp ((-2 * θ * (x - T) + κ * (x ^ 2 - T ^ 2)) / σ ^ 2)
    + 2 * b * Real.sqrt Real.pi / (σ * Real.sqrt κ)
      * Real.exp ((κ * x - θ) ^ 2 / (κ * σ ^ 2))
      * (Cohen2019.Robust.Phi ((κ * x - θ) / (σ * Real.sqrt (κ / 2)))
        - Cohen2019.Robust.Phi ((κ * T - θ) / (σ * Real.sqrt (κ / 2))))

lemma vetU_deriv (p ch θ κ σ b T t : ℝ) (hκ : 0 < κ) (hσ : 0 < σ) :
    HasDerivAt (vetU p ch θ κ σ b T)
      (2 / σ ^ 2 * (b - (κ * t - θ) * (p - vetU p ch θ κ σ b T t))) t := by
  have hs2 : 0 < Real.sqrt (κ / 2) := Real.sqrt_pos.2 (by positivity)
  have hd1 : HasDerivAt (fun x : ℝ => (-2 * θ * (x - T) + κ * (x ^ 2 - T ^ 2)) / σ ^ 2)
      ((-2 * θ + κ * (2 * t)) / σ ^ 2) t := by
    have := (((hasDerivAt_id t).sub_const T).const_mul (-2 * θ)).add
      ((((hasDerivAt_pow 2 t)).sub_const (T ^ 2)).const_mul κ)
    have := this.div_const (σ ^ 2)
    exact this.congr_deriv (by simp)
  have hd2 : HasDerivAt (fun x : ℝ => (κ * x - θ) ^ 2 / (κ * σ ^ 2))
      (2 * (κ * t - θ) * κ / (κ * σ ^ 2)) t := by
    have h0 : HasDerivAt (fun x : ℝ => κ * x - θ) κ t :=
      ((hasDerivAt_id t).const_mul κ).sub_const θ |>.congr_deriv (by simp)
    have := (h0.pow 2).div_const (κ * σ ^ 2)
    exact this.congr_deriv (by simp)
  have hz : HasDerivAt (fun x : ℝ => (κ * x - θ) / (σ * Real.sqrt (κ / 2)))
      (κ / (σ * Real.sqrt (κ / 2))) t := by
    have h0 : HasDerivAt (fun x : ℝ => κ * x - θ) κ t :=
      ((hasDerivAt_id t).const_mul κ).sub_const θ |>.congr_deriv (by simp)
    exact h0.div_const _
  have hPhi := (vet_Phi_deriv ((κ * t - θ) / (σ * Real.sqrt (κ / 2)))).comp t hz
  have hE1 := hd1.exp
  have hE2 := hd2.exp
  have hfull := ((((hasDerivAt_const t p).sub (hE1.const_mul ch)).add
    ((hE2.const_mul (2 * b * Real.sqrt Real.pi / (σ * Real.sqrt κ))).mul
      (hPhi.sub_const (Cohen2019.Robust.Phi ((κ * T - θ) / (σ * Real.sqrt (κ / 2))))))))
  refine hfull.congr_deriv ?_
  have hz2 := vet_z_alg κ σ θ t hκ hσ
  have hexp : Real.exp ((κ * t - θ) ^ 2 / (κ * σ ^ 2)) *
      Real.exp (-((κ * t - θ) / (σ * Real.sqrt (κ / 2))) ^ 2 / 2) = 1 := by
    rw [← Real.exp_add]
    have : (κ * t - θ) ^ 2 / (κ * σ ^ 2) + -((κ * t - θ) / (σ * Real.sqrt (κ / 2))) ^ 2 / 2 = 0 := by
      linarith
    rw [this]; simp
  have hc := vet_const_alg κ σ b hκ hσ
  have h3 : 2 * (κ * t - θ) * κ / (κ * σ ^ 2) = 2 * (κ * t - θ) / σ ^ 2 := by
    field_simp
  rw [h3]
  unfold vetU
  simp only [Function.comp]
  linear_combination
    (2 * b * Real.sqrt Real.pi / (σ * Real.sqrt κ) * ((Real.sqrt (2 * Real.pi))⁻¹ * (κ / (σ * Real.sqrt (κ / 2))))) * hexp + hc

theorem solution (M : Model) (hM : M.Standing) (β : ℝ) (v v' : ℝ → ℝ)
    (hv : IsBellmanSol M β v v') (τ : ℕ → ℝ) (hτL : τ (M.L + 1) = 0)
    (hτ : ∀ l ∈ Finset.Icc 1 M.L, 0 ≤ τ l ∧ v (τ l) = M.p - chat M l) :
    ∀ l ∈ Finset.Icc 1 (M.L + 1), ∀ x : ℝ, τ l ≤ x → (l = 1 ∨ x < τ (l - 1)) →
      v x = u M β τ l x := by
  have hκ : 0 < M.κ := hM.2.2.2.2.2.2.2.1
  have hσ : 0 < M.σ := hM.2.2.2.2.2.2.2.2
  have hL1 : 1 ≤ M.L := hM.1
  obtain ⟨hβ, hcont, hder, hode, hv0, hmono, htend⟩ := hv
  intro l hl x hTx hx
  obtain ⟨hl1, hlL⟩ := Finset.mem_Icc.mp hl
  have hT0 : 0 ≤ τ l := by
    rcases Nat.lt_or_ge M.L l with h | h
    · have : l = M.L + 1 := by omega
      rw [this, hτL]
    · exact (hτ l (Finset.mem_Icc.mpr ⟨hl1, h⟩)).1
  have hvT : v (τ l) = M.p - chat M l := by
    rcases Nat.lt_or_ge M.L l with h | h
    · have : l = M.L + 1 := by omega
      subst this
      rw [hτL, hv0]; simp [chat]
    · exact (hτ l (Finset.mem_Icc.mpr ⟨hl1, h⟩)).2
  have hvm : ∀ a b : ℝ, 0 ≤ a → a < b → v a < v b := fun a b ha hab =>
    hmono ha (le_trans ha hab.le) hab
  have hvm' : ∀ a b : ℝ, 0 ≤ a → a ≤ b → v a ≤ v b := fun a b ha hab =>
    hmono.monotoneOn ha (le_trans ha hab) hab
  -- phi on the region
  have hE9 := vet_E9 M hM
  have hphi : ∀ t : ℝ, τ l ≤ t → t ≤ x →
      phi M (M.p - v t) = M.θ (l - 1) * (M.p - v t) - cost M (M.θ (l - 1)) := by
    intro t ht1 ht2
    have ht0 : 0 ≤ t := le_trans hT0 ht1
    have hlow : M.p - v t ≤ chat M l := by
      have := hvm' _ _ hT0 ht1
      linarith
    -- upper region information (for l ≥ 2)
    have hup : l ≠ 1 → v t < v (τ (l - 1)) := by
      intro hne
      have : t < τ (l - 1) := by
        rcases hx with h | h
        · exact absurd h hne
        · exact lt_of_le_of_lt ht2 h
      have hτ0 : 0 ≤ τ (l - 1) := (hτ (l - 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)).1
      exact hvm _ _ ht0 this
    by_cases hl1' : l = 1
    · subst hl1'
      have hc1 : chat M 1 = M.c 1 := by
        unfold chat; rw [if_neg]; omega
      rw [hc1] at hlow
      have := hE9.1 (M.p - v t) hlow
      simp only [Nat.sub_self]
      rw [this, vet_cost_theta0 M hM]; ring
    · by_cases hlL' : l = M.L + 1
      · subst hlL'
        have hτL' := hτ M.L (Finset.mem_Icc.mpr ⟨hL1, le_rfl⟩)
        have h1 := hup hl1'
        simp only [Nat.add_sub_cancel] at h1
        rw [hτL'.2] at h1
        have hcL : chat M M.L = M.c M.L := by
          unfold chat; rw [if_neg]; omega
        rw [hcL] at h1
        have := hE9.2.2 (M.p - v t) (by linarith)
        simp only [Nat.add_sub_cancel]
        rw [this]
      · have hlL2 : l ≤ M.L := by omega
        have hcl : chat M l = M.c l := by
          unfold chat; rw [if_neg hlL']
        have h1 := hup hl1'
        rw [(hτ (l - 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)).2] at h1
        have hcl1 : chat M (l - 1) = M.c (l - 1) := by
          unfold chat; rw [if_neg]; omega
        rw [hcl1] at h1
        rw [hcl] at hlow
        have := hE9.2.1 l (Finset.mem_Icc.mpr ⟨by omega, hlL2⟩) (M.p - v t)
          (by linarith) hlow
        rw [this]
  -- the ODE for v on the region
  have hvode : ∀ t : ℝ, τ l ≤ t → t ≤ x →
      v' t = 2 / M.σ ^ 2 * (β - cost M (M.θ (l - 1))
        - (M.κ * t - M.θ (l - 1)) * (M.p - v t)) := by
    intro t ht1 ht2
    have ht0 : 0 ≤ t := le_trans hT0 ht1
    have h1 := hode t ht0
    rw [hphi t ht1 ht2] at h1
    have : M.σ ^ 2 ≠ 0 := by positivity
    field_simp
    linarith
  -- u = vetU
  have hU : ∀ y : ℝ, u M β τ l y = vetU M.p (chat M l) (M.θ (l - 1)) M.κ M.σ
      (β - cost M (M.θ (l - 1))) (τ l) y := fun y => rfl
  set θ := M.θ (l - 1) with hθ
  set b := β - cost M θ with hb
  set U := vetU M.p (chat M l) θ M.κ M.σ b (τ l) with hUdef
  have hUd : ∀ t : ℝ, HasDerivAt U (2 / M.σ ^ 2 * (b - (M.κ * t - θ) * (M.p - U t))) t :=
    fun t => vetU_deriv _ _ _ _ _ _ _ t hκ hσ
  have hUT : U (τ l) = M.p - chat M l := by
    simp [hUdef, vetU]
  -- the Gronwall-type function
  let E : ℝ → ℝ := fun t => Real.exp (-(M.κ * t ^ 2 - 2 * θ * t) / M.σ ^ 2)
  have hEd : ∀ t : ℝ, HasDerivAt E (E t * (-(2 * M.κ * t - 2 * θ) / M.σ ^ 2)) t := by
    intro t
    have h0 : HasDerivAt (fun t : ℝ => -(M.κ * t ^ 2 - 2 * θ * t) / M.σ ^ 2)
        (-(2 * M.κ * t - 2 * θ) / M.σ ^ 2) t := by
      have := ((((hasDerivAt_pow 2 t).const_mul M.κ).sub
        ((hasDerivAt_id t).const_mul (2 * θ))).neg).div_const (M.σ ^ 2)
      refine this.congr_deriv ?_
      simp
      ring
    exact h0.exp
  have hvc : ContinuousOn v (Set.Ici 0) := fun t ht => (hder t ht).continuousWithinAt
  have hUc : Continuous U := continuous_iff_continuousAt.2 fun t => (hUd t).continuousAt
  have hEc : Continuous E := continuous_iff_continuousAt.2 fun t => (hEd t).continuousAt
  have hw := constant_of_has_deriv_right_zero
    (f := fun t => (v t - U t) * E t) (a := τ l) (b := x)
    (((hvc.mono (fun t ht => le_trans hT0 ht.1)).sub hUc.continuousOn).mul hEc.continuousOn)
    (by
      intro t ht
      have ht0 : 0 ≤ t := le_trans hT0 ht.1
      have hv1 : HasDerivWithinAt v (v' t) (Set.Ici t) t :=
        (hder t ht0).mono (Set.Ici_subset_Ici.2 ht0)
      have h2 := ((hv1.sub (hUd t).hasDerivWithinAt).mul (hEd t).hasDerivWithinAt)
      refine h2.congr_deriv ?_
      rw [hvode t ht.1 ht.2.le]
      simp only [Pi.sub_apply]
      ring) x ⟨hTx, le_rfl⟩
  simp only [hvT, hUT, sub_self, zero_mul] at hw
  have hEpos : 0 < E x := Real.exp_pos _
  have : v x - U x = 0 := by
    rcases mul_eq_zero.mp hw with h | h
    · exact h
    · exact absurd h hEpos.ne'
  rw [hU x]
  linarith
