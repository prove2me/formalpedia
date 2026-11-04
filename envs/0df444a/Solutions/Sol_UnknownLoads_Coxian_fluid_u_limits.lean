-- Prove2me | solution 1 for UnknownLoads.Coxian.fluid_u_limits
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T20:54:54.070693+00:00
-- url     : https://prove2.me/submissions/ad58c372-6fc8-4abe-8e99-0cd7509aec1b

import Mathlib
import Definitions.Def_UnknownLoads_Coxian_Model
open MeasureTheory Filter Topology

namespace UnknownLoads.Coxian.FluidAux
open UnknownLoads.Coxian

/-- If `f' = -a f + g` with `a > 0` and `g → 0`, then `f → 0`. -/
lemma tendsto_zero_of_linear_ode {f g : ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (hf : ∀ t, HasDerivAt f (-a * f t + g t) t) (hg : Tendsto g atTop (𝓝 0)) :
    Tendsto f atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨T0, hT0⟩ := Metric.tendsto_atTop.1 hg (a * ε / 2) (by positivity)
  have hcont : Continuous f := continuous_iff_continuousAt.2 (fun t => (hf t).continuousAt)
  -- upper function
  set φ : ℝ → ℝ := fun t => Real.exp (a * t) * (f t - ε / 2) with hφ
  set ψ : ℝ → ℝ := fun t => Real.exp (a * t) * (f t + ε / 2) with hψ
  have hexp : ∀ t, HasDerivAt (fun t => Real.exp (a * t)) (Real.exp (a * t) * a) t := by
    intro t
    have := ((hasDerivAt_id t).const_mul a).exp
    simpa [mul_comm] using this
  have hφd : ∀ t, HasDerivAt φ (Real.exp (a * t) * (g t - a * ε / 2)) t := by
    intro t
    have := (hexp t).mul ((hf t).sub_const (ε / 2))
    exact this.congr_deriv (by ring)
  have hψd : ∀ t, HasDerivAt ψ (Real.exp (a * t) * (g t + a * ε / 2)) t := by
    intro t
    have := (hexp t).mul ((hf t).add_const (ε / 2))
    exact this.congr_deriv (by ring)
  have hφanti : AntitoneOn φ (Set.Ici T0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici T0)
    · exact (continuous_iff_continuousAt.2 (fun t => (hφd t).continuousAt)).continuousOn
    · exact fun t _ => (hφd t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hφd t).deriv]
      have h1 := hT0 t (le_of_lt ht)
      rw [Real.dist_eq, sub_zero] at h1
      have := (abs_lt.1 h1).2
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by linarith)
  have hψmono : MonotoneOn ψ (Set.Ici T0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici T0)
    · exact (continuous_iff_continuousAt.2 (fun t => (hψd t).continuousAt)).continuousOn
    · exact fun t _ => (hψd t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hψd t).deriv]
      have h1 := hT0 t (le_of_lt ht)
      rw [Real.dist_eq, sub_zero] at h1
      have := (abs_lt.1 h1).1
      exact mul_nonneg (Real.exp_pos _).le (by linarith)
  -- exponential decay of constants
  set C := |φ T0| + |ψ T0| + 1 with hC
  have hCpos : 0 < C := by positivity
  have hdec : Tendsto (fun t => Real.exp (-(a * t))) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    apply tendsto_neg_atTop_atBot.comp
    exact tendsto_id.const_mul_atTop ha
  obtain ⟨T1, hT1⟩ := Metric.tendsto_atTop.1 hdec (ε / (2 * C)) (by positivity)
  refine ⟨max T0 T1, fun t ht => ?_⟩
  have htT0 : T0 ≤ t := le_trans (le_max_left _ _) ht
  have htT1 : T1 ≤ t := le_trans (le_max_right _ _) ht
  have h1 := hφanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 htT0) htT0
  have h2 := hψmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 htT0) htT0
  have h3 := hT1 t htT1
  rw [Real.dist_eq, sub_zero, abs_of_pos (Real.exp_pos _)] at h3
  simp only [hφ, hψ] at h1 h2
  have he : Real.exp (a * t) * Real.exp (-(a * t)) = 1 := by
    rw [← Real.exp_add]; simp
  have hepos : 0 < Real.exp (a * t) := Real.exp_pos _
  have hem : 0 < Real.exp (-(a * t)) := Real.exp_pos _
  -- f t - ε/2 ≤ φ T0 * exp(-a t), f t + ε/2 ≥ ψ T0 * exp(-a t)
  have hφT := le_abs_self (Real.exp (a * T0) * (f T0 - ε / 2))
  have hψT := neg_abs_le (Real.exp (a * T0) * (f T0 + ε / 2))
  have k1 : f t - ε / 2 ≤ |Real.exp (a * T0) * (f T0 - ε / 2)| * Real.exp (-(a * t)) := by
    have : (f t - ε / 2) = (Real.exp (a * t) * (f t - ε / 2)) * Real.exp (-(a * t)) := by
      rw [mul_comm (Real.exp (a * t)), mul_assoc, he, mul_one]
    rw [this]
    exact mul_le_mul_of_nonneg_right (h1.trans hφT) hem.le
  have k2 : -|Real.exp (a * T0) * (f T0 + ε / 2)| * Real.exp (-(a * t)) ≤ f t + ε / 2 := by
    have : (f t + ε / 2) = (Real.exp (a * t) * (f t + ε / 2)) * Real.exp (-(a * t)) := by
      rw [mul_comm (Real.exp (a * t)), mul_assoc, he, mul_one]
    rw [this]
    exact mul_le_mul_of_nonneg_right (hψT.trans h2) hem.le
  have k3 : C * Real.exp (-(a * t)) < ε / 2 := by
    have := mul_lt_mul_of_pos_left h3 hCpos
    rwa [show C * (ε / (2 * C)) = ε / 2 by field_simp] at this
  have hA : |Real.exp (a * T0) * (f T0 - ε / 2)| ≤ C := by
    simp only [hC, hφ]; linarith [abs_nonneg (Real.exp (a * T0) * (f T0 + ε / 2))]
  have hB : |Real.exp (a * T0) * (f T0 + ε / 2)| ≤ C := by
    simp only [hC, hψ]; linarith [abs_nonneg (Real.exp (a * T0) * (f T0 - ε / 2))]
  have k4 := mul_le_mul_of_nonneg_right hA hem.le
  have k5 := mul_le_mul_of_nonneg_right hB hem.le
  rw [Real.dist_eq, sub_zero, abs_lt]
  constructor <;> nlinarith

end UnknownLoads.Coxian.FluidAux

namespace UnknownLoads.Coxian.FluidAux
open UnknownLoads.Coxian

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

lemma G_hasDerivAt (P : Params) (m : Fin P.r) (t : ℝ) :
    HasDerivAt (fun u => Gsurv P m u) (∑ k, subGenerator P m k * Gsurv P k t) t := by
  have h := hasDerivAt_exp_smul_const' (𝕂 := ℝ) (subGenerator P) t
  have hL : HasDerivAt (fun u => (NormedSpace.exp (u • subGenerator P)).mulVec (fun _ => (1:ℝ)) m)
      ((subGenerator P * NormedSpace.exp (t • subGenerator P)).mulVec (fun _ => (1:ℝ)) m) t := by
    let L : Matrix (Fin P.r) (Fin P.r) ℝ →L[ℝ] ℝ :=
      { toFun := fun A => A.mulVec (fun _ => (1:ℝ)) m
        map_add' := by intro A B; simp [Matrix.add_mulVec]
        map_smul' := by intro c A; simp [Matrix.smul_mulVec]
        cont := by
          simp only [Matrix.mulVec, dotProduct]
          fun_prop }
    exact L.hasFDerivAt.comp_hasDerivAt t h
  unfold Gsurv
  convert hL using 1
  rw [← Matrix.mulVec_mulVec]
  simp [Matrix.mulVec, dotProduct]

lemma G_zero (P : Params) (m : Fin P.r) : Gsurv P m 0 = 1 := by
  simp [Gsurv]

noncomputable def aN (P : Params) (m : ℕ) : ℝ := if h : m < P.r then P.p ⟨m, h⟩ else 0
noncomputable def μN (P : Params) (m : ℕ) : ℝ := if h : m < P.r then P.μ ⟨m, h⟩ else 1
noncomputable def gN (P : Params) (m : ℕ) (t : ℝ) : ℝ :=
  if h : m < P.r then Gsurv P ⟨m, h⟩ t else 0

noncomputable def Vrec (P : Params) : ℕ → ℝ
  | 0 => 0
  | j + 1 => 1 / μN P (P.r - 1 - j) + aN P (P.r - 1 - j) * Vrec P j

noncomputable def W (P : Params) (m : ℕ) : ℝ := Vrec P (P.r - m)

lemma μN_pos (P : Params) (m : ℕ) : 0 < μN P m := by
  unfold μN; split_ifs
  · exact P.μ_pos _
  · norm_num

lemma W_succ (P : Params) {m : ℕ} (hm : m < P.r) :
    W P m = 1 / μN P m + aN P m * W P (m + 1) := by
  unfold W
  have e : P.r - m = (P.r - (m + 1)) + 1 := by omega
  rw [e, Vrec]
  have e2 : P.r - 1 - (P.r - (m + 1)) = m := by omega
  rw [e2]

lemma W_r (P : Params) : W P P.r = 0 := by simp [W, Vrec]

lemma gN_fin (P : Params) (m : Fin P.r) : gN P m.val = Gsurv P m := by
  funext t; simp [gN, m.isLt]

lemma sum_Q (P : Params) (m : Fin P.r) (t : ℝ) :
    ∑ k, subGenerator P m k * Gsurv P k t =
      -(P.μ m) * Gsurv P m t + aN P m.val * P.μ m * gN P (m.val + 1) t := by
  have e : ∀ k : Fin P.r, subGenerator P m k * Gsurv P k t =
      (if k = m then -(P.μ m) * Gsurv P k t else 0) +
      (if k.val = m.val + 1 then P.p m * P.μ m * Gsurv P k t else 0) := by
    intro k
    unfold subGenerator
    by_cases h1 : k = m
    · subst h1; simp
    · simp [h1]
  rw [Finset.sum_congr rfl (fun k _ => e k), Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  congr 1
  by_cases h : m.val + 1 < P.r
  · have hk : ∀ k : Fin P.r, (k.val = m.val + 1) ↔ k = ⟨m.val + 1, h⟩ := by
      intro k; rw [Fin.ext_iff]
    simp only [hk, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp [aN, gN, h, m.isLt]
  · have h0 : ∀ k : Fin P.r, ¬ (k.val = m.val + 1) := by
      intro k hk; have := k.isLt; omega
    simp only [h0, if_false, Finset.sum_const_zero]
    have hp : P.p m = 0 := P.p_last m (by have := m.isLt; omega)
    simp [aN, m.isLt, hp]

lemma gN_deriv (P : Params) {m : ℕ} (hm : m < P.r) (t : ℝ) :
    HasDerivAt (gN P m) (-(μN P m) * gN P m t + aN P m * μN P m * gN P (m + 1) t) t := by
  have h := G_hasDerivAt P ⟨m, hm⟩ t
  rw [sum_Q] at h
  have e : gN P m = fun u => Gsurv P ⟨m, hm⟩ u := gN_fin P ⟨m, hm⟩
  rw [e]
  convert h using 1
  simp [μN, gN, hm]

lemma gN_ge (P : Params) {m : ℕ} (hm : P.r ≤ m) : gN P m = fun _ => 0 := by
  funext t; simp [gN, not_lt.2 hm]

lemma gN_cont (P : Params) (m : ℕ) : Continuous (gN P m) := by
  by_cases hm : m < P.r
  · exact continuous_iff_continuousAt.2 (fun t => (gN_deriv P hm t).continuousAt)
  · rw [gN_ge P (not_lt.1 hm)]; exact continuous_const

lemma gN_zero (P : Params) {m : ℕ} (hm : m < P.r) : gN P m 0 = 1 := by
  simp [gN, hm, G_zero]

lemma main_induction (P : Params) : ∀ k m : ℕ, m + k = P.r →
    Tendsto (gN P m) atTop (𝓝 0) ∧
    Tendsto (fun t => ∫ τ in (0:ℝ)..t, gN P m τ) atTop (𝓝 (W P m)) := by
  intro k
  induction k with
  | zero =>
    intro m hm
    simp only [add_zero] at hm
    subst hm
    rw [gN_ge P le_rfl, W_r]
    simp
  | succ k ih =>
    intro m hm
    have hmr : m < P.r := by omega
    obtain ⟨ih1, ih2⟩ := ih (m + 1) (by omega)
    have hμ := μN_pos P m
    have h1 : Tendsto (gN P m) atTop (𝓝 0) := by
      apply tendsto_zero_of_linear_ode hμ (gN_deriv P hmr)
      have := ih1.const_mul (aN P m * μN P m)
      simpa using this
    refine ⟨h1, ?_⟩
    have hint : ∀ t, ∫ τ in (0:ℝ)..t, gN P m τ =
        (1 - gN P m t + aN P m * μN P m * ∫ τ in (0:ℝ)..t, gN P (m + 1) τ) / μN P m := by
      intro t
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := t)
        (fun x _ => gN_deriv P hmr x)
        ((((gN_cont P m).const_mul (-(μN P m))).add
          ((gN_cont P (m + 1)).const_mul (aN P m * μN P m))).intervalIntegrable 0 t)
      rw [intervalIntegral.integral_add (((gN_cont P m).const_mul _).intervalIntegrable 0 t)
          (((gN_cont P (m + 1)).const_mul _).intervalIntegrable 0 t),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        gN_zero P hmr] at hftc
      field_simp
      linarith
    have hlim : Tendsto (fun t => (1 - gN P m t + aN P m * μN P m *
        ∫ τ in (0:ℝ)..t, gN P (m + 1) τ) / μN P m) atTop
        (𝓝 ((1 - 0 + aN P m * μN P m * W P (m + 1)) / μN P m)) :=
      ((tendsto_const_nhds.sub h1).add (ih2.const_mul _)).div_const _
    have hW : (1 - 0 + aN P m * μN P m * W P (m + 1)) / μN P m = W P m := by
      rw [W_succ P hmr, sub_zero]; field_simp
    rw [hW] at hlim
    exact hlim.congr (fun t => (hint t).symm)

end UnknownLoads.Coxian.FluidAux

namespace UnknownLoads.Coxian.FluidAux
open UnknownLoads.Coxian

noncomputable def piN (P : Params) (n : ℕ) : ℝ := ∏ j ∈ Finset.range n, aN P j
noncomputable def bN (P : Params) (j : ℕ) : ℝ := 1 / μN P j
noncomputable def BN (P : Params) (n : ℕ) : ℝ := ∑ j ∈ Finset.range n, bN P j

lemma piW (P : Params) : ∀ k m : ℕ, m + k = P.r →
    piN P m * W P m = ∑ j ∈ Finset.Ico m P.r, piN P j * bN P j := by
  intro k
  induction k with
  | zero => intro m hm; simp only [add_zero] at hm; subst hm; simp [W_r]
  | succ k ih =>
    intro m hm
    have hmr : m < P.r := by omega
    rw [W_succ P hmr, Finset.sum_eq_sum_Ico_succ_bot hmr, ← ih (m + 1) (by omega)]
    simp only [piN, bN, Finset.prod_range_succ]
    ring

lemma abel (P : Params) (n : ℕ) :
    ∑ i ∈ Finset.range n, (piN P i - piN P (i + 1)) * BN P (i + 1) =
      ∑ k ∈ Finset.range n, piN P k * bN P k - piN P n * BN P n := by
  induction n with
  | zero => simp [BN]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    simp only [BN, Finset.sum_range_succ]
    ring

lemma piN_r (P : Params) : piN P P.r = 0 := by
  unfold piN
  apply Finset.prod_eq_zero (i := P.r - 1) (Finset.mem_range.2 (by have := P.r_pos; omega))
  have h : P.r - 1 < P.r := by have := P.r_pos; omega
  simp only [aN, h, dif_pos]
  exact P.p_last _ (by simp; omega)

lemma aN_fin (P : Params) (j : Fin P.r) : aN P j.val = P.p j := by simp [aN, j.isLt]
lemma μN_fin (P : Params) (j : Fin P.r) : μN P j.val = P.μ j := by simp [μN, j.isLt]

lemma prod_filter_lt (P : Params) (i : Fin P.r) :
    ∏ j ∈ Finset.univ.filter (fun j : Fin P.r => j < i), P.p j = piN P i.val := by
  rw [Finset.prod_filter]
  have := Fin.prod_univ_eq_prod_range (fun j => if j < i.val then aN P j else 1) P.r
  have e : ∀ j : Fin P.r, (if j < i then P.p j else 1) =
      (fun j => if j < i.val then aN P j else 1) j.val := by
    intro j; simp only [Fin.lt_iff_val_lt_val, aN_fin]
  rw [Finset.prod_congr rfl (fun j _ => e j), this, ← Finset.prod_filter, piN]
  congr 1
  ext j; simp only [Finset.mem_filter, Finset.mem_range]; have := i.isLt; omega

lemma sum_filter_le (P : Params) (i : Fin P.r) :
    ∑ k ∈ Finset.univ.filter (fun k : Fin P.r => k ≤ i), 1 / P.μ k = BN P (i.val + 1) := by
  rw [Finset.sum_filter]
  have := Fin.sum_univ_eq_sum_range (fun j => if j < i.val + 1 then bN P j else 0) P.r
  have e : ∀ j : Fin P.r, (if j ≤ i then 1 / P.μ j else 0) =
      (fun j => if j < i.val + 1 then bN P j else 0) j.val := by
    intro j
    simp only [bN, μN_fin]
    have : j ≤ i ↔ j.val < i.val + 1 := by rw [Fin.le_iff_val_le_val]; omega
    simp only [this]
  rw [Finset.sum_congr rfl (fun j _ => e j), this, ← Finset.sum_filter, BN]
  congr 1
  ext j; simp only [Finset.mem_filter, Finset.mem_range]; have := i.isLt; omega

lemma meanService_eq (P : Params) : meanService P = W P 0 := by
  have h1 : meanService P = ∑ i ∈ Finset.range P.r, (piN P i - piN P (i + 1)) * BN P (i + 1) := by
    unfold meanService
    rw [← Fin.sum_univ_eq_sum_range (fun i => (piN P i - piN P (i + 1)) * BN P (i + 1))]
    apply Finset.sum_congr rfl
    intro i _
    rw [prod_filter_lt, sum_filter_le]
    simp only [piN, Finset.prod_range_succ, aN_fin]
    ring
  rw [h1, abel, piN_r, zero_mul, sub_zero]
  have := piW P P.r 0 (by simp)
  simp only [piN, Finset.range_zero, Finset.prod_empty, one_mul] at this
  rw [this, Finset.range_eq_Ico]
  rfl

end UnknownLoads.Coxian.FluidAux
open UnknownLoads.Coxian UnknownLoads.Coxian.FluidAux

theorem solution {P : Params} (s0 : Profile P.r → ℝ) (hs0 : InS s0) :
    (∀ t : ℝ, 0 < t → DifferentiableAt ℝ (fluidU P s0) t) ∧
    Tendsto (fluidU P s0) atTop (𝓝 (rho P)) ∧
    Tendsto (deriv (fluidU P s0)) atTop (𝓝 0) := by
  set c := phaseMass0 P s0 with hc
  have h0 : (0 : ℕ) < P.r := P.r_pos
  have hfirst : gN P 0 = Gsurv P (firstPhase P) := gN_fin P (firstPhase P)
  have hrep : fluidU P s0 = fun t => ∑ m : Fin P.r, c m * gN P m.val t +
      P.lam * ∫ τ in (0:ℝ)..t, gN P 0 τ := by
    funext t
    unfold fluidU
    congr 1
    · apply Finset.sum_congr rfl; intro m _; rw [gN_fin]
    · rw [intervalIntegral.integral_const_mul, hfirst,
        intervalIntegral.integral_comp_sub_left (fun x => Gsurv P (firstPhase P) x) t]
      simp
  set D : ℝ → ℝ := fun t => ∑ m : Fin P.r, c m *
      (-(μN P m.val) * gN P m.val t + aN P m.val * μN P m.val * gN P (m.val + 1) t) +
      P.lam * gN P 0 t with hD
  have hderiv : ∀ t, HasDerivAt (fluidU P s0) (D t) t := by
    intro t
    rw [hrep]
    apply HasDerivAt.add
    · apply HasDerivAt.fun_sum
      intro m _
      exact (gN_deriv P m.isLt t).const_mul (c m)
    · exact ((gN_cont P 0).integral_hasStrictDerivAt 0 t).hasDerivAt.const_mul P.lam
  have hg : ∀ m : ℕ, Tendsto (gN P m) atTop (𝓝 0) := by
    intro m
    by_cases hm : m < P.r
    · exact (main_induction P (P.r - m) m (by omega)).1
    · rw [gN_ge P (not_lt.1 hm)]; exact tendsto_const_nhds
  refine ⟨fun t _ => (hderiv t).differentiableAt, ?_, ?_⟩
  · rw [hrep]
    have hI := (main_induction P P.r 0 (by simp)).2
    have : rho P = ∑ m : Fin P.r, c m * 0 + P.lam * W P 0 := by
      simp [rho, meanService_eq]
    rw [this]
    apply Tendsto.add
    · exact tendsto_finset_sum _ (fun m _ => (hg m.val).const_mul (c m))
    · exact hI.const_mul P.lam
  · have he : deriv (fluidU P s0) = D := funext fun t => (hderiv t).deriv
    rw [he]
    have : (0:ℝ) = ∑ m : Fin P.r, c m *
        (-(μN P m.val) * 0 + aN P m.val * μN P m.val * 0) + P.lam * 0 := by simp
    rw [this]
    apply Tendsto.add
    · apply tendsto_finset_sum
      intro m _
      exact (((hg m.val).const_mul _).add ((hg (m.val + 1)).const_mul _)).const_mul (c m)
    · exact (hg 0).const_mul P.lam
