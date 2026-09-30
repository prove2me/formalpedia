-- Prove2me | solution 1 for SupplyChainTheory.bullwhip_signal_processing
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T14:51:44.929838+00:00
-- url     : https://prove2.me/submissions/56c87eb1-83a3-4313-9497-12bc52cd7494

import Mathlib
import Definitions.Def_SupplyChainTheory_bullwhip

set_option autoImplicit false

/-- One-period forecast error of a deterministic path (mirrors `AR1Demand.err`). -/
noncomputable def bwd_err (m : ℕ) (x : ℤ → ℝ) (s : ℤ) : ℝ :=
  x s - ((1 : ℕ) : ℝ) * ((∑ i ∈ Finset.Icc 1 m, x (s - i)) / m)

/-- The error-spread estimate of a deterministic path (mirrors `AR1Demand.sigmaHat`). -/
noncomputable def bwd_sig (C : ℝ) (m : ℕ) (x : ℤ → ℝ) (t : ℤ) : ℝ :=
  C * Real.sqrt ((∑ i ∈ Finset.Icc 1 m, (bwd_err m x (t - i)) ^ 2) / m)

open SupplyChainTheory MeasureTheory in
theorem bwd_sigmaHat_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (X : AR1Demand P)
    (C : ℝ) (m : ℕ) (t : ℤ) (ω : Ω) :
    X.sigmaHat C m t ω = bwd_sig C m (fun s => X.D s ω) t := rfl

theorem bwd_err_congr (m : ℕ) (x y : ℤ → ℝ) (s : ℤ)
    (h : ∀ k : ℤ, s - m ≤ k → k ≤ s → x k = y k) :
    bwd_err m x s = bwd_err m y s := by
  unfold bwd_err
  rw [h s (by omega) le_rfl]
  congr 3
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.mem_Icc] at hi
  exact h _ (by omega) (by omega)

theorem bwd_sig_congr (C : ℝ) (m : ℕ) (x y : ℤ → ℝ) (t : ℤ)
    (h : ∀ k : ℤ, t - 2 * m ≤ k → k ≤ t - 1 → x k = y k) :
    bwd_sig C m x t = bwd_sig C m y t := by
  unfold bwd_sig
  congr 3
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.mem_Icc] at hi
  rw [bwd_err_congr m x y (t - i) (fun k hk1 hk2 => h k (by omega) (by omega))]

theorem bwd_err_reflect (m : ℕ) (hm : 0 < m) (x : ℤ → ℝ) (a : ℝ) (s : ℤ) :
    bwd_err m (fun k => a - x k) s = - bwd_err m x s := by
  unfold bwd_err
  rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc]
  have hm' : (m : ℝ) ≠ 0 := by positivity
  have h1 : m + 1 - 1 = m := by omega
  rw [h1, nsmul_eq_mul]
  field_simp
  ring

theorem bwd_sig_reflect (C : ℝ) (m : ℕ) (hm : 0 < m) (x : ℤ → ℝ) (a : ℝ) (t : ℤ) :
    bwd_sig C m (fun k => a - x k) t = bwd_sig C m x t := by
  unfold bwd_sig
  simp only [bwd_err_reflect m hm x a, neg_sq]

/-- The centred demand window `(D (s0 + j) - d/(1-ρ))_{j ≤ N}`, padded with zeros. -/
noncomputable def bwd_T {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    (X : SupplyChainTheory.AR1Demand P) (s0 : ℤ) (N : ℕ) (ω : Ω) : ℕ → ℝ :=
  fun j => if j ≤ N then X.D (s0 + j) ω - X.d / (1 - X.rho) else 0

open SupplyChainTheory MeasureTheory in
theorem bwd_T_meas {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (X : AR1Demand P)
    (s0 : ℤ) (N : ℕ) : Measurable (bwd_T X s0 N) := by
  refine measurable_pi_lambda _ (fun j => ?_)
  by_cases hj : j ≤ N
  · simp only [bwd_T, hj, ↓reduceIte]
    exact (X.measurable_D _).sub_const _
  · simp only [bwd_T, hj, ↓reduceIte]
    exact measurable_const

open SupplyChainTheory MeasureTheory in
theorem bwd_eps_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (X : AR1Demand P) (k : ℤ) :
    X.eps k = fun ω => X.D k ω - X.d - X.rho * X.D (k - 1) ω := by
  funext ω
  rw [X.recursion k ω]
  ring

open SupplyChainTheory MeasureTheory in
theorem bwd_eps_meas {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (X : AR1Demand P) (k : ℤ) :
    Measurable (X.eps k) := by
  rw [bwd_eps_eq X k]
  exact (((X.measurable_D k).sub_const _)).sub ((X.measurable_D (k - 1)).const_mul _)

open SupplyChainTheory MeasureTheory ProbabilityTheory in
theorem bwd_eps_symm {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (X : AR1Demand P) (k : ℤ) :
    P.map (fun ω => -X.eps k ω) = P.map (X.eps k) := by
  rw [show (fun ω => -X.eps k ω) = (fun x : ℝ => -x) ∘ X.eps k from rfl,
    ← Measure.map_map measurable_neg (bwd_eps_meas X k), X.eps_law, gaussianReal_map_neg,
    neg_zero]

open MeasureTheory ProbabilityTheory in
theorem bwd_pair_symm {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Y : Ω → (ℕ → ℝ)) (e : Ω → ℝ) (hY : Measurable Y) (he : Measurable e)
    (hind : IndepFun Y e P)
    (hYs : P.map (fun ω => -Y ω) = P.map Y) (hes : P.map (fun ω => -e ω) = P.map e)
    (Φ : (ℕ → ℝ) × ℝ → (ℕ → ℝ)) (hΦ : Measurable Φ)
    (hΦneg : ∀ v x, Φ (-v, -x) = -Φ (v, x)) :
    P.map (fun ω => -Φ (Y ω, e ω)) = P.map (fun ω => Φ (Y ω, e ω)) := by
  have hind' : IndepFun (fun ω => -Y ω) (fun ω => -e ω) P :=
    hind.comp (φ := fun v => -v) (ψ := fun x => -x) measurable_neg measurable_neg
  have h1 : P.map (fun ω => (Y ω, e ω)) = (P.map Y).prod (P.map e) :=
    (indepFun_iff_map_prod_eq_prod_map_map hY.aemeasurable he.aemeasurable).mp hind
  have h2 : P.map (fun ω => (-Y ω, -e ω))
      = (P.map (fun ω => -Y ω)).prod (P.map (fun ω => -e ω)) :=
    (indepFun_iff_map_prod_eq_prod_map_map hY.neg.aemeasurable he.neg.aemeasurable).mp hind'
  have e1 : (fun ω => Φ (Y ω, e ω)) = Φ ∘ (fun ω => (Y ω, e ω)) := rfl
  have e2 : (fun ω => -Φ (Y ω, e ω)) = Φ ∘ (fun ω => (-Y ω, -e ω)) := by
    funext ω
    simp only [Function.comp, hΦneg]
  rw [e1, e2, ← Measure.map_map (f := fun ω => (-Y ω, -e ω)) hΦ (hY.neg.prodMk he.neg),
    ← Measure.map_map (f := fun ω => (Y ω, e ω)) hΦ (hY.prodMk he), h1, h2, hYs, hes]

open SupplyChainTheory MeasureTheory ProbabilityTheory in
theorem bwd_window_symm {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : AR1Demand P) (s0 : ℤ) (N : ℕ) :
    P.map (fun ω => -bwd_T X s0 N ω) = P.map (bwd_T X s0 N) := by
  have hρ : 1 - X.rho ≠ 0 := by
    have := (abs_lt.mp X.rho_lt).2
    linarith
  induction N with
  | zero =>
    have hZ : Measurable (fun ω => X.D s0 ω - X.d / (1 - X.rho)) :=
      (X.measurable_D _).sub_const _
    have hψ : Measurable (fun x : ℝ => fun j : ℕ => if j ≤ 0 then x else 0) := by
      refine measurable_pi_lambda _ (fun j => ?_)
      by_cases hj : j ≤ 0
      · simp only [hj, ↓reduceIte]
        exact measurable_id
      · simp only [hj, ↓reduceIte]
        exact measurable_const
    have e1 : bwd_T X s0 0 = (fun x : ℝ => fun j : ℕ => if j ≤ 0 then x else 0) ∘
        (fun ω => X.D s0 ω - X.d / (1 - X.rho)) := by
      funext ω j
      by_cases hj : j ≤ 0
      · have : j = 0 := by omega
        subst this
        simp [bwd_T]
      · have hj' : j ≠ 0 := by omega
        simp [bwd_T, hj']
    have e2 : (fun ω => -bwd_T X s0 0 ω) = (fun x : ℝ => fun j : ℕ => if j ≤ 0 then x else 0) ∘
        (fun ω => -(X.D s0 ω - X.d / (1 - X.rho))) := by
      funext ω j
      by_cases hj : j ≤ 0
      · have : j = 0 := by omega
        subst this
        simp [bwd_T]
      · have hj' : j ≠ 0 := by omega
        simp [bwd_T, hj']
    rw [e2, e1, ← Measure.map_map hψ hZ,
      ← Measure.map_map (f := fun ω => -(X.D s0 ω - X.d / (1 - X.rho))) hψ hZ.neg]
    congr 1
    have m1 : P.map (fun ω => X.D s0 ω - X.d / (1 - X.rho))
        = gaussianReal 0 (Real.toNNReal (X.sigma ^ 2 / (1 - X.rho ^ 2))) := by
      rw [show (fun ω => X.D s0 ω - X.d / (1 - X.rho))
          = (fun x : ℝ => x - X.d / (1 - X.rho)) ∘ X.D s0 from rfl,
        ← Measure.map_map (measurable_sub_const _) (X.measurable_D s0), X.stationary,
        gaussianReal_map_sub_const, sub_self]
    have m2 : P.map (fun ω => -(X.D s0 ω - X.d / (1 - X.rho)))
        = (P.map (fun ω => X.D s0 ω - X.d / (1 - X.rho))).map (fun x : ℝ => -x) := by
      rw [Measure.map_map measurable_neg hZ]
      rfl
    rw [m2, m1, gaussianReal_map_neg, neg_zero]
  | succ N ih =>
    let Φ : (ℕ → ℝ) × ℝ → (ℕ → ℝ) := fun p j => if j = N + 1 then X.rho * p.1 N + p.2 else p.1 j
    have hΦ : Measurable Φ := by
      refine measurable_pi_lambda _ (fun j => ?_)
      by_cases hj : j = N + 1
      · simp only [Φ, hj, ↓reduceIte]
        fun_prop
      · simp only [Φ, hj, ↓reduceIte]
        fun_prop
    have hΦneg : ∀ v x, Φ (-v, -x) = -Φ (v, x) := by
      intro v x
      funext j
      by_cases hj : j = N + 1
      · simp only [Φ, hj, ↓reduceIte, Pi.neg_apply]
        ring
      · simp only [Φ, hj, ↓reduceIte, Pi.neg_apply]
    have hstep : bwd_T X s0 (N + 1)
        = fun ω => Φ (bwd_T X s0 N ω, X.eps (s0 + ((N + 1 : ℕ) : ℤ)) ω) := by
      funext ω j
      by_cases hj : j = N + 1
      · subst hj
        simp only [bwd_T, Φ, le_refl, ↓reduceIte]
        rw [X.recursion (s0 + ((N + 1 : ℕ) : ℤ)) ω]
        have hidx : s0 + ((N + 1 : ℕ) : ℤ) - 1 = s0 + (N : ℤ) := by push_cast; ring
        rw [hidx]
        have hc1 : X.d / (1 - X.rho) * (1 - X.rho) = X.d := div_mul_cancel₀ _ hρ
        linear_combination (-1 : ℝ) * hc1
      · by_cases hjN : j ≤ N
        · have hj2 : j ≤ N + 1 := by omega
          simp only [bwd_T, Φ, hj, hjN, hj2, ↓reduceIte]
        · have hj2 : ¬ j ≤ N + 1 := by omega
          simp only [bwd_T, Φ, hj, hjN, hj2, ↓reduceIte]
    have hind : IndepFun (bwd_T X s0 N) (X.eps (s0 + ((N + 1 : ℕ) : ℤ))) P := by
      have h0 := (X.eps_indep_past (s0 + ((N + 1 : ℕ) : ℤ))).symm
      let h : (ℕ → ℝ) → (ℕ → ℝ) := fun p j => if j ≤ N then p (N - j) - X.d / (1 - X.rho) else 0
      have hh : Measurable h := by
        refine measurable_pi_lambda _ (fun j => ?_)
        by_cases hj : j ≤ N
        · simp only [h, hj, ↓reduceIte]
          fun_prop
        · simp only [h, hj, ↓reduceIte]
          fun_prop
      have h1 := h0.comp hh measurable_id
      have h2 : bwd_T X s0 N = h ∘ fun ω k => X.D (s0 + ((N + 1 : ℕ) : ℤ) - 1 - k) ω := by
        funext ω j
        by_cases hj : j ≤ N
        · simp only [Function.comp, bwd_T, h, hj, ↓reduceIte]
          congr 2
          omega
        · simp only [Function.comp, bwd_T, h, hj, ↓reduceIte]
      rw [h2]
      exact h1
    rw [hstep]
    exact bwd_pair_symm _ _ (bwd_T_meas X s0 N) (bwd_eps_meas X _) hind ih (bwd_eps_symm X _)
      Φ hΦ hΦneg

/-- Reconstruct a path from a centred window. -/
noncomputable def bwd_path (c : ℝ) (s0 : ℤ) (v : ℕ → ℝ) (s : ℤ) : ℝ := c + v (Int.toNat (s - s0))

/-- The covariance integrand as a function of the centred window. -/
noncomputable def bwd_G (C c EB : ℝ) (L m : ℕ) (s0 t : ℤ) (v : ℕ → ℝ) : ℝ :=
  ((1 + (L : ℝ) / m) * bwd_path c s0 v (t - 1) - ((L : ℝ) / m) * bwd_path c s0 v (t - m - 1) - c) *
    (bwd_sig C m (bwd_path c s0 v) t - bwd_sig C m (bwd_path c s0 v) (t - 1) - EB)

theorem bwd_G_odd (C c EB : ℝ) (L m : ℕ) (hm : 0 < m) (s0 t : ℤ) (v : ℕ → ℝ) :
    bwd_G C c EB L m s0 t (-v) = - bwd_G C c EB L m s0 t v := by
  have hp : bwd_path c s0 (-v) = fun k => 2 * c - bwd_path c s0 v k := by
    funext k
    simp only [bwd_path, Pi.neg_apply]
    ring
  unfold bwd_G
  rw [hp, bwd_sig_reflect C m hm _ _ t, bwd_sig_reflect C m hm _ _ (t - 1)]
  ring

theorem bwd_G_meas (C c EB : ℝ) (L m : ℕ) (s0 t : ℤ) :
    Measurable (bwd_G C c EB L m s0 t) := by
  have hcont : Continuous (bwd_G C c EB L m s0 t) := by
    unfold bwd_G bwd_sig bwd_err bwd_path
    fun_prop
  exact hcont.measurable

open SupplyChainTheory MeasureTheory ProbabilityTheory in
theorem bsp_cov_vanish {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] (X : AR1Demand P) (C : ℝ) (L m : ℕ) (hm : 0 < m)
    (t : ℤ) :
    ProbabilityTheory.covariance
      (fun ω => (1 + (L : ℝ) / m) * X.D (t - 1) ω - ((L : ℝ) / m) * X.D (t - m - 1) ω)
      (fun ω => X.sigmaHat C m t ω - X.sigmaHat C m (t - 1) ω) P = 0 := by
  have hDint : ∀ s, Integrable (X.D s) P := by
    intro s
    have hi : Integrable (fun x : ℝ => x) (P.map (X.D s)) := by
      rw [X.stationary s]
      exact memLp_one_iff_integrable.mp (memLp_id_gaussianReal' 1 ENNReal.one_ne_top)
    exact (integrable_map_measure aestronglyMeasurable_id (X.measurable_D s).aemeasurable).mp hi
  have hDmean : ∀ s, ∫ ω, X.D s ω ∂P = X.d / (1 - X.rho) := by
    intro s
    have h := integral_map (μ := P) (X.measurable_D s).aemeasurable
      (f := fun x : ℝ => x) aestronglyMeasurable_id
    rw [← h, X.stationary s, integral_id_gaussianReal]
  have hA : ∫ ω, ((1 + (L : ℝ) / m) * X.D (t - 1) ω - ((L : ℝ) / m) * X.D (t - m - 1) ω) ∂P
      = X.d / (1 - X.rho) := by
    rw [integral_sub ((hDint _).const_mul _) ((hDint _).const_mul _), integral_const_mul,
      integral_const_mul, hDmean, hDmean]
    ring
  set c := X.d / (1 - X.rho) with hc
  set s0 : ℤ := t - 2 * m - 1 with hs0
  set EB := ∫ ω, (X.sigmaHat C m t ω - X.sigmaHat C m (t - 1) ω) ∂P with hEB
  have hpath : ∀ ω s, s0 ≤ s → s ≤ t - 1 → bwd_path c s0 (bwd_T X s0 (2 * m) ω) s = X.D s ω := by
    intro ω s h1 h2
    have hle : Int.toNat (s - s0) ≤ 2 * m := by omega
    have heq : s0 + ((Int.toNat (s - s0) : ℕ) : ℤ) = s := by omega
    simp only [bwd_path, bwd_T, hle, ↓reduceIte, heq]
    ring
  have hsig : ∀ ω u, s0 + 2 * m ≤ u → u ≤ t →
      bwd_sig C m (bwd_path c s0 (bwd_T X s0 (2 * m) ω)) u = X.sigmaHat C m u ω := by
    intro ω u h1 h2
    rw [bwd_sigmaHat_eq]
    exact bwd_sig_congr C m _ _ u (fun k hk1 hk2 => hpath ω k (by omega) (by omega))
  have hint : ∀ ω, ((1 + (L : ℝ) / m) * X.D (t - 1) ω - ((L : ℝ) / m) * X.D (t - m - 1) ω - c) *
      (X.sigmaHat C m t ω - X.sigmaHat C m (t - 1) ω - EB)
        = bwd_G C c EB L m s0 t (bwd_T X s0 (2 * m) ω) := by
    intro ω
    unfold bwd_G
    rw [hpath ω (t - 1) (by omega) le_rfl, hpath ω (t - m - 1) (by omega) (by omega),
      hsig ω t (by omega) le_rfl, hsig ω (t - 1) (by omega) (by omega)]
  have hcov : ProbabilityTheory.covariance
      (fun ω => (1 + (L : ℝ) / m) * X.D (t - 1) ω - ((L : ℝ) / m) * X.D (t - m - 1) ω)
      (fun ω => X.sigmaHat C m t ω - X.sigmaHat C m (t - 1) ω) P
        = ∫ ω, bwd_G C c EB L m s0 t (bwd_T X s0 (2 * m) ω) ∂P := by
    unfold covariance
    rw [hA]
    exact integral_congr_ae (Filter.Eventually.of_forall hint)
  have hT := bwd_T_meas X s0 (2 * m)
  have hGm := bwd_G_meas C c EB L m s0 t
  have h1 : ∫ ω, bwd_G C c EB L m s0 t (bwd_T X s0 (2 * m) ω) ∂P
      = ∫ v, bwd_G C c EB L m s0 t v ∂(P.map (bwd_T X s0 (2 * m))) :=
    (integral_map hT.aemeasurable hGm.aestronglyMeasurable).symm
  have h2 : ∫ ω, bwd_G C c EB L m s0 t (-bwd_T X s0 (2 * m) ω) ∂P
      = ∫ v, bwd_G C c EB L m s0 t v ∂(P.map (fun ω => -bwd_T X s0 (2 * m) ω)) :=
    (integral_map (φ := fun ω => -bwd_T X s0 (2 * m) ω) hT.neg.aemeasurable
      hGm.aestronglyMeasurable).symm
  rw [bwd_window_symm X s0 (2 * m)] at h2
  have h3 : ∫ ω, bwd_G C c EB L m s0 t (-bwd_T X s0 (2 * m) ω) ∂P
      = - ∫ ω, bwd_G C c EB L m s0 t (bwd_T X s0 (2 * m) ω) ∂P := by
    simp_rw [bwd_G_odd C c EB L m hm s0 t]
    exact integral_neg _
  rw [hcov]
  linarith

/-- Telescoping over `Icc 1 m`: `∑ f i - ∑ f (i+1) = f 1 - f (m+1)`. -/
theorem bsp_tele (f : ℕ → ℝ) (m : ℕ) :
    ∑ i ∈ Finset.Icc 1 m, f i - ∑ i ∈ Finset.Icc 1 m, f (i + 1) = f 1 - f (m + 1) := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1),
      Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
    linear_combination ih

open SupplyChainTheory in
/-- The order identity: `Qₜ = (1 + L/m) D_{t-1} - (L/m) D_{t-m-1} + z (σ̂ₜ - σ̂ₜ₋₁)`. -/
theorem bsp_order_eq {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    (X : AR1Demand P) (C z : ℝ) (L m : ℕ) (t : ℤ) (ω : Ω) :
    X.order C z L m t ω
      = (1 + (L : ℝ) / m) * X.D (t - 1) ω - ((L : ℝ) / m) * X.D (t - m - 1) ω
        + z * (X.sigmaHat C m t ω - X.sigmaHat C m (t - 1) ω) := by
  have key := bsp_tele (fun k : ℕ => X.D (t - (k : ℤ)) ω) m
  have hshift : ∑ i ∈ Finset.Icc 1 m, X.D (t - 1 - (i : ℤ)) ω
      = ∑ i ∈ Finset.Icc 1 m, X.D (t - ((i + 1 : ℕ) : ℤ)) ω := by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    push_cast
    ring
  have h1 : X.D (t - ((1 : ℕ) : ℤ)) ω = X.D (t - 1) ω := by
    congr 1
  have h2 : X.D (t - ((m + 1 : ℕ) : ℤ)) ω = X.D (t - m - 1) ω := by
    congr 1
    push_cast
    ring
  rw [h1, h2, ← hshift] at key
  unfold AR1Demand.order AR1Demand.baseStock AR1Demand.muHat
  linear_combination ((L : ℝ) / m) * key

open SupplyChainTheory MeasureTheory ProbabilityTheory in
theorem bsp_D_memLp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (X : AR1Demand P) (s : ℤ) :
    MemLp (X.D s) 2 P := by
  have hi : MemLp id 2 (P.map (X.D s)) := by
    rw [X.stationary s]
    exact memLp_id_gaussianReal' 2 (by norm_num)
  exact (memLp_map_measure_iff aestronglyMeasurable_id (X.measurable_D s).aemeasurable).mp hi

open SupplyChainTheory MeasureTheory ProbabilityTheory in
theorem bsp_var_D {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (X : AR1Demand P) (s : ℤ) :
    variance (X.D s) P = X.sigma ^ 2 / (1 - X.rho ^ 2) := by
  have h := variance_map (μ := P) (X := id) (Y := X.D s) measurable_id.aemeasurable
    (X.measurable_D s).aemeasurable
  rw [X.stationary s, variance_id_gaussianReal] at h
  have hr : 0 < 1 - X.rho ^ 2 := by
    have := abs_lt.mp X.rho_lt
    nlinarith
  rw [Real.coe_toNNReal _ (div_nonneg (sq_nonneg _) hr.le)] at h
  rw [h]
  rfl

open SupplyChainTheory MeasureTheory ProbabilityTheory in
theorem bsp_eps_memLp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : AR1Demand P) (k : ℤ) : MemLp (X.eps k) 2 P := by
  rw [bwd_eps_eq X k]
  exact ((bsp_D_memLp X k).sub (memLp_const _)).sub ((bsp_D_memLp X (k - 1)).const_mul _)

open SupplyChainTheory MeasureTheory ProbabilityTheory in
/-- Autocovariance (13.4): `Cov[D_{s+k}, D_s] = ρ^k σ²/(1-ρ²)`. -/
theorem bsp_autocov {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : AR1Demand P) (s : ℤ) (k : ℕ) :
    covariance (X.D (s + k)) (X.D s) P = X.rho ^ k * (X.sigma ^ 2 / (1 - X.rho ^ 2)) := by
  induction k with
  | zero =>
    simp only [Nat.cast_zero, add_zero, pow_zero, one_mul]
    rw [covariance_self (X.measurable_D s).aemeasurable, bsp_var_D]
  | succ k ih =>
    have hrec : X.D (s + ((k + 1 : ℕ) : ℤ))
        = fun ω => X.d + (X.rho * X.D (s + (k : ℤ)) ω + X.eps (s + ((k + 1 : ℕ) : ℤ)) ω) := by
      funext ω
      rw [X.recursion (s + ((k + 1 : ℕ) : ℤ)) ω]
      have hidx : s + ((k + 1 : ℕ) : ℤ) - 1 = s + (k : ℤ) := by push_cast; ring
      rw [hidx]
      ring
    have hind : IndepFun (X.eps (s + ((k + 1 : ℕ) : ℤ))) (X.D s) P := by
      have h0 := X.eps_indep_past (s + ((k + 1 : ℕ) : ℤ))
      have hψ : Measurable (fun p : ℕ → ℝ => p k) := measurable_pi_apply k
      have h1 := h0.comp (φ := id) (ψ := fun p : ℕ → ℝ => p k) measurable_id hψ
      have h2 : X.D s = (fun p : ℕ → ℝ => p k) ∘
          (fun ω (j : ℕ) => X.D (s + ((k + 1 : ℕ) : ℤ) - 1 - j) ω) := by
        funext ω
        simp only [Function.comp]
        congr 1
        push_cast
        ring
      rw [h2]
      exact h1
    have hDk := bsp_D_memLp X (s + (k : ℤ))
    have hDs := bsp_D_memLp X s
    have heps := bsp_eps_memLp X (s + ((k + 1 : ℕ) : ℤ))
    have hadd : covariance (fun ω => X.rho * X.D (s + (k : ℤ)) ω + X.eps (s + ((k + 1 : ℕ) : ℤ)) ω)
        (X.D s) P
        = covariance (fun ω => X.rho * X.D (s + (k : ℤ)) ω) (X.D s) P
          + covariance (X.eps (s + ((k + 1 : ℕ) : ℤ))) (X.D s) P :=
      covariance_add_left (hDk.const_mul _) heps hDs
    have hint : Integrable
        (fun ω => X.rho * X.D (s + (k : ℤ)) ω + X.eps (s + ((k + 1 : ℕ) : ℤ)) ω) P :=
      ((hDk.const_mul _).add heps).integrable one_le_two
    rw [hrec, covariance_const_add_left hint, hadd, covariance_const_mul_left, ih, hind.covariance_eq_zero heps hDs]
    ring

open SupplyChainTheory MeasureTheory ProbabilityTheory in
theorem bsp_err_memLp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : AR1Demand P) (m : ℕ) (s : ℤ) : MemLp (X.err m s) 2 P := by
  have h : X.err m s = fun ω => X.D s ω - ((1 : ℕ) : ℝ) *
      ((∑ i ∈ Finset.Icc 1 m, X.D (s - i) ω) * (m : ℝ)⁻¹) := by
    funext ω
    simp only [AR1Demand.err, AR1Demand.muHat, div_eq_mul_inv]
  rw [h]
  exact (bsp_D_memLp X s).sub
    (((memLp_finsetSum (Finset.Icc 1 m) (fun i _ => bsp_D_memLp X (s - i))).mul_const _).const_mul _)

open SupplyChainTheory MeasureTheory ProbabilityTheory in
theorem bsp_sig_memLp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : AR1Demand P) (C : ℝ) (m : ℕ) (s : ℤ) : MemLp (X.sigmaHat C m s) 2 P := by
  have hc : Continuous (fun x : ℤ → ℝ => bwd_sig C m x s) := by
    unfold bwd_sig bwd_err
    fun_prop
  have hp : Measurable (fun ω => fun k : ℤ => X.D k ω) := measurable_pi_lambda _ X.measurable_D
  have e : X.sigmaHat C m s
      = (fun x : ℤ → ℝ => bwd_sig C m x s) ∘ (fun ω => fun k : ℤ => X.D k ω) := by
    funext ω
    exact bwd_sigmaHat_eq X C m s ω
  have hmeas : Measurable (X.sigmaHat C m s) := by
    rw [e]
    exact hc.measurable.comp hp
  rw [memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable]
  have heq : (fun ω => X.sigmaHat C m s ω ^ 2)
      = fun ω => C ^ 2 * ((∑ i ∈ Finset.Icc 1 m, (X.err m (s - i) ω) ^ 2) * (m : ℝ)⁻¹) := by
    funext ω
    simp only [AR1Demand.sigmaHat]
    rw [mul_pow, Real.sq_sqrt (by positivity), div_eq_mul_inv]
  have hsum : Integrable (fun ω => ∑ i ∈ Finset.Icc 1 m, (X.err m (s - i) ω) ^ 2) P :=
    integrable_finsetSum _ (fun i _ => (bsp_err_memLp X m (s - i)).integrable_sq)
  rw [heq]
  exact (hsum.mul_const _).const_mul _

open SupplyChainTheory MeasureTheory ProbabilityTheory in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] (X : AR1Demand P) (C z : ℝ)
    (L m : ℕ) (hm : 0 < m) (t : ℤ) :
    ProbabilityTheory.variance (X.order C z L m t) P / ProbabilityTheory.variance (X.D t) P
        ≥ 1 + (2 * (L : ℝ) / m + 2 * (L : ℝ) ^ 2 / (m : ℝ) ^ 2) * (1 - X.rho ^ m)
      ∧ (z = 0 →
          ProbabilityTheory.variance (X.order C z L m t) P / ProbabilityTheory.variance (X.D t) P
            = 1 + (2 * (L : ℝ) / m + 2 * (L : ℝ) ^ 2 / (m : ℝ) ^ 2) * (1 - X.rho ^ m)) := by
  have hQ : X.order C z L m t = fun ω =>
      ((1 + (L : ℝ) / m) * X.D (t - 1) ω - ((L : ℝ) / m) * X.D (t - m - 1) ω)
        + z * (X.sigmaHat C m t ω - X.sigmaHat C m (t - 1) ω) := by
    funext ω
    exact bsp_order_eq X C z L m t ω
  have hAm : MemLp (fun ω => (1 + (L : ℝ) / m) * X.D (t - 1) ω - ((L : ℝ) / m) * X.D (t - m - 1) ω)
      2 P := ((bsp_D_memLp X _).const_mul _).sub ((bsp_D_memLp X _).const_mul _)
  have hBm : MemLp (fun ω => X.sigmaHat C m t ω - X.sigmaHat C m (t - 1) ω) 2 P :=
    (bsp_sig_memLp X C m t).sub (bsp_sig_memLp X C m (t - 1))
  have hcov := bsp_cov_vanish X C L m hm t
  have hr : 0 < 1 - X.rho ^ 2 := by
    have := abs_lt.mp X.rho_lt
    nlinarith
  have hvpos : 0 < X.sigma ^ 2 / (1 - X.rho ^ 2) := div_pos (pow_pos X.sigma_pos 2) hr
  have hVA : variance
      (fun ω => (1 + (L : ℝ) / m) * X.D (t - 1) ω - ((L : ℝ) / m) * X.D (t - m - 1) ω) P
      = (X.sigma ^ 2 / (1 - X.rho ^ 2))
        * (1 + (2 * (L : ℝ) / m + 2 * (L : ℝ) ^ 2 / (m : ℝ) ^ 2) * (1 - X.rho ^ m)) := by
    rw [variance_fun_sub ((bsp_D_memLp X _).const_mul _) ((bsp_D_memLp X _).const_mul _),
      variance_const_mul, variance_const_mul, covariance_const_mul_left,
      covariance_const_mul_right, bsp_var_D, bsp_var_D]
    have hac := bsp_autocov X (t - m - 1) m
    have hidx : t - (m : ℤ) - 1 + (m : ℤ) = t - 1 := by ring
    rw [hidx] at hac
    rw [hac]
    ring
  have hVQ : variance (X.order C z L m t) P
      = variance
          (fun ω => (1 + (L : ℝ) / m) * X.D (t - 1) ω - ((L : ℝ) / m) * X.D (t - m - 1) ω) P
        + z ^ 2 * variance (fun ω => X.sigmaHat C m t ω - X.sigmaHat C m (t - 1) ω) P := by
    rw [hQ, variance_fun_add hAm (hBm.const_mul z), covariance_const_mul_right, hcov,
      variance_const_mul]
    ring
  have hVB := variance_nonneg (fun ω => X.sigmaHat C m t ω - X.sigmaHat C m (t - 1) ω) P
  refine ⟨?_, ?_⟩
  · rw [hVQ, hVA, bsp_var_D, ge_iff_le, le_div_iff₀ hvpos]
    nlinarith [mul_nonneg (sq_nonneg z) hVB]
  · intro hz
    rw [hVQ, hVA, bsp_var_D, hz, zero_pow two_ne_zero, zero_mul, add_zero]
    exact mul_div_cancel_left₀ _ hvpos.ne'
