-- Prove2me | solution 1 for SupplyChainTheory.bullwhip_lemma_13_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T14:27:47.445492+00:00
-- url     : https://prove2.me/submissions/ed0b7803-7d8f-489d-a302-888fe35d3ae6

import Mathlib
import Definitions.Def_SupplyChainTheory_bullwhip

set_option autoImplicit false

/-- One-period forecast error of a deterministic path (mirrors `AR1Demand.err`). -/
noncomputable def bwl_err (m : ℕ) (x : ℤ → ℝ) (s : ℤ) : ℝ :=
  x s - ((1 : ℕ) : ℝ) * ((∑ i ∈ Finset.Icc 1 m, x (s - i)) / m)

/-- The error-spread estimate of a deterministic path (mirrors `AR1Demand.sigmaHat`). -/
noncomputable def bwl_sig (C : ℝ) (m : ℕ) (x : ℤ → ℝ) (t : ℤ) : ℝ :=
  C * Real.sqrt ((∑ i ∈ Finset.Icc 1 m, (bwl_err m x (t - i)) ^ 2) / m)

open SupplyChainTheory MeasureTheory in
theorem bwl_sigmaHat_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (X : AR1Demand P)
    (C : ℝ) (m : ℕ) (t : ℤ) (ω : Ω) :
    X.sigmaHat C m t ω = bwl_sig C m (fun s => X.D s ω) t := rfl

theorem bwl_err_congr (m : ℕ) (x y : ℤ → ℝ) (s : ℤ)
    (h : ∀ k : ℤ, s - m ≤ k → k ≤ s → x k = y k) :
    bwl_err m x s = bwl_err m y s := by
  unfold bwl_err
  rw [h s (by omega) le_rfl]
  congr 3
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.mem_Icc] at hi
  exact h _ (by omega) (by omega)

theorem bwl_sig_congr (C : ℝ) (m : ℕ) (x y : ℤ → ℝ) (t : ℤ)
    (h : ∀ k : ℤ, t - 2 * m ≤ k → k ≤ t - 1 → x k = y k) :
    bwl_sig C m x t = bwl_sig C m y t := by
  unfold bwl_sig
  congr 3
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.mem_Icc] at hi
  rw [bwl_err_congr m x y (t - i) (fun k hk1 hk2 => h k (by omega) (by omega))]

theorem bwl_err_reflect (m : ℕ) (hm : 0 < m) (x : ℤ → ℝ) (a : ℝ) (s : ℤ) :
    bwl_err m (fun k => a - x k) s = - bwl_err m x s := by
  unfold bwl_err
  rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc]
  have hm' : (m : ℝ) ≠ 0 := by positivity
  have h1 : m + 1 - 1 = m := by omega
  rw [h1, nsmul_eq_mul]
  field_simp
  ring

theorem bwl_sig_reflect (C : ℝ) (m : ℕ) (hm : 0 < m) (x : ℤ → ℝ) (a : ℝ) (t : ℤ) :
    bwl_sig C m (fun k => a - x k) t = bwl_sig C m x t := by
  unfold bwl_sig
  simp only [bwl_err_reflect m hm x a, neg_sq]

/-- The centred demand window `(D (s0 + j) - d/(1-ρ))_{j ≤ N}`, padded with zeros. -/
noncomputable def bwl_T {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    (X : SupplyChainTheory.AR1Demand P) (s0 : ℤ) (N : ℕ) (ω : Ω) : ℕ → ℝ :=
  fun j => if j ≤ N then X.D (s0 + j) ω - X.d / (1 - X.rho) else 0

open SupplyChainTheory MeasureTheory in
theorem bwl_T_meas {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (X : AR1Demand P)
    (s0 : ℤ) (N : ℕ) : Measurable (bwl_T X s0 N) := by
  refine measurable_pi_lambda _ (fun j => ?_)
  by_cases hj : j ≤ N
  · simp only [bwl_T, hj, ↓reduceIte]
    exact (X.measurable_D _).sub_const _
  · simp only [bwl_T, hj, ↓reduceIte]
    exact measurable_const

open SupplyChainTheory MeasureTheory in
theorem bwl_eps_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (X : AR1Demand P) (k : ℤ) :
    X.eps k = fun ω => X.D k ω - X.d - X.rho * X.D (k - 1) ω := by
  funext ω
  rw [X.recursion k ω]
  ring

open SupplyChainTheory MeasureTheory in
theorem bwl_eps_meas {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (X : AR1Demand P) (k : ℤ) :
    Measurable (X.eps k) := by
  rw [bwl_eps_eq X k]
  exact (((X.measurable_D k).sub_const _)).sub ((X.measurable_D (k - 1)).const_mul _)

open SupplyChainTheory MeasureTheory ProbabilityTheory in
theorem bwl_eps_symm {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (X : AR1Demand P) (k : ℤ) :
    P.map (fun ω => -X.eps k ω) = P.map (X.eps k) := by
  rw [show (fun ω => -X.eps k ω) = (fun x : ℝ => -x) ∘ X.eps k from rfl,
    ← Measure.map_map measurable_neg (bwl_eps_meas X k), X.eps_law, gaussianReal_map_neg,
    neg_zero]

open MeasureTheory ProbabilityTheory in
theorem bwl_pair_symm {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
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
theorem bwl_window_symm {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : AR1Demand P) (s0 : ℤ) (N : ℕ) :
    P.map (fun ω => -bwl_T X s0 N ω) = P.map (bwl_T X s0 N) := by
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
    have e1 : bwl_T X s0 0 = (fun x : ℝ => fun j : ℕ => if j ≤ 0 then x else 0) ∘
        (fun ω => X.D s0 ω - X.d / (1 - X.rho)) := by
      funext ω j
      by_cases hj : j ≤ 0
      · have : j = 0 := by omega
        subst this
        simp [bwl_T]
      · have hj' : j ≠ 0 := by omega
        simp [bwl_T, hj']
    have e2 : (fun ω => -bwl_T X s0 0 ω) = (fun x : ℝ => fun j : ℕ => if j ≤ 0 then x else 0) ∘
        (fun ω => -(X.D s0 ω - X.d / (1 - X.rho))) := by
      funext ω j
      by_cases hj : j ≤ 0
      · have : j = 0 := by omega
        subst this
        simp [bwl_T]
      · have hj' : j ≠ 0 := by omega
        simp [bwl_T, hj']
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
    have hstep : bwl_T X s0 (N + 1)
        = fun ω => Φ (bwl_T X s0 N ω, X.eps (s0 + ((N + 1 : ℕ) : ℤ)) ω) := by
      funext ω j
      by_cases hj : j = N + 1
      · subst hj
        simp only [bwl_T, Φ, le_refl, ↓reduceIte]
        rw [X.recursion (s0 + ((N + 1 : ℕ) : ℤ)) ω]
        have hidx : s0 + ((N + 1 : ℕ) : ℤ) - 1 = s0 + (N : ℤ) := by push_cast; ring
        rw [hidx]
        have hc1 : X.d / (1 - X.rho) * (1 - X.rho) = X.d := div_mul_cancel₀ _ hρ
        linear_combination (-1 : ℝ) * hc1
      · by_cases hjN : j ≤ N
        · have hj2 : j ≤ N + 1 := by omega
          simp only [bwl_T, Φ, hj, hjN, hj2, ↓reduceIte]
        · have hj2 : ¬ j ≤ N + 1 := by omega
          simp only [bwl_T, Φ, hj, hjN, hj2, ↓reduceIte]
    have hind : IndepFun (bwl_T X s0 N) (X.eps (s0 + ((N + 1 : ℕ) : ℤ))) P := by
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
      have h2 : bwl_T X s0 N = h ∘ fun ω k => X.D (s0 + ((N + 1 : ℕ) : ℤ) - 1 - k) ω := by
        funext ω j
        by_cases hj : j ≤ N
        · simp only [Function.comp, bwl_T, h, hj, ↓reduceIte]
          congr 2
          omega
        · simp only [Function.comp, bwl_T, h, hj, ↓reduceIte]
      rw [h2]
      exact h1
    rw [hstep]
    exact bwl_pair_symm _ _ (bwl_T_meas X s0 N) (bwl_eps_meas X _) hind ih (bwl_eps_symm X _)
      Φ hΦ hΦneg

/-- Reconstruct a path from a centred window. -/
noncomputable def bwl_path (c : ℝ) (s0 : ℤ) (v : ℕ → ℝ) (s : ℤ) : ℝ := c + v (Int.toNat (s - s0))

/-- The covariance integrand as a function of the centred window. -/
noncomputable def bwl_G (C c EB : ℝ) (m : ℕ) (s0 t u : ℤ) (v : ℕ → ℝ) : ℝ :=
  (bwl_path c s0 v u - c) * (bwl_sig C m (bwl_path c s0 v) t - EB)

theorem bwl_G_odd (C c EB : ℝ) (m : ℕ) (hm : 0 < m) (s0 t u : ℤ) (v : ℕ → ℝ) :
    bwl_G C c EB m s0 t u (-v) = - bwl_G C c EB m s0 t u v := by
  have hp : bwl_path c s0 (-v) = fun k => 2 * c - bwl_path c s0 v k := by
    funext k
    simp only [bwl_path, Pi.neg_apply]
    ring
  unfold bwl_G
  rw [hp, bwl_sig_reflect C m hm _ _ t]
  ring

theorem bwl_G_meas (C c EB : ℝ) (m : ℕ) (s0 t u : ℤ) :
    Measurable (bwl_G C c EB m s0 t u) := by
  have hcont : Continuous (bwl_G C c EB m s0 t u) := by
    unfold bwl_G bwl_sig bwl_err bwl_path
    fun_prop
  exact hcont.measurable

open SupplyChainTheory MeasureTheory ProbabilityTheory in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] (X : AR1Demand P) (C : ℝ) (m : ℕ) (hm : 0 < m)
    (t : ℤ) (i : ℕ) (hi1 : 1 ≤ i) (him : i ≤ m) :
    ProbabilityTheory.covariance (X.D (t - i)) (X.sigmaHat C m t) P = 0 := by
  have hDmean : ∀ s, ∫ ω, X.D s ω ∂P = X.d / (1 - X.rho) := by
    intro s
    have h := integral_map (μ := P) (X.measurable_D s).aemeasurable
      (f := fun x : ℝ => x) aestronglyMeasurable_id
    rw [← h, X.stationary s, integral_id_gaussianReal]
  set c := X.d / (1 - X.rho) with hc
  set s0 : ℤ := t - 2 * m - 1 with hs0
  set EB := ∫ ω, X.sigmaHat C m t ω ∂P with hEB
  have hpath : ∀ ω s, s0 ≤ s → s ≤ t - 1 → bwl_path c s0 (bwl_T X s0 (2 * m) ω) s = X.D s ω := by
    intro ω s h1 h2
    have hle : Int.toNat (s - s0) ≤ 2 * m := by omega
    have heq : s0 + ((Int.toNat (s - s0) : ℕ) : ℤ) = s := by omega
    simp only [bwl_path, bwl_T, hle, ↓reduceIte, heq]
    ring
  have hsig : ∀ ω, bwl_sig C m (bwl_path c s0 (bwl_T X s0 (2 * m) ω)) t = X.sigmaHat C m t ω := by
    intro ω
    rw [bwl_sigmaHat_eq]
    exact bwl_sig_congr C m _ _ t (fun k hk1 hk2 => hpath ω k (by omega) (by omega))
  have hint : ∀ ω, (X.D (t - i) ω - c) * (X.sigmaHat C m t ω - EB)
        = bwl_G C c EB m s0 t (t - i) (bwl_T X s0 (2 * m) ω) := by
    intro ω
    unfold bwl_G
    rw [hpath ω (t - i) (by omega) (by omega), hsig ω]
  have hcov : ProbabilityTheory.covariance (X.D (t - i)) (X.sigmaHat C m t) P
        = ∫ ω, bwl_G C c EB m s0 t (t - i) (bwl_T X s0 (2 * m) ω) ∂P := by
    unfold covariance
    rw [hDmean]
    exact integral_congr_ae (Filter.Eventually.of_forall hint)
  have hT := bwl_T_meas X s0 (2 * m)
  have hGm := bwl_G_meas C c EB m s0 t (t - i)
  have h1 : ∫ ω, bwl_G C c EB m s0 t (t - i) (bwl_T X s0 (2 * m) ω) ∂P
      = ∫ v, bwl_G C c EB m s0 t (t - i) v ∂(P.map (bwl_T X s0 (2 * m))) :=
    (integral_map hT.aemeasurable hGm.aestronglyMeasurable).symm
  have h2 : ∫ ω, bwl_G C c EB m s0 t (t - i) (-bwl_T X s0 (2 * m) ω) ∂P
      = ∫ v, bwl_G C c EB m s0 t (t - i) v ∂(P.map (fun ω => -bwl_T X s0 (2 * m) ω)) :=
    (integral_map (φ := fun ω => -bwl_T X s0 (2 * m) ω) hT.neg.aemeasurable
      hGm.aestronglyMeasurable).symm
  rw [bwl_window_symm X s0 (2 * m)] at h2
  have h3 : ∫ ω, bwl_G C c EB m s0 t (t - i) (-bwl_T X s0 (2 * m) ω) ∂P
      = - ∫ ω, bwl_G C c EB m s0 t (t - i) (bwl_T X s0 (2 * m) ω) ∂P := by
    simp_rw [bwl_G_odd C c EB m hm s0 t (t - i)]
    exact integral_neg _
  rw [hcov]
  linarith
