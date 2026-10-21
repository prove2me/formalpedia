-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P42.circularFlow_eikonal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T01:55:13.331894+00:00
-- url     : https://prove2.me/submissions/6d923a51-fa83-40bb-a808-54191fd09b05

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P42
open QAlgorithms.Papers.Independent.Renew46.P42

noncomputable section

open scoped BigOperators

open Filter Set MeasureTheory

-- Reuse the pinned accepted real quadratic form (arbitrary finite real matrices).

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

theorem g65c_cp {d : ℕ} (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) (i : Fin d)
    (hf : DifferentiableAt ℝ f x) :
    cartesianPartial f x i = deriv (fun t : ℝ => f (x + t • Pi.single i 1)) 0 := by
  have hL : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin d) => WithLp.ofLp y)
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ) : EuclideanSpace ℝ (Fin d) →L[ℝ] (Fin d → ℝ))
      (WithLp.toLp 2 x) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).toContinuousLinearMap.hasFDerivAt
  have hf' : HasFDerivAt f (fderiv ℝ f x) (WithLp.ofLp (WithLp.toLp 2 x)) := hf.hasFDerivAt
  have hc := hf'.comp (WithLp.toLp 2 x) hL
  have hline : HasDerivAt (fun t : ℝ => x + t • Pi.single i (1:ℝ)) (Pi.single i 1) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (Pi.single i (1:ℝ))).const_add x
  have h2 := (by simpa using hf.hasFDerivAt : HasFDerivAt f (fderiv ℝ f x) (x + (0:ℝ) • Pi.single i 1)).comp_hasDerivAt (0:ℝ) hline
  rw [show (fun t : ℝ => f (x + t • Pi.single i 1)) = (f ∘ fun t => x + t • Pi.single i 1) from rfl,
    h2.deriv, cartesianPartial, QAlgorithms.Papers.Independent.Dependency50.P20.coordinatePartial]
  simp only
  rw [show (fun y : EuclideanSpace ℝ (Fin d) => f (WithLp.ofLp y)) = f ∘ WithLp.ofLp from rfl, hc.fderiv]
  simp [EuclideanSpace.single]
  congr 1

theorem g65c_cp_const {d : ℕ} (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) (i : Fin d)
    (h : ∀ t : ℝ, f (x + t • Pi.single i 1) = f x) : cartesianPartial f x i = 0 := by
  by_cases hd : DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin d) => f (WithLp.ofLp y)) (WithLp.toLp 2 x)
  · have hf : DifferentiableAt ℝ f x := by
      have h2 : DifferentiableAt ℝ (fun z : Fin d → ℝ => WithLp.toLp 2 z) x :=
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap.differentiableAt
      have := hd.comp x h2
      simpa [Function.comp_def] using this
    rw [g65c_cp f x i hf]
    simp [h]
  · simp [cartesianPartial, QAlgorithms.Papers.Independent.Dependency50.P20.coordinatePartial,
      fderiv_zero_of_not_differentiableAt hd]


theorem g65c_sep (c omega l R' : ℝ) (R : ℝ → ℝ) (z : V3) (hR : HasDerivAt R R' (z 1)) :
    DifferentiableAt ℝ (separatedPhase c omega l R) z ∧
    cartesianPartial (separatedPhase c omega l R) z 0 = omega / c * (-c) ∧
    cartesianPartial (separatedPhase c omega l R) z 1 = omega / c * R' ∧
    cartesianPartial (separatedPhase c omega l R) z 2 = omega / c * l := by
  have hRd := hR.differentiableAt
  have hd : DifferentiableAt ℝ (separatedPhase c omega l R) z := by
    unfold separatedPhase
    have : DifferentiableAt ℝ (fun y : V3 => R (y 1)) z := hRd.comp z (by fun_prop)
    fun_prop
  refine ⟨hd, ?_, ?_, ?_⟩
  · rw [g65c_cp _ _ _ hd]; apply HasDerivAt.deriv
    have H := (((hasDerivAt_id' (0:ℝ)).const_add (z 0)).const_mul (-c)).add_const (l * z 2 + R (z 1)) |>.const_mul (omega / c)
    refine (H.congr_deriv (by ring)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    simp only [separatedPhase]; simp [add_assoc]
  · rw [g65c_cp _ _ _ hd]; apply HasDerivAt.deriv
    have hl : HasDerivAt (fun t : ℝ => z 1 + t) 1 0 := by simpa using (hasDerivAt_id (0:ℝ)).const_add (z 1)
    have hR' : HasDerivAt R R' (z 1 + 0) := by simpa using hR
    have H := ((hR'.comp (0:ℝ) hl).const_add (-c * z 0 + l * z 2)).const_mul (omega / c)
    refine (H.congr_deriv (by ring)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    simp [separatedPhase]
  · rw [g65c_cp _ _ _ hd]; apply HasDerivAt.deriv
    have H := ((((hasDerivAt_id' (0:ℝ)).const_add (z 2)).const_mul l).const_add (-c * z 0) |>.add_const (R (z 1))).const_mul (omega / c)
    refine (H.congr_deriv (by ring)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    simp [separatedPhase]

theorem g65c_symb (c n omega l R' : ℝ) (u : ℝ → ℝ) (R : ℝ → ℝ) (z : V3) (hR : HasDerivAt R R' (z 1))
    (hc : 0 < c) (hz : z 1 ≠ 0) :
    cylindricalSymbol c n u (separatedPhase c omega l R) z = omega ^ 2 * (radialF c n u (z 1) l - R' ^ 2) := by
  obtain ⟨-, h0, h1, h2⟩ := g65c_sep c omega l R' R z hR
  unfold cylindricalSymbol
  rw [h0, h1, h2]
  unfold radialF
  field_simp
  ring
theorem solution (c n omega l sigma rBase : ℝ)
    (u : ℝ → ℝ) (J : Set ℝ) (z : V3)
    (hc : 0 < c) (hn : 1 ≤ n) (ho : omega ≠ 0)
    (hsigma : sigma = 1 ∨ sigma = -1) (hJ : IsOpen J) (hconv : Convex ℝ J)
    (hbase : rBase ∈ J) (hz : z 1 ∈ J) (hreg : ContDiffOn ℝ 1 u J)
    (hpositive : ∀ r ∈ J, 0 < r)
    (hsub : ∀ r ∈ J, |u r| < c)
    (hallowed : ∀ r ∈ J, 0 ≤ radialF c n u r l) :
    (∀ R : ℝ → ℝ, DifferentiableAt ℝ R (z 1) →
      (cylindricalSymbol c n u (separatedPhase c omega l R) z = 0 ↔
        (deriv R (z 1)) ^ 2 = radialF c n u (z 1) l)) ∧
    DifferentiableAt ℝ (circularEikonal c n omega l sigma rBase u) z ∧
    cylindricalSymbol c n u (circularEikonal c n omega l sigma rBase u) z = 0 ∧
    (∀ r : ℝ, radialF c n u r l < 0 → ¬∃ a : ℝ, a ^ 2 = radialF c n u r l) := by


  have hc0 : c ≠ 0 := hc.ne'
  have hrc : ∀ s ∈ J, ContinuousAt (fun a => radialF c n u a l) s := by
    intro s hs
    have hus : ContinuousAt u s := hreg.continuousOn.continuousAt (hJ.mem_nhds hs)
    have hs0 : s ≠ 0 := (hpositive s hs).ne'
    have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs0
    have hcs : c * s ≠ 0 := mul_ne_zero hc0 hs0
    have hD : 1 - u s ^ 2 / c ^ 2 ≠ 0 := by
      have h1 := hsub s hs
      have : u s ^ 2 < c ^ 2 := by
        have := sq_lt_sq' (abs_lt.1 h1).1 (abs_lt.1 h1).2; linarith
      have : u s ^ 2 / c ^ 2 < 1 := by rw [div_lt_one (by positivity)]; exact this
      linarith
    unfold radialF
    fun_prop (disch := assumption)
  have hfJ : ContinuousOn (fun s => Real.sqrt (radialF c n u s l)) J := fun s hs =>
    ((hrc s hs).sqrt).continuousWithinAt
  have hsub' : Set.uIcc rBase (z 1) ⊆ J := (convex_iff_ordConnected.1 hconv).uIcc_subset hbase hz
  have hint : IntervalIntegrable (fun s => Real.sqrt (radialF c n u s l)) MeasureTheory.volume rBase (z 1) :=
    (hfJ.mono hsub').intervalIntegrable
  have hFTC := intervalIntegral.integral_hasDerivAt_right hint (hfJ.stronglyMeasurableAtFilter hJ _ hz)
    (hfJ.continuousAt (hJ.mem_nhds hz))
  set R : ℝ → ℝ := fun r => sigma * ∫ s in rBase..r, Real.sqrt (radialF c n u s l) with hRdef
  have hR : HasDerivAt R (sigma * Real.sqrt (radialF c n u (z 1) l)) (z 1) := hFTC.const_mul sigma
  have heq : circularEikonal c n omega l sigma rBase u = separatedPhase c omega l R := rfl
  have hz0 : z 1 ≠ 0 := (hpositive _ hz).ne'
  have hsq : sigma ^ 2 = 1 := by rcases hsigma with h | h <;> subst h <;> norm_num
  refine ⟨fun R hR => ?_, ?_, ?_, ?_⟩
  · rw [g65c_symb c n omega l _ u R z hR.hasDerivAt hc hz0]
    constructor
    · intro h
      rcases mul_eq_zero.1 h with h | h
      · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h) ho
      · linarith
    · intro h; rw [h]; ring
  · rw [heq]; exact (g65c_sep c omega l _ R z hR).1
  · rw [heq, g65c_symb c n omega l _ u R z hR hc hz0, mul_pow, Real.sq_sqrt (hallowed _ hz), hsq]
    ring
  · rintro r hr ⟨a, ha⟩
    nlinarith [sq_nonneg a]
