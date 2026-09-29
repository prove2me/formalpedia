-- Prove2me | solution 1 for PeriodPair.exists_forall_apply_toPoint_eq_toPoint_mul_of_mem_rationalHomSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/e6def3dd-bad9-5dc7-9c17-0de19238ec42

import Mathlib
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_PeriodPair_Uniformization
import Theorems.Thm_PeriodPair_isUniformization_toPoint
import Theorems.Thm_PeriodPair_discriminant_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PeriodPair_exists_forall_apply_toPoint_eq_toPoint_mul_of_mem_rationalHomSet

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Complex Filter Set Polynomial
p2m_open_scoped "PeriodPair P2MW.S_PeriodPair_exists_forall_apply_toPoint_eq_toPoint_mul_of_mem_rationalHomSet.PeriodPair Topology Polynomial.Bivariate"

namespace PeriodPair
p2m_export "PeriodPair" "differentiableOn_derivWeierstrassP isClosed_lattice lattice differentiableOn_weierstrassP g₃ deriv_weierstrassP g₂ analyticOnNhd_weierstrassP weierstrassCurve weierstrassCurve_a₁ weierstrassCurve_a₂ weierstrassCurve_a₃ weierstrassCurve_a₄ weierstrassCurve_a₆ equation_weierstrassP DiscriminantNeZero toPoint toPoint_of_mem toPoint_zero toPoint_of_notMem isUniformization_toPoint discriminant_ne_zero"
namespace RatToMul
p2m_open "PeriodPair"

section Param

variable (L : PeriodPair) (hL : L.DiscriminantNeZero)

noncomputable def T : ℂ →+ L.weierstrassCurve.toAffine.Point :=
  AddMonoidHom.mk' (L.toPoint hL) (PeriodPair.isUniformization_toPoint L hL).1

theorem T_apply (z : ℂ) : T L hL z = L.toPoint hL z := rfl

theorem T_surjective : Function.Surjective (T L hL) :=
  (PeriodPair.isUniformization_toPoint L hL).2.1

theorem T_eq_zero_iff {z : ℂ} : T L hL z = 0 ↔ z ∈ L.lattice :=
  ⟨(PeriodPair.isUniformization_toPoint L hL).2.2 z, fun h => L.toPoint_of_mem hL h⟩

theorem T_natCast_mul (n : ℕ) (z : ℂ) : T L hL (n * z) = n • T L hL z := by
  rw [← nsmul_eq_mul, map_nsmul]

end Param

theorem addMonoidHom_eq_zero_of_ball {A : Type*} [AddCommGroup A] (φ : ℂ →+ A) {c : ℂ} {r : ℝ}
    (hr : 0 < r) (h : ∀ z ∈ Metric.ball c r, φ z = 0) : φ = 0 := by
  have h0 : ∀ w : ℂ, ‖w‖ < r → φ w = 0 := by
    intro w hw
    have h1 := h (c + w) (by simpa [Metric.mem_ball, dist_eq_norm] using hw)
    have h2 := h c (Metric.mem_ball_self hr)
    rw [map_add, h2, zero_add] at h1
    exact h1
  ext z
  obtain ⟨N, hN⟩ := exists_nat_gt (‖z‖ / r)
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (div_nonneg (norm_nonneg _) hr.le) hN
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hNpos.ne'
  have hz : z = (N : ℂ) * (z / N) := by field_simp
  have hsmall : ‖z / (N : ℂ)‖ < r := by
    rw [norm_div, Complex.norm_natCast, div_lt_iff₀ hNpos]
    calc ‖z‖ = ‖z‖ / r * r := by field_simp
      _ < N * r := by gcongr
      _ = r * N := by ring
  rw [hz, ← nsmul_eq_mul, map_nsmul, h0 _ hsmall, smul_zero, AddMonoidHom.zero_apply]

theorem addMonoidHom_eq_of_ball {A : Type*} [AddCommGroup A] (φ : ℂ →+ A) (ψ : ℂ →+ A) (c : ℂ)
    {r : ℝ} (hr : 0 < r) (h : ∀ z : ℂ, ‖z‖ < r → φ z = ψ (c * z)) (z : ℂ) : φ z = ψ (c * z) := by
  have : φ - ψ.comp (AddMonoidHom.mulLeft c) = 0 := by
    refine addMonoidHom_eq_zero_of_ball _ (c := 0) hr fun w hw => ?_
    rw [Metric.mem_ball, dist_zero_right] at hw
    simp [h w hw]
  have hz := congrArg (fun f : ℂ →+ A => f z) this
  simpa [sub_eq_zero] using hz

section Analytic

variable (L : PeriodPair)

theorem differentiableAt_evalEval {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z)
    (hg : DifferentiableAt ℂ g z) (p : ℂ[X][Y]) :
    DifferentiableAt ℂ (fun w => (p.evalEval (f w) (g w))) z := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [evalEval_add]
    exact hp.add hq
  | monomial n c =>
    have hm : ∀ w, (monomial n c : ℂ[X][Y]).evalEval (f w) (g w) = c.eval (f w) * (g w) ^ n := by
      intro w
      rw [← C_mul_X_pow_eq_monomial, evalEval_mul, evalEval_pow, evalEval_C, evalEval_X]
    simp only [hm]
    refine DifferentiableAt.mul ?_ (hg.pow n)

    have hc : DifferentiableAt ℂ (fun x : ℂ => c.eval x) (f z) := by
      have := Polynomial.differentiableAt_aeval (𝕜 := ℂ) (R := ℂ) (x := f z) c
      simpa only [Polynomial.coe_aeval_eq_eval] using this
    exact hc.comp z hf

theorem evalEvalBC_self (p : ℂ[X][Y]) (x y : ℂ) :
    WeierstrassCurve.evalEvalBC ℂ (F := ℂ) p x y = p.evalEval x y := by
  simp only [WeierstrassCurve.evalEvalBC, Algebra.algebraMap_self, Polynomial.mapRingHom_id,
    Polynomial.map_id]

theorem differentiableAt_weierstrassP {z : ℂ} (hz : z ∉ L.lattice) : DifferentiableAt ℂ ℘[L] z :=
  L.differentiableOn_weierstrassP.differentiableAt (L.isClosed_lattice.isOpen_compl.mem_nhds hz)

theorem differentiableAt_derivWeierstrassP {z : ℂ} (hz : z ∉ L.lattice) :
    DifferentiableAt ℂ ℘'[L] z :=
  L.differentiableOn_derivWeierstrassP.differentiableAt (L.isClosed_lattice.isOpen_compl.mem_nhds hz)

theorem differentiableAt_half_derivWeierstrassP {z : ℂ} (hz : z ∉ L.lattice) :
    DifferentiableAt ℂ (fun w => ℘'[L] w / 2) z :=
  (differentiableAt_derivWeierstrassP L hz).div_const 2

theorem differentiableAt_evalEval_weierstrassP {z : ℂ} (hz : z ∉ L.lattice) (p : ℂ[X][Y]) :
    DifferentiableAt ℂ (fun w => p.evalEval (℘[L] w) (℘'[L] w / 2)) z :=
  differentiableAt_evalEval (differentiableAt_weierstrassP L hz)
    (differentiableAt_half_derivWeierstrassP L hz) p

theorem hasStrictDerivAt_weierstrassP {z : ℂ} (hz : z ∉ L.lattice) :
    HasStrictDerivAt ℘[L] (℘'[L] z) z := by
  have ha : AnalyticAt ℂ ℘[L] z := L.analyticOnNhd_weierstrassP z hz
  have := ha.hasStrictDerivAt
  rwa [L.deriv_weierstrassP] at this

theorem isOpen_good {B : Set ℂ} (hB : B.Finite) : IsOpen {z : ℂ | z ∉ L.lattice ∧ ℘[L] z ∉ B} := by
  have h1 : IsOpen ((L.lattice : Set ℂ)ᶜ) := L.isClosed_lattice.isOpen_compl
  have h2 := L.differentiableOn_weierstrassP.continuousOn.isOpen_inter_preimage h1 hB.isClosed.isOpen_compl
  convert h2 using 1
  rfl

end Analytic

section Setup

variable {L L' : PeriodPair} {hL : L.DiscriminantNeZero} {hL' : L'.DiscriminantNeZero}
  {α : L.weierstrassCurve.toAffine.Point →+ L'.weierstrassCurve.toAffine.Point}
  {nX dX nY dY : ℂ[X][Y]} {B : Set ℂ}

def Rep (L L' : PeriodPair) (α : L.weierstrassCurve.toAffine.Point →+ L'.weierstrassCurve.toAffine.Point)
    (nX dX nY dY : ℂ[X][Y]) (B : Set ℂ) : Prop :=
  ∀ (x y : ℂ) (h : L.weierstrassCurve.toAffine.Nonsingular x y), x ∉ B →
    dX.evalEval x y ≠ 0 ∧ dY.evalEval x y ≠ 0 ∧
      ∃ h', α (.some x y h) = .some (nX.evalEval x y / dX.evalEval x y)
        (nY.evalEval x y / dY.evalEval x y) h'

theorem rep_of_isRationallyRepresented
    (h : ∀ (x y : ℂ) (h : (L.weierstrassCurve.baseChange ℂ).toAffine.Nonsingular x y), x ∉ B →
      WeierstrassCurve.evalEvalBC ℂ dX x y ≠ 0 ∧ WeierstrassCurve.evalEvalBC ℂ dY x y ≠ 0 ∧
        ∃ h', α (.some x y h) = .some
          (WeierstrassCurve.evalEvalBC ℂ nX x y / WeierstrassCurve.evalEvalBC ℂ dX x y)
          (WeierstrassCurve.evalEvalBC ℂ nY x y / WeierstrassCurve.evalEvalBC ℂ dY x y) h') :
    Rep L L' α nX dX nY dY B := by
  intro x y hxy hx
  have := h x y hxy hx
  simp only [evalEvalBC_self] at this
  exact this

variable (L) in

noncomputable def U (nX dX : ℂ[X][Y]) (z : ℂ) : ℂ :=
  nX.evalEval (℘[L] z) (℘'[L] z / 2) / dX.evalEval (℘[L] z) (℘'[L] z / 2)

theorem alpha_T_eq (hrep : Rep L L' α nX dX nY dY B) {z : ℂ} (hz : z ∉ L.lattice) (hzB : ℘[L] z ∉ B) :
    ∃ h', α (T L hL z) = .some (U L nX dX z) (U L nY dY z) h' := by
  obtain ⟨-, -, h', hP⟩ := hrep (℘[L] z) (℘'[L] z / 2)
    ((WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero
      hL.weierstrassCurve_Δ_ne_zero).mp (L.equation_weierstrassP hz)) hzB
  refine ⟨h', ?_⟩
  rw [T_apply, L.toPoint_of_notMem hL hz]
  exact hP

theorem differentiableAt_U (hrep : Rep L L' α nX dX nY dY B) {z : ℂ} (hz : z ∉ L.lattice)
    (hzB : ℘[L] z ∉ B) : DifferentiableAt ℂ (U L nX dX) z ∧ DifferentiableAt ℂ (U L nY dY) z := by
  have hL := PeriodPair.discriminant_ne_zero L
  obtain ⟨hdX, hdY, -⟩ := hrep (℘[L] z) (℘'[L] z / 2)
    ((WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero
      hL.weierstrassCurve_Δ_ne_zero).mp (L.equation_weierstrassP hz)) hzB
  exact ⟨(differentiableAt_evalEval_weierstrassP L hz nX).div
      (differentiableAt_evalEval_weierstrassP L hz dX) hdX,
    (differentiableAt_evalEval_weierstrassP L hz nY).div
      (differentiableAt_evalEval_weierstrassP L hz dY) hdY⟩

theorem equation_iff' (M : PeriodPair) (x y : ℂ) :
    M.weierstrassCurve.toAffine.Equation x y ↔ y ^ 2 = x ^ 3 - M.g₂ / 4 * x - M.g₃ / 4 := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [WeierstrassCurve.toAffine, weierstrassCurve_a₁, weierstrassCurve_a₂, weierstrassCurve_a₃,
    weierstrassCurve_a₄, weierstrassCurve_a₆]
  constructor <;> intro h <;> linear_combination h

theorem exists_good (hrep : Rep L L' α nX dX nY dY B) (hB : B.Finite) :
    ∃ z₀ : ℂ, z₀ ∉ L.lattice ∧ ℘[L] z₀ ∉ B ∧ U L nY dY z₀ ≠ 0 := by
  classical
  have hL := PeriodPair.discriminant_ne_zero L

  have hex : ∃ z : ℂ, z ∉ L.lattice ∧ ℘[L] z ∉ B := by
    obtain ⟨x, hx⟩ := (hB.infinite_compl).nonempty
    have hdeg : (L.weierstrassCurve.toAffine.polynomial.map (evalRingHom x)).degree ≠ 0 := by
      rw [WeierstrassCurve.Affine.monic_polynomial.degree_map, WeierstrassCurve.Affine.degree_polynomial]
      norm_num
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_root _ hdeg
    have heq : L.weierstrassCurve.toAffine.Equation x y := by
      rw [IsRoot.def, map_evalRingHom_eval] at hy; exact hy
    have hns : L.weierstrassCurve.toAffine.Nonsingular x y :=
      (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero
        hL.weierstrassCurve_Δ_ne_zero).mp heq
    obtain ⟨z, hz⟩ := T_surjective L hL (.some x y hns)
    have hzL : z ∉ L.lattice := by
      intro hmem
      rw [T_apply, L.toPoint_of_mem hL hmem] at hz
      cases hz
    refine ⟨z, hzL, ?_⟩
    rw [T_apply, L.toPoint_of_notMem hL hzL] at hz
    rw [(WeierstrassCurve.Affine.Point.some.inj hz).1]
    exact hx
  obtain ⟨z₀, hz₀, hz₀B⟩ := hex
  by_contra hcon
  push Not at hcon

  have hopen := isOpen_good L hB
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen z₀ ⟨hz₀, hz₀B⟩
  set φ : ℂ →+ L'.weierstrassCurve.toAffine.Point := α.comp (T L hL) with hφ
  have hvan : ∀ w ∈ Metric.ball (2 * z₀) (2 * r), φ w = 0 := by
    intro w hw
    have hw2 : w / 2 ∈ Metric.ball z₀ r := by
      rw [Metric.mem_ball, dist_eq_norm] at hw ⊢
      have : w / 2 - z₀ = (w - 2 * z₀) / 2 := by ring
      rw [this, norm_div, Complex.norm_ofNat]
      linarith
    obtain ⟨hwL, hwB⟩ := hball hw2
    obtain ⟨h', hP⟩ := alpha_T_eq (hL := hL) hrep hwL hwB
    have hV0 : U L nY dY (w / 2) = 0 := hcon (w / 2) hwL hwB
    have h2 : φ (w / 2) + φ (w / 2) = 0 := by
      simp only [hφ, AddMonoidHom.coe_comp, Function.comp_apply]
      rw [hP]
      refine WeierstrassCurve.Affine.Point.add_of_Y_eq rfl ?_
      simp only [WeierstrassCurve.Affine.negY, WeierstrassCurve.toAffine, weierstrassCurve_a₁,
        weierstrassCurve_a₃, hV0]
      ring
    have : w = w / 2 + w / 2 := by ring
    rw [this, map_add, h2]
  have hφ0 : φ = 0 := addMonoidHom_eq_zero_of_ball φ (by positivity) hvan
  obtain ⟨h', hP⟩ := alpha_T_eq (hL := hL) hrep hz₀ hz₀B
  have : φ z₀ = 0 := by rw [hφ0, AddMonoidHom.zero_apply]
  simp only [hφ, AddMonoidHom.coe_comp, Function.comp_apply, hP] at this
  cases this

end Setup

theorem some_eq_some {W : WeierstrassCurve.Affine ℂ} {x₁ y₁ x₂ y₂ : ℂ} (hx : x₁ = x₂) (hy : y₁ = y₂)
    {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂} :
    WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ = .some x₂ y₂ h₂ := by
  subst hx hy; rfl

theorem exists_norm_lt_imp_eq_zero (M : PeriodPair) :
    ∃ ρ > 0, ∀ l ∈ M.lattice, ‖l‖ < ρ → l = 0 := by
  have hd : DiscreteTopology M.lattice := inferInstance
  have hopen : IsOpen ({0} : Set M.lattice) := isOpen_discrete _
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen 0 (Set.mem_singleton 0)
  refine ⟨ε, hε, fun l hl hnorm => ?_⟩
  have hmem : (⟨l, hl⟩ : M.lattice) ∈ Metric.ball (0 : M.lattice) ε := by
    rw [Metric.mem_ball, Subtype.dist_eq]
    simpa using hnorm
  have := hball hmem
  rw [Set.mem_singleton_iff] at this
  exact congrArg Subtype.val this

section Lift

variable {L L' : PeriodPair} (hL : L.DiscriminantNeZero) (hL' : L'.DiscriminantNeZero)
  {α : L.weierstrassCurve.toAffine.Point →+ L'.weierstrassCurve.toAffine.Point}
  {nX dX nY dY : ℂ[X][Y]} {B : Set ℂ}

theorem local_lift (hrep : Rep L L' α nX dX nY dY B) (hB : B.Finite) {z₀ : ℂ}
    (hz₀ : z₀ ∉ L.lattice) (hz₀B : ℘[L] z₀ ∉ B) (hV₀ : U L nY dY z₀ ≠ 0) :
    ∃ F : ℂ → ℂ, (∀ᶠ z in 𝓝 z₀, α (T L hL z) = T L' hL' (F z)) ∧
      (∀ᶠ z in 𝓝 z₀, DifferentiableAt ℂ F z) := by

  obtain ⟨h₀', hP₀⟩ := alpha_T_eq (hL := hL) hrep hz₀ hz₀B
  obtain ⟨w₀, hw₀⟩ := T_surjective L' hL' (.some (U L nX dX z₀) (U L nY dY z₀) h₀')
  have hw₀L : w₀ ∉ L'.lattice := by
    intro hmem
    rw [T_apply, L'.toPoint_of_mem hL' hmem] at hw₀
    cases hw₀
  have hcoord : ℘[L'] w₀ = U L nX dX z₀ ∧ ℘'[L'] w₀ / 2 = U L nY dY z₀ := by
    rw [T_apply, L'.toPoint_of_notMem hL' hw₀L] at hw₀
    obtain ⟨h1, h2⟩ := WeierstrassCurve.Affine.Point.some.inj hw₀
    exact ⟨h1, h2⟩

  have hP : HasStrictDerivAt ℘[L'] (℘'[L'] w₀) w₀ := hasStrictDerivAt_weierstrassP L' hw₀L
  have hne : ℘'[L'] w₀ ≠ 0 := by
    intro h0; apply hV₀; rw [← hcoord.2, h0, zero_div]
  set g : ℂ → ℂ := HasStrictDerivAt.localInverse ℘[L'] _ w₀ hP hne with hg
  have L1 : ∀ᶠ x in 𝓝 w₀, g (℘[L'] x) = x := hP.eventually_left_inverse hne
  have R1 : ∀ᶠ u in 𝓝 (℘[L'] w₀), ℘[L'] (g u) = u := hP.eventually_right_inverse hne
  have hg' : HasStrictDerivAt g (℘'[L'] w₀)⁻¹ (℘[L'] w₀) := hP.to_localInverse hne
  have gc : ContinuousAt g (℘[L'] w₀) := hg'.hasDerivAt.continuousAt
  have g0 : g (℘[L'] w₀) = w₀ := L1.self_of_nhds

  have Dg : ∀ᶠ u in 𝓝 (℘[L'] w₀), DifferentiableAt ℂ g u := by
    have hsrc : ∀ᶠ x in 𝓝 w₀, DifferentiableAt ℂ g (℘[L'] x) := by
      have e1 : ∀ᶠ x in 𝓝 w₀, x ∉ L'.lattice := L'.isClosed_lattice.isOpen_compl.mem_nhds hw₀L
      have e2 : ∀ᶠ x in 𝓝 w₀, ℘'[L'] x ≠ 0 :=
        (differentiableAt_derivWeierstrassP L' hw₀L).continuousAt.eventually_ne hne
      have e3 : ∀ᶠ x in 𝓝 w₀, ∀ᶠ x' in 𝓝 x, g (℘[L'] x') = x' := L1.eventually_nhds
      filter_upwards [e1, e2, e3] with x hx1 hx2 hx3
      exact ((hasStrictDerivAt_weierstrassP L' hx1).to_local_left_inverse hx2 hx3).hasDerivAt.differentiableAt
    have ht : Tendsto g (𝓝 (℘[L'] w₀)) (𝓝 w₀) := by
      have := gc.tendsto
      rwa [g0] at this
    have h1 : ∀ᶠ u in 𝓝 (℘[L'] w₀), DifferentiableAt ℂ g (℘[L'] (g u)) := ht.eventually hsrc
    filter_upwards [h1, R1] with u hu1 hu2
    rwa [hu2] at hu1

  set F : ℂ → ℂ := fun z => g (U L nX dX z) with hF
  have hUdiff := (differentiableAt_U (L' := L') hrep hz₀ hz₀B).1
  have hVdiff := (differentiableAt_U (L' := L') hrep hz₀ hz₀B).2
  have hUcont : ContinuousAt (U L nX dX) z₀ := hUdiff.continuousAt
  have hUz₀ : U L nX dX z₀ = ℘[L'] w₀ := hcoord.1.symm
  have hUt : Tendsto (U L nX dX) (𝓝 z₀) (𝓝 (℘[L'] w₀)) := by
    have := hUcont.tendsto
    rwa [hUz₀] at this
  have hFz₀ : F z₀ = w₀ := by simp only [hF]; rw [hUz₀, g0]
  have hFcont : ContinuousAt F z₀ := by
    have h1 : ContinuousAt g (U L nX dX z₀) := by rw [hUz₀]; exact gc
    exact ContinuousAt.comp (f := U L nX dX) h1 hUcont

  have ev_good : ∀ᶠ z in 𝓝 z₀, z ∉ L.lattice ∧ ℘[L] z ∉ B :=
    (isOpen_good L hB).mem_nhds ⟨hz₀, hz₀B⟩
  have ev_FΛ : ∀ᶠ z in 𝓝 z₀, F z ∉ L'.lattice := by
    have : ((L'.lattice : Set ℂ)ᶜ) ∈ 𝓝 (F z₀) := by
      rw [hFz₀]; exact L'.isClosed_lattice.isOpen_compl.mem_nhds hw₀L
    exact hFcont.preimage_mem_nhds this
  have ev_PF : ∀ᶠ z in 𝓝 z₀, ℘[L'] (F z) = U L nX dX z := hUt.eventually R1
  have ev_Fdiff : ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℂ F z := by
    have h1 : ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℂ g (U L nX dX z) := hUt.eventually Dg
    filter_upwards [h1, ev_good] with z hz1 hz2
    exact hz1.comp z (differentiableAt_U (L' := L') hrep hz2.1 hz2.2).1

  have ev_V : ∀ᶠ z in 𝓝 z₀, U L nY dY z = ℘'[L'] (F z) / 2 := by
    have hS : ContinuousAt (fun z => U L nY dY z + ℘'[L'] (F z) / 2) z₀ := by
      refine hVdiff.continuousAt.add ?_
      have h1 : ContinuousAt ℘'[L'] (F z₀) := by
        rw [hFz₀]; exact (differentiableAt_derivWeierstrassP L' hw₀L).continuousAt
      exact (ContinuousAt.comp (f := F) h1 hFcont).div_const 2
    have hS0 : U L nY dY z₀ + ℘'[L'] (F z₀) / 2 ≠ 0 := by
      rw [hFz₀, hcoord.2]
      intro h
      apply hV₀
      linear_combination h / 2
    have ev_S : ∀ᶠ z in 𝓝 z₀, U L nY dY z + ℘'[L'] (F z) / 2 ≠ 0 := hS.eventually_ne hS0
    filter_upwards [ev_S, ev_good, ev_FΛ, ev_PF] with z hzS hzg hzF hzP
    obtain ⟨h', -⟩ := alpha_T_eq (hL := hL) hrep hzg.1 hzg.2
    have e1 := (equation_iff' L' _ _).mp h'.1
    have e2 := (equation_iff' L' _ _).mp (L'.equation_weierstrassP hzF)
    rw [hzP] at e2
    have hprod : (U L nY dY z - ℘'[L'] (F z) / 2) * (U L nY dY z + ℘'[L'] (F z) / 2) = 0 := by
      linear_combination e1 - e2
    rcases mul_eq_zero.mp hprod with h | h
    · linear_combination h
    · exact absurd h hzS
  refine ⟨F, ?_, ev_Fdiff⟩
  filter_upwards [ev_good, ev_FΛ, ev_PF, ev_V] with z hzg hzF hzP hzV
  obtain ⟨h', hP'⟩ := alpha_T_eq (hL := hL) hrep hzg.1 hzg.2
  rw [hP', T_apply, L'.toPoint_of_notMem hL' hzF]
  exact some_eq_some hzP.symm hzV

theorem linear_of_local_lift (F : ℂ → ℂ) {z₀ : ℂ}
    (hlift : ∀ᶠ z in 𝓝 z₀, α (T L hL z) = T L' hL' (F z))
    (hdiff : ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℂ F z) :
    ∃ a : ℂ, ∀ z, α (T L hL z) = T L' hL' (a * z) := by
  set f : ℂ → ℂ := fun h => F (z₀ + h) - F z₀ with hf
  have hsh : Tendsto (fun h : ℂ => z₀ + h) (𝓝 0) (𝓝 z₀) := by
    have := ((continuous_const_add z₀).tendsto (0 : ℂ))
    rwa [add_zero] at this

  have E5 : ∀ᶠ h in 𝓝 (0 : ℂ), α (T L hL h) = T L' hL' (f h) := by
    have h1 : ∀ᶠ h in 𝓝 (0 : ℂ), α (T L hL (z₀ + h)) = T L' hL' (F (z₀ + h)) := hsh.eventually hlift
    have h0 : α (T L hL z₀) = T L' hL' (F z₀) := hlift.self_of_nhds
    filter_upwards [h1] with h hh
    have e : T L hL h = T L hL (z₀ + h) - T L hL z₀ := by rw [map_add]; abel
    rw [e, map_sub, hh, h0, hf]
    simp only [map_sub]
  have Ed : ∀ᶠ h in 𝓝 (0 : ℂ), DifferentiableAt ℂ f h := by
    have h1 : ∀ᶠ h in 𝓝 (0 : ℂ), DifferentiableAt ℂ F (z₀ + h) := hsh.eventually hdiff
    filter_upwards [h1] with h hh
    have : DifferentiableAt ℂ (fun h => F (z₀ + h)) h :=
      hh.comp h ((differentiableAt_const z₀).add differentiableAt_id)
    exact this.sub_const _
  have f0 : f 0 = 0 := by simp [hf]

  obtain ⟨ρ, hρ, hdisc⟩ := exists_norm_lt_imp_eq_zero L'
  have E6 : ∀ᶠ p in 𝓝 ((0 : ℂ), (0 : ℂ)), f (p.1 + p.2) = f p.1 + f p.2 := by
    have t1 : Tendsto (fun p : ℂ × ℂ => p.1) (𝓝 ((0 : ℂ), (0 : ℂ))) (𝓝 0) := continuousAt_fst.tendsto
    have t2 : Tendsto (fun p : ℂ × ℂ => p.2) (𝓝 ((0 : ℂ), (0 : ℂ))) (𝓝 0) := continuousAt_snd.tendsto
    have t3 : Tendsto (fun p : ℂ × ℂ => p.1 + p.2) (𝓝 ((0 : ℂ), (0 : ℂ))) (𝓝 0) := by
      have := (continuous_add (M := ℂ)).tendsto ((0 : ℂ), (0 : ℂ))
      rwa [add_zero] at this
    have hmem : ∀ᶠ p in 𝓝 ((0 : ℂ), (0 : ℂ)), f (p.1 + p.2) - f p.1 - f p.2 ∈ L'.lattice := by
      filter_upwards [t1.eventually E5, t2.eventually E5, t3.eventually E5] with p h1 h2 h3
      rw [← T_eq_zero_iff L' hL', map_sub, map_sub, ← h1, ← h2, ← h3, map_add, map_add]
      abel
    have fc : ContinuousAt f 0 := (Ed.self_of_nhds).continuousAt
    have hcont : ContinuousAt (fun p : ℂ × ℂ => f (p.1 + p.2) - f p.1 - f p.2) ((0 : ℂ), (0 : ℂ)) := by
      have c3 : ContinuousAt (fun p : ℂ × ℂ => f (p.1 + p.2)) ((0 : ℂ), (0 : ℂ)) :=
        fc.comp_of_eq (continuous_add.continuousAt) (by simp)
      have c1 : ContinuousAt (fun p : ℂ × ℂ => f p.1) ((0 : ℂ), (0 : ℂ)) :=
        fc.comp_of_eq continuousAt_fst rfl
      have c2 : ContinuousAt (fun p : ℂ × ℂ => f p.2) ((0 : ℂ), (0 : ℂ)) :=
        fc.comp_of_eq continuousAt_snd rfl
      exact (c3.sub c1).sub c2
    have hsmall : ∀ᶠ p in 𝓝 ((0 : ℂ), (0 : ℂ)), ‖f (p.1 + p.2) - f p.1 - f p.2‖ < ρ := by
      have ht := hcont.tendsto
      simp only [add_zero, f0, sub_self] at ht
      have := ht.eventually (Metric.ball_mem_nhds (0 : ℂ) hρ)
      filter_upwards [this] with p hp
      simpa using hp
    filter_upwards [hmem, hsmall] with p h1 h2
    have := hdisc _ h1 h2
    linear_combination this
  have E6' : ∀ᶠ h in 𝓝 (0 : ℂ), ∀ᶠ ε in 𝓝 (0 : ℂ), f (h + ε) = f h + f ε := by
    rw [nhds_prod_eq] at E6
    exact E6.curry

  set c := deriv f 0 with hc
  have E7 : ∀ᶠ h in 𝓝 (0 : ℂ), DifferentiableAt ℂ f h ∧ deriv f h = c := by
    have hd0 : HasDerivAt f c 0 := (Ed.self_of_nhds).hasDerivAt
    filter_upwards [Ed, E6'] with h hdh hadd
    refine ⟨hdh, ?_⟩
    have h1 : HasDerivAt (fun ε => f (h + ε)) (deriv f h) 0 := by
      have h' : HasDerivAt f (deriv f h) (h + 0) := by rw [add_zero]; exact hdh.hasDerivAt
      exact h'.comp_const_add h 0
    have h2 : HasDerivAt (fun ε => f h + f ε) c 0 := hd0.const_add (f h)
    have h3 : HasDerivAt (fun ε => f (h + ε)) c 0 :=
      h2.congr_of_eventuallyEq (hadd.mono fun ε hε => hε)
    exact h1.unique h3
  obtain ⟨δ, hδ, hballδ⟩ := Metric.eventually_nhds_iff_ball.mp E7
  have hlin : ∀ h ∈ Metric.ball (0 : ℂ) δ, f h = c * h := by
    intro h hh
    have hdo : DifferentiableOn ℂ (fun h => f h - c * h) (Metric.ball (0 : ℂ) δ) := fun x hx =>
      (((hballδ x hx).1).sub (differentiableAt_id.const_mul c)).differentiableWithinAt
    have hder : Set.EqOn (deriv (fun h => f h - c * h)) 0 (Metric.ball (0 : ℂ) δ) := by
      intro x hx
      have hfx := (hballδ x hx).1
      have hd : HasDerivAt (fun h => f h - c * h) (deriv f x - c) x := by
        have := hfx.hasDerivAt.sub ((hasDerivAt_id x).const_mul c)
        simp at this
        exact this
      rw [Pi.zero_apply, hd.deriv, (hballδ x hx).2, sub_self]
    have key := Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) δ).isPreconnected
      hdo hder hh (Metric.mem_ball_self hδ)
    simp only [f0, mul_zero, sub_zero] at key
    linear_combination key

  obtain ⟨δ₅, hδ₅, hball₅⟩ := Metric.eventually_nhds_iff_ball.mp E5
  refine ⟨c, addMonoidHom_eq_of_ball (α.comp (T L hL)) (T L' hL') c (lt_min hδ hδ₅) fun z hz => ?_⟩
  have hz1 : z ∈ Metric.ball (0 : ℂ) δ := by
    rw [Metric.mem_ball, dist_zero_right]; exact lt_of_lt_of_le hz (min_le_left _ _)
  have hz2 : z ∈ Metric.ball (0 : ℂ) δ₅ := by
    rw [Metric.mem_ball, dist_zero_right]; exact lt_of_lt_of_le hz (min_le_right _ _)
  rw [AddMonoidHom.coe_comp, Function.comp_apply, hball₅ z hz2, hlin z hz1]

end Lift

theorem exists_mul (L L' : PeriodPair) (hL : L.DiscriminantNeZero) (hL' : L'.DiscriminantNeZero)
    {α : L.weierstrassCurve.toAffine.Point →+ L'.weierstrassCurve.toAffine.Point}
    (hα : α ∈ WeierstrassCurve.rationalHomSet ℂ L.weierstrassCurve L'.weierstrassCurve) :
    ∃ a : ℂ, ∀ z : ℂ, α (L.toPoint hL z) = L'.toPoint hL' (a * z) := by
  rcases hα with h0 | ⟨nX, dX, nY, dY, B, hB, hrep⟩
  · refine ⟨0, fun z => ?_⟩
    rw [h0, zero_mul, L'.toPoint_zero]
    rfl
  have hrep' : Rep L L' α nX dX nY dY B := rep_of_isRationallyRepresented hrep
  obtain ⟨z₀, hz₀, hz₀B, hV₀⟩ := exists_good (L' := L') hrep' hB
  obtain ⟨F, hlift, hdiff⟩ := local_lift hL hL' hrep' hB hz₀ hz₀B hV₀
  obtain ⟨a, ha⟩ := linear_of_local_lift hL hL' F hlift hdiff
  exact ⟨a, fun z => ha z⟩

end PeriodPair.RatToMul

open PeriodPair.RatToMul in
theorem solution (L L' : PeriodPair) (hL : L.DiscriminantNeZero) (hL' : L'.DiscriminantNeZero) {α : L.weierstrassCurve.toAffine.Point →+ L'.weierstrassCurve.toAffine.Point} (hα : α ∈ WeierstrassCurve.rationalHomSet ℂ L.weierstrassCurve L'.weierstrassCurve) : ∃ a : ℂ, ∀ z : ℂ, α (L.toPoint hL z) = L'.toPoint hL' (a * z) :=
  exists_mul L L' hL hL' hα

end S_PeriodPair_exists_forall_apply_toPoint_eq_toPoint_mul_of_mem_rationalHomSet
end P2MW
export P2MW.S_PeriodPair_exists_forall_apply_toPoint_eq_toPoint_mul_of_mem_rationalHomSet (solution)
