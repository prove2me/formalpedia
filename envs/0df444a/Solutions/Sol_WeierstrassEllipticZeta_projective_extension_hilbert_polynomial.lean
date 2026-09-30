-- Prove2me | solution 1 for WeierstrassEllipticZeta.projective_extension_hilbert_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-24T06:31:32.154552+00:00
-- url     : https://prove2.me/submissions/d73f4f89-1267-48fd-bdcb-8fd9de537563

import Definitions.Def_WeierstrassEllipticZeta_FirstChartSections
import Mathlib
import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.LinearCombination
import Definitions.Def_WeierstrassEllipticZeta_Defs
import Mathlib.Topology.Order.Compact
import Definitions.Def_TranscendenceTheory_GraphQuotientExtension
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_WeierstrassEllipticZeta_FirstCubicChartBase
import Mathlib.Tactic
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionFiberModel
import Mathlib.Analysis.Analytic.Polynomial
import Definitions.Def_PhilipponMultiplicity_Geometry
import Definitions.Def_PhilipponMultiplicity_Degree

-- Source: Solutions.WeierstrassChartVanishingIdeal
set_option autoImplicit true
set_option maxHeartbeats 200000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000
noncomputable section
open scoped Polynomial
open MvPolynomial TranscendenceTheory

namespace WeierstrassEllipticZeta

/-- A polynomial over a complex polynomial ring vanishes on a double cover
`y² = f(x)` precisely when it is divisible by its defining equation.  The
nonzero hypothesis on `f` prevents the nonreduced double hyperplane. -/
theorem quadratic_cover_vanishing_iff_dvd {ι : Type*}
    (f : MvPolynomial ι ℂ) (hf : f ≠ 0)
    (P : Polynomial (MvPolynomial ι ℂ)) :
    (∀ x : ι → ℂ, ∀ y : ℂ, y ^ 2 = eval x f →
      Polynomial.eval₂ (eval x) y P = 0) ↔
      Polynomial.X ^ 2 - Polynomial.C f ∣ P := by
  classical
  let F : Polynomial (MvPolynomial ι ℂ) := Polynomial.X ^ 2 - Polynomial.C f
  have hF : F.Monic := Polynomial.monic_X_pow_sub_C f (by decide)
  have hdeg : F.natDegree = 2 := Polynomial.natDegree_X_pow_sub_C
  constructor
  · intro hP
    let R := P %ₘ F
    have hRdeg : R.natDegree < 2 := by
      rw [← hdeg]
      apply Polynomial.natDegree_modByMonic_lt P hF
      intro he
      rw [he, Polynomial.natDegree_one] at hdeg
      omega
    have hR : R = Polynomial.C (R.coeff 0) + Polynomial.C (R.coeff 1) * Polynomial.X := by
      ext n
      rcases n with _ | _ | n
      · simp
      · simp
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
        simp
    have hRzero (x : ι → ℂ) (y : ℂ) (hy : y ^ 2 = eval x f) :
        eval x (R.coeff 0) + eval x (R.coeff 1) * y = 0 := by
      have hh := congrArg (Polynomial.eval₂ (eval x) y) (Polynomial.modByMonic_add_div P F)
      have hFy : Polynomial.eval₂ (eval x) y F = 0 := by simp [F, hy]
      change Polynomial.eval₂ (eval x) y (R + F * (P /ₘ F)) = _ at hh
      rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, hFy, zero_mul, add_zero,
        hP x y hy, hR] at hh
      simpa using hh
    have hc (j : ℕ) (hj : j = 0 ∨ j = 1) : R.coeff j = 0 := by
      have hprod : f * R.coeff j = 0 := by
        apply MvPolynomial.funext
        intro x
        rw [map_mul, map_zero]
        by_cases hx : eval x f = 0
        · simp [hx]
        obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (eval x f) (n := 2) (by decide)
        have hy0 : y ≠ 0 := by
          intro hz
          simp [hz] at hy
          exact hx hy.symm
        have hp := hRzero x y hy
        have hn := hRzero x (-y) (by simpa using hy)
        have h0 : eval x (R.coeff 0) = 0 := by linear_combination (hp + hn) / 2
        have h1 : eval x (R.coeff 1) = 0 := by
          apply (mul_eq_zero.mp (show eval x (R.coeff 1) * y = 0 by
            linear_combination hp - h0)).resolve_right hy0
        rcases hj with rfl | rfl <;> simp [h0, h1]
      exact (mul_eq_zero.mp hprod).resolve_left hf
    apply (Polynomial.modByMonic_eq_zero_iff_dvd hF).mp
    change R = 0
    rw [hR, hc 0 (Or.inl rfl), hc 1 (Or.inr rfl)]
    simp
  · rintro ⟨Q, rfl⟩ x y hy
    simp [Polynomial.eval₂_mul, hy]

private def WeierstrassChartVanishingIdeal_separateDerivative :
    MvPolynomial (Fin 4) ℂ ≃ₐ[ℂ] Polynomial (MvPolynomial (Fin 3) ℂ) :=
  (renameEquiv ℂ (Equiv.swap (0 : Fin 4) 2)).trans (finSuccEquiv ℂ 3)

private theorem WeierstrassChartVanishingIdeal_separateDerivative_X0 : WeierstrassChartVanishingIdeal_separateDerivative (X 0) = Polynomial.C (X 1) := by
  simp only [WeierstrassChartVanishingIdeal_separateDerivative, AlgEquiv.coe_trans, Function.comp_apply, renameEquiv_apply, rename_X,
    Equiv.swap_apply_left]
  exact finSuccEquiv_X_succ (j := 1)

private theorem WeierstrassChartVanishingIdeal_separateDerivative_X1 : WeierstrassChartVanishingIdeal_separateDerivative (X 1) = Polynomial.C (X 0) := by
  simp only [WeierstrassChartVanishingIdeal_separateDerivative, AlgEquiv.coe_trans, Function.comp_apply, renameEquiv_apply, rename_X,
    show (Equiv.swap (0 : Fin 4) 2) 1 = 1 from by decide]
  exact finSuccEquiv_X_succ (j := 0)

private theorem WeierstrassChartVanishingIdeal_separateDerivative_X2 : WeierstrassChartVanishingIdeal_separateDerivative (X 2) = Polynomial.X := by
  simp only [WeierstrassChartVanishingIdeal_separateDerivative, AlgEquiv.coe_trans, Function.comp_apply, renameEquiv_apply, rename_X,
    Equiv.swap_apply_right]
  exact finSuccEquiv_X_zero

private theorem WeierstrassChartVanishingIdeal_separateDerivative_X3 : WeierstrassChartVanishingIdeal_separateDerivative (X 3) = Polynomial.C (X 2) := by
  simp only [WeierstrassChartVanishingIdeal_separateDerivative, AlgEquiv.coe_trans, Function.comp_apply, renameEquiv_apply, rename_X,
    show (Equiv.swap (0 : Fin 4) 2) 3 = 3 from by decide]
  exact finSuccEquiv_X_succ (j := 2)

private theorem WeierstrassChartVanishingIdeal_separateDerivative_C (c : ℂ) :
    WeierstrassChartVanishingIdeal_separateDerivative (C c) = Polynomial.C (C c) := by
  simp [WeierstrassChartVanishingIdeal_separateDerivative, finSuccEquiv_apply]

private theorem WeierstrassChartVanishingIdeal_separateDerivative_eval (P : MvPolynomial (Fin 4) ℂ)
    (t x y u : ℂ) :
    Polynomial.eval₂ (eval ![x, t, u]) y (WeierstrassChartVanishingIdeal_separateDerivative P) =
      eval ![t, x, y, u] P := by
  have h : (Polynomial.eval₂RingHom (eval ![x, t, u]) y).comp
      WeierstrassChartVanishingIdeal_separateDerivative.toRingHom = eval ![t, x, y, u] := by
    ext i
    · simp only [RingHom.comp_apply, eval_C]
      change Polynomial.eval₂ (eval ![x, t, u]) y (WeierstrassChartVanishingIdeal_separateDerivative (C i)) = i
      simp [WeierstrassChartVanishingIdeal_separateDerivative_C]
    · change Polynomial.eval₂ (eval ![x, t, u]) y (WeierstrassChartVanishingIdeal_separateDerivative (X i)) = _
      fin_cases i <;>
        simp [WeierstrassChartVanishingIdeal_separateDerivative_X0, WeierstrassChartVanishingIdeal_separateDerivative_X1,
          WeierstrassChartVanishingIdeal_separateDerivative_X2, WeierstrassChartVanishingIdeal_separateDerivative_X3]
  exact DFunLike.congr_fun h P

/-- The first affine chart has exactly its cubic equation as vanishing
ideal, including the independent additive and extension-fiber coordinates. -/
theorem first_chart_cubic_vanishing_iff_mem (g₂ g₃ : ℂ)
    (P : MvPolynomial (Fin 4) ℂ) :
    (∀ t x y u : ℂ, y ^ 2 = 4 * x ^ 3 - g₂ * x - g₃ →
      eval ![t, x, y, u] P = 0) ↔
      P ∈ Ideal.span {extensionChartCubic g₂ g₃ 0} := by
  classical
  let f : MvPolynomial (Fin 3) ℂ := C 4 * X 0 ^ 3 - C g₂ * X 0 - C g₃
  have hf : f ≠ 0 := by
    intro h
    have hh := congrArg (coeff (Finsupp.single (0 : Fin 3) 3)) h
    have h13 : Finsupp.single (0 : Fin 3) 1 ≠ Finsupp.single 0 3 := by
      intro h; have hh := DFunLike.congr_fun h 0; norm_num at hh
    have h03 : (0 : Fin 3 →₀ ℕ) ≠ Finsupp.single 0 3 := by
      intro h; have hh := DFunLike.congr_fun h 0; norm_num at hh
    norm_num [f, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, h13, h03] at hh
  have he : WeierstrassChartVanishingIdeal_separateDerivative (extensionChartCubic g₂ g₃ 0) =
      Polynomial.X ^ 2 - Polynomial.C f := by
    simp [extensionChartCubic, WeierstrassChartVanishingIdeal_separateDerivative_X1, WeierstrassChartVanishingIdeal_separateDerivative_X2,
      WeierstrassChartVanishingIdeal_separateDerivative_C, f]
    ring
  rw [Ideal.mem_span_singleton]
  rw [← map_dvd_iff WeierstrassChartVanishingIdeal_separateDerivative, he,
    ← quadratic_cover_vanishing_iff_dvd f hf]
  constructor
  · intro h v y hy
    have hv : ![v 0, v 1, v 2] = v := by ext i; fin_cases i <;> rfl
    rw [← hv, WeierstrassChartVanishingIdeal_separateDerivative_eval]
    apply h
    simpa [f] using hy
  · intro h t x y u hy
    rw [← WeierstrassChartVanishingIdeal_separateDerivative_eval]
    apply h
    simpa [f] using hy

/-- Evaluation on all complex points of the cubic detects zero in the
specific coordinate ring used by the section-dimension calculations. -/
theorem first_cubic_quotient_eq_zero_iff_vanishes (L : PeriodPair)
    (P : MvPolynomial (Fin 4) ℂ) :
    firstCubicQuotient L P = 0 ↔
      ∀ t x y u : ℂ, y ^ 2 = 4 * x ^ 3 - L.g₂ * x - L.g₃ →
        eval ![t, x, y, u] P = 0 := by
  change (Ideal.Quotient.mk (Ideal.span {extensionChartCubic L.g₂ L.g₃ 0})) P = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact (first_chart_cubic_vanishing_iff_mem L.g₂ L.g₃ P).symm

end WeierstrassEllipticZeta


-- Source: Solutions.SigmaConstruction
set_option autoImplicit true
set_option maxHeartbeats 200000

noncomputable section
open Filter
open scoped Topology

namespace WeierstrassEllipticZeta

private def SigmaConstruction_canonicalFactor (z : ℂ) : ℂ :=
  (1 - z) * Complex.exp (z + z ^ 2 / 2)

private lemma SigmaConstruction_factor_deriv (z : ℂ) :
    HasDerivAt SigmaConstruction_canonicalFactor (-z ^ 2 * Complex.exp (z + z ^ 2 / 2)) z := by
  convert! ((hasDerivAt_const z (1 : ℂ)).sub (hasDerivAt_id z)).mul
    (((hasDerivAt_id z).add (((hasDerivAt_id z).pow 2).div_const 2)).cexp) using 1
  simp only [Pi.sub_apply, Pi.add_apply, Pi.pow_apply, id_eq]
  ring

private lemma SigmaConstruction_factor_entire : Differentiable ℂ SigmaConstruction_canonicalFactor :=
  fun z ↦ (SigmaConstruction_factor_deriv z).differentiableAt

private lemma SigmaConstruction_factor_cubic_bound : ∃ C r : ℝ, 0 < C ∧ 0 < r ∧
    ∀ z : ℂ, ‖z‖ < r → ‖SigmaConstruction_canonicalFactor z - 1‖ ≤ C * ‖z‖ ^ 3 := by
  have hd : deriv SigmaConstruction_canonicalFactor = fun z ↦ -z ^ 2 * Complex.exp (z + z ^ 2 / 2) :=
    funext fun z ↦ (SigmaConstruction_factor_deriv z).deriv
  have h2 : iteratedDeriv 2 SigmaConstruction_canonicalFactor 0 = 0 := by
    rw [iteratedDeriv_succ', iteratedDeriv_one, hd]
    have H : HasDerivAt (fun z : ℂ ↦ -z ^ 2 * Complex.exp (z + z ^ 2 / 2)) 0 0 := by
      have he := (((hasDerivAt_id (0 : ℂ)).add
        (((hasDerivAt_id (0 : ℂ)).pow 2).div_const 2)).cexp)
      convert! (((hasDerivAt_id (0 : ℂ)).pow 2).neg).mul he using 1
      simp
    exact H.deriv
  obtain ⟨F, hF, heq⟩ := (SigmaConstruction_factor_entire.analyticAt 0).exists_eventuallyEq_sum_add_pow_mul 3
  have heq' : ∀ᶠ z in 𝓝 (0 : ℂ), SigmaConstruction_canonicalFactor z - 1 = z ^ 3 * F z := by
    filter_upwards [heq] with z hz
    apply sub_eq_iff_eq_add.mpr
    simpa [Finset.sum_range_succ, iteratedDeriv_one, hd, h2, SigmaConstruction_canonicalFactor,
      add_comm] using hz
  have hbound : ∀ᶠ z in 𝓝 (0 : ℂ), ‖F z‖ < ‖F 0‖ + 1 :=
    hF.continuousAt.norm.eventually (gt_mem_nhds (by linarith))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp (heq'.and hbound)
  refine ⟨‖F 0‖ + 1, r, by positivity, hr, fun z hz ↦ ?_⟩
  have H := hball (by simpa [dist_zero_right] using hz)
  rw [H.1, norm_mul, norm_pow]
  nlinarith [pow_nonneg (norm_nonneg z) 3]

private lemma SigmaConstruction_factor_uniform_bound (L : PeriodPair) (R : ℝ) (hR : 0 < R) :
    ∃ u : L.lattice → ℝ, Summable u ∧
      ∀ᶠ l : L.lattice in cofinite, ∀ z : ℂ, ‖z‖ < R →
        ‖SigmaConstruction_canonicalFactor (z / (l : ℂ)) - 1‖ ≤ u l := by
  obtain ⟨C, r, hC, hr, hbound⟩ := SigmaConstruction_factor_cubic_bound
  refine ⟨fun l ↦ C * R ^ 3 * ‖l‖ ^ (-3 : ℝ),
    (ZLattice.summable_norm_rpow _ _ (by simp; norm_num)).mul_left _, ?_⟩
  have hlarge : ∀ᶠ l : L.lattice in cofinite, R / r < ‖l‖ := by
    refine (isCompact_iff_finite.mp (isCompact_closedBall (0 : L.lattice) (R / r))).subset ?_
    intro l hl
    simpa only [Metric.mem_closedBall, dist_zero_right, Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] using hl
  filter_upwards [hlarge] with l hl z hz
  have hlpos : 0 < ‖(l : ℂ)‖ := lt_trans (div_pos hR hr) hl
  have hratio : ‖z / (l : ℂ)‖ < r := by
    rw [norm_div, div_lt_iff₀ hlpos]
    have H := (div_lt_iff₀ hr).mp hl
    change R < ‖(l : ℂ)‖ * r at H
    nlinarith
  calc
    _ ≤ C * ‖z / (l : ℂ)‖ ^ 3 := hbound _ hratio
    _ ≤ C * (R / ‖(l : ℂ)‖) ^ 3 := by rw [norm_div]; gcongr
    _ = C * R ^ 3 * ‖l‖ ^ (-3 : ℝ) := by simp [div_eq_mul_inv, mul_pow, mul_assoc]

private lemma SigmaConstruction_factor_multipliable_locally (L : PeriodPair) :
    MultipliableLocallyUniformlyOn
      (fun (l : L.lattice) (z : ℂ) ↦ SigmaConstruction_canonicalFactor (z / (l : ℂ))) Set.univ := by
  use fun z ↦ ∏' l : L.lattice, SigmaConstruction_canonicalFactor (z / (l : ℂ))
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hK
  obtain ⟨R, hR, hnorm⟩ := hK.isBounded.exists_pos_norm_lt
  obtain ⟨u, hu, hbound⟩ := SigmaConstruction_factor_uniform_bound L R hR
  have h := hu.hasProdUniformlyOn_one_add hK (f := fun (l : L.lattice) (z : ℂ) ↦
    SigmaConstruction_canonicalFactor (z / (l : ℂ)) - 1) ?_ ?_
  · simpa only [add_sub_cancel] using h
  · filter_upwards [hbound] with l hl z hz using hl z (hnorm z hz)
  · intro l
    exact ((SigmaConstruction_factor_entire.comp (differentiable_id.div_const (l : ℂ))).sub
      (differentiable_const 1)).continuous.continuousOn

private lemma SigmaConstruction_summable_factor_sub_one (L : PeriodPair) (z : ℂ) :
    Summable fun l : L.lattice ↦ ‖SigmaConstruction_canonicalFactor (z / (l : ℂ)) - 1‖ := by
  obtain ⟨u, hu, hbound⟩ := SigmaConstruction_factor_uniform_bound L (‖z‖ + 1) (by positivity)
  apply hu.of_norm_bounded_eventually
  filter_upwards [hbound] with l hl
  simpa using hl z (by linarith)

private lemma SigmaConstruction_factor_ne_zero (L : PeriodPair) (l : L.lattice) (z : ℂ)
    (hz : z ∉ L.lattice) : SigmaConstruction_canonicalFactor (z / (l : ℂ)) ≠ 0 := by
  unfold SigmaConstruction_canonicalFactor
  refine mul_ne_zero ?_ (Complex.exp_ne_zero _)
  by_cases hl : (l : ℂ) = 0
  · simp [hl]
  · intro h
    have hzl : z = (l : ℂ) := (div_eq_one_iff_eq hl).mp (sub_eq_zero.mp h).symm
    exact hz (hzl ▸ l.property)

private lemma SigmaConstruction_product_ne_zero (L : PeriodPair) (z : ℂ) (hz : z ∉ L.lattice) :
    ∏' l : L.lattice, SigmaConstruction_canonicalFactor (z / (l : ℂ)) ≠ 0 := by
  have h := tprod_one_add_ne_zero_of_summable
    (f := fun l : L.lattice ↦ SigmaConstruction_canonicalFactor (z / (l : ℂ)) - 1)
    (fun l ↦ by simpa only [add_sub_cancel] using SigmaConstruction_factor_ne_zero L l z hz)
    (SigmaConstruction_summable_factor_sub_one L z)
  simpa only [add_sub_cancel] using h

private lemma SigmaConstruction_factor_logDeriv (L : PeriodPair) (l : L.lattice) (z : ℂ)
    (hz : z ∉ L.lattice) :
    logDeriv (fun w : ℂ ↦ SigmaConstruction_canonicalFactor (w / (l : ℂ))) z =
      if l = 0 then 0 else 1 / (z - (l : ℂ)) + 1 / (l : ℂ) + z / (l : ℂ) ^ 2 := by
  classical
  by_cases hl : l = 0
  · simp [hl, SigmaConstruction_canonicalFactor]
  have hlc : (l : ℂ) ≠ 0 := fun h ↦ hl (Subtype.ext h)
  have hzl : z - (l : ℂ) ≠ 0 := fun h ↦ hz (sub_eq_zero.mp h ▸ l.property)
  have hlin : 1 - z / (l : ℂ) ≠ 0 := by
    intro h
    exact hzl (sub_eq_zero.mpr ((div_eq_one_iff_eq hlc).mp (sub_eq_zero.mp h).symm))
  have hder := (SigmaConstruction_factor_deriv (z / (l : ℂ))).comp z
    ((hasDerivAt_id z).div_const (l : ℂ))
  have hd : deriv (fun w : ℂ ↦ SigmaConstruction_canonicalFactor (w / (l : ℂ))) z =
      -(z / (l : ℂ)) ^ 2 * Complex.exp (z / (l : ℂ) + (z / (l : ℂ)) ^ 2 / 2) *
        (1 / (l : ℂ)) := by simpa using! hder.deriv
  rw [logDeriv_apply, hd, if_neg hl, SigmaConstruction_canonicalFactor]
  have he := Complex.exp_ne_zero (z / (l : ℂ) + (z / (l : ℂ)) ^ 2 / 2)
  have hlz : -z + (l : ℂ) ≠ 0 := by
    rw [neg_add_eq_sub]
    exact sub_ne_zero.mpr (sub_ne_zero.mp hzl).symm
  field_simp [hlz]
  ring_nf
  field_simp [hlz]
  ring

private lemma SigmaConstruction_product_entire (L : PeriodPair) :
    Differentiable ℂ (fun z ↦ ∏' l : L.lattice, SigmaConstruction_canonicalFactor (z / (l : ℂ))) := by
  rw [← differentiableOn_univ]
  exact (SigmaConstruction_factor_multipliable_locally L).hasProdLocallyUniformlyOn.differentiableOn
    (.of_forall fun s ↦ by
      simpa only [Finset.prod_fn] using! DifferentiableOn.finsetProd (u := s)
        (fun l _ ↦ (SigmaConstruction_factor_entire.comp
          (differentiable_id.div_const (l : ℂ))).differentiableOn)) isOpen_univ

private lemma SigmaConstruction_zetaSummand_bound (r : ℝ) (hr : 0 < r) (z : ℂ) (hz : ‖z‖ < r)
    (l : ℂ) (hl : 2 * r ≤ ‖l‖) :
    ‖1 / (z - l) + 1 / l + z / l ^ 2‖ ≤ 2 * r ^ 2 * ‖l‖ ^ (-3 : ℝ) := by
  have hlpos : 0 < ‖l‖ := by linarith
  have hlne : l ≠ 0 := norm_pos_iff.mp hlpos
  have hzl : z - l ≠ 0 := by
    intro h
    have heq := sub_eq_zero.mp h
    subst z
    linarith
  have hnorm : ‖l‖ / 2 ≤ ‖z - l‖ := by
    rw [norm_sub_rev]
    exact le_trans (by linarith) (norm_sub_norm_le l z)
  calc
    _ = ‖z ^ 2 / (l ^ 2 * (z - l))‖ := by
      congr 1
      field_simp
      ring
    _ = ‖z‖ ^ 2 / (‖l‖ ^ 2 * ‖z - l‖) := by simp
    _ ≤ r ^ 2 / (‖l‖ ^ 2 * (‖l‖ / 2)) := by gcongr
    _ = 2 * r ^ 2 / ‖l‖ ^ 3 := by field
    _ = _ := by norm_cast

private theorem SigmaConstruction_zeta_series_converges (L : PeriodPair) :
    HasSumLocallyUniformly
      (fun (l : L.lattice) (z : ℂ) ↦ if l = 0 then 0 else
        1 / (z - (l : ℂ)) + 1 / (l : ℂ) + z / (l : ℂ) ^ 2)
      (fun z ↦ ∑' l : L.lattice, if l = 0 then 0 else
        1 / (z - (l : ℂ)) + 1 / (l : ℂ) + z / (l : ℂ) ^ 2) := by
  refine L.hasSumLocallyUniformly_aux (u := fun r l ↦ 2 * r ^ 2 * ‖l‖ ^ (-3 : ℝ)) _
    (fun _ _ ↦ (ZLattice.summable_norm_rpow _ _ (by simp; norm_num)).mul_left _)
    fun r hr ↦ Filter.eventually_atTop.mpr ⟨2 * r, ?_⟩
  rintro _ h z hz l rfl
  split_ifs
  · simp only [norm_zero]
    positivity
  · exact SigmaConstruction_zetaSummand_bound r hr z hz l h

theorem exists_elliptic_sigma_differential_data (L : PeriodPair) :
    Nonempty (EllipticSigmaDifferentialData L) := by
  let P : ℂ → ℂ := fun z ↦ ∏' l : L.lattice, SigmaConstruction_canonicalFactor (z / (l : ℂ))
  have hP : Differentiable ℂ P := SigmaConstruction_product_entire L
  refine ⟨{ sigma := fun z ↦ z * P z
            entire := differentiable_id.mul hP
            zero := by simp
            deriv_zero := ?_
            hasDerivAt := ?_ }⟩
  · have h := (hasDerivAt_id (0 : ℂ)).mul (hP 0).hasDerivAt
    simpa [P, SigmaConstruction_canonicalFactor] using! h
  · intro z hz
    have hz0 : z ≠ 0 := fun h ↦ hz (h ▸ L.lattice.zero_mem)
    have hPne : P z ≠ 0 := SigmaConstruction_product_ne_zero L z hz
    have hsum : Summable fun l : L.lattice ↦
        logDeriv (fun w : ℂ ↦ SigmaConstruction_canonicalFactor (w / (l : ℂ))) z :=
      (SigmaConstruction_zeta_series_converges L).hasSum.summable.congr
        (fun l ↦ (SigmaConstruction_factor_logDeriv L l z hz).symm)
    have hlogP := logDeriv_tprod_eq_tsum isOpen_univ (Set.mem_univ z)
      (fun l ↦ SigmaConstruction_factor_ne_zero L l z hz)
      (fun l ↦ (SigmaConstruction_factor_entire.comp
        (differentiable_id.div_const (l : ℂ))).differentiableOn)
      hsum (SigmaConstruction_factor_multipliable_locally L) hPne
    have hlog : logDeriv (fun w ↦ w * P w) z = weierstrassZeta L z := by
      have hm : logDeriv (fun w : ℂ ↦ w * P w) z = 1 / z + logDeriv P z := by
        simpa using! logDeriv_mul z hz0 hPne differentiableAt_id (hP z)
      apply hm.trans
      convert! congrArg (1 / z + ·)
        (hlogP.trans (tsum_congr fun l ↦ SigmaConstruction_factor_logDeriv L l z hz)) using 1
    have heq : deriv (fun w ↦ w * P w) z = weierstrassZeta L z * (z * P z) :=
      (div_eq_iff (mul_ne_zero hz0 hPne)).mp hlog
    rw [← heq]
    exact ((differentiable_id.mul hP) z).hasDerivAt

end WeierstrassEllipticZeta

-- Source: Solutions.SigmaAdditionFromDifferential
set_option autoImplicit true
set_option maxHeartbeats 200000

noncomputable section
open Filter
open scoped Topology

namespace WeierstrassEllipticZeta

private lemma SigmaAdditionFromDifferential_zeta_neg (L : PeriodPair) (z : ℂ) :
    weierstrassZeta L (-z) = -weierstrassZeta L z := by
  classical
  have hsum : (∑' l : L.lattice, if -l = 0 then (0 : ℂ) else
      1 / (-z - ((-l : L.lattice) : ℂ)) + 1 / ((-l : L.lattice) : ℂ) +
        -z / ((-l : L.lattice) : ℂ) ^ 2) =
      ∑' l : L.lattice, -(if l = 0 then 0 else
        1 / (z - (l : ℂ)) + 1 / (l : ℂ) + z / (l : ℂ) ^ 2) := by
    apply tsum_congr
    intro l
    by_cases hl : l = 0
    · simp [hl]
    · simp only [neg_eq_zero, if_neg hl, NegMemClass.coe_neg, even_two, Even.neg_pow]
      rw [show -z - -(l : ℂ) = -(z - (l : ℂ)) by ring]
      simp only [div_neg, neg_div]
      ring
  unfold weierstrassZeta
  conv_lhs => arg 2; rw [← (Equiv.neg L.lattice).tsum_eq]
  simp only [Equiv.neg_apply, hsum, tsum_neg, div_neg]
  ring

private lemma SigmaAdditionFromDifferential_sigma_ne_zero (L : PeriodPair) (S : EllipticSigmaDifferentialData L)
    (hzeta : ∀ z : ℂ, z ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z)
    (z : ℂ) (hz : z ∉ L.lattice) : S.sigma z ≠ 0 := by
  intro hzero
  have hf := S.entire.analyticAt z
  have ha : AnalyticAt ℂ (weierstrassZeta L) z :=
    (show DifferentiableOn ℂ (weierstrassZeta L) L.latticeᶜ from
      fun w hw => (hzeta w hw).differentiableAt.differentiableWithinAt).analyticOnNhd
        L.isClosed_lattice.isOpen_compl z hz
  have hfinite : analyticOrderAt S.sigma z ≠ ⊤ := by
    intro ho
    have heq : S.sigma = fun _ => 0 :=
      (show AnalyticOnNhd ℂ S.sigma Set.univ from fun w _ => S.entire.analyticAt w).eq_of_eventuallyEq
        (fun _ _ => analyticAt_const) (analyticOrderAt_eq_top.mp ho)
    have h0 := S.deriv_zero
    rw [heq] at h0
    have hbad := h0.unique (hasDerivAt_const (0 : ℂ) (0 : ℂ))
    norm_num at hbad
  have hderiv : deriv S.sigma =ᶠ[𝓝 z] S.sigma * weierstrassZeta L := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    simpa [mul_comm] using (S.hasDerivAt w hw).deriv
  have ho : analyticOrderAt (deriv S.sigma) z + 1 = analyticOrderAt S.sigma z := by
    simpa [hzero] using hf.analyticOrderAt_deriv_add_one
  rw [analyticOrderAt_congr hderiv, analyticOrderAt_mul hf ha] at ho
  have hle : analyticOrderAt S.sigma z + 1 ≤ analyticOrderAt S.sigma z := by
    calc
      _ ≤ (analyticOrderAt S.sigma z + analyticOrderAt (weierstrassZeta L) z) + 1 :=
        add_le_add (show analyticOrderAt S.sigma z ≤
          analyticOrderAt S.sigma z + analyticOrderAt (weierstrassZeta L) z from le_self_add) le_rfl
      _ = _ := ho
  exact (lt_irrefl _ ((ENat.add_one_le_iff hfinite).mp hle))

private lemma SigmaAdditionFromDifferential_sigma_neg (L : PeriodPair) (S : EllipticSigmaDifferentialData L)
    (hne : ∀ z : ℂ, z ∉ L.lattice → S.sigma z ≠ 0)
    (z : ℂ) (hz : z ∉ L.lattice) : S.sigma (-z) = -S.sigma z := by
  have hopen := L.isClosed_lattice.isOpen_compl
  have hd (w : ℂ) (hw : w ∉ L.lattice) :
      HasDerivAt (fun x => S.sigma (-x) / S.sigma x) 0 w := by
    have hm : HasDerivAt (fun x => S.sigma (-x))
        (weierstrassZeta L w * S.sigma (-w)) w := by
      convert! (S.hasDerivAt (-w) (by simpa using hw)).comp w
        (hasDerivAt_id w).neg using 1
      simp [SigmaAdditionFromDifferential_zeta_neg]
    convert! hm.div (S.hasDerivAt w hw) (hne w hw) using 1
    ring
  obtain ⟨c, hc⟩ := hopen.exists_is_const_of_deriv_eq_zero
    (Set.Countable.isConnected_compl_of_one_lt_rank (by simp)
      (countable_of_Lindelof_of_discrete (X := L.lattice))).2
    (fun w hw => (hd w hw).differentiableAt.differentiableWithinAt)
    (fun w hw => (hd w hw).deriv)
  have heq : (fun w => S.sigma (-w)) =ᶠ[𝓝 (0 : ℂ)]
      (fun w => c * S.sigma w) := by
    filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds 0] with w hw
    by_cases hw0 : w = 0
    · simp [hw0, S.zero]
    · have hwL : w ∉ L.lattice := fun h => hw ⟨h, hw0⟩
      exact (div_eq_iff (hne w hwL)).mp (hc w hwL)
  have hm : HasDerivAt (fun w => S.sigma (-w)) (-1) 0 := by
    have hh : HasDerivAt S.sigma 1 (-(0 : ℂ)) := by simpa using S.deriv_zero
    simpa using! hh.comp 0 (hasDerivAt_id (0 : ℂ)).neg
  have hcc := (hm.congr_of_eventuallyEq heq.symm).unique (S.deriv_zero.const_mul c)
  simp only [mul_one] at hcc
  have h := (div_eq_iff (hne z hz)).mp (hc z hz)
  simpa [← hcc] using h

private lemma SigmaAdditionFromDifferential_analytic_locally_constant {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z)
    (hd : ∀ᶠ w in 𝓝[≠] z, deriv f w = 0) :
    f =ᶠ[𝓝 z] (fun _ => f z) := by
  have hdeq : deriv f =ᶠ[𝓝[≠] z] (fun _ => 0) := hd
  have hdz : deriv f z = 0 := tendsto_nhds_unique
    (hf.deriv.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (tendsto_const_nhds.congr' hdeq.symm)
  have hdall : ∀ᶠ w in 𝓝 z, deriv f w = 0 := by
    rw [eventually_nhdsWithin_iff] at hd
    filter_upwards [hd] with w hw
    by_cases hwz : w = z
    · simpa [hwz] using hdz
    · exact hw hwz
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp
    (hf.eventually_analyticAt.and hdall)
  filter_upwards [Metric.ball_mem_nhds z hr] with w hw
  exact Metric.isOpen_ball.is_const_of_deriv_eq_zero Metric.isPreconnected_ball
    (fun x hx => (hball hx).1.differentiableAt.differentiableWithinAt)
    (fun x hx => (hball hx).2) hw (Metric.mem_ball_self hr)

private lemma SigmaAdditionFromDifferential_sigma_ratio_deriv (L : PeriodPair) (S : EllipticSigmaDifferentialData L)
    (hadd : ∀ z v : ℂ,
      z ∉ L.lattice → v ∉ L.lattice → z + v ∉ L.lattice →
      2 * (L.weierstrassP v - L.weierstrassP z) * weierstrassZeta L (z + v) =
        2 * (weierstrassZeta L z + weierstrassZeta L v) *
          (L.weierstrassP v - L.weierstrassP z) +
        L.derivWeierstrassP v - L.derivWeierstrassP z)
    (w v : ℂ) (hw : w ∉ L.lattice) (hv : v ∉ L.lattice)
    (hp : w + v ∉ L.lattice) (hm : w - v ∉ L.lattice)
    (hB : (L.weierstrassP v - L.weierstrassP w) * S.sigma w ^ 2 * S.sigma v ^ 2 ≠ 0) :
    HasDerivAt (fun x => (S.sigma (x + v) * S.sigma (x - v)) /
      ((L.weierstrassP v - L.weierstrassP x) * S.sigma x ^ 2 * S.sigma v ^ 2)) 0 w := by
  have h1 := hadd w v hw hv hp
  have h2 := hadd w (-v) hw (by simpa using hv) (by simpa [sub_eq_add_neg] using hm)
  rw [L.weierstrassP_neg, L.derivWeierstrassP_neg, SigmaAdditionFromDifferential_zeta_neg] at h2
  have hZ : (L.weierstrassP v - L.weierstrassP w) *
      (weierstrassZeta L (w + v) + weierstrassZeta L (w - v) -
        2 * weierstrassZeta L w) = -L.derivWeierstrassP w := by
    simp only [sub_eq_add_neg] at h2 ⊢
    linear_combination (h1 + h2) / 2
  have hplus : HasDerivAt (fun x => S.sigma (x + v))
      (weierstrassZeta L (w + v) * S.sigma (w + v)) w := by
    simpa using! (S.hasDerivAt (w + v) hp).comp w ((hasDerivAt_id w).add_const v)
  have hminus : HasDerivAt (fun x => S.sigma (x - v))
      (weierstrassZeta L (w - v) * S.sigma (w - v)) w := by
    simpa using! (S.hasDerivAt (w - v) hm).comp w ((hasDerivAt_id w).sub_const v)
  have hP : HasDerivAt L.weierstrassP (L.derivWeierstrassP w) w := by
    simpa using (L.differentiableOn_weierstrassP.differentiableAt
      (L.isClosed_lattice.isOpen_compl.mem_nhds hw)).hasDerivAt
  have hden := (((hasDerivAt_const w (L.weierstrassP v)).sub hP).mul
    ((S.hasDerivAt w hw).pow 2)).mul_const (S.sigma v ^ 2)
  convert! (hplus.mul hminus).div hden hB using 1
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, zero_sub]
  symm
  apply (div_eq_zero_iff).mpr
  left
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply]
  linear_combination hZ * (S.sigma (w + v) * S.sigma (w - v) *
    S.sigma w ^ 2 * S.sigma v ^ 2)

/-- The sigma addition identity follows from the normalized entire solution
of its differential equation and the canonical zeta addition identity. -/
theorem sigma_addition_from_differential
    (L : PeriodPair) (S : EllipticSigmaDifferentialData L)
    (h_zeta_deriv : ∀ z : ℂ, z ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z)
    (h_zeta_addition : ∀ z v : ℂ,
      z ∉ L.lattice → v ∉ L.lattice → z + v ∉ L.lattice →
      2 * (L.weierstrassP v - L.weierstrassP z) * weierstrassZeta L (z + v) =
        2 * (weierstrassZeta L z + weierstrassZeta L v) *
          (L.weierstrassP v - L.weierstrassP z) +
        L.derivWeierstrassP v - L.derivWeierstrassP z) :
    (∀ z : ℂ, z ∉ L.lattice → S.sigma z ≠ 0) ∧
      ∀ z v : ℂ, z ∉ L.lattice → v ∉ L.lattice →
        S.sigma (z + v) * S.sigma (z - v) =
          (L.weierstrassP v - L.weierstrassP z) * S.sigma z ^ 2 * S.sigma v ^ 2 := by
  have hne := SigmaAdditionFromDifferential_sigma_ne_zero L S h_zeta_deriv
  refine ⟨hne, ?_⟩
  intro z v hz hv
  let t := dslope S.sigma 0
  have ht0 : t 0 = 1 := by simp [t, dslope_same, S.deriv_zero.deriv]
  have htx (x : ℂ) : x * t x = S.sigma x := by
    simpa only [t, sub_zero, smul_eq_mul] using sub_smul_dslope_of_zero S.zero x
  have ht (x : ℂ) : AnalyticAt ℂ t x := by
    by_cases hx : x = 0
    · subst x
      obtain ⟨p, hp⟩ := S.entire.analyticAt (0 : ℂ)
      exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩
    · have heq : t =ᶠ[𝓝 x] (fun w => S.sigma w / w) := by
        filter_upwards [eventually_ne_nhds hx] with w hw
        simp [t, dslope_of_ne _ hw, slope, S.zero, div_eq_mul_inv, mul_comm]
      exact ((S.entire.analyticAt x).div analyticAt_id hx).congr heq.symm
  let A : ℂ → ℂ := fun x => S.sigma (x + v) * S.sigma (x - v)
  let B : ℂ → ℂ := fun x =>
    ((L.weierstrassP v - L.weierstrassPExcept 0 x) * x ^ 2 - 1) *
      t x ^ 2 * S.sigma v ^ 2
  have hA (x : ℂ) : AnalyticAt ℂ A x := by
    exact ((S.entire.analyticAt (x + v)).comp
      (f := fun x : ℂ => x + v) (analyticAt_id.add analyticAt_const)).mul
      ((S.entire.analyticAt (x - v)).comp
        (f := fun x : ℂ => x - v) (analyticAt_id.sub analyticAt_const))
  have hB : AnalyticOnNhd ℂ B ((L.lattice : Set ℂ) \ {0})ᶜ := by
    intro x hx
    exact (((analyticAt_const.sub (L.analyticOnNhd_weierstrassPExcept 0 x hx)).mul
      (analyticAt_id.pow 2)).sub analyticAt_const).mul ((ht x).pow 2) |>.mul analyticAt_const
  have hB0 : B 0 = -(S.sigma v ^ 2) := by simp [B, ht0]
  have hBn : B 0 ≠ 0 := by rw [hB0]; exact neg_ne_zero.mpr (pow_ne_zero _ (hne v hv))
  have hAB0 : A 0 = B 0 := by simp [A, hB0, SigmaAdditionFromDifferential_sigma_neg L S hne v hv, pow_two]
  have hB_eq (x : ℂ) (hx : x ≠ 0) : B x =
      (L.weierstrassP v - L.weierstrassP x) * S.sigma x ^ 2 * S.sigma v ^ 2 := by
    have hP := L.weierstrassPExcept_add (0 : L.lattice) x
    simp only [ZeroMemClass.coe_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, div_zero, sub_zero] at hP
    rw [← hP, ← htx x]
    dsimp [B]
    field_simp
    ring
  let R : ℂ → ℂ := fun x => A x / B x
  have hR : AnalyticAt ℂ R 0 := (hA 0).div (hB 0 (by simp)) hBn
  have hR0 : R 0 = 1 := by exact (div_eq_one_iff_eq hBn).mpr hAB0
  have hd : ∀ᶠ w in 𝓝[≠] (0 : ℂ), deriv R w = 0 := by
    have hreg : ∀ᶠ w in 𝓝 (0 : ℂ), w ∈ ((L.lattice : Set ℂ) \ {0})ᶜ :=
      L.compl_lattice_sdiff_singleton_mem_nhds 0
    have hp : ∀ᶠ w in 𝓝 (0 : ℂ), w + v ∉ L.lattice := by
      simpa using (continuousAt_id.add continuousAt_const).eventually
        (L.isClosed_lattice.isOpen_compl.mem_nhds (show 0 + v ∉ L.lattice by simpa using hv))
    have hm : ∀ᶠ w in 𝓝 (0 : ℂ), w - v ∉ L.lattice := by
      simpa using (continuousAt_id.sub continuousAt_const).eventually
        (L.isClosed_lattice.isOpen_compl.mem_nhds (show 0 - v ∉ L.lattice by simpa using hv))
    filter_upwards [hreg.filter_mono nhdsWithin_le_nhds,
      hp.filter_mono nhdsWithin_le_nhds, hm.filter_mono nhdsWithin_le_nhds,
      ((hB 0 (by simp)).continuousAt.eventually_ne hBn).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with w hw hwp hwm hBw hw0
    have hwr : w ∉ L.lattice := fun h => hw ⟨h, hw0⟩
    have hBd : (L.weierstrassP v - L.weierstrassP w) * S.sigma w ^ 2 * S.sigma v ^ 2 ≠ 0 := by
      rwa [hB_eq w hw0] at hBw
    have hh := SigmaAdditionFromDifferential_sigma_ratio_deriv L S h_zeta_addition w v hwr hv hwp hwm hBd
    have heq : R =ᶠ[𝓝 w] (fun x => (S.sigma (x + v) * S.sigma (x - v)) /
        ((L.weierstrassP v - L.weierstrassP x) * S.sigma x ^ 2 * S.sigma v ^ 2)) := by
      filter_upwards [eventually_ne_nhds hw0] with x hx
      simp only [R, A, hB_eq x hx]
    exact (hh.congr_of_eventuallyEq heq).deriv
  have hnear : A =ᶠ[𝓝 (0 : ℂ)] B := by
    filter_upwards [SigmaAdditionFromDifferential_analytic_locally_constant hR hd,
      (hB 0 (by simp)).continuousAt.eventually_ne hBn] with w hw hn
    change A w / B w = R 0 at hw
    rw [hR0] at hw
    exact (div_eq_one_iff_eq hn).mp hw
  have hcount : (L.lattice : Set ℂ).Countable :=
    countable_of_Lindelof_of_discrete (X := L.lattice)
  have hconn : IsPreconnected (((L.lattice : Set ℂ) \ {0})ᶜ) :=
    (Set.Countable.isConnected_compl_of_one_lt_rank (by simp)
      (hcount.mono Set.sdiff_subset)).2
  have hglobal := (show AnalyticOnNhd ℂ A ((L.lattice : Set ℂ) \ {0})ᶜ from
    fun x _ => hA x).eqOn_of_preconnected_of_eventuallyEq hB hconn (by simp) hnear
  have hz0 : z ≠ 0 := fun h => hz (h ▸ L.lattice.zero_mem)
  exact (hglobal (fun h => hz h.1)).trans (hB_eq z hz0)

end WeierstrassEllipticZeta

-- Source: Solutions.WeierstrassEllipticZeta_ZetaAnalysis
set_option autoImplicit true
set_option maxHeartbeats 200000

/-!
Analytic foundations for the canonical lattice-series zeta function.

The normalization and analytic identities are those of NIST DLMF §23.2,
https://dlmf.nist.gov/23.2 (equations 23.2.5 and 23.2.7).
The convergence proof uses a cubic tail bound and Mathlib's lattice summability.
-/

noncomputable section

open Filter
open scoped Topology

namespace WeierstrassEllipticZeta

/-- Cubic decay of the regularized zeta summand, uniformly on a bounded disk. -/
lemma zetaSummand_bound (r : ℝ) (hr : 0 < r) (z : ℂ) (hz : ‖z‖ < r)
    (l : ℂ) (hl : 2 * r ≤ ‖l‖) :
    ‖1 / (z - l) + 1 / l + z / l ^ 2‖ ≤ 2 * r ^ 2 * ‖l‖ ^ (-3 : ℝ) := by
  have hlpos : 0 < ‖l‖ := by linarith
  have hlne : l ≠ 0 := norm_pos_iff.mp hlpos
  have hzl : z - l ≠ 0 := by
    intro h
    have heq := sub_eq_zero.mp h
    subst z
    linarith
  have hnorm : ‖l‖ / 2 ≤ ‖z - l‖ := by
    rw [norm_sub_rev]
    exact le_trans (by linarith) (norm_sub_norm_le l z)
  calc
    _ = ‖z ^ 2 / (l ^ 2 * (z - l))‖ := by
      congr 1
      field_simp
      ring
    _ = ‖z‖ ^ 2 / (‖l‖ ^ 2 * ‖z - l‖) := by simp
    _ ≤ r ^ 2 / (‖l‖ ^ 2 * (‖l‖ / 2)) := by gcongr
    _ = 2 * r ^ 2 / ‖l‖ ^ 3 := by field
    _ = _ := by norm_cast

/-- The regularized zeta series converges locally uniformly. The individual terms
are totalized at their poles; differentiability is asserted only off the lattice. -/
theorem hasSumLocallyUniformly_zetaSeries (L : PeriodPair) :
    HasSumLocallyUniformly
      (fun (l : L.lattice) (z : ℂ) ↦ if l = 0 then 0 else
        1 / (z - (l : ℂ)) + 1 / (l : ℂ) + z / (l : ℂ) ^ 2)
      (fun z ↦ ∑' l : L.lattice, if l = 0 then 0 else
        1 / (z - (l : ℂ)) + 1 / (l : ℂ) + z / (l : ℂ) ^ 2) := by
  refine L.hasSumLocallyUniformly_aux (u := fun r l ↦ 2 * r ^ 2 * ‖l‖ ^ (-3 : ℝ)) _
    (fun _ _ ↦ (ZLattice.summable_norm_rpow _ _ (by simp; norm_num)).mul_left _)
    fun r hr ↦ Filter.eventually_atTop.mpr ⟨2 * r, ?_⟩
  rintro _ h z hz l rfl
  split_ifs
  · simp only [norm_zero]
    positivity
  · exact zetaSummand_bound r hr z hz l h

/-- In particular, the defining series is summable at every regular point (and
also under Lean's totalized convention at lattice points). -/
theorem summable_zetaSeries (L : PeriodPair) (z : ℂ) :
    Summable (fun l : L.lattice ↦ if l = 0 then 0 else
      1 / (z - (l : ℂ)) + 1 / (l : ℂ) + z / (l : ℂ) ^ 2) :=
  (hasSumLocallyUniformly_zetaSeries L).hasSum.summable

private lemma WeierstrassEllipticZeta_ZetaAnalysis_hasDerivAt_zetaSummand (L : PeriodPair) (l : L.lattice) (z : ℂ)
    (hz : z ∉ L.lattice) :
    HasDerivAt (fun w : ℂ ↦ if l = 0 then 0 else
      1 / (w - (l : ℂ)) + 1 / (l : ℂ) + w / (l : ℂ) ^ 2)
      (if l = 0 then 0 else -(1 / (z - (l : ℂ)) ^ 2 - 1 / (l : ℂ) ^ 2)) z := by
  by_cases hl : l = 0
  · simpa only [if_pos hl] using hasDerivAt_const z (0 : ℂ)
  simp only [if_neg hl]
  have hzl : z - (l : ℂ) ≠ 0 := fun h ↦ hz (sub_eq_zero.mp h ▸ l.property)
  convert! ((((hasDerivAt_id z).sub_const (l : ℂ)).inv hzl).add_const
    (1 / (l : ℂ))).add ((hasDerivAt_id z).div_const ((l : ℂ) ^ 2)) using 1 <;>
    simp [funext_iff, Pi.add_apply, one_div, neg_div, sub_eq_add_neg, add_comm]

private lemma WeierstrassEllipticZeta_ZetaAnalysis_differentiableOn_zetaSeries (L : PeriodPair) :
    DifferentiableOn ℂ (fun z ↦ ∑' l : L.lattice, if l = 0 then 0 else
      1 / (z - (l : ℂ)) + 1 / (l : ℂ) + z / (l : ℂ) ^ 2) L.latticeᶜ := by
  exact (hasSumLocallyUniformly_zetaSeries L).tendstoLocallyUniformlyOn.differentiableOn
    (.of_forall fun s ↦ .fun_sum fun l _ z hz ↦
      (WeierstrassEllipticZeta_ZetaAnalysis_hasDerivAt_zetaSummand L l z hz).differentiableAt.differentiableWithinAt)
    L.isClosed_lattice.isOpen_compl

private lemma WeierstrassEllipticZeta_ZetaAnalysis_deriv_zetaSeries (L : PeriodPair) (z : ℂ) (hz : z ∉ L.lattice) :
    deriv (fun w ↦ ∑' l : L.lattice, if l = 0 then 0 else
      1 / (w - (l : ℂ)) + 1 / (l : ℂ) + w / (l : ℂ) ^ 2) z =
      -L.weierstrassPExcept 0 z := by
  have hd := ((hasSumLocallyUniformly_zetaSeries L).tendstoLocallyUniformlyOn.deriv
    (.of_forall fun s ↦ .fun_sum fun l _ w hw ↦
      (WeierstrassEllipticZeta_ZetaAnalysis_hasDerivAt_zetaSummand L l w hw).differentiableAt.differentiableWithinAt)
    L.isClosed_lattice.isOpen_compl).tendsto_at hz
  have hsum : HasSum (fun l : L.lattice ↦ if l = 0 then 0 else
      -(1 / (z - (l : ℂ)) ^ 2 - 1 / (l : ℂ) ^ 2)) (-L.weierstrassPExcept 0 z) := by
    convert! (L.hasSum_weierstrassPExcept 0 z).neg using 1
    ext l
    by_cases hl : l = 0
    · subst l
      simp
    · have hlc : (l : ℂ) ≠ 0 := fun h ↦ hl (Subtype.ext h)
      simp only [if_neg hl, if_neg hlc]
  apply HasSum.unique _ hsum
  change Tendsto _ atTop _
  convert! hd using 1
  funext s
  exact (HasDerivAt.fun_sum fun l _ ↦ WeierstrassEllipticZeta_ZetaAnalysis_hasDerivAt_zetaSummand L l z hz).deriv.symm

/-- The canonical zeta function is holomorphic away from the lattice. -/
theorem differentiableOn_weierstrassZeta (L : PeriodPair) :
    DifferentiableOn ℂ (weierstrassZeta L) L.latticeᶜ := by
  refine DifferentiableOn.add ?_ (WeierstrassEllipticZeta_ZetaAnalysis_differentiableOn_zetaSeries L)
  intro z hz
  have hz0 : z ≠ 0 := fun h ↦ hz (h ▸ L.lattice.zero_mem)
  change DifferentiableWithinAt ℂ (fun w : ℂ ↦ 1 / w) L.latticeᶜ z
  simpa only [one_div] using (hasDerivAt_inv hz0).differentiableAt.differentiableWithinAt

/-- DLMF 23.2.7: the derivative of the canonical zeta function is `-℘`. -/
theorem hasDerivAt_weierstrassZeta (L : PeriodPair) (z : ℂ) (hz : z ∉ L.lattice) :
    HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z := by
  have hz0 : z ≠ 0 := fun h ↦ hz (h ▸ L.lattice.zero_mem)
  have htail := ((WeierstrassEllipticZeta_ZetaAnalysis_differentiableOn_zetaSeries L).differentiableAt
    (L.isClosed_lattice.isOpen_compl.mem_nhds hz)).hasDerivAt
  rw [WeierstrassEllipticZeta_ZetaAnalysis_deriv_zetaSeries L z hz] at htail
  convert! (hasDerivAt_inv hz0).add htail using 1
  · ext w
    simp only [weierstrassZeta, one_div, Pi.add_apply]
  · have hP := L.weierstrassPExcept_add (0 : L.lattice) z
    simp only [ZeroMemClass.coe_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, div_zero, sub_zero] at hP
    rw [← hP]
    simp only [one_div]
    ring

theorem deriv_weierstrassZeta (L : PeriodPair) (z : ℂ) (hz : z ∉ L.lattice) :
    deriv (weierstrassZeta L) z = -L.weierstrassP z :=
  (hasDerivAt_weierstrassZeta L z hz).deriv

end WeierstrassEllipticZeta

-- Source: Solutions.WeierstrassEllipticZeta_ZetaRegularity
set_option autoImplicit true
set_option maxHeartbeats 200000

noncomputable section

open Filter
open scoped Topology

namespace WeierstrassEllipticZeta

theorem weierstrassZeta_neg (L : PeriodPair) (z : ℂ) :
    weierstrassZeta L (-z) = -weierstrassZeta L z := by
  classical
  have hsum : (∑' l : L.lattice, if -l = 0 then (0 : ℂ) else
      1 / (-z - ((-l : L.lattice) : ℂ)) + 1 / ((-l : L.lattice) : ℂ) +
        -z / ((-l : L.lattice) : ℂ) ^ 2) =
      ∑' l : L.lattice, -(if l = 0 then 0 else
        1 / (z - (l : ℂ)) + 1 / (l : ℂ) + z / (l : ℂ) ^ 2) := by
    apply tsum_congr
    intro l
    by_cases hl : l = 0
    · simp [hl]
    · simp only [neg_eq_zero, if_neg hl, NegMemClass.coe_neg, even_two, Even.neg_pow]
      rw [show -z - -(l : ℂ) = -(z - (l : ℂ)) by ring]
      simp only [div_neg, neg_div]
      ring
  unfold weierstrassZeta
  conv_lhs => arg 2; rw [← (Equiv.neg L.lattice).tsum_eq]
  simp only [Equiv.neg_apply, hsum, tsum_neg, div_neg]
  ring

theorem weierstrassZeta_add_period (L : PeriodPair) (ω z : ℂ)
    (hω : ω ∈ L.lattice) (hz : z ∉ L.lattice) :
    weierstrassZeta L (z + ω) = weierstrassZeta L z + zetaQuasiPeriod L ω := by
  have hopen := L.isClosed_lattice.isOpen_compl
  have hshift (w : ℂ) (hw : w ∉ L.lattice) : w + ω ∉ L.lattice :=
    fun h ↦ hw (by simpa using L.lattice.sub_mem h hω)
  have hd (w : ℂ) (hw : w ∉ L.lattice) :
      HasDerivAt (fun x ↦ weierstrassZeta L (x + ω) - weierstrassZeta L x) 0 w := by
    have hs : HasDerivAt (fun x ↦ weierstrassZeta L (x + ω))
        (-L.weierstrassP (w + ω)) w := by
      convert! (hasDerivAt_weierstrassZeta L (w + ω) (hshift w hw)).comp w
        ((hasDerivAt_id w).add_const ω) using 1
      simp
    convert! hs.sub (hasDerivAt_weierstrassZeta L w hw) using 1
    rw [L.weierstrassP_add_coe w ⟨ω, hω⟩]
    ring
  have heq := hopen.is_const_of_deriv_eq_zero
    (Set.Countable.isConnected_compl_of_one_lt_rank (by simp)
      (countable_of_Lindelof_of_discrete (X := L.lattice))).2
    (fun w hw ↦ (hd w hw).differentiableAt.differentiableWithinAt)
    (fun w hw ↦ (hd w hw).deriv) hz L.ω₁_div_two_notMem_lattice
  change weierstrassZeta L (z + ω) - weierstrassZeta L z = zetaQuasiPeriod L ω at heq
  linear_combination heq

private def WeierstrassEllipticZeta_ZetaRegularity_zetaTail (L : PeriodPair) (z : ℂ) : ℂ :=
  ∑' l : L.lattice, if l = 0 then 0 else
    1 / (z - (l : ℂ)) + 1 / (l : ℂ) + z / (l : ℂ) ^ 2

private lemma WeierstrassEllipticZeta_ZetaRegularity_zetaTail_zero (L : PeriodPair) : WeierstrassEllipticZeta_ZetaRegularity_zetaTail L 0 = 0 := by
  simp [WeierstrassEllipticZeta_ZetaRegularity_zetaTail]

private lemma WeierstrassEllipticZeta_ZetaRegularity_differentiableOn_zetaTail (L : PeriodPair) :
    DifferentiableOn ℂ (WeierstrassEllipticZeta_ZetaRegularity_zetaTail L) (L.lattice \ {0})ᶜ := by
  refine (hasSumLocallyUniformly_zetaSeries L).hasSumLocallyUniformlyOn.differentiableOn
    (.of_forall fun s ↦ .fun_sum fun l _ ↦ ?_) L.isOpen_compl_lattice_sdiff
  by_cases hl : l = 0
  · simp only [hl, if_true]
    fun_prop
  simp only [if_neg hl]
  refine .add (.add (.div (by fun_prop) (by fun_prop) ?_) (by fun_prop)) (by fun_prop)
  intro z hz h
  apply hz
  have heq := sub_eq_zero.mp h
  exact ⟨heq ▸ l.property, fun hz0 ↦ hl (Subtype.ext (heq.symm.trans hz0))⟩

private lemma WeierstrassEllipticZeta_ZetaRegularity_hasDerivAt_zetaTail_zero (L : PeriodPair) :
    HasDerivAt (WeierstrassEllipticZeta_ZetaRegularity_zetaTail L) 0 0 := by
  have h0 : (0 : ℂ) ∈ ((L.lattice : Set ℂ) \ {(0 : ℂ)})ᶜ := by simp
  have hd := ((hasSumLocallyUniformly_zetaSeries L).tendstoLocallyUniformlyOn.deriv
    (.of_forall fun s ↦ .fun_sum fun l _ ↦ ?_) L.isOpen_compl_lattice_sdiff).tendsto_at h0
  · have hs (l : L.lattice) : HasDerivAt (fun w : ℂ ↦ if l = 0 then 0 else
        1 / (w - (l : ℂ)) + 1 / (l : ℂ) + w / (l : ℂ) ^ 2) 0 0 := by
      by_cases hl : l = 0
      · simpa only [if_pos hl] using hasDerivAt_const (0 : ℂ) (0 : ℂ)
      simp only [if_neg hl]
      have hlc : (l : ℂ) ≠ 0 := fun h ↦ hl (Subtype.ext h)
      convert! ((((hasDerivAt_id (0 : ℂ)).sub_const (l : ℂ)).inv
        (by simpa using hlc)).add_const (1 / (l : ℂ))).add
          ((hasDerivAt_id (0 : ℂ)).div_const ((l : ℂ) ^ 2)) using 1
      · ext w
        simp [one_div]
      · simp [one_div, neg_div]
    have heq : (fun s : Finset L.lattice ↦ deriv (fun w : ℂ ↦ ∑ l ∈ s,
        if l = 0 then 0 else 1 / (w - (l : ℂ)) + 1 / (l : ℂ) +
          w / (l : ℂ) ^ 2) 0) = fun _ ↦ (0 : ℂ) := by
      funext s
      simpa using (HasDerivAt.fun_sum fun l _ ↦ hs l).deriv
    change Tendsto (fun s : Finset L.lattice ↦ deriv (fun w : ℂ ↦ ∑ l ∈ s,
      if l = 0 then 0 else 1 / (w - (l : ℂ)) + 1 / (l : ℂ) +
        w / (l : ℂ) ^ 2) 0) atTop (𝓝 (deriv (WeierstrassEllipticZeta_ZetaRegularity_zetaTail L) 0)) at hd
    rw [heq] at hd
    have hder := tendsto_nhds_unique hd tendsto_const_nhds
    simpa only [hder] using ((WeierstrassEllipticZeta_ZetaRegularity_differentiableOn_zetaTail L).differentiableAt
      (L.isOpen_compl_lattice_sdiff.mem_nhds h0)).hasDerivAt
  · by_cases hl : l = 0
    · simp only [hl, if_true]
      fun_prop
    simp only [if_neg hl]
    refine .add (.add (.div (by fun_prop) (by fun_prop) ?_) (by fun_prop)) (by fun_prop)
    intro z hz h
    apply hz
    have heq := sub_eq_zero.mp h
    exact ⟨heq ▸ l.property, fun hz0 ↦ hl (Subtype.ext (heq.symm.trans hz0))⟩

private def WeierstrassEllipticZeta_ZetaRegularity_fsRelation (L : PeriodPair) (v z : ℂ) : ℂ :=
  letI := Classical.propDecidable
  if z ∈ L.lattice ∨ z + v ∈ L.lattice then 0 else
    (weierstrassZeta L (z + v) - weierstrassZeta L z - weierstrassZeta L v) ^ 2 -
      L.weierstrassP z - L.weierstrassP v - L.weierstrassP (z + v)

private lemma WeierstrassEllipticZeta_ZetaRegularity_fsRelation_add_period (L : PeriodPair) (v z ω : ℂ) (hω : ω ∈ L.lattice) :
    WeierstrassEllipticZeta_ZetaRegularity_fsRelation L v (z + ω) = WeierstrassEllipticZeta_ZetaRegularity_fsRelation L v z := by
  have hmem (w : ℂ) : w + ω ∈ L.lattice ↔ w ∈ L.lattice :=
    ⟨fun h ↦ by simpa using L.lattice.sub_mem h hω, fun h ↦ L.lattice.add_mem h hω⟩
  have hswap : z + ω + v = (z + v) + ω := by ring
  unfold WeierstrassEllipticZeta_ZetaRegularity_fsRelation
  rw [hswap, hmem, hmem]
  by_cases hz : z ∈ L.lattice ∨ z + v ∈ L.lattice
  · simp [hz]
  · rw [if_neg hz, if_neg hz, weierstrassZeta_add_period L ω z hω
        (fun h ↦ hz (Or.inl h)), weierstrassZeta_add_period L ω (z + v) hω
        (fun h ↦ hz (Or.inr h)), L.weierstrassP_add_coe z ⟨ω, hω⟩,
        L.weierstrassP_add_coe (z + v) ⟨ω, hω⟩]
    ring

private lemma WeierstrassEllipticZeta_ZetaRegularity_fsRelation_reflection (L : PeriodPair) (v z : ℂ) :
    WeierstrassEllipticZeta_ZetaRegularity_fsRelation L v (-v - z) = WeierstrassEllipticZeta_ZetaRegularity_fsRelation L v z := by
  classical
  have h1 : -v - z = -(z + v) := by ring
  have h2 : -v - z + v = -z := by ring
  unfold WeierstrassEllipticZeta_ZetaRegularity_fsRelation
  rw [h2, h1]
  simp only [neg_mem_iff, weierstrassZeta_neg, L.weierstrassP_neg]
  simp only [or_comm (a := z + v ∈ L.lattice)]
  split_ifs <;> ring

private lemma WeierstrassEllipticZeta_ZetaRegularity_analyticAt_fsRelation_zero (L : PeriodPair) (v : ℂ) (hv : v ∉ L.lattice) :
    AnalyticAt ℂ (WeierstrassEllipticZeta_ZetaRegularity_fsRelation L v) 0 := by
  let a : ℂ → ℂ := fun z ↦ weierstrassZeta L (z + v) - weierstrassZeta L v - WeierstrassEllipticZeta_ZetaRegularity_zetaTail L z
  let b := dslope a 0
  have htail : AnalyticAt ℂ (WeierstrassEllipticZeta_ZetaRegularity_zetaTail L) 0 :=
    (WeierstrassEllipticZeta_ZetaRegularity_differentiableOn_zetaTail L).analyticOnNhd L.isOpen_compl_lattice_sdiff 0 (by simp)
  have hza : AnalyticAt ℂ (weierstrassZeta L) v :=
    (differentiableOn_weierstrassZeta L).analyticOnNhd L.isClosed_lattice.isOpen_compl v hv
  have hzcomp : AnalyticAt ℂ (fun z ↦ weierstrassZeta L (z + v)) 0 := by
    have hh : AnalyticAt ℂ (weierstrassZeta L) (0 + v) := by simpa using hza
    exact hh.comp (f := fun z : ℂ ↦ z + v) (by fun_prop : AnalyticAt ℂ (fun z : ℂ ↦ z + v) 0)
  have ha : AnalyticAt ℂ a 0 := (hzcomp.sub analyticAt_const).sub htail
  have ha0 : a 0 = 0 := by simp [a, WeierstrassEllipticZeta_ZetaRegularity_zetaTail_zero]
  have had : HasDerivAt a (-L.weierstrassP v) 0 := by
    have hzcompd : HasDerivAt (fun z ↦ weierstrassZeta L (z + v)) (-L.weierstrassP v) 0 := by
      have hh : HasDerivAt (weierstrassZeta L) (-L.weierstrassP v) (0 + v) :=
        by simpa using hasDerivAt_weierstrassZeta L v hv
      convert! hh.comp 0
        ((hasDerivAt_id (0 : ℂ)).add_const v) using 1
      simp
    convert! (hzcompd.sub_const (weierstrassZeta L v)).sub
      (WeierstrassEllipticZeta_ZetaRegularity_hasDerivAt_zetaTail_zero L) using 1
    simp
  have hb : AnalyticAt ℂ b 0 := by
    obtain ⟨p, hp⟩ := ha
    exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩
  have hb0 : b 0 = -L.weierstrassP v := by simp only [b, dslope_same, had.deriv]
  have hab (z : ℂ) : z * b z = a z := by
    simpa only [b, sub_zero, smul_eq_mul] using sub_smul_dslope_of_zero ha0 z
  have hpa : AnalyticAt ℂ (fun z ↦ L.weierstrassP (z + v)) 0 := by
    have hh : AnalyticAt ℂ L.weierstrassP (0 + v) := by
      simpa using L.analyticOnNhd_weierstrassP v hv
    exact hh.comp (f := fun z : ℂ ↦ z + v) (by fun_prop : AnalyticAt ℂ (fun z : ℂ ↦ z + v) 0)
  let g : ℂ → ℂ := fun z ↦ (z * b z) ^ 2 - 2 * b z - L.weierstrassPExcept 0 z -
    L.weierstrassP v - L.weierstrassP (z + v)
  have hg : AnalyticAt ℂ g 0 := by
    have hp0 := L.analyticAt_weierstrassPExcept 0
    dsimp [g]
    fun_prop
  apply hg.congr
  have hnear : ∀ᶠ z in 𝓝 (0 : ℂ), z + v ∉ L.lattice := by
    have hh : Tendsto (fun z : ℂ ↦ z + v) (𝓝 0) (𝓝 v) := by
      convert! (continuousAt_id.add continuousAt_const :
        ContinuousAt (fun z : ℂ ↦ z + v) 0).tendsto using 1
      simp
    exact hh.eventually (L.isClosed_lattice.isOpen_compl.mem_nhds hv)
  filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds 0, hnear] with z hz hzv
  by_cases hz0 : z = 0
  · subst z
    simp [g, WeierstrassEllipticZeta_ZetaRegularity_fsRelation, hb0]
    ring
  · have hzreg : z ∉ L.lattice := by simpa [hz0] using hz
    have hP := L.weierstrassPExcept_add (0 : L.lattice) z
    simp only [ZeroMemClass.coe_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, div_zero, sub_zero] at hP
    simp only [g, WeierstrassEllipticZeta_ZetaRegularity_fsRelation, hzreg, hzv, or_self, if_false]
    rw [← hP]
    have haeq := hab z
    dsimp [a] at haeq
    change z * b z = weierstrassZeta L (z + v) - weierstrassZeta L v - WeierstrassEllipticZeta_ZetaRegularity_zetaTail L z at haeq
    change _ = ((weierstrassZeta L (z + v) - (1 / z + WeierstrassEllipticZeta_ZetaRegularity_zetaTail L z) -
      weierstrassZeta L v) ^ 2 - (L.weierstrassPExcept 0 z + 1 / z ^ 2) -
      L.weierstrassP v - L.weierstrassP (z + v))
    rw [show weierstrassZeta L (z + v) - (1 / z + WeierstrassEllipticZeta_ZetaRegularity_zetaTail L z) -
      weierstrassZeta L v = z * b z - 1 / z by linear_combination -haeq]
    field_simp
    ring

private lemma WeierstrassEllipticZeta_ZetaRegularity_analyticAt_fsRelation (L : PeriodPair) (v : ℂ) (hv : v ∉ L.lattice) (z : ℂ) :
    AnalyticAt ℂ (WeierstrassEllipticZeta_ZetaRegularity_fsRelation L v) z := by
  have hzero := WeierstrassEllipticZeta_ZetaRegularity_analyticAt_fsRelation_zero L v hv
  by_cases hz : z ∈ L.lattice
  · have hcomp : AnalyticAt ℂ (fun w ↦ WeierstrassEllipticZeta_ZetaRegularity_fsRelation L v (w - z)) z := by
      have hh : AnalyticAt ℂ (WeierstrassEllipticZeta_ZetaRegularity_fsRelation L v) (z - z) := by simpa using hzero
      exact hh.comp (f := fun w : ℂ ↦ w - z) (by fun_prop : AnalyticAt ℂ (fun w : ℂ ↦ w - z) z)
    convert! hcomp using 1
    ext w
    simpa using WeierstrassEllipticZeta_ZetaRegularity_fsRelation_add_period L v (w - z) z hz
  by_cases hzv : z + v ∈ L.lattice
  · have hnegv : AnalyticAt ℂ (WeierstrassEllipticZeta_ZetaRegularity_fsRelation L v) (-v) := by
      have hc : AnalyticAt ℂ (fun w ↦ WeierstrassEllipticZeta_ZetaRegularity_fsRelation L v (-v - w)) (-v) := by
        have hh : AnalyticAt ℂ (WeierstrassEllipticZeta_ZetaRegularity_fsRelation L v) (-v - -v) := by simpa using hzero
        exact hh.comp (f := fun w : ℂ ↦ -v - w) (by fun_prop : AnalyticAt ℂ (fun w : ℂ ↦ -v - w) (-v))
      simpa only [WeierstrassEllipticZeta_ZetaRegularity_fsRelation_reflection] using hc
    have hc : AnalyticAt ℂ (fun w ↦ WeierstrassEllipticZeta_ZetaRegularity_fsRelation L v (w - (z + v))) z := by
      have hh : AnalyticAt ℂ (WeierstrassEllipticZeta_ZetaRegularity_fsRelation L v) (z - (z + v)) := by simpa using hnegv
      exact hh.comp (f := fun w : ℂ ↦ w - (z + v)) (by fun_prop : AnalyticAt ℂ (fun w : ℂ ↦ w - (z + v)) z)
    convert! hc using 1
    ext w
    simpa using WeierstrassEllipticZeta_ZetaRegularity_fsRelation_add_period L v (w - (z + v)) (z + v) hzv
  · have hZ := (differentiableOn_weierstrassZeta L).analyticOnNhd L.isClosed_lattice.isOpen_compl
    have hZz := hZ z hz
    have hZv := hZ (z + v) hzv
    have hPz := L.analyticOnNhd_weierstrassP z hz
    have hPv := L.analyticOnNhd_weierstrassP (z + v) hzv
    have ha : AnalyticAt ℂ (fun w ↦
        (weierstrassZeta L (w + v) - weierstrassZeta L w - weierstrassZeta L v) ^ 2 -
          L.weierstrassP w - L.weierstrassP v - L.weierstrassP (w + v)) z := by fun_prop
    apply ha.congr
    have hnear : ∀ᶠ w in 𝓝 z, w ∉ L.lattice := L.isClosed_lattice.isOpen_compl.mem_nhds hz
    have hnearv : ∀ᶠ w in 𝓝 z, w + v ∉ L.lattice :=
      (continuousAt_id.add continuousAt_const).eventually (L.isClosed_lattice.isOpen_compl.mem_nhds hzv)
    filter_upwards [hnear, hnearv] with w hw hwv
    simp [WeierstrassEllipticZeta_ZetaRegularity_fsRelation, hw, hwv]

/-- Frobenius–Stickelberger's zeta identity (DLMF 23.10.6), with the third
argument equal to the negative of the sum of the first two. -/
theorem frobenius_stickelberger (L : PeriodPair) (z v : ℂ)
    (hz : z ∉ L.lattice) (hv : v ∉ L.lattice) (hzv : z + v ∉ L.lattice) :
    (weierstrassZeta L (z + v) - weierstrassZeta L z - weierstrassZeta L v) ^ 2 =
      L.weierstrassP z + L.weierstrassP v + L.weierstrassP (z + v) := by
  have hd : Differentiable ℂ (WeierstrassEllipticZeta_ZetaRegularity_fsRelation L v) :=
    fun w ↦ (WeierstrassEllipticZeta_ZetaRegularity_analyticAt_fsRelation L v hv w).differentiableAt
  have hconst := hd.apply_eq_apply_of_bounded
    (IsZLattice.isCompact_range_of_periodic L.lattice _ hd.continuous
      (fun w ω hω ↦ WeierstrassEllipticZeta_ZetaRegularity_fsRelation_add_period L v w ω hω)).isBounded z 0
  simp only [WeierstrassEllipticZeta_ZetaRegularity_fsRelation, hz, hzv, or_self, if_false, zero_mem,
    true_or, if_true] at hconst
  linear_combination hconst

end WeierstrassEllipticZeta

-- Source: Solutions.WeierstrassEllipticZeta_ZetaAddition
set_option autoImplicit true
set_option maxHeartbeats 200000

noncomputable section

open Filter
open scoped Topology

namespace WeierstrassEllipticZeta

private lemma WeierstrassEllipticZeta_ZetaAddition_frobenius_stickelberger_derivative (L : PeriodPair) (z v : ℂ)
    (hz : z ∉ L.lattice) (hv : v ∉ L.lattice) (hzv : z + v ∉ L.lattice) :
    2 * (weierstrassZeta L (z + v) - weierstrassZeta L z - weierstrassZeta L v) *
      (-L.weierstrassP (z + v) + L.weierstrassP v) =
        L.derivWeierstrassP v + L.derivWeierstrassP (z + v) := by
  have hopen := L.isClosed_lattice.isOpen_compl
  have hZ := hasDerivAt_weierstrassZeta L v hv
  have hZv : HasDerivAt (fun w ↦ weierstrassZeta L (z + w))
      (-L.weierstrassP (z + v)) v := by
    convert! (hasDerivAt_weierstrassZeta L (z + v) hzv).comp v
      ((hasDerivAt_const v z).add (hasDerivAt_id v)) using 1
    simp
  have hP : HasDerivAt L.weierstrassP (L.derivWeierstrassP v) v := by
    simpa using (L.differentiableOn_weierstrassP.differentiableAt
      (hopen.mem_nhds hv)).hasDerivAt
  have hPv : HasDerivAt (fun w ↦ L.weierstrassP (z + w))
      (L.derivWeierstrassP (z + v)) v := by
    have hh : HasDerivAt L.weierstrassP (L.derivWeierstrassP (z + v)) (z + v) := by
      simpa using (L.differentiableOn_weierstrassP.differentiableAt
        (hopen.mem_nhds hzv)).hasDerivAt
    convert! hh.comp v ((hasDerivAt_const v z).add (hasDerivAt_id v)) using 1
    simp
  have hnear : ∀ᶠ w in 𝓝 v, w ∉ L.lattice := hopen.mem_nhds hv
  have hnearv : ∀ᶠ w in 𝓝 v, z + w ∉ L.lattice :=
    (continuousAt_const.add continuousAt_id).eventually (hopen.mem_nhds hzv)
  have heq : (fun w ↦
      (weierstrassZeta L (z + w) - weierstrassZeta L z - weierstrassZeta L w) ^ 2)
      =ᶠ[𝓝 v] (fun w ↦ L.weierstrassP z + L.weierstrassP w + L.weierstrassP (z + w)) := by
    filter_upwards [hnear, hnearv] with w hw hzw
    exact frobenius_stickelberger L z w hz hw hzw
  have hleft := ((hZv.sub_const (weierstrassZeta L z)).sub hZ).pow 2
  have hright := ((hasDerivAt_const v (L.weierstrassP z)).add hP).add hPv
  have he := (hleft.congr_of_eventuallyEq heq.symm).unique hright
  simp only [Pi.sub_apply, Nat.cast_ofNat, show 2 - 1 = (1 : ℕ) by decide,
    pow_one, sub_neg_eq_add, zero_add] at he
  exact he

/-- The full multiplied identity follows by differentiating the symmetric
Frobenius–Stickelberger identity in each of its two arguments and subtracting. -/
theorem zeta_addition_formula_proved (L : PeriodPair) (z v : ℂ)
    (hz : z ∉ L.lattice) (hv : v ∉ L.lattice) (hzv : z + v ∉ L.lattice) :
    2 * (L.weierstrassP v - L.weierstrassP z) * weierstrassZeta L (z + v) =
      2 * (weierstrassZeta L z + weierstrassZeta L v) *
        (L.weierstrassP v - L.weierstrassP z) +
      L.derivWeierstrassP v - L.derivWeierstrassP z := by
  have hdv := WeierstrassEllipticZeta_ZetaAddition_frobenius_stickelberger_derivative L z v hz hv hzv
  have hdz := WeierstrassEllipticZeta_ZetaAddition_frobenius_stickelberger_derivative L v z hv hz (by simpa [add_comm] using hzv)
  rw [add_comm v z] at hdz
  linear_combination hdv - hdz

theorem zeta_addition_nondegenerate_proved (L : PeriodPair) (z v : ℂ)
    (hz : z ∉ L.lattice) (hv : v ∉ L.lattice) (hzv : z + v ∉ L.lattice)
    (hdelta : L.weierstrassP v ≠ L.weierstrassP z) :
    weierstrassZeta L (z + v) = weierstrassZeta L z + weierstrassZeta L v +
      (L.derivWeierstrassP v - L.derivWeierstrassP z) /
        (2 * (L.weierstrassP v - L.weierstrassP z)) := by
  have h := zeta_addition_formula_proved L z v hz hv hzv
  have hne : L.weierstrassP v - L.weierstrassP z ≠ 0 := sub_ne_zero.mpr hdelta
  field_simp
  linear_combination h

end WeierstrassEllipticZeta

-- Source: Solutions.QuasiperiodDeterminant
set_option autoImplicit true
set_option maxHeartbeats 200000

noncomputable section
open Filter
open scoped Topology

namespace WeierstrassEllipticZeta

/-- Integrate the logarithmic derivative under a period translation, then extend globally. -/
private lemma QuasiperiodDeterminant_sigma_norm_translation (L : PeriodPair) (S : EllipticSigmaDifferentialData L)
    (hne : ∀ z : ℂ, z ∉ L.lattice → S.sigma z ≠ 0)
    (hzeta : ∀ ω z : ℂ, ω ∈ L.lattice → z ∉ L.lattice →
      weierstrassZeta L (z + ω) = weierstrassZeta L z + zetaQuasiPeriod L ω)
    (ω : ℂ) (hω : ω ∈ L.lattice) :
    ∃ a : ℝ, ∀ z : ℂ, ‖S.sigma (z + ω)‖ =
      Real.exp (a + (zetaQuasiPeriod L ω * z).re) * ‖S.sigma z‖ := by
  let η := zetaQuasiPeriod L ω
  have hshift (z : ℂ) (hz : z ∉ L.lattice) : z + ω ∉ L.lattice := by
    intro h
    exact hz (by simpa using L.lattice.sub_mem h hω)
  have hd (z : ℂ) (hz : z ∉ L.lattice) :
      HasDerivAt (fun w => S.sigma (w + ω) / S.sigma w * Complex.exp (-η * w)) 0 z := by
    have h1 : HasDerivAt (fun w => S.sigma (w + ω))
        ((weierstrassZeta L z + η) * S.sigma (z + ω)) z := by
      simpa [hzeta ω z hω hz, η] using!
        (S.hasDerivAt (z + ω) (hshift z hz)).comp z ((hasDerivAt_id z).add_const ω)
    have h2 := ((hasDerivAt_id z).const_mul (-η)).cexp
    convert! ((h1.div (S.hasDerivAt z hz) (hne z hz)).mul h2) using 1
    simp only [Pi.div_apply, id_eq]
    field_simp
    ring
  obtain ⟨c, hc⟩ := L.isClosed_lattice.isOpen_compl.exists_is_const_of_deriv_eq_zero
    (Set.Countable.isConnected_compl_of_one_lt_rank (by simp)
      (countable_of_Lindelof_of_discrete (X := L.lattice))).2
    (fun z hz => (hd z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hd z hz).deriv)
  have heq (z : ℂ) (hz : z ∉ L.lattice) :
      S.sigma (z + ω) = c * Complex.exp (η * z) * S.sigma z := by
    have h := congrArg (fun w : ℂ => w * Complex.exp (η * z) * S.sigma z) (hc z hz)
    simpa [mul_assoc, ← Complex.exp_add, hne z hz] using h
  let u := L.ω₁ / 2
  have hu : u ∉ L.lattice := L.ω₁_div_two_notMem_lattice
  have hc0 : c ≠ 0 := by
    intro hc0
    have h := heq u hu
    simp only [hc0, zero_mul] at h
    exact hne (u + ω) (hshift u hu) h
  have hall : (fun z => S.sigma (z + ω)) =
      (fun z => c * Complex.exp (η * z) * S.sigma z) := by
    apply AnalyticOnNhd.eq_of_eventuallyEq
      (show AnalyticOnNhd ℂ (fun z => S.sigma (z + ω)) Set.univ from
        fun z _ => (S.entire.analyticAt (z + ω)).comp (f := fun w : ℂ => w + ω) (x := z)
          (analyticAt_id.add analyticAt_const))
      (show AnalyticOnNhd ℂ (fun z => c * Complex.exp (η * z) * S.sigma z) Set.univ from
        fun z _ => ((analyticAt_const.mul
          (analyticAt_const.mul analyticAt_id).cexp).mul (S.entire.analyticAt z)))
      (z₀ := u)
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hu] with z hz
    exact heq z hz
  refine ⟨Real.log ‖c‖, fun z => ?_⟩
  rw [congrFun hall z, norm_mul, norm_mul, Complex.norm_exp, Real.exp_add,
    Real.exp_log (norm_pos_iff.mpr hc0)]

private lemma QuasiperiodDeterminant_real_linear_is_real_mul (B : ℂ →ₗ[ℝ] ℝ) :
    ∃ b : ℂ, ∀ z : ℂ, (b * z).re = B z := by
  refine ⟨(B 1 : ℂ) - (B Complex.I : ℂ) * Complex.I, fun z => ?_⟩
  have hz : z.re • (1 : ℂ) + z.im • Complex.I = z := by
    simpa only [Complex.real_smul, mul_one] using Complex.re_add_im z
  have hB : B z = z.re * B 1 + z.im * B Complex.I := by
    conv_lhs => rw [← hz]
    simp only [map_add, map_smul, smul_eq_mul]
  rw [hB]
  simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, sub_zero]
  ring

theorem period_quasiperiod_determinant_ne_zero (L : PeriodPair) :
    L.ω₁ * zetaQuasiPeriod L L.ω₂ - L.ω₂ * zetaQuasiPeriod L L.ω₁ ≠ 0 := by
  intro hdet
  have hω₁ : L.ω₁ ≠ 0 := by
    simpa using L.indep.ne_zero (0 : Fin 2)
  let a := zetaQuasiPeriod L L.ω₁ / L.ω₁
  have hη₁ : zetaQuasiPeriod L L.ω₁ = a * L.ω₁ := by
    dsimp [a]
    rw [div_mul_cancel₀ _ hω₁]
  have hη₂ : zetaQuasiPeriod L L.ω₂ = a * L.ω₂ := by
    apply mul_left_cancel₀ hω₁
    calc
      _ = L.ω₂ * zetaQuasiPeriod L L.ω₁ := sub_eq_zero.mp hdet
      _ = _ := by rw [hη₁]; ring
  obtain ⟨S⟩ := exists_elliptic_sigma_differential_data L
  have hne := (sigma_addition_from_differential L S (hasDerivAt_weierstrassZeta L)
    (zeta_addition_formula_proved L)).1
  obtain ⟨r₁, hr₁⟩ := QuasiperiodDeterminant_sigma_norm_translation L S hne
    (weierstrassZeta_add_period L) L.ω₁ L.ω₁_mem_lattice
  obtain ⟨r₂, hr₂⟩ := QuasiperiodDeterminant_sigma_norm_translation L S hne
    (weierstrassZeta_add_period L) L.ω₂ L.ω₂_mem_lattice
  let B : ℂ →ₗ[ℝ] ℝ :=
    (r₁ - (a * L.ω₁ ^ 2 / 2).re) • L.basis.coord 0 +
    (r₂ - (a * L.ω₂ ^ 2 / 2).re) • L.basis.coord 1
  have hB₁ : B L.ω₁ = r₁ - (a * L.ω₁ ^ 2 / 2).re := by
    rw [← L.basis_zero]
    simp only [B, LinearMap.add_apply, LinearMap.smul_apply,
      Module.Basis.coord_apply, Module.Basis.repr_self]
    norm_num
  have hB₂ : B L.ω₂ = r₂ - (a * L.ω₂ ^ 2 / 2).re := by
    rw [← L.basis_one]
    simp only [B, LinearMap.add_apply, LinearMap.smul_apply,
      Module.Basis.coord_apply, Module.Basis.repr_self]
    norm_num
  obtain ⟨b, hb⟩ := QuasiperiodDeterminant_real_linear_is_real_mul B
  let Q : ℂ → ℂ := fun z => a * z ^ 2 / 2 + b * z
  let F : ℂ → ℂ := fun z => Complex.exp (-Q z) * S.sigma z
  have hF : Differentiable ℂ F := by
    have hS := S.entire
    dsimp only [F, Q]
    fun_prop
  have hQ (ω η : ℂ) (r : ℝ) (hη : η = a * ω)
      (hB : B ω = r - (a * ω ^ 2 / 2).re) (z : ℂ) :
      (Q (z + ω)).re = (Q z).re + r + (η * z).re := by
    have heq : Q (z + ω) = Q z + η * z + (a * ω ^ 2 / 2 + b * ω) := by
      rw [hη]
      dsimp only [Q]
      ring
    rw [heq]
    simp only [Complex.add_re, hb, hB]
    ring
  have hp (ω η : ℂ) (r : ℝ)
      (hr : ∀ z : ℂ, ‖S.sigma (z + ω)‖ = Real.exp (r + (η * z).re) * ‖S.sigma z‖)
      (hη : η = a * ω) (hB : B ω = r - (a * ω ^ 2 / 2).re) :
      Function.Periodic (fun z => ‖F z‖) ω := by
    intro z
    dsimp only [F]
    rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp,
      Complex.neg_re, Complex.neg_re, hr, hQ ω η r hη hB z, ← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hp₁ := hp L.ω₁ _ r₁ hr₁ hη₁ hB₁
  have hp₂ := hp L.ω₂ _ r₂ hr₂ hη₂ hB₂
  have hcompact : IsCompact (Set.range (fun z => ‖F z‖)) :=
    IsZLattice.isCompact_range_of_periodic L.lattice _ hF.continuous.norm (by
      intro z w hw
      obtain ⟨m, n, rfl⟩ := L.mem_lattice.mp hw
      simpa only [zsmul_eq_mul] using ((hp₁.zsmul m).add_period (hp₂.zsmul n)) z)
  obtain ⟨M, hM⟩ := hcompact.bddAbove
  have hbounded : Bornology.IsBounded (Set.range F) :=
    isBounded_iff_forall_norm_le.mpr ⟨M, by
      rintro _ ⟨z, rfl⟩
      exact hM (Set.mem_range_self z)⟩
  have hzero := hF.apply_eq_apply_of_bounded hbounded (L.ω₁ / 2) 0
  have hnonzero : F (L.ω₁ / 2) ≠ 0 :=
    mul_ne_zero (Complex.exp_ne_zero _) (hne _ L.ω₁_div_two_notMem_lattice)
  apply hnonzero
  simpa [F, Q, S.zero] using hzero

end WeierstrassEllipticZeta

-- Source: Solutions.EllipticPolynomialSaturation
set_option autoImplicit true
set_option maxHeartbeats 200000

noncomputable section
open MvPolynomial
open WeierstrassEllipticZeta TranscendenceTheory
open scoped Classical

namespace WeierstrassEllipticZeta

private lemma EllipticPolynomialSaturation_nat_period_mem (L : PeriodPair) (ω : ℂ)
    (hω : ω ∈ L.lattice) (n : ℕ) : (n : ℂ) * ω ∈ L.lattice := by
  simpa [nsmul_eq_mul] using L.lattice.nsmul_mem hω n

private lemma EllipticPolynomialSaturation_regular_add_period (L : PeriodPair) (z ω : ℂ)
    (hz : z ∉ L.lattice) (hω : ω ∈ L.lattice) : z + ω ∉ L.lattice := by
  intro h
  exact hz (by simpa only [add_sub_cancel_right] using L.lattice.sub_mem h hω)

private lemma EllipticPolynomialSaturation_zeta_add_nat_period (L : PeriodPair) (ω : ℂ)
    (hω : ω ∈ L.lattice) (z : ℂ) (hz : z ∉ L.lattice) (n : ℕ) :
    weierstrassZeta L (z + (n : ℂ) * ω) =
      weierstrassZeta L z + (n : ℂ) * zetaQuasiPeriod L ω := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show z + ((n + 1 : ℕ) : ℂ) * ω = (z + (n : ℂ) * ω) + ω by
      push_cast; ring]
    rw [weierstrassZeta_add_period L ω _ hω
      (EllipticPolynomialSaturation_regular_add_period L z _ hz (EllipticPolynomialSaturation_nat_period_mem L ω hω n)), ih]
    push_cast
    ring

/-- A nonvertical analytic line saturates both additive coordinates in every regular
elliptic fibre. The derivative coordinate is retained, so no false independence of
`wp` and `wp'` is asserted. -/
theorem linear_direction_polynomial_saturation (L : PeriodPair)
    (α β : ℂ) (hα : α ≠ 0) (P : MvPolynomial (Fin 4) ℂ)
    (hP : ∀ z : ℂ, z ∉ L.lattice →
      eval ![α * z, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z + β * z] P = 0) :
    ∀ z : ℂ, z ∉ L.lattice → ∀ t u : ℂ,
      eval ![t, L.weierstrassP z, L.derivWeierstrassP z, u] P = 0 := by
  classical
  intro z hz t u
  let a₁ := α * L.ω₁
  let a₂ := α * L.ω₂
  let b₁ := zetaQuasiPeriod L L.ω₁ + β * L.ω₁
  let b₂ := zetaQuasiPeriod L L.ω₂ + β * L.ω₂
  let d := a₁ * b₂ - a₂ * b₁
  have hd : d ≠ 0 := by
    have heq : d = α * (L.ω₁ * zetaQuasiPeriod L L.ω₂ -
        L.ω₂ * zetaQuasiPeriod L L.ω₁) := by
      dsimp [d, a₁, a₂, b₁, b₂]
      ring
    rw [heq]
    exact mul_ne_zero hα (period_quasiperiod_determinant_ne_zero L)
  let f : Fin 4 → MvPolynomial (Fin 2) ℂ :=
    ![C (α * z) + C a₁ * X 0 + C a₂ * X 1,
      C (L.weierstrassP z), C (L.derivWeierstrassP z),
      C (weierstrassZeta L z + β * z) + C b₁ * X 0 + C b₂ * X 1]
  let Q : MvPolynomial (Fin 2) ℂ := eval₂ C f P
  have hQeval (a b : ℂ) : eval ![a, b] Q =
      eval ![α * z + a * a₁ + b * a₂, L.weierstrassP z,
        L.derivWeierstrassP z, weierstrassZeta L z + β * z + a * b₁ + b * b₂] P := by
    dsimp only [Q]
    rw [← eval_assoc]
    apply congrArg (fun v : Fin 4 → ℂ => eval v P)
    funext i
    fin_cases i <;> simp [f, mul_comm]
  have hQ : Q = 0 := by
    apply funext_set (fun _ : Fin 2 => Set.range (fun n : ℕ => (n : ℂ)))
      (fun _ => Set.infinite_range_of_injective Nat.cast_injective)
    intro v hv
    obtain ⟨a, ha⟩ := hv 0 (Set.mem_univ _)
    obtain ⟨b, hb⟩ := hv 1 (Set.mem_univ _)
    have hvval : v = ![(a : ℂ), (b : ℂ)] := by
      funext i
      fin_cases i
      · exact ha.symm
      · exact hb.symm
    rw [hvval, hQeval, map_zero]
    have haL := EllipticPolynomialSaturation_nat_period_mem L L.ω₁ L.ω₁_mem_lattice a
    have hbL := EllipticPolynomialSaturation_nat_period_mem L L.ω₂ L.ω₂_mem_lattice b
    have hza := EllipticPolynomialSaturation_regular_add_period L z _ hz haL
    have hzab := EllipticPolynomialSaturation_regular_add_period L _ _ hza hbL
    have hwp : L.weierstrassP (z + (a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂) =
        L.weierstrassP z := by
      rw [L.weierstrassP_add_coe _ ⟨_, hbL⟩, L.weierstrassP_add_coe _ ⟨_, haL⟩]
    have hwpp : L.derivWeierstrassP (z + (a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂) =
        L.derivWeierstrassP z := by
      rw [L.derivWeierstrassP_add_coe _ ⟨_, hbL⟩, L.derivWeierstrassP_add_coe _ ⟨_, haL⟩]
    have hζ := EllipticPolynomialSaturation_zeta_add_nat_period L L.ω₂ L.ω₂_mem_lattice _ hza b
    rw [EllipticPolynomialSaturation_zeta_add_nat_period L L.ω₁ L.ω₁_mem_lattice z hz a] at hζ
    have he := hP _ hzab
    rw [hwp, hwpp, hζ] at he
    convert he using 1
    apply congrArg (fun w : Fin 4 → ℂ => eval w P)
    funext i
    fin_cases i <;> simp [a₁, a₂, b₁, b₂, mul_add, add_mul] <;> ring
  let a := ((t - α * z) * b₂ - a₂ * (u - (weierstrassZeta L z + β * z))) / d
  let b := (a₁ * (u - (weierstrassZeta L z + β * z)) - (t - α * z) * b₁) / d
  have ht : α * z + a * a₁ + b * a₂ = t := by
    calc
      _ = α * z + ((t - α * z) * d) / d := by dsimp [a, b, d]; ring
      _ = t := by rw [mul_div_cancel_right₀ _ hd]; ring
  have hu : weierstrassZeta L z + β * z + a * b₁ + b * b₂ = u := by
    calc
      _ = weierstrassZeta L z + β * z +
          ((u - (weierstrassZeta L z + β * z)) * d) / d := by
        dsimp [a, b, d]; ring
      _ = u := by rw [mul_div_cancel_right₀ _ hd]; ring
  have hh := hQeval a b
  rw [hQ, map_zero, ht, hu] at hh
  exact hh.symm


end WeierstrassEllipticZeta

-- Source: Solutions.EllipticFirstChartIdeal
set_option autoImplicit true
set_option maxHeartbeats 200000

noncomputable section
open MvPolynomial Filter
open scoped Topology
namespace WeierstrassEllipticZeta

private lemma EllipticFirstChartIdeal_wp_regular_image_infinite (L : PeriodPair) :
    (L.weierstrassP '' (L.lattice : Set ℂ)ᶜ).Infinite := by
  intro hfinite
  have hpole : meromorphicOrderAt L.weierstrassP 0 < 0 := by
    rw [L.order_weierstrassP 0 L.lattice.zero_mem]
    exact WithTop.coe_lt_coe.mpr (by decide)
  have hout := (tendsto_cobounded_of_meromorphicOrderAt_neg hpole)
    hfinite.isBounded
  have hregular : ∀ᶠ w in 𝓝[≠] (0 : ℂ), w ∉ L.lattice := by
    have hnhds : ∀ᶠ w in 𝓝 (0 : ℂ), w ∈ ((L.lattice : Set ℂ) \ {0})ᶜ :=
      L.compl_lattice_sdiff_singleton_mem_nhds 0
    filter_upwards [hnhds.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with w hw hw0
    exact fun hwL => hw ⟨hwL, hw0⟩
  obtain ⟨w, hw, hwout⟩ := (hregular.and hout).exists
  exact hwout ⟨w, hw, rfl⟩

private def EllipticFirstChartIdeal_omitY : MvPolynomial (Fin 3) ℂ →ₐ[ℂ] MvPolynomial (Fin 4) ℂ :=
  aeval ![X 0, X 1, X 3]

private def EllipticFirstChartIdeal_cubicRHS (g₂ g₃ : ℂ) : MvPolynomial (Fin 3) ℂ :=
  C 4 * X 1 ^ 3 - C g₂ * X 1 - C g₃

private lemma EllipticFirstChartIdeal_omitY_eval (A : MvPolynomial (Fin 3) ℂ) (t x y u : ℂ) :
    eval ![t, x, y, u] (EllipticFirstChartIdeal_omitY A) = eval ![t, x, u] A := by
  change (aeval ![t, x, y, u]) ((aeval ![X 0, X 1, X 3]) A) =
    (aeval ![t, x, u]) A
  rw [comp_aeval_apply]
  apply congrArg (fun f : Fin 3 → ℂ => (aeval f) A)
  funext i
  fin_cases i <;> simp

private lemma EllipticFirstChartIdeal_cubic_normal_form (g₂ g₃ : ℂ) (P : MvPolynomial (Fin 4) ℂ) :
    ∃ A B : MvPolynomial (Fin 3) ℂ, ∃ H : MvPolynomial (Fin 4) ℂ,
      P = EllipticFirstChartIdeal_omitY A + X 2 * EllipticFirstChartIdeal_omitY B + extensionChartCubic g₂ g₃ 0 * H := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => exact ⟨C a, 0, 0, by simp [EllipticFirstChartIdeal_omitY]⟩
  | add P Q hP hQ =>
    obtain ⟨A, B, H, rfl⟩ := hP
    obtain ⟨A', B', H', rfl⟩ := hQ
    exact ⟨A + A', B + B', H + H', by simp only [map_add]; ring⟩
  | mul_X P i hP =>
    obtain ⟨A, B, H, rfl⟩ := hP
    fin_cases i
    · refine ⟨A * X 0, B * X 0, H * X 0, ?_⟩
      simp [EllipticFirstChartIdeal_omitY]
      ring
    · refine ⟨A * X 1, B * X 1, H * X 1, ?_⟩
      simp [EllipticFirstChartIdeal_omitY]
      ring
    · refine ⟨EllipticFirstChartIdeal_cubicRHS g₂ g₃ * B, A, EllipticFirstChartIdeal_omitY B + H * X 2, ?_⟩
      simp [EllipticFirstChartIdeal_omitY, EllipticFirstChartIdeal_cubicRHS, extensionChartCubic]
      ring
    · refine ⟨A * X 2, B * X 2, H * X 3, ?_⟩
      simp [EllipticFirstChartIdeal_omitY]
      ring

private lemma EllipticFirstChartIdeal_polynomial_zero_on_regular_fibres (L : PeriodPair)
    (A : MvPolynomial (Fin 3) ℂ)
    (hA : ∀ z, z ∉ L.lattice → ∀ t u : ℂ, eval ![t, L.weierstrassP z, u] A = 0) :
    A = 0 := by
  classical
  let s : Fin 3 → Set ℂ := ![Set.univ, L.weierstrassP '' (L.lattice : Set ℂ)ᶜ, Set.univ]
  have hs : ∀ i, (s i).Infinite := by
    intro i
    fin_cases i
    · exact Set.infinite_univ
    · exact EllipticFirstChartIdeal_wp_regular_image_infinite L
    · exact Set.infinite_univ
  apply funext_set s hs
  intro x hx
  obtain ⟨z, hz, hzx⟩ := hx 1 (Set.mem_univ _)
  have he := hA z hz (x 0) (x 2)
  have hxvec : ![x 0, x 1, x 2] = x := by ext i; fin_cases i <;> rfl
  simpa only [hzx, hxvec, map_zero] using he

/-- The only polynomial relation on the regular elliptic-zeta orbit is the
Weierstrass cubic, despite the extra two additive coordinates. -/
theorem regular_orbit_relation_iff_cubic (L : PeriodPair)
    (P : MvPolynomial (Fin 4) ℂ) :
    (∀ z : ℂ, z ∉ L.lattice →
      eval ![z, L.weierstrassP z, L.derivWeierstrassP z, weierstrassZeta L z] P = 0) ↔
      P ∈ Ideal.span {extensionChartCubic L.g₂ L.g₃ 0} := by
  classical
  constructor
  · intro hP
    have hs := linear_direction_polynomial_saturation L 1 0 one_ne_zero P (by
      simpa using hP)
    obtain ⟨A, B, H, heq⟩ := EllipticFirstChartIdeal_cubic_normal_form L.g₂ L.g₃ P
    have hAB (z : ℂ) (hz : z ∉ L.lattice) (t u : ℂ) :
        eval ![t, L.weierstrassP z, u] A = 0 ∧
        (L.derivWeierstrassP z) * eval ![t, L.weierstrassP z, u] B = 0 := by
      have hm : -z ∉ L.lattice := fun h => hz (by simpa using L.lattice.neg_mem h)
      have hc : eval ![t, L.weierstrassP z, L.derivWeierstrassP z, u]
          (extensionChartCubic L.g₂ L.g₃ 0) = 0 := by
        simp [extensionChartCubic, L.derivWeierstrassP_sq z hz]
        ring
      have hc' : eval ![t, L.weierstrassP z, -L.derivWeierstrassP z, u]
          (extensionChartCubic L.g₂ L.g₃ 0) = 0 := by
        simp [extensionChartCubic, L.derivWeierstrassP_sq z hz]
        ring
      have hp := hs z hz t u
      have hn := hs (-z) hm t u
      rw [heq] at hp hn
      simp only [L.weierstrassP_neg, L.derivWeierstrassP_neg] at hn
      simp only [map_add, map_mul, eval_X, EllipticFirstChartIdeal_omitY_eval, hc, hc', zero_mul, add_zero] at hp hn
      change eval ![t, L.weierstrassP z, u] A +
        L.derivWeierstrassP z * eval ![t, L.weierstrassP z, u] B = 0 at hp
      change eval ![t, L.weierstrassP z, u] A +
        -L.derivWeierstrassP z * eval ![t, L.weierstrassP z, u] B = 0 at hn
      constructor
      · linear_combination (hp + hn) / 2
      · linear_combination (hp - hn) / 2
    have hA : A = 0 := EllipticFirstChartIdeal_polynomial_zero_on_regular_fibres L A
      (fun z hz t u => (hAB z hz t u).1)
    have hFB : EllipticFirstChartIdeal_cubicRHS L.g₂ L.g₃ * B = 0 := by
      apply EllipticFirstChartIdeal_polynomial_zero_on_regular_fibres L
      intro z hz t u
      have hb := (hAB z hz t u).2
      simp only [map_mul]
      have hf : eval ![t, L.weierstrassP z, u] (EllipticFirstChartIdeal_cubicRHS L.g₂ L.g₃) =
          L.derivWeierstrassP z ^ 2 := by
        simp [EllipticFirstChartIdeal_cubicRHS, L.derivWeierstrassP_sq z hz]
      rw [hf, pow_two, mul_assoc, hb, mul_zero]
    have hF : EllipticFirstChartIdeal_cubicRHS L.g₂ L.g₃ ≠ 0 := by
      intro h
      have hc := congrArg (coeff (Finsupp.single (1 : Fin 3) 3)) h
      norm_num [EllipticFirstChartIdeal_cubicRHS, C_mul_X_pow_eq_monomial, C_mul_X_eq_monomial,
        coeff_monomial, coeff_C,
        show Finsupp.single (1 : Fin 3) 1 ≠ Finsupp.single 1 3 from fun h => by
          have hh := congrArg (fun f : Fin 3 →₀ ℕ => f 1) h
          norm_num at hh,
        show (0 : Fin 3 →₀ ℕ) ≠ Finsupp.single 1 3 from fun h => by
          have hh := congrArg (fun f : Fin 3 →₀ ℕ => f 1) h
          norm_num at hh] at hc
    have hB : B = 0 := (mul_eq_zero.mp hFB).resolve_left hF
    rw [heq, hA, hB, map_zero, mul_zero, add_zero, zero_add]
    exact Ideal.mul_mem_right H _ (Ideal.subset_span (Set.mem_singleton _))
  · intro hP z hz
    have hc : eval ![z, L.weierstrassP z, L.derivWeierstrassP z, weierstrassZeta L z]
        (extensionChartCubic L.g₂ L.g₃ 0) = 0 := by
      simp [extensionChartCubic, L.derivWeierstrassP_sq z hz]
      ring
    have hle : Ideal.span {extensionChartCubic L.g₂ L.g₃ 0} ≤
        RingHom.ker (eval ![z, L.weierstrassP z, L.derivWeierstrassP z,
          weierstrassZeta L z]) := by
      exact Ideal.span_le.mpr (by simpa only [Set.singleton_subset_iff, RingHom.mem_ker])
    exact hle hP

private lemma EllipticFirstChartIdeal_first_chart_cubic_relation
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j) :
    extensionChartCubic L.g₂ L.g₃ 0 ∈ extensionGlobalChartKernel S 0 := by
  have ha (j : Fin 5) (w : ℂ) : AnalyticAt ℂ (S j) w := hS j w trivial
  have heq : (fun w => S 2 w ^ 2 * S 0 w - 4 * S 1 w ^ 3 +
      L.g₂ * S 1 w * S 0 w ^ 2 + L.g₃ * S 0 w ^ 3) = (0 : ℂ → ℂ) := by
    apply AnalyticOnNhd.eq_of_eventuallyEq
      (show AnalyticOnNhd ℂ _ Set.univ from fun w _ => by fun_prop)
      (show AnalyticOnNhd ℂ (0 : ℂ → ℂ) Set.univ from fun _ _ => analyticAt_const)
      (z₀ := L.ω₁ / 2)
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds
      L.ω₁_div_two_notMem_lattice] with u hu
    have hc := L.derivWeierstrassP_sq u hu
    simp [hS_value u hu]
    linear_combination D.sigma u ^ 9 * hc
  simp only [extensionGlobalChartKernel, Submodule.mem_iInf, RingHom.mem_ker]
  intro z hz
  have hc : S 2 z ^ 2 * S 0 z - 4 * S 1 z ^ 3 +
      L.g₂ * S 1 z * S 0 z ^ 2 + L.g₃ * S 0 z ^ 3 = 0 := congrFun heq z
  have hz0 : S 0 z ≠ 0 := hz
  simp [extensionChartCoordinates, extensionChartCubic]
  field_simp
  linear_combination hc

/-- In the first chart the global analytic relation ideal is exactly the cubic
ideal. Consequently the canonical base there has the two explicit generators
given by the cubic and normalized auxiliary polynomial. -/
theorem elliptic_first_chart_relation_ideal
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0) :
    extensionGlobalChartKernel S 0 = Ideal.span {extensionChartCubic L.g₂ L.g₃ 0} ∧
      ∀ (Q : MvPolynomial (Fin 7) ℂ) (c : Fin 2),
        extensionFirstCubicChartBaseIdeal L S Q c = extensionGlobalChartBaseIdeal S Q c := by
  classical
  have hkernel : extensionGlobalChartKernel S 0 =
      Ideal.span {extensionChartCubic L.g₂ L.g₃ 0} := by
    apply le_antisymm
    · intro P hP
      apply (regular_orbit_relation_iff_cubic L P).mp
      intro z hz
      have hsig : D.sigma z ≠ 0 := by
        intro h
        obtain ⟨j, hj⟩ := hS_ne z
        exact hj (by simp [hS_value z hz, h])
      have h0 : S 0 z ≠ 0 := by simpa [hS_value z hz] using pow_ne_zero 3 hsig
      have he : eval (extensionChartCoordinates S 0 z) P = 0 := by
        have hh := hP
        simp only [extensionGlobalChartKernel, Submodule.mem_iInf, RingHom.mem_ker] at hh
        exact hh z h0
      have hv : extensionChartCoordinates S 0 z =
          ![z, L.weierstrassP z, L.derivWeierstrassP z, weierstrassZeta L z] := by
        ext i
        fin_cases i <;> simp [extensionChartCoordinates, hS_value z hz, hsig]
      rwa [hv] at he
    · apply Ideal.span_le.mpr
      rintro f rfl
      exact EllipticFirstChartIdeal_first_chart_cubic_relation L D S hS hS_value
  refine ⟨hkernel, ?_⟩
  intro Q c
  by_cases hc : c = 0
  · simp [extensionFirstCubicChartBaseIdeal, extensionGlobalChartBaseIdeal, hc, hkernel]
  · simp [extensionFirstCubicChartBaseIdeal, extensionGlobalChartBaseIdeal, hc]

end WeierstrassEllipticZeta

-- Source: Solutions.WeierstrassProjectiveVanishing
set_option autoImplicit true
set_option maxHeartbeats 200000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
noncomputable section
open MvPolynomial TranscendenceTheory Filter
open scoped Topology
namespace WeierstrassEllipticZeta

private theorem WeierstrassProjectiveVanishing_normalize_eval (Q : MvPolynomial (Fin 7) ℂ) (t x y u : ℂ) :
    eval ![t, x, y, u] (extensionChartNormalize 0 Q) =
      eval ![1, t, 1, x, y, u, y * u + 2 * x ^ 2] Q := by
  change (aeval ![t, x, y, u]) ((aeval (extensionChartSubstitution 0)) Q) = _
  rw [comp_aeval_apply]
  apply congrArg (fun v : Fin 7 → ℂ => eval v Q)
  ext i
  fin_cases i <;> simp [extensionChartSubstitution]

private theorem WeierstrassProjectiveVanishing_extension_block_scale (Q : MvPolynomial (Fin 7) ℂ) (n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 2 + d 3 + d 4 + d 5 + d 6 = n)
    (X : Fin 7 → ℂ) (r : ℂ) :
    eval ![X 0, X 1, r * X 2, r * X 3, r * X 4, r * X 5, r * X 6] Q =
      r ^ n * eval X Q := by
  classical
  rw [eval_eq', eval_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← hQ d hd]
  simp [Fin.prod_univ_seven, mul_pow, pow_add]
  ring

private theorem WeierstrassProjectiveVanishing_regular_fiber_eval
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L) (S : Fin 5 → ℂ → ℂ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (Q : MvPolynomial (Fin 7) ℂ) (n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 2 + d 3 + d 4 + d 5 + d 6 = n)
    (t z u : ℂ) (hz : z ∉ L.lattice) :
    eval ![1, t, S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z,
      S 4 z + u * S 2 z] Q =
      (D.sigma z ^ 3) ^ n * eval
        ![t, L.weierstrassP z, L.derivWeierstrassP z, weierstrassZeta L z + u]
        (extensionChartNormalize 0 Q) := by
  rw [WeierstrassProjectiveVanishing_normalize_eval]
  rw [← WeierstrassProjectiveVanishing_extension_block_scale Q n hQ _ (D.sigma z ^ 3)]
  apply congrArg (fun v : Fin 7 → ℂ => eval v Q)
  ext i
  fin_cases i <;> simp [hS_value z hz] <;> ring

/-- A homogeneous section is zero in the cubic coordinate ring exactly when
it vanishes on every point of the entire extension parametrization, including
the fibers above lattice points. -/
theorem first_chart_section_zero_iff_projective_fibers
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L) (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (Q : MvPolynomial (Fin 7) ℂ) (n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 2 + d 3 + d 4 + d 5 + d 6 = n) :
    firstCubicQuotient L (extensionChartNormalize 0 Q) = 0 ↔
      ∀ t z u : ℂ, eval ![1, t, S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z,
        S 4 z + u * S 2 z] Q = 0 := by
  constructor
  · intro hzero t z u
    have hzpoly := (first_cubic_quotient_eq_zero_iff_vanishes L _).mp hzero
    have ha : AnalyticOnNhd ℂ (fun w : ℂ =>
        eval ![1, t, S 0 w, S 1 w, S 2 w, S 3 w + u * S 0 w,
          S 4 w + u * S 2 w] Q) Set.univ := by
      intro w _
      apply AnalyticAt.aeval_mvPolynomial
      intro i
      fin_cases i
      · exact analyticAt_const
      · exact analyticAt_const
      · exact hS 0 w trivial
      · exact hS 1 w trivial
      · exact hS 2 w trivial
      · exact (hS 3 w trivial).add (analyticAt_const.mul (hS 0 w trivial))
      · exact (hS 4 w trivial).add (analyticAt_const.mul (hS 2 w trivial))
    have hall := AnalyticOnNhd.eq_of_eventuallyEq ha
      (show AnalyticOnNhd ℂ (0 : ℂ → ℂ) Set.univ from fun _ _ => analyticAt_const)
      (z₀ := L.ω₁ / 2) (by
        filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds L.ω₁_div_two_notMem_lattice]
          with w hw
        rw [WeierstrassProjectiveVanishing_regular_fiber_eval L D S hS_value Q n hQ t w u hw]
        rw [hzpoly t (L.weierstrassP w) (L.derivWeierstrassP w)
          (weierstrassZeta L w + u) (L.derivWeierstrassP_sq w hw), mul_zero]
        rfl)
    exact congrFun hall z
  · intro hzero
    change (Ideal.Quotient.mk (Ideal.span {extensionChartCubic L.g₂ L.g₃ 0})) _ = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply (regular_orbit_relation_iff_cubic L _).mp
    intro z hz
    have hsig : D.sigma z ≠ 0 := by
      intro hs
      obtain ⟨j, hj⟩ := hS_ne z
      exact hj (by simp [hS_value z hz, hs])
    have hh := hzero z z 0
    rw [WeierstrassProjectiveVanishing_regular_fiber_eval L D S hS_value Q n hQ z z 0 hz] at hh
    simpa using (mul_eq_zero.mp hh).resolve_left (pow_ne_zero _ (pow_ne_zero 3 hsig))

/-- The one-parameter Weierstrass curve and the complete parametrized
extension have the same homogeneous polynomial relations. -/
theorem projective_curve_fiber_vanishing_criterion
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L) (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (Q : MvPolynomial (Fin 7) ℂ) (n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 2 + d 3 + d 4 + d 5 + d 6 = n) :
    (∀ z : ℂ, eval ![1, z, S 0 z, S 1 z, S 2 z, S 3 z, S 4 z] Q = 0) ↔
      ∀ t z u : ℂ, eval ![1, t, S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z,
        S 4 z + u * S 2 z] Q = 0 := by
  constructor
  · intro hzero
    apply (first_chart_section_zero_iff_projective_fibers L D S hS hS_value hS_ne Q n hQ).mp
    change (Ideal.Quotient.mk (Ideal.span {extensionChartCubic L.g₂ L.g₃ 0})) _ = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply (regular_orbit_relation_iff_cubic L _).mp
    intro z hz
    have hsig : D.sigma z ≠ 0 := by
      intro hs
      obtain ⟨j, hj⟩ := hS_ne z
      exact hj (by simp [hS_value z hz, hs])
    have hh : eval ![1, z, S 0 z, S 1 z, S 2 z, S 3 z + 0 * S 0 z,
        S 4 z + 0 * S 2 z] Q = 0 := by simpa using hzero z
    rw [WeierstrassProjectiveVanishing_regular_fiber_eval L D S hS_value Q n hQ z z 0 hz] at hh
    simpa using (mul_eq_zero.mp hh).resolve_left (pow_ne_zero _ (pow_ne_zero 3 hsig))
  · intro h z
    simpa using h z z 0

/-- The zero section in the cubic quotient is exactly a section vanishing
on the actual projective extension carrier, rather than just its affine
chart or an unspecified coordinate ring. -/
theorem projective_extension_section_vanishing_criterion
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L) (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (η : L.lattice →ₗ[ℤ] ℂ)
    [AddCommGroup (ProjectiveExtensionChartLocus L.g₂ L.g₃)]
    (e : GraphQuotientExtension L.lattice η ≃+ ProjectiveExtensionChartLocus L.g₂ L.g₃)
    (he : ∀ z u : ℂ, ∃ hv :
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] ≠ 0,
        (e ((extensionPeriodGraph L.lattice η).mkQ (z, u))).val.val = Projectivization.mk ℂ
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] hv)
    (Q : MvPolynomial (Fin 7) ℂ) (n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 2 + d 3 + d 4 + d 5 + d 6 = n) :
    firstCubicQuotient L (extensionChartNormalize 0 Q) = 0 ↔
      ∀ (t : ℂ) (p : ProjectiveExtensionChartLocus L.g₂ L.g₃),
        eval ![1, t, p.val.val.rep 0, p.val.val.rep 1, p.val.val.rep 2,
          p.val.val.rep 3, p.val.val.rep 4] Q = 0 := by
  have hrep (t z u : ℂ) : ∃ c : ℂ, c ≠ 0 ∧
      (let p := e ((extensionPeriodGraph L.lattice η).mkQ (z, u))
       eval ![1, t, p.val.val.rep 0, p.val.val.rep 1, p.val.val.rep 2,
         p.val.val.rep 3, p.val.val.rep 4] Q) = c ^ n *
           eval ![1, t, S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z,
             S 4 z + u * S 2 z] Q := by
    obtain ⟨hv, hp⟩ := he z u
    obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep ℂ _ hv
    refine ⟨c.val, c.ne_zero, ?_⟩
    dsimp only
    rw [hp, ← hc]
    simp only [Units.smul_def, Pi.smul_apply, smul_eq_mul]
    exact WeierstrassProjectiveVanishing_extension_block_scale Q n hQ
        ![1, t, S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] c.val
  rw [first_chart_section_zero_iff_projective_fibers L D S hS hS_value hS_ne Q n hQ]
  constructor
  · intro h t p
    obtain ⟨p, rfl⟩ := e.surjective p
    obtain ⟨⟨z, u⟩, rfl⟩ := (extensionPeriodGraph L.lattice η).mkQ_surjective p
    obtain ⟨c, _, hc⟩ := hrep t z u
    rw [hc, h t z u, mul_zero]
  · intro h t z u
    obtain ⟨c, hc0, hc⟩ := hrep t z u
    rw [h] at hc
    exact (mul_eq_zero.mp hc.symm).resolve_left (pow_ne_zero n hc0)

end WeierstrassEllipticZeta


-- Source: Solutions.PhilipponProjectiveGeometry
set_option autoImplicit true
set_option maxHeartbeats 200000

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity
universe u
namespace MultiProjectiveSpace

variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem IsHomogeneous.mul {P Q : M.CoordinateRing} {D E : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (hQ : M.IsHomogeneous Q E) :
    M.IsHomogeneous (P * Q) (D + E) := by
  classical
  intro d hd i
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q hd)
  simpa only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hP a ha i,
    hQ b hb i]

theorem isHomogeneous_one : M.IsHomogeneous 1 0 := by
  classical
  intro d hd i
  have hd0 : d = 0 := by simpa using hd
  simp [hd0]

theorem isOpen_basic (P : M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : M.IsHomogeneous P D) :
    @IsOpen _ M.zariskiTopology {x | M.eval P x ≠ 0} := by
  exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨P, D, hP, rfl⟩

theorem isClosed_zero (P : M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : M.IsHomogeneous P D) :
    @IsClosed _ M.zariskiTopology {x | M.eval P x = 0} := by
  letI := M.zariskiTopology
  simpa only [Set.compl_setOf, not_not] using (M.isOpen_basic P D hP).isClosed_compl

theorem isTopologicalBasis_basic :
    @TopologicalSpace.IsTopologicalBasis _ M.zariskiTopology
      {U | ∃ P : M.CoordinateRing, ∃ D, M.IsHomogeneous P D ∧
        U = {x | M.eval P x ≠ 0}} := by
  classical
  letI := M.zariskiTopology
  have h := TopologicalSpace.isTopologicalBasis_of_subbasis_of_inter
    (show M.zariskiTopology = TopologicalSpace.generateFrom _ from rfl) (by
      rintro U ⟨P, D, hP, rfl⟩ V ⟨Q, E, hQ, rfl⟩
      refine ⟨P * Q, D + E, hP.mul M hQ, ?_⟩
      ext x
      simp [eval, mul_ne_zero_iff])
  have huniv : Set.univ ∈ {U | ∃ P : M.CoordinateRing, ∃ D,
      M.IsHomogeneous P D ∧ U = {x | M.eval P x ≠ 0}} := by
    refine ⟨1, 0, M.isHomogeneous_one, ?_⟩
    ext x
    simp [eval]
  simpa only [Set.insert_eq_of_mem huniv] using h

theorem eval_eq_zero_of_mem_vanishingIdeal {S : Set M.Point}
    {P : M.CoordinateRing} (hP : P ∈ M.vanishingIdeal S)
    {x : M.Point} (hx : x ∈ S) : M.eval P x = 0 := by
  have hle : M.vanishingIdeal S ≤ RingHom.ker (MvPolynomial.eval (M.coordinate x)) := by
    apply Ideal.span_le.mpr
    rintro Q ⟨_, hQ⟩
    exact hQ x hx
  exact hle hP

theorem vanishingIdeal_antitone {S T : Set M.Point} (h : S ⊆ T) :
    M.vanishingIdeal T ≤ M.vanishingIdeal S := by
  apply Ideal.span_mono
  rintro P ⟨hP, hz⟩
  exact ⟨hP, fun x hx => hz x (h hx)⟩

theorem isClosed_zeroLocus_vanishingIdeal (S : Set M.Point) :
    @IsClosed _ M.zariskiTopology (M.zeroLocus (M.vanishingIdeal S)) := by
  letI := M.zariskiTopology
  have hset : M.zeroLocus (M.vanishingIdeal S) =
      ⋂ P : {P : M.CoordinateRing // (∃ D, M.IsHomogeneous P D) ∧
        ∀ x ∈ S, M.eval P x = 0}, {x | M.eval P.val x = 0} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_setOf_eq, zeroLocus]
    constructor
    · intro hx P
      exact hx P (Ideal.subset_span P.property)
    · intro hx P hP
      have hle : M.vanishingIdeal S ≤ RingHom.ker (MvPolynomial.eval (M.coordinate x)) := by
        apply Ideal.span_le.mpr
        intro Q hQ
        exact hx ⟨Q, hQ⟩
      exact hle hP
  rw [hset]
  apply isClosed_iInter
  intro P
  obtain ⟨D, hD⟩ := P.property.1
  exact M.isClosed_zero P.val D hD

/-- The chosen-representative ideal agrees with Zariski closure. -/
theorem zeroLocus_vanishingIdeal_eq_closure (S : Set M.Point) :
    M.zeroLocus (M.vanishingIdeal S) = @closure _ M.zariskiTopology S := by
  letI := M.zariskiTopology
  apply Set.Subset.antisymm
  · intro x hx
    apply M.isTopologicalBasis_basic.mem_closure_iff.mpr
    rintro U ⟨P, D, hP, rfl⟩ hxU
    by_contra hn
    have hPS : ∀ y ∈ S, M.eval P y = 0 := by
      intro y hy
      by_contra hp
      exact hn ⟨y, hp, hy⟩
    exact hxU (hx P (Ideal.subset_span ⟨⟨D, hP⟩, hPS⟩))
  · apply closure_minimal
    · intro x hx P hP
      exact M.eval_eq_zero_of_mem_vanishingIdeal hP hx
    · exact M.isClosed_zeroLocus_vanishingIdeal S

end MultiProjectiveSpace

theorem singleBlock_isHomogeneous {K : Type*} [Field K] {N d : ℕ}
    {P : MvPolynomial (Fin (N + 1)) K} (hP : P.IsHomogeneous d) :
    (projectiveSpace K N).IsHomogeneous
      (MvPolynomial.rename (fun j => ⟨(0 : Fin 1), j⟩) P) (fun _ => d) := by
  classical
  intro a ha i
  have h := hP.rename_isHomogeneous (f := fun j => (⟨(0 : Fin 1), j⟩ :
    (projectiveSpace K N).Variable)) (MvPolynomial.mem_support_iff.mp ha)
  change Finsupp.weight (1 : (projectiveSpace K N).Variable → ℕ) a = d at h
  rw [Finsupp.weight_eq_sum] at h
  simp only [Pi.one_apply, smul_eq_mul, mul_one] at h
  rw [Fintype.sum_sigma] at h
  change (∑ x : Fin 1, ∑ y : Fin (N + 1), a ⟨x, y⟩) = d at h
  change Fin 1 at i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  change (∑ j : Fin (N + 1), a ⟨(0 : Fin 1), j⟩) = d
  exact (Fin.sum_univ_one _).symm.trans h

theorem projective_isClosed_zero {K : Type*} [Field K] {N d : ℕ}
    {P : MvPolynomial (Fin (N + 1)) K} (hP : P.IsHomogeneous d) :
    @IsClosed _
      (TopologicalSpace.induced (fun (p : Projectivization K (Fin (N + 1) → K)) =>
        (fun _ => p : (projectiveSpace K N).Point)) (projectiveSpace K N).zariskiTopology)
      {p | MvPolynomial.eval p.rep P = 0} := by
  letI := (projectiveSpace K N).zariskiTopology
  letI := TopologicalSpace.induced (fun (p : Projectivization K (Fin (N + 1) → K)) =>
    (fun _ => p : (projectiveSpace K N).Point)) (projectiveSpace K N).zariskiTopology
  have hcont : @Continuous _ (projectiveSpace K N).Point _ (projectiveSpace K N).zariskiTopology
      (fun (p : Projectivization K (Fin (N + 1) → K)) =>
      (fun _ => p : (projectiveSpace K N).Point)) := continuous_induced_dom
  have h := ((projectiveSpace K N).isClosed_zero _ _
    (singleBlock_isHomogeneous hP)).preimage hcont
  convert h using 1
  ext p
  change MvPolynomial.eval p.rep P = 0 ↔
    (projectiveSpace K N).eval
      (MvPolynomial.rename (fun j => ⟨(0 : Fin 1), j⟩) P) (fun _ => p) = 0
  simp only [MultiProjectiveSpace.eval, MvPolynomial.eval_rename]
  rfl

theorem projective_isOpen_coordinate {K : Type*} [Field K] {N : ℕ}
    (j : Fin (N + 1)) :
    @IsOpen _
      (TopologicalSpace.induced (fun (p : Projectivization K (Fin (N + 1) → K)) =>
        (fun _ => p : (projectiveSpace K N).Point)) (projectiveSpace K N).zariskiTopology)
      {p | p.rep j ≠ 0} := by
  letI := (projectiveSpace K N).zariskiTopology
  letI := TopologicalSpace.induced (fun (p : Projectivization K (Fin (N + 1) → K)) =>
    (fun _ => p : (projectiveSpace K N).Point)) (projectiveSpace K N).zariskiTopology
  have hcont : @Continuous _ (projectiveSpace K N).Point _ (projectiveSpace K N).zariskiTopology
      (fun (p : Projectivization K (Fin (N + 1) → K)) =>
      (fun _ => p : (projectiveSpace K N).Point)) := continuous_induced_dom
  have h := ((projectiveSpace K N).isOpen_basic _ _
    (singleBlock_isHomogeneous (MvPolynomial.isHomogeneous_X K j))).preimage
      hcont
  convert h using 1
  ext p
  change p.rep j ≠ 0 ↔
    (projectiveSpace K N).eval
      (MvPolynomial.rename (fun j => ⟨(0 : Fin 1), j⟩) (MvPolynomial.X j)) (fun _ => p) ≠ 0
  simp [MultiProjectiveSpace.eval, MultiProjectiveSpace.coordinate]

theorem projective_regular_of_homogeneous
    {K X : Type u} [Field K] {N N' d : ℕ}
    (e : X → Projectivization K (Fin (N + 1) → K))
    (f : X → Projectivization K (Fin (N' + 1) → K))
    (P : Fin (N' + 1) → MvPolynomial (Fin (N + 1)) K)
    (hP : ∀ j, (P j).IsHomogeneous d)
    (hf : ∀ x, ∃ h : (fun j => MvPolynomial.eval (e x).rep (P j)) ≠ 0,
      Projectivization.mk K (fun j => MvPolynomial.eval (e x).rep (P j)) h = f x) :
    MultiProjectiveSpace.IsRegularAlong (projectiveSpace K N) (projectiveSpace K N')
      (fun x => fun _ => e x) (fun x => fun _ => f x) := by
  letI := (projectiveSpace K N).zariskiTopology
  intro x b
  let Q : Fin (N' + 1) → (projectiveSpace K N).CoordinateRing :=
    fun j => MvPolynomial.rename (fun k => ⟨(0 : Fin 1), k⟩) (P j)
  refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, fun _ => d,
    Q,
    (fun j => singleBlock_isHomogeneous (hP j)), ?_⟩
  intro y _
  have heq : (fun j => (projectiveSpace K N).eval (Q j) (fun _ => e y)) =
      (fun j => MvPolynomial.eval (e y).rep (P j)) := by
    ext j
    change MvPolynomial.eval _ (MvPolynomial.rename _ (P j)) = _
    rw [MvPolynomial.eval_rename]
    rfl
  obtain ⟨hne, hmk⟩ := hf y
  change ∃ h : (fun j : Fin (N' + 1) =>
      (projectiveSpace K N).eval (Q j) (fun _ => e y)) ≠ 0,
    Projectivization.mk K
      (fun j : Fin (N' + 1) => (projectiveSpace K N).eval (Q j) (fun _ => e y)) h = f y
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact hne
  · simpa only [heq] using hmk

end PhilipponMultiplicity

namespace WeierstrassEllipticZeta
open PhilipponMultiplicity

theorem projective_extension_locallyClosed (g₂ g₃ : ℂ) :
    @IsLocallyClosed _
      (TopologicalSpace.induced (fun p _ => p) (projectiveSpace ℂ 4).zariskiTopology)
      {p : Projectivization ℂ (Fin 5 → ℂ) |
        MvPolynomial.eval p.rep extensionQuadric = 0 ∧
        MvPolynomial.eval p.rep (extensionCubic g₂ g₃) = 0 ∧
        (p.rep 0 ≠ 0 ∨ p.rep 2 ≠ 0)} := by
  letI := TopologicalSpace.induced (fun (p : Projectivization ℂ (Fin 5 → ℂ)) =>
    (fun _ => p : (projectiveSpace ℂ 4).Point)) (projectiveSpace ℂ 4).zariskiTopology
  have hq : extensionQuadric.IsHomogeneous 2 := by
    exact ((MvPolynomial.isHomogeneous_X ℂ 0).mul
      (MvPolynomial.isHomogeneous_X ℂ 4)).sub
      ((MvPolynomial.isHomogeneous_X ℂ 2).mul (MvPolynomial.isHomogeneous_X ℂ 3)) |>.sub
        (MvPolynomial.isHomogeneous_C_mul_X_pow 2 1 2)
  have hc : (extensionCubic g₂ g₃).IsHomogeneous 3 := by
    exact (((MvPolynomial.isHomogeneous_X ℂ 0).mul
      (MvPolynomial.isHomogeneous_X_pow 2 2)).sub
      (MvPolynomial.isHomogeneous_C_mul_X_pow 4 1 3)).add
        ((MvPolynomial.isHomogeneous_C_mul_X_pow g₂ 0 2).mul
          (MvPolynomial.isHomogeneous_X ℂ 1)) |>.add
        (MvPolynomial.isHomogeneous_C_mul_X_pow g₃ 0 3)
  convert
    ((projective_isClosed_zero hq).inter (projective_isClosed_zero hc)).isLocallyClosed.inter
      ((projective_isOpen_coordinate (K := ℂ) (0 : Fin 5)).union
        (projective_isOpen_coordinate (K := ℂ) (2 : Fin 5))).isLocallyClosed using 1
  ext p
  simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq, and_assoc]

theorem projective_extension_fiber_action_regular (g₂ g₃ u : ℂ)
    (F : ProjectiveExtensionFiberModel g₂ g₃) :
    MultiProjectiveSpace.IsRegularAlong (projectiveSpace ℂ 4) (projectiveSpace ℂ 4)
      (fun p : ProjectiveExtensionChartLocus g₂ g₃ => fun _ => extensionProjectivePoint p)
      (fun p => fun _ => extensionProjectivePoint (F.action u p)) := by
  let P : Fin 5 → MvPolynomial (Fin 5) ℂ :=
    ![MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2,
      MvPolynomial.X 3 + MvPolynomial.C u * MvPolynomial.X 0,
      MvPolynomial.X 4 + MvPolynomial.C u * MvPolynomial.X 2]
  apply projective_regular_of_homogeneous _ _ P (d := 1)
  · intro j
    fin_cases j
    · exact MvPolynomial.isHomogeneous_X ℂ 0
    · exact MvPolynomial.isHomogeneous_X ℂ 1
    · exact MvPolynomial.isHomogeneous_X ℂ 2
    · exact (MvPolynomial.isHomogeneous_X ℂ 3).add
        ((MvPolynomial.isHomogeneous_C (Fin 5) u).mul (MvPolynomial.isHomogeneous_X ℂ 0))
    · exact (MvPolynomial.isHomogeneous_X ℂ 4).add
        ((MvPolynomial.isHomogeneous_C (Fin 5) u).mul (MvPolynomial.isHomogeneous_X ℂ 2))
  · intro p
    have heq : (fun j => MvPolynomial.eval (extensionProjectivePoint p).rep (P j)) =
        extensionFiberShear u (extensionProjectivePoint p).rep := by
      ext j
      fin_cases j <;> simp [P, extensionFiberShear]
    obtain ⟨h, hh⟩ := F.action_coords u p
    exact ⟨by simpa only [heq] using h, by simpa only [heq] using hh.symm⟩

end WeierstrassEllipticZeta

-- Source: Solutions.WeierstrassHilbertSections
set_option autoImplicit true
set_option maxHeartbeats 200000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
noncomputable section
open scoped BigOperators
open MvPolynomial TranscendenceTheory PhilipponMultiplicity

namespace WeierstrassEllipticZeta

abbrev ExtensionProjectiveVariable := Sigma fun _ : Fin 1 => Fin 5

/-- Include the extension's five variables as the last block of the seven
coordinates used in the original section-space calculation. -/
def extensionCoordinateInjection (i : ExtensionProjectiveVariable) : Fin 7 :=
  Fin.natAdd 2 i.2

theorem extensionCoordinateInjection_injective :
    Function.Injective extensionCoordinateInjection := by
  rintro ⟨a, j⟩ ⟨b, k⟩ h
  have ha : a = (0 : Fin 1) := Subsingleton.elim _ _
  have hb : b = (0 : Fin 1) := Subsingleton.elim _ _
  subst a
  subst b
  have hj : j = k := Fin.ext (by
    have hh := congrArg Fin.val h
    dsimp [extensionCoordinateInjection, Fin.natAdd] at hh
    omega)
  subst k
  rfl

private theorem WeierstrassHilbertSections_extension_weight (m : ExtensionProjectiveVariable →₀ ℕ) :
    Finsupp.weight (Hilbert.blockWeight 1 (fun _ => 4)) m =
      fun _ => ∑ j : Fin 5, m ⟨(0 : Fin 1), j⟩ := by
  ext i
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  subst i
  simp [Finsupp.weight_eq_sum, Hilbert.blockWeight, Fintype.sum_sigma]

theorem extension_degreePiece_iff (P : (projectiveSpace ℂ 4).CoordinateRing) (n : ℕ) :
    P ∈ Hilbert.degreePiece ℂ 1 (fun _ => 4) (fun _ => n) ↔
      ∀ m ∈ P.support, ∑ j : Fin 5, m ⟨(0 : Fin 1), j⟩ = n := by
  change (∀ m, coeff m P ≠ 0 → _ = _) ↔ _
  simp only [WeierstrassHilbertSections_extension_weight, ← mem_support_iff]
  constructor
  · intro h m hm
    exact congrFun (h m hm) 0
  · intro h m hm
    exact _root_.funext (fun _ => h m hm)

private theorem WeierstrassHilbertSections_extension_renamed_exponent (m : ExtensionProjectiveVariable →₀ ℕ) :
    (m.mapDomain extensionCoordinateInjection) 0 = 0 ∧
    (m.mapDomain extensionCoordinateInjection) 1 = 0 ∧
    (∀ j : Fin 5, (m.mapDomain extensionCoordinateInjection) (Fin.natAdd 2 j) = m ⟨(0 : Fin 1), j⟩) := by
  constructor
  · apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨⟨a, j⟩, h⟩
    have hh := congrArg Fin.val h
    dsimp [extensionCoordinateInjection, Fin.natAdd] at hh
    omega
  constructor
  · apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨⟨a, j⟩, h⟩
    have hh := congrArg Fin.val h
    dsimp [extensionCoordinateInjection, Fin.natAdd] at hh
    omega
  · intro j
    exact Finsupp.mapDomain_apply extensionCoordinateInjection_injective m ⟨(0 : Fin 1), j⟩

theorem extension_rename_bihomogeneous_iff
    (P : (projectiveSpace ℂ 4).CoordinateRing) (n : ℕ) :
    P ∈ Hilbert.degreePiece ℂ 1 (fun _ => 4) (fun _ => n) ↔
      ∀ d ∈ (rename extensionCoordinateInjection P).support,
        d 0 + d 1 = 0 ∧ d 2 + d 3 + d 4 + d 5 + d 6 = n := by
  classical
  rw [extension_degreePiece_iff]
  have hexp (m : ExtensionProjectiveVariable →₀ ℕ) :
      (m.mapDomain extensionCoordinateInjection) 0 +
          (m.mapDomain extensionCoordinateInjection) 1 = 0 ∧
      ((m.mapDomain extensionCoordinateInjection) 2 +
          (m.mapDomain extensionCoordinateInjection) 3 +
          (m.mapDomain extensionCoordinateInjection) 4 +
          (m.mapDomain extensionCoordinateInjection) 5 +
          (m.mapDomain extensionCoordinateInjection) 6) = ∑ j : Fin 5, m ⟨(0 : Fin 1), j⟩ := by
    obtain ⟨h0, h1, h⟩ := WeierstrassHilbertSections_extension_renamed_exponent m
    constructor
    · simp [h0, h1]
    · have h2 := h 0
      have h3 := h 1
      have h4 := h 2
      have h5 := h 3
      have h6 := h 4
      change (m.mapDomain extensionCoordinateInjection) 2 = m ⟨(0 : Fin 1), 0⟩ at h2
      change (m.mapDomain extensionCoordinateInjection) 3 = m ⟨(0 : Fin 1), 1⟩ at h3
      change (m.mapDomain extensionCoordinateInjection) 4 = m ⟨(0 : Fin 1), 2⟩ at h4
      change (m.mapDomain extensionCoordinateInjection) 5 = m ⟨(0 : Fin 1), 3⟩ at h5
      change (m.mapDomain extensionCoordinateInjection) 6 = m ⟨(0 : Fin 1), 4⟩ at h6
      rw [h2, h3, h4, h5, h6]
      simp [Fin.sum_univ_succ]
      omega
  rw [support_rename_of_injective extensionCoordinateInjection_injective]
  constructor
  · intro h d hd
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hd
    exact ⟨(hexp m).1, (hexp m).2.trans (h m hm)⟩
  · intro h m hm
    have hh := (h _ (Finset.mem_image.mpr ⟨m, hm, rfl⟩)).2
    rwa [(hexp m).2] at hh

/-- Every section with additive degree zero is the unique renaming of an
extension-only homogeneous form. -/
theorem exists_extension_form (Q : MvPolynomial (Fin 7) ℂ) (n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 0 + d 1 = 0 ∧ d 2 + d 3 + d 4 + d 5 + d 6 = n) :
    ∃ P : (projectiveSpace ℂ 4).CoordinateRing,
      P ∈ Hilbert.degreePiece ℂ 1 (fun _ => 4) (fun _ => n) ∧
      rename extensionCoordinateInjection P = Q := by
  classical
  have hvars : (Q.vars : Set (Fin 7)) ⊆ Set.range extensionCoordinateInjection := by
    intro i hi
    obtain ⟨d, hd, hi⟩ := (mem_vars_iff_mem_support i).mp hi
    have hnonzero : d i ≠ 0 := Finsupp.mem_support_iff.mp hi
    have hd01 := (hQ d hd).1
    have hi0 : i ≠ 0 := by intro h; subst i; omega
    have hi1 : i ≠ 1 := by intro h; subst i; omega
    refine ⟨⟨0, ⟨i.val - 2, by omega⟩⟩, ?_⟩
    apply Fin.ext
    simp only [extensionCoordinateInjection, Fin.val_natAdd]
    have hi0' : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
    have hi1' : i.val ≠ 1 := fun h => hi1 (Fin.ext h)
    omega
  obtain ⟨P, hP⟩ := exists_rename_eq_of_vars_subset_range Q extensionCoordinateInjection
    extensionCoordinateInjection_injective hvars
  exact ⟨P, (extension_rename_bihomogeneous_iff P n).mpr (hP ▸ hQ), hP⟩

def extensionSectionRestriction (L : PeriodPair) :
    (projectiveSpace ℂ 4).CoordinateRing →ₗ[ℂ] FirstCubicCoordinateRing L :=
  ((firstCubicQuotient L).comp ((extensionChartNormalize 0).comp
    (rename extensionCoordinateInjection))).toLinearMap

theorem firstChartSectionSpace_eq_extension_image (L : PeriodPair) (n : ℕ) :
    firstChartSectionSpace L 0 n =
      (Hilbert.degreePiece ℂ 1 (fun _ => 4) (fun _ => n)).map
        (extensionSectionRestriction L) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro r ⟨Q, hQ, rfl⟩
    obtain ⟨P, hP, rfl⟩ := exists_extension_form Q n hQ
    exact Submodule.mem_map.mpr ⟨P, hP, rfl⟩
  · rintro r ⟨P, hP, rfl⟩
    apply Submodule.subset_span
    exact ⟨rename extensionCoordinateInjection P,
      (extension_rename_bihomogeneous_iff P n).mp hP, rfl⟩

private theorem WeierstrassHilbertSections_extension_form_eval (P : (projectiveSpace ℂ 4).CoordinateRing)
    (t : ℂ) {g₂ g₃ : ℂ} (p : ProjectiveExtensionChartLocus g₂ g₃) :
    eval ![1, t, p.val.val.rep 0, p.val.val.rep 1, p.val.val.rep 2,
      p.val.val.rep 3, p.val.val.rep 4] (rename extensionCoordinateInjection P) =
      (projectiveSpace ℂ 4).eval P (fun _ => p.val.val) := by
  rw [eval_rename]
  apply congrArg (fun v => eval v P)
  funext i
  rcases i with ⟨b, j⟩
  change Fin 1 at b
  have hb : b = 0 := Subsingleton.elim _ _
  subst b
  fin_cases j <;> rfl

section Geometry

variable (L : PeriodPair) (D : EllipticSigmaDifferentialData L) (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (η : L.lattice →ₗ[ℤ] ℂ)
    [AddCommGroup (ProjectiveExtensionChartLocus L.g₂ L.g₃)]
    (e : GraphQuotientExtension L.lattice η ≃+ ProjectiveExtensionChartLocus L.g₂ L.g₃)
    (he : ∀ z u : ℂ, ∃ hv :
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] ≠ 0,
        (e ((extensionPeriodGraph L.lattice η).mkQ (z, u))).val.val = Projectivization.mk ℂ
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] hv)

private abbrev WeierstrassHilbertSections_extensionProjectiveIdeal :=
  (projectiveSpace ℂ 4).vanishingIdeal
    (Set.range (fun p : ProjectiveExtensionChartLocus L.g₂ L.g₃ =>
      fun _ : Fin 1 => p.val.val))

include D S hS hS_value hS_ne η e he in
theorem extensionSectionRestriction_eq_zero_iff
    (P : (projectiveSpace ℂ 4).CoordinateRing) (n : ℕ)
    (hP : P ∈ Hilbert.degreePiece ℂ 1 (fun _ => 4) (fun _ => n)) :
    extensionSectionRestriction L P = 0 ↔ P ∈ WeierstrassHilbertSections_extensionProjectiveIdeal L := by
  have hQ := (extension_rename_bihomogeneous_iff P n).mp hP
  have hPhom : (projectiveSpace ℂ 4).IsHomogeneous P (fun _ => n) := by
    intro m hm i
    change Fin 1 at i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact (extension_degreePiece_iff P n).mp hP m hm
  change firstCubicQuotient L (extensionChartNormalize 0
    (rename extensionCoordinateInjection P)) = 0 ↔ _
  rw [projective_extension_section_vanishing_criterion L D S hS hS_value hS_ne η e he
    _ n (fun d hd => (hQ d hd).2)]
  simp only [WeierstrassHilbertSections_extension_form_eval]
  constructor
  · intro h
    apply Ideal.subset_span
    refine ⟨⟨fun _ => n, hPhom⟩, ?_⟩
    rintro _ ⟨p, rfl⟩
    exact h 0 p
  · intro h t p
    exact (projectiveSpace ℂ 4).eval_eq_zero_of_mem_vanishingIdeal h ⟨p, rfl⟩

include D S hS hS_value hS_ne η e he in
/-- The actual quotient Hilbert function of the projective extension agrees
with the section-space dimension calculated in its cubic affine chart. -/
theorem projective_extension_hilbert_function_eq_sections (n : ℕ) :
    Hilbert.hilbertFunction ℂ 1 (fun _ => 4)
      ((projectiveSpace ℂ 4).vanishingIdeal
        (Set.range (fun p : ProjectiveExtensionChartLocus L.g₂ L.g₃ =>
          fun _ : Fin 1 => p.val.val))) (fun _ => n) =
      Module.finrank ℂ (firstChartSectionSpace L 0 n) := by
  let V := Hilbert.degreePiece ℂ 1 (fun _ => 4) (fun _ => n)
  let I := WeierstrassHilbertSections_extensionProjectiveIdeal L
  let f := (Ideal.Quotient.mkₐ ℂ I).toLinearMap.domRestrict V
  let g := (extensionSectionRestriction L).domRestrict V
  have hker : LinearMap.ker f = LinearMap.ker g := by
    ext P
    change (Ideal.Quotient.mk I) P.val = 0 ↔ extensionSectionRestriction L P.val = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact (extensionSectionRestriction_eq_zero_iff L D S hS hS_value hS_ne η e he
      P.val n P.property).symm
  let E := f.quotKerEquivRange.symm.trans
    ((Submodule.quotEquivOfEq _ _ hker).trans g.quotKerEquivRange)
  have hdim := E.finrank_eq
  have hf : LinearMap.range f = Hilbert.quotientPiece ℂ 1 (fun _ => 4) I
      (fun _ => n) := by
    ext x
    constructor
    · rintro ⟨P, rfl⟩
      exact ⟨P.val, P.property, rfl⟩
    · rintro ⟨P, hP, rfl⟩
      exact ⟨⟨P, hP⟩, rfl⟩
  have hg : LinearMap.range g = firstChartSectionSpace L 0 n := by
    rw [firstChartSectionSpace_eq_extension_image L n]
    ext x
    constructor
    · rintro ⟨P, rfl⟩
      exact ⟨P.val, P.property, rfl⟩
    · rintro ⟨P, hP, rfl⟩
      exact ⟨⟨P, hP⟩, rfl⟩
  rw [hf, hg] at hdim
  exact hdim

end Geometry

end WeierstrassEllipticZeta


-- Source: Solutions.BirelationCubicSections
set_option autoImplicit true
set_option maxHeartbeats 200000

noncomputable section
open scoped Classical
open MvPolynomial
namespace WeierstrassEllipticZeta

private abbrev BirelationCubicSections_SectionIndex (m n : ℕ) :=
  Fin (m + 1) × (Σ a : Fin (min 2 n + 1),
    Fin (n - a.val + 1) × Fin (n - a.val + 1))

private def BirelationCubicSections_sectionFamily {A : Type*} [CommRing A]
    (t x y u w : A) (m n : ℕ) (s : BirelationCubicSections_SectionIndex m n) : A :=
  t ^ s.1.val * x ^ s.2.1.val * y ^ (s.2.2.1.val - s.2.2.2.val) *
    u ^ (s.2.2.2.val - s.2.2.1.val) * w ^ min s.2.2.1.val s.2.2.2.val

private def BirelationCubicSections_sectionSpan {A : Type*} [CommRing A] [Algebra ℂ A]
    (t x y u w : A) (m n : ℕ) : Submodule ℂ A :=
  Submodule.span ℂ (Set.range (BirelationCubicSections_sectionFamily t x y u w m n))

variable {A : Type*} [CommRing A] [Algebra ℂ A]

private lemma BirelationCubicSections_normal_monomial_mem (t x y u w : A) (m n i j k l r : ℕ)
    (hi : i ≤ m) (hj : j ≤ 2) (hkl : k = 0 ∨ l = 0) (hdeg : j + k + l + r ≤ n) :
    t ^ i * x ^ j * y ^ k * u ^ l * w ^ r ∈ BirelationCubicSections_sectionSpan t x y u w m n := by
  let s : BirelationCubicSections_SectionIndex m n := (⟨i, by omega⟩,
    ⟨⟨j, by omega⟩, ⟨⟨k + r, by change k + r < n - j + 1; omega⟩,
      ⟨l + r, by change l + r < n - j + 1; omega⟩⟩⟩)
  refine Submodule.subset_span ⟨s, ?_⟩
  rcases hkl with rfl | rfl <;>
    simp [BirelationCubicSections_sectionFamily, s]

private lemma BirelationCubicSections_all_monomial_mem (g₂ g₃ : ℂ) (t x y u w : A)
    (hx : x ^ 3 = (1 / 4 : ℂ) • y ^ 2 + (g₂ / 4) • x + (g₃ / 4) • (1 : A))
    (hw : y * u = w - 2 * x ^ 2)
    (m n i j k l r : ℕ) (hi : i ≤ m) (hdeg : j + k + l + r ≤ n) :
    t ^ i * x ^ j * y ^ k * u ^ l * w ^ r ∈ BirelationCubicSections_sectionSpan t x y u w m n := by
  generalize hs : 2 * j + 2 * k + 3 * l = s
  induction s using Nat.strong_induction_on generalizing j k l r with
  | h s ih =>
    have hsmaller (j' k' l' r' : ℕ) (hlt : 2 * j' + 2 * k' + 3 * l' < s)
        (hd : j' + k' + l' + r' ≤ n) :
        t ^ i * x ^ j' * y ^ k' * u ^ l' * w ^ r' ∈ BirelationCubicSections_sectionSpan t x y u w m n :=
      ih _ hlt j' k' l' r' hd rfl
    by_cases hj : 3 ≤ j
    · obtain ⟨a, rfl⟩ : ∃ a, j = a + 3 := ⟨j - 3, by omega⟩
      have h₀ := hsmaller a (k + 2) l r (by omega) (by omega)
      have h₁ := hsmaller (a + 1) k l r (by omega) (by omega)
      have h₂ := hsmaller a k l r (by omega) (by omega)
      have heq : t ^ i * x ^ (a + 3) * y ^ k * u ^ l * w ^ r =
          (1 / 4 : ℂ) • (t ^ i * x ^ a * y ^ (k + 2) * u ^ l * w ^ r) +
          (g₂ / 4) • (t ^ i * x ^ (a + 1) * y ^ k * u ^ l * w ^ r) +
          (g₃ / 4) • (t ^ i * x ^ a * y ^ k * u ^ l * w ^ r) := by
        rw [pow_add, hx]
        simp only [Algebra.smul_def, pow_add]
        ring
      rw [heq]
      exact (BirelationCubicSections_sectionSpan t x y u w m n).add_mem
        ((BirelationCubicSections_sectionSpan t x y u w m n).add_mem
          ((BirelationCubicSections_sectionSpan t x y u w m n).smul_mem _ h₀)
          ((BirelationCubicSections_sectionSpan t x y u w m n).smul_mem _ h₁))
        ((BirelationCubicSections_sectionSpan t x y u w m n).smul_mem _ h₂)
    · by_cases hk : k = 0
      · exact BirelationCubicSections_normal_monomial_mem t x y u w m n i j k l r hi (by omega) (Or.inl hk) hdeg
      by_cases hl : l = 0
      · exact BirelationCubicSections_normal_monomial_mem t x y u w m n i j k l r hi (by omega) (Or.inr hl) hdeg
      obtain ⟨b, rfl⟩ : ∃ b, k = b + 1 := ⟨k - 1, by omega⟩
      obtain ⟨c, rfl⟩ : ∃ c, l = c + 1 := ⟨l - 1, by omega⟩
      have h₀ := hsmaller j b c (r + 1) (by omega) (by omega)
      have h₁ := hsmaller (j + 2) b c r (by omega) (by omega)
      have heq : t ^ i * x ^ j * y ^ (b + 1) * u ^ (c + 1) * w ^ r =
          t ^ i * x ^ j * y ^ b * u ^ c * w ^ (r + 1) -
          (2 : ℂ) • (t ^ i * x ^ (j + 2) * y ^ b * u ^ c * w ^ r) := by
        calc
          _ = t ^ i * x ^ j * y ^ b * u ^ c * w ^ r * (y * u) := by ring
          _ = _ := by rw [hw]; simp only [Algebra.smul_def, map_ofNat]; ring
      rw [heq]
      exact (BirelationCubicSections_sectionSpan t x y u w m n).sub_mem h₀
        ((BirelationCubicSections_sectionSpan t x y u w m n).smul_mem 2 h₁)

private lemma BirelationCubicSections_normalized_polynomial_mem (g₂ g₃ : ℂ) (t x y u w : A)
    (hx : x ^ 3 = (1 / 4 : ℂ) • y ^ 2 + (g₂ / 4) • x + (g₃ / 4) • (1 : A))
    (hw : y * u = w - 2 * x ^ 2)
    (m n : ℕ) (Q : MvPolynomial (Fin 7) ℂ)
    (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧
      d 2 + d 3 + d 4 + d 5 + d 6 = n) :
    aeval ![1, t, 1, x, y, u, w] Q ∈ BirelationCubicSections_sectionSpan t x y u w m n := by
  rw [Q.as_sum, map_sum]
  apply (BirelationCubicSections_sectionSpan t x y u w m n).sum_mem
  intro d hd
  have hh := hQ d hd
  have hmem := BirelationCubicSections_all_monomial_mem g₂ g₃ t x y u w hx hw m n (d 1) (d 3) (d 4)
    (d 5) (d 6) (by omega) (by omega)
  have hm := (BirelationCubicSections_sectionSpan t x y u w m n).smul_mem (coeff d Q) hmem
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Finset.univ_eq_empty, Finset.prod_empty, one_pow, one_mul, mul_one]
  change algebraMap ℂ A (coeff d Q) *
    (t ^ d 1 * (x ^ d 3 * (y ^ d 4 * (u ^ d 5 * w ^ d 6)))) ∈ _
  convert hm using 1
  simp only [Algebra.smul_def]
  ring

private lemma BirelationCubicSections_quotient_cubic_relation (L : PeriodPair) :
    firstCubicQuotient L (X 1) ^ 3 =
      (1 / 4 : ℂ) • firstCubicQuotient L (X 2) ^ 2 +
      (L.g₂ / 4) • firstCubicQuotient L (X 1) +
      (L.g₃ / 4) • (1 : FirstCubicCoordinateRing L) := by
  have hzero : firstCubicQuotient L (extensionChartCubic L.g₂ L.g₃ 0) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  have hpoly : (X (1 : Fin 4) ^ 3 -
      (C (1 / 4 : ℂ) * X 2 ^ 2 + C (L.g₂ / 4) * X 1 + C (L.g₃ / 4))) =
      C (-1 / 4 : ℂ) * extensionChartCubic L.g₂ L.g₃ 0 := by
    simp only [extensionChartCubic, ↓reduceIte]
    simp only [div_eq_mul_inv, map_mul, map_neg, map_one, one_mul]
    have hc : C (4⁻¹ : ℂ) * C 4 = (1 : MvPolynomial (Fin 4) ℂ) := by
      rw [← map_mul]
      norm_num
    linear_combination -(X (1 : Fin 4) ^ 3) * hc
  have heq := congrArg (firstCubicQuotient L) hpoly
  have hC (a : ℂ) : firstCubicQuotient L (C a) =
      algebraMap ℂ (FirstCubicCoordinateRing L) a := (firstCubicQuotient L).commutes a
  simp only [map_sub, map_add, map_mul, map_pow, hC, hzero, mul_zero] at heq
  simp only [Algebra.smul_def (R := ℂ) (A := FirstCubicCoordinateRing L), mul_one]
  exact sub_eq_zero.mp heq

private lemma BirelationCubicSections_section_space_le (L : PeriodPair) (m n : ℕ) :
    firstChartSectionSpace L m n ≤ BirelationCubicSections_sectionSpan
      (firstCubicQuotient L (X 0)) (firstCubicQuotient L (X 1))
      (firstCubicQuotient L (X 2)) (firstCubicQuotient L (X 3))
      (firstCubicQuotient L (X 2) * firstCubicQuotient L (X 3) +
        2 * firstCubicQuotient L (X 1) ^ 2) m n := by
  apply Submodule.span_le.mpr
  rintro _ ⟨Q, hQ, rfl⟩
  have htwo : firstCubicQuotient L (C (2 : ℂ)) = (2 : FirstCubicCoordinateRing L) := by
    change firstCubicQuotient L (2 : MvPolynomial (Fin 4) ℂ) = 2
    exact map_ofNat _ _
  have hnorm : firstCubicQuotient L (extensionChartNormalize 0 Q) =
      aeval ![1, firstCubicQuotient L (X 0), 1, firstCubicQuotient L (X 1),
        firstCubicQuotient L (X 2), firstCubicQuotient L (X 3),
        firstCubicQuotient L (X 2) * firstCubicQuotient L (X 3) +
          2 * firstCubicQuotient L (X 1) ^ 2] Q := by
    rw [extensionChartNormalize, comp_aeval_apply]
    apply congrArg (fun f : Fin 7 → FirstCubicCoordinateRing L => aeval f Q)
    funext i
    fin_cases i <;> simp [extensionChartSubstitution, htwo]
  rw [hnorm]
  exact BirelationCubicSections_normalized_polynomial_mem L.g₂ L.g₃ _ _ _ _ _
    (BirelationCubicSections_quotient_cubic_relation L) (by ring) m n Q hQ

private lemma BirelationCubicSections_index_card (m n : ℕ) (hn : 1 ≤ n) :
    Fintype.card (BirelationCubicSections_SectionIndex m n) = (m + 1) * (3 * n ^ 2 + 2) := by
  simp only [BirelationCubicSections_SectionIndex, Fintype.card_prod, Fintype.card_fin, Fintype.card_sigma]
  congr 1
  by_cases h : n = 1
  · subst n
    norm_num [Fin.sum_univ_succ]
  · have hn2 : 2 ≤ n := by omega
    rw [min_eq_left hn2]
    simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ,
      Finset.univ_eq_empty, Finset.sum_empty, add_zero, Nat.sub_zero]
    have h1 : n - 1 + 1 = n := by omega
    have h2 : n - 2 + 1 = n - 1 := by omega
    rw [h1, h2]
    have he : n = (n - 1) + 1 := by omega
    nlinarith

/-- Using the cubic and quadratic coordinate relations together gives a spanning
family of size (m+1)(3n²+2), hence uniform coefficient five for n at least one. -/
theorem elliptic_first_chart_birelation_dimension (L : PeriodPair) (m n : ℕ)
    (hn : 1 ≤ n) :
    Module.Finite ℂ (firstChartSectionSpace L m n) ∧
    Module.finrank ℂ (firstChartSectionSpace L m n) ≤ (m + 1) * (3 * n ^ 2 + 2) ∧
    Module.finrank ℂ (firstChartSectionSpace L m n) ≤ 5 * (m + 1) * n ^ 2 := by
  let t := firstCubicQuotient L (X 0)
  let x := firstCubicQuotient L (X 1)
  let y := firstCubicQuotient L (X 2)
  let u := firstCubicQuotient L (X 3)
  let w := y * u + 2 * x ^ 2
  let V := BirelationCubicSections_sectionSpan t x y u w m n
  have hle : firstChartSectionSpace L m n ≤ V := BirelationCubicSections_section_space_le L m n
  let : Module.Finite ℂ V := Module.Finite.span_of_finite ℂ (Set.finite_range _)
  let : Module.Finite ℂ (firstChartSectionSpace L m n) :=
    Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  have hdimV : Module.finrank ℂ V ≤ Fintype.card (BirelationCubicSections_SectionIndex m n) :=
    finrank_range_le_card (R := ℂ) (BirelationCubicSections_sectionFamily t x y u w m n)
  have hdim := (Submodule.finrank_mono hle).trans hdimV
  rw [BirelationCubicSections_index_card m n hn] at hdim
  refine ⟨inferInstance, hdim, hdim.trans ?_⟩
  calc
    _ ≤ (m + 1) * (5 * n ^ 2) := Nat.mul_le_mul_left _ (by nlinarith)
    _ = _ := by ring

end WeierstrassEllipticZeta

-- Source: Solutions.EllipticExactSectionDimension
set_option autoImplicit true
set_option maxHeartbeats 200000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
noncomputable section
open scoped BigOperators
open MvPolynomial

namespace WeierstrassEllipticZeta

/-- A finite polynomial family is independent when its highest coefficients
are independent separately at each specified degree. -/
theorem polynomial_family_independent_of_top_coeff
    {ι K A : Type*} [Fintype ι] [Field K] [CommRing A] [Algebra K A]
    (p : ι → Polynomial A) (w : ι → ℕ)
    (hdeg : ∀ i, (p i).natDegree ≤ w i)
    (htop : ∀ d, LinearIndependent K
      (fun i : {i : ι // w i = d} => (p i.val).coeff d)) :
    LinearIndependent K p := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  by_contra h
  obtain ⟨i₀, hi₀⟩ := not_forall.mp h
  let s : Finset ι := Finset.univ.filter (fun i => c i ≠ 0)
  have hs : s.Nonempty := ⟨i₀, by simpa [s] using hi₀⟩
  obtain ⟨i, hi, hmax⟩ := s.exists_max_image w hs
  have hsum : ∑ j : {j : ι // w j = w i}, c j.val • (p j.val).coeff (w i) = 0 := by
    rw [← Finset.sum_subtype (p := fun j => w j = w i)
      (Finset.univ.filter (fun j => w j = w i)) (by simp)
      (fun j => c j • (p j).coeff (w i)),
      Finset.sum_filter]
    have heq : (∑ j, if w j = w i then c j • (p j).coeff (w i) else 0) =
        ∑ j, c j • (p j).coeff (w i) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : w j = w i
      · simp [hj]
      · by_cases hcj : c j = 0
        · simp [hcj]
        · have hjmem : j ∈ s := by simp [s, hcj]
          have hlt : (p j).natDegree < w i := by
            have := hmax j hjmem
            have := hdeg j
            omega
          simp [hj, Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
    rw [heq]
    simpa only [Polynomial.finsetSum_coeff, Polynomial.coeff_smul, Polynomial.coeff_zero]
      using congrArg (fun q : Polynomial A => q.coeff (w i)) hc
  have hz := Fintype.linearIndependent_iff.mp (htop (w i)) (fun j => c j.val) hsum ⟨i, rfl⟩
  exact (Finset.mem_filter.mp hi).2 hz

private lemma EllipticExactSectionDimension_cubic_x_degree (L : PeriodPair) :
    (extensionChartCubic L.g₂ L.g₃ 0).degreeOf (1 : Fin 4) = 3 := by
  let q : MvPolynomial (Fin 4) ℂ := X 2 ^ 2 + C L.g₂ * X 1 + C L.g₃
  have hq : q.degreeOf 1 ≤ 1 := by
    apply (degreeOf_add_le 1 _ _).trans
    apply max_le _ (by simp)
    apply (degreeOf_add_le 1 _ _).trans
    apply max_le
    · rw [degreeOf_X_pow_of_ne 2 (by decide)]
      omega
    · exact (degreeOf_C_mul_le _ _ _).trans (by simp)
  have hterm : (-(C (4 : ℂ) * X (1 : Fin 4) ^ 3)).degreeOf 1 = 3 := by
    rw [degreeOf_neg, degreeOf_C_mul 1 4 (by simp)]
    exact degreeOf_X_self_pow 1 3
  have heq : extensionChartCubic L.g₂ L.g₃ 0 = -(C 4 * X 1 ^ 3) + q := by
    simp only [extensionChartCubic, q, if_true]
    ring
  rw [heq, degreeOf_add_eq_of_degreeOf_lt (by omega), hterm]

private lemma EllipticExactSectionDimension_x_reduced_quotient_injective (L : PeriodPair)
    (P : MvPolynomial (Fin 4) ℂ) (hP : P.degreeOf 1 ≤ 2)
    (hz : firstCubicQuotient L P = 0) : P = 0 := by
  have hmem : P ∈ Ideal.span {extensionChartCubic L.g₂ L.g₃ 0} :=
    Ideal.Quotient.eq_zero_iff_mem.mp hz
  obtain ⟨H, hH⟩ := Ideal.mem_span_singleton.mp hmem
  by_cases hzero : H = 0
  · simpa [hzero] using hH
  have hc : extensionChartCubic L.g₂ L.g₃ 0 ≠ 0 := by
    intro h
    have hd := EllipticExactSectionDimension_cubic_x_degree L
    rw [h, degreeOf_zero] at hd
    omega
  have hd := degreeOf_mul_eq (n := (1 : Fin 4)) hc hzero
  rw [← hH, EllipticExactSectionDimension_cubic_x_degree L] at hd
  omega

private def EllipticExactSectionDimension_coefficientExponent (i j a : ℕ) : Fin 4 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![i, j, a, 0]

private theorem EllipticExactSectionDimension_cubic_coefficient_monomials_independent (L : PeriodPair)
    {ι : Type*} [Fintype ι] (v : ι → ℕ × ℕ × ℕ)
    (hv : Function.Injective v) (hj : ∀ i, (v i).2.1 ≤ 2) :
    LinearIndependent ℂ (fun i => firstCubicQuotient L
      (monomial (EllipticExactSectionDimension_coefficientExponent (v i).1 (v i).2.1 (v i).2.2) (1 : ℂ))) := by
  classical
  let exponent := fun i => EllipticExactSectionDimension_coefficientExponent (v i).1 (v i).2.1 (v i).2.2
  have hexp : Function.Injective exponent := by
    intro i j h
    apply hv
    have h0 := DFunLike.congr_fun h 0
    have h1 := DFunLike.congr_fun h 1
    have h2 := DFunLike.congr_fun h 2
    simp [exponent, EllipticExactSectionDimension_coefficientExponent] at h0 h1 h2
    exact Prod.ext h0 (Prod.ext h1 h2)
  have hbase : LinearIndependent ℂ (fun i => monomial (exponent i) (1 : ℂ)) := by
    simpa only [coe_basisMonomials, Function.comp_def] using
      (basisMonomials (Fin 4) ℂ).linearIndependent.comp exponent hexp
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  apply Fintype.linearIndependent_iff.mp hbase c
  apply EllipticExactSectionDimension_x_reduced_quotient_injective L
  · apply (degreeOf_sum_le 1 Finset.univ _).trans
    apply Finset.sup_le
    intro i _
    rw [smul_monomial]
    apply degreeOf_le_iff.mpr
    intro d hd
    rw [Finset.mem_singleton.mp (support_monomial_subset hd)]
    simpa [exponent, EllipticExactSectionDimension_coefficientExponent] using hj i
  · simpa only [map_sum, map_smul] using hc

private def EllipticExactSectionDimension_fiberPolynomialSubstitution (L : PeriodPair) :
    MvPolynomial (Fin 4) ℂ →ₐ[ℂ] Polynomial (FirstCubicCoordinateRing L) :=
  aeval ![Polynomial.C (firstCubicQuotient L (X 0)),
    Polynomial.C (firstCubicQuotient L (X 1)),
    Polynomial.C (firstCubicQuotient L (X 2)), Polynomial.X]

private lemma EllipticExactSectionDimension_fiberPolynomialSubstitution_cubic (L : PeriodPair) :
    EllipticExactSectionDimension_fiberPolynomialSubstitution L (extensionChartCubic L.g₂ L.g₃ 0) = 0 := by
  have hz : firstCubicQuotient L (extensionChartCubic L.g₂ L.g₃ 0) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  have hC (c : ℂ) : firstCubicQuotient L (C c) =
      algebraMap ℂ (FirstCubicCoordinateRing L) c := (firstCubicQuotient L).commutes c
  have heq : EllipticExactSectionDimension_fiberPolynomialSubstitution L (extensionChartCubic L.g₂ L.g₃ 0) =
      Polynomial.C (firstCubicQuotient L (extensionChartCubic L.g₂ L.g₃ 0)) := by
    simp [EllipticExactSectionDimension_fiberPolynomialSubstitution, extensionChartCubic, map_add, map_sub,
      map_mul, map_pow, hC]
  rw [heq, hz, map_zero]

private def EllipticExactSectionDimension_fiberPolynomialMap (L : PeriodPair) :
    FirstCubicCoordinateRing L →ₐ[ℂ] Polynomial (FirstCubicCoordinateRing L) :=
  Ideal.Quotient.liftₐ _ (EllipticExactSectionDimension_fiberPolynomialSubstitution L) (by
    intro P hP
    obtain ⟨H, rfl⟩ := Ideal.mem_span_singleton.mp hP
    rw [map_mul, EllipticExactSectionDimension_fiberPolynomialSubstitution_cubic, zero_mul])

private lemma EllipticExactSectionDimension_fiberPolynomialMap_mk (L : PeriodPair) (P : MvPolynomial (Fin 4) ℂ) :
    EllipticExactSectionDimension_fiberPolynomialMap L (firstCubicQuotient L P) = EllipticExactSectionDimension_fiberPolynomialSubstitution L P := rfl

private def EllipticExactSectionDimension_normalFiberPolynomial {A : Type*} [CommRing A]
    (t x y : A) (i j a b : ℕ) : Polynomial A :=
  Polynomial.C (t ^ i * x ^ j * y ^ (a - b)) * Polynomial.X ^ (b - a) *
    (Polynomial.C y * Polynomial.X + Polynomial.C (2 * x ^ 2)) ^ min a b

private lemma EllipticExactSectionDimension_normalFiberPolynomial_spec {A : Type*} [CommRing A]
    (t x y : A) (i j a b : ℕ) :
    (EllipticExactSectionDimension_normalFiberPolynomial t x y i j a b).natDegree ≤ b ∧
    (EllipticExactSectionDimension_normalFiberPolynomial t x y i j a b).coeff b = t ^ i * x ^ j * y ^ a := by
  let q : Polynomial A := Polynomial.C y * Polynomial.X + Polynomial.C (2 * x ^ 2)
  have hq : q.natDegree ≤ 1 := by
    apply Polynomial.natDegree_add_le_of_degree_le
    · exact (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le
    · rw [Polynomial.natDegree_C]
      omega
  have hqc : q.coeff 1 = y := by
    simp only [q, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_one, Polynomial.coeff_C, one_ne_zero, ↓reduceIte, mul_one, add_zero]
  have hp : (q ^ min a b).natDegree ≤ min a b :=
    (Polynomial.natDegree_pow_le).trans (by simpa using Nat.mul_le_mul_left (min a b) hq)
  have hpc : (q ^ min a b).coeff (min a b) = y ^ min a b := by
    simpa only [mul_one, hqc] using Polynomial.coeff_pow_of_natDegree_le (m := min a b) hq
  have hb : b - a + min a b = b := by omega
  have ha : a - b + min a b = a := by omega
  constructor
  · exact Polynomial.natDegree_mul_le.trans ((add_le_add
      ((Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_X_pow_le _)) hp).trans_eq hb)
  · change (Polynomial.C _ * Polynomial.X ^ (b - a) * q ^ min a b).coeff b = _
    have hcoeff := Polynomial.coeff_mul_add_eq_of_natDegree_le
      (Polynomial.natDegree_X_pow_le (R := A) (b - a)) hp
    rw [hb] at hcoeff
    rw [mul_assoc, Polynomial.coeff_C_mul, hcoeff, Polynomial.coeff_X_pow_self, one_mul, hpc]
    rw [mul_assoc, ← pow_add, ha]

private abbrev EllipticExactSectionDimension_ExactSectionIndex (m n : ℕ) :=
  Fin (m + 1) × (Σ j : Fin (min 2 n + 1),
    Fin (n - j.val + 1) × Fin (n - j.val + 1))

private def EllipticExactSectionDimension_exactSection (L : PeriodPair) (m n : ℕ) (s : EllipticExactSectionDimension_ExactSectionIndex m n) :
    FirstCubicCoordinateRing L :=
  firstCubicQuotient L
    (X 0 ^ s.1.val * X 1 ^ s.2.1.val * X 2 ^ (s.2.2.1.val - s.2.2.2.val) *
      X 3 ^ (s.2.2.2.val - s.2.2.1.val) *
      (X 2 * X 3 + 2 * X 1 ^ 2) ^ min s.2.2.1.val s.2.2.2.val)

private lemma EllipticExactSectionDimension_exactSection_polynomial (L : PeriodPair) (m n : ℕ)
    (s : EllipticExactSectionDimension_ExactSectionIndex m n) :
    EllipticExactSectionDimension_fiberPolynomialMap L (EllipticExactSectionDimension_exactSection L m n s) =
      EllipticExactSectionDimension_normalFiberPolynomial (firstCubicQuotient L (X 0))
        (firstCubicQuotient L (X 1)) (firstCubicQuotient L (X 2))
        s.1.val s.2.1.val s.2.2.1.val s.2.2.2.val := by
  rw [EllipticExactSectionDimension_exactSection, EllipticExactSectionDimension_fiberPolynomialMap_mk]
  simp [EllipticExactSectionDimension_fiberPolynomialSubstitution, EllipticExactSectionDimension_normalFiberPolynomial, map_ofNat]

private lemma EllipticExactSectionDimension_coefficient_monomial_eq (i j a : ℕ) :
    monomial (EllipticExactSectionDimension_coefficientExponent i j a) (1 : ℂ) =
      X (0 : Fin 4) ^ i * X 1 ^ j * X 2 ^ a := by
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp [EllipticExactSectionDimension_coefficientExponent, Fin.prod_univ_succ, mul_assoc]

private lemma EllipticExactSectionDimension_exactSection_top_independent (L : PeriodPair) (m n d : ℕ) :
    LinearIndependent ℂ (fun s : {s : EllipticExactSectionDimension_ExactSectionIndex m n // s.2.2.2.val = d} =>
      firstCubicQuotient L (X 0) ^ s.val.1.val *
        firstCubicQuotient L (X 1) ^ s.val.2.1.val *
        firstCubicQuotient L (X 2) ^ s.val.2.2.1.val) := by
  let v := fun s : {s : EllipticExactSectionDimension_ExactSectionIndex m n // s.2.2.2.val = d} =>
    (s.val.1.val, s.val.2.1.val, s.val.2.2.1.val)
  have hv : Function.Injective v := by
    rintro ⟨⟨i, ⟨j, a, b⟩⟩, hs⟩ ⟨⟨i', ⟨j', a', b'⟩⟩, hs'⟩ h
    have hi : i = i' := Fin.ext (congrArg Prod.fst h)
    have hj : j = j' := Fin.ext (congrArg (fun z : ℕ × ℕ × ℕ => z.2.1) h)
    subst i'
    subst j'
    have ha : a = a' := Fin.ext (congrArg (fun z : ℕ × ℕ × ℕ => z.2.2) h)
    have hb : b = b' := Fin.ext (hs.trans hs'.symm)
    subst a'
    subst b'
    rfl
  have hj (s : {s : EllipticExactSectionDimension_ExactSectionIndex m n // s.2.2.2.val = d}) : (v s).2.1 ≤ 2 := by
    have hh := s.val.2.1.isLt
    dsimp [v]
    omega
  simpa only [v, EllipticExactSectionDimension_coefficient_monomial_eq, map_mul, map_pow] using
    EllipticExactSectionDimension_cubic_coefficient_monomials_independent L v hv hj

private lemma EllipticExactSectionDimension_exactSection_independent (L : PeriodPair) (m n : ℕ) :
    LinearIndependent ℂ (EllipticExactSectionDimension_exactSection L m n) := by
  apply LinearIndependent.of_comp (EllipticExactSectionDimension_fiberPolynomialMap L).toLinearMap
  apply polynomial_family_independent_of_top_coeff _ (fun s => s.2.2.2.val)
  · intro s
    change (EllipticExactSectionDimension_fiberPolynomialMap L (EllipticExactSectionDimension_exactSection L m n s)).natDegree ≤ _
    rw [EllipticExactSectionDimension_exactSection_polynomial]
    exact (EllipticExactSectionDimension_normalFiberPolynomial_spec _ _ _ _ _ _ _).1
  · intro d
    have heq : (fun s : {s : EllipticExactSectionDimension_ExactSectionIndex m n // s.2.2.2.val = d} =>
        (EllipticExactSectionDimension_fiberPolynomialMap L (EllipticExactSectionDimension_exactSection L m n s.val)).coeff d) =
        (fun s : {s : EllipticExactSectionDimension_ExactSectionIndex m n // s.2.2.2.val = d} =>
          firstCubicQuotient L (X 0) ^ s.val.1.val *
          firstCubicQuotient L (X 1) ^ s.val.2.1.val *
          firstCubicQuotient L (X 2) ^ s.val.2.2.1.val) := by
      funext s
      rcases s with ⟨s, rfl⟩
      rw [EllipticExactSectionDimension_exactSection_polynomial]
      exact (EllipticExactSectionDimension_normalFiberPolynomial_spec _ _ _ _ _ _ _).2
    change LinearIndependent ℂ (fun s : {s : EllipticExactSectionDimension_ExactSectionIndex m n // s.2.2.2.val = d} =>
      (EllipticExactSectionDimension_fiberPolynomialMap L (EllipticExactSectionDimension_exactSection L m n s.val)).coeff d)
    rw [heq]
    exact EllipticExactSectionDimension_exactSection_top_independent L m n d

private lemma EllipticExactSectionDimension_exactSection_mem (L : PeriodPair) (m n : ℕ) (s : EllipticExactSectionDimension_ExactSectionIndex m n) :
    EllipticExactSectionDimension_exactSection L m n s ∈ firstChartSectionSpace L m n := by
  let i := s.1.val
  let j := s.2.1.val
  let a := s.2.2.1.val
  let b := s.2.2.2.val
  let d : Fin 7 →₀ ℕ := Finsupp.equivFunOnFinite.symm
    ![m - i, i, n - j - max a b, j, a - b, b - a, min a b]
  refine Submodule.subset_span ⟨monomial d 1, ?_, ?_⟩
  · intro d' hd'
    have he : d' = d := Finset.mem_singleton.mp (support_monomial_subset hd')
    subst d'
    have hi := s.1.isLt
    have hj := s.2.1.isLt
    have ha := s.2.2.1.isLt
    have hb := s.2.2.2.isLt
    simp only [d, Finsupp.equivFunOnFinite, Equiv.coe_fn_symm_mk]
    dsimp [i, j, a, b] at *
    omega
  · congr 1
    change (aeval (extensionChartSubstitution 0)) (monomial d (1 : ℂ)) = _
    rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    simp [d, extensionChartSubstitution, Fin.prod_univ_succ,
      i, j, a, b, mul_assoc, map_ofNat]

private lemma EllipticExactSectionDimension_exactSectionIndex_card (m n : ℕ) (hn : 1 ≤ n) :
    Fintype.card (EllipticExactSectionDimension_ExactSectionIndex m n) = (m + 1) * (3 * n ^ 2 + 2) := by
  simp only [EllipticExactSectionDimension_ExactSectionIndex, Fintype.card_prod, Fintype.card_fin, Fintype.card_sigma]
  congr 1
  by_cases h : n = 1
  · subst n
    norm_num [Fin.sum_univ_succ]
  · have hn2 : 2 ≤ n := by omega
    rw [min_eq_left hn2]
    simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ,
      Finset.univ_eq_empty, Finset.sum_empty, add_zero, Nat.sub_zero]
    have h1 : n - 1 + 1 = n := by omega
    have h2 : n - 2 + 1 = n - 1 := by omega
    rw [h1, h2]
    have he : n = (n - 1) + 1 := by omega
    nlinarith

/-- The cubic/quadratic normal forms form a basis, so the section dimension is
exactly `(m+1)(3n²+2)` in every positive extension degree. -/
theorem elliptic_first_chart_exact_section_dimension (L : PeriodPair) (m n : ℕ)
    (hn : 1 ≤ n) :
    Module.finrank ℂ (firstChartSectionSpace L m n) = (m + 1) * (3 * n ^ 2 + 2) := by
  let : Module.Finite ℂ (firstChartSectionSpace L m n) :=
    (elliptic_first_chart_birelation_dimension L m n hn).1
  apply Nat.le_antisymm (elliptic_first_chart_birelation_dimension L m n hn).2.1
  let f : EllipticExactSectionDimension_ExactSectionIndex m n → firstChartSectionSpace L m n :=
    fun s => ⟨EllipticExactSectionDimension_exactSection L m n s, EllipticExactSectionDimension_exactSection_mem L m n s⟩
  have hf : LinearIndependent ℂ f :=
    LinearIndependent.of_comp (firstChartSectionSpace L m n).subtype
      (EllipticExactSectionDimension_exactSection_independent L m n)
  have hdim := hf.fintype_card_le_finrank
  rwa [EllipticExactSectionDimension_exactSectionIndex_card m n hn] at hdim

end WeierstrassEllipticZeta


-- Source: Solutions.WeierstrassExtensionDimension
set_option autoImplicit true
set_option maxHeartbeats 200000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MvPolynomial TranscendenceTheory PhilipponMultiplicity
namespace WeierstrassEllipticZeta

variable (L : PeriodPair) (D : EllipticSigmaDifferentialData L) (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (η : L.lattice →ₗ[ℤ] ℂ)
    [AddCommGroup (ProjectiveExtensionChartLocus L.g₂ L.g₃)]
    (e : GraphQuotientExtension L.lattice η ≃+ ProjectiveExtensionChartLocus L.g₂ L.g₃)
    (he : ∀ z u : ℂ, ∃ hv :
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] ≠ 0,
        (e ((extensionPeriodGraph L.lattice η).mkQ (z, u))).val.val = Projectivization.mk ℂ
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] hv)

include D S hS hS_value hS_ne η e he in
/-- The actual Hilbert polynomial of the extension surface is 3n²+2. -/
theorem projective_extension_hilbert_polynomial_implementation :
    Hilbert.hilbertPolynomial ℂ 1 (fun _ => 4)
      ((projectiveSpace ℂ 4).vanishingIdeal
        (Set.range (fun p : ProjectiveExtensionChartLocus L.g₂ L.g₃ =>
          fun _ : Fin 1 => p.val.val))) =
      C 3 * X 0 ^ 2 + C 2 := by
  apply Hilbert.hilbertPolynomial_eq_of_isHilbertPolynomial
  refine ⟨fun _ => 1, ?_⟩
  intro d hd
  have hdeq : d = fun _ => d 0 := by
    funext i
    exact congrArg d (Subsingleton.elim _ _)
  have hfun := projective_extension_hilbert_function_eq_sections
    L D S hS hS_value hS_ne η e he (d 0)
  rw [elliptic_first_chart_exact_section_dimension L 0 (d 0) (hd 0)] at hfun
  rw [hdeq, hfun]
  simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X]
  norm_cast
  simp

include D S hS hS_value hS_ne η e he in
/-- Hilbert dimension of the actual projective extension carrier. -/
theorem projective_extension_hilbert_dimension :
    (Hilbert.hilbertPolynomial ℂ 1 (fun _ => 4)
      ((projectiveSpace ℂ 4).vanishingIdeal
        (Set.range (fun p : ProjectiveExtensionChartLocus L.g₂ L.g₃ =>
          fun _ : Fin 1 => p.val.val)))).totalDegree = 2 := by
  rw [projective_extension_hilbert_polynomial_implementation L D S hS hS_value hS_ne η e he]
  have hp : (C (3 : ℚ) * (X (0 : Fin 1) ^ 2)).totalDegree = 2 := by
    rw [totalDegree_mul_of_isDomain (by norm_num) (by simp), totalDegree_C, zero_add,
      totalDegree_X_pow]
  rw [totalDegree_add_eq_left_of_totalDegree_lt (by simp [hp]), hp]

end WeierstrassEllipticZeta


open MvPolynomial TranscendenceTheory PhilipponMultiplicity WeierstrassEllipticZeta
theorem solution
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L) (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (η : L.lattice →ₗ[ℤ] ℂ)
    [AddCommGroup (ProjectiveExtensionChartLocus L.g₂ L.g₃)]
    (e : GraphQuotientExtension L.lattice η ≃+ ProjectiveExtensionChartLocus L.g₂ L.g₃)
    (he : ∀ z u : ℂ, ∃ hv :
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] ≠ 0,
        (e ((extensionPeriodGraph L.lattice η).mkQ (z, u))).val.val = Projectivization.mk ℂ
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] hv)
    :
    Hilbert.hilbertPolynomial ℂ 1 (fun _ => 4)
      ((projectiveSpace ℂ 4).vanishingIdeal
        (Set.range (fun p : ProjectiveExtensionChartLocus L.g₂ L.g₃ =>
          fun _ : Fin 1 => p.val.val))) =
      C 3 * X 0 ^ 2 + C 2 := by
  exact WeierstrassEllipticZeta.projective_extension_hilbert_polynomial_implementation L D S hS hS_value hS_ne η e he

#print axioms solution
