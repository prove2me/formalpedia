-- Prove2me | solution 1 for StochKolmogorov.Extinct.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-01T21:58:40.468922+00:00
-- url     : https://prove2.me/submissions/66bfa3b8-7fac-45ab-8fc1-45025efaa184

import Mathlib
import Definitions.Def_StochKolmogorov_Extinct_Extinction
import Definitions.Def_StochKolmogorov_Persist_Model
import Definitions.Def_StochKolmogorov_Persist_Persistence
import Theorems.Thm_StochKolmogorov_Persist_kolmogorov_sde_pathwise_unique
import Theorems.Thm_StochKolmogorov_Persist_kolmogorov_sde_face_invariance
import Theorems.Thm_StochKolmogorov_Persist_kolmogorov_lyapunov_moment_bound

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false

namespace ExtinctGlue

open EthierKurtz

/-- The same coefficients, read in the `Persist` copy of the model. -/
def toP {n : ℕ} (C : StochKolmogorov.Extinct.Coeffs n) : StochKolmogorov.Persist.Coeffs n :=
  ⟨C.f, C.g, C.Γ⟩

theorem drift_eq {n : ℕ} (C : StochKolmogorov.Extinct.Coeffs n) :
    StochKolmogorov.Persist.drift (toP C) = StochKolmogorov.Extinct.drift C := rfl

theorem diffusion_eq {n : ℕ} (C : StochKolmogorov.Extinct.Coeffs n) :
    StochKolmogorov.Persist.diffusion (toP C) = StochKolmogorov.Extinct.diffusion C := rfl

theorem openOrthant_of_face_univ {n : ℕ} (y : SDEState n)
    (hy : y ∈ StochKolmogorov.Persist.faceOpen (Finset.univ : Finset (Fin n))) :
    y ∈ StochKolmogorov.Extinct.openOrthant n :=
  fun i => hy.2.2 i (Finset.mem_univ i)

theorem measurable_Vfun_pow {n : ℕ} (c p : SDEState n) (δ₀ : ℝ) :
    Measurable (fun y : SDEState n => (StochKolmogorov.Extinct.Vfun c p y) ^ δ₀) := by
  unfold StochKolmogorov.Extinct.Vfun
  have h1 : Measurable (fun y : SDEState n => 1 + ∑ i, c i * y i) := by
    refine measurable_const.add ?_
    refine Finset.measurable_sum _ (fun i _ => ?_)
    exact measurable_const.mul ((PiLp.continuous_apply 2 _ i).measurable)
  have h2 : Measurable (fun y : SDEState n => ∏ i, y i ^ p i) := by
    refine Finset.measurable_prod _ (fun i _ => ?_)
    exact ((PiLp.continuous_apply 2 _ i).measurable).pow_const _
  exact (h1.div h2).pow_const _

end ExtinctGlue

open StochKolmogorov.Extinct EthierKurtz in
theorem solution {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (hX : IsSolutionFamily P C B X)
    (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (δ₀ : ℝ) (hδ₀ : IsDelta0 C γb δ₀) :
    (∀ x ∈ orthant n, ∀ Y : ℝ≥0 → Ω → SDEState n,
      SolvesBrownianSDE P (diffusion C) (drift C) B (fun _ => x) Y →
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, Y t ω = X x t ω) ∧
    (∀ (I : Finset (Fin n)) (x : SDEState n), x ∈ orthant n →
      (∀ i, i ∈ I ↔ 0 < x i) →
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        (∀ i ∈ I, 0 < X x t ω i) ∧ (∀ i, i ∉ I → X x t ω i = 0)) ∧
    (∀ (p : SDEState n), p ∈ openOrthant n → l1 p ≤ δ₀ →
      ∀ x ∈ openOrthant n, ∀ t : ℝ≥0,
        Integrable (fun ω => (Vfun c p (X x t ω)) ^ δ₀) P ∧
        ∫ ω, (Vfun c p (X x t ω)) ^ δ₀ ∂P ≤
          Real.exp (δ₀ * Hconst C c γb δ₀ * (t : ℝ)) * (Vfun c p x) ^ δ₀) := by
  obtain ⟨hP, hB, hsol⟩ := hX
  have hC : ∀ i, LocallyLipschitzOn (StochKolmogorov.Persist.orthant n)
      ((ExtinctGlue.toP C).f i) ∧
      LocallyLipschitzOn (StochKolmogorov.Persist.orthant n) ((ExtinctGlue.toP C).g i) :=
    hA.2.1
  -- face invariance for the family, in the Persist form
  have hface : ∀ (I : Finset (Fin n)) (x : SDEState n),
      x ∈ StochKolmogorov.Persist.faceOpen I →
      ∀ᵐ ω ∂P, ∀ t, X x t ω ∈ StochKolmogorov.Persist.faceOpen I := by
    intro I x hx
    have hxo : x ∈ orthant n := hx.1
    exact StochKolmogorov.Persist.kolmogorov_sde_face_invariance (P := P) (ExtinctGlue.toP C)
      hB hC hx (hsol x hxo)
  refine ⟨?_, ?_, ?_⟩
  · intro x hx Y hY
    exact StochKolmogorov.Persist.kolmogorov_sde_pathwise_unique P (ExtinctGlue.toP C) B hB hC
      x hx Y (X x) hY (hsol x hx)
  · intro I x hx hI
    have hxf : x ∈ StochKolmogorov.Persist.faceOpen I := by
      refine ⟨hx, ?_, ?_⟩
      · intro i hi
        have h0 : 0 ≤ x i := hx i
        have hn' : ¬ 0 < x i := fun h => hi ((hI i).2 h)
        linarith [not_lt.mp hn']
      · intro i hi
        exact (hI i).1 hi
    filter_upwards [hface I x hxf] with ω hω t
    exact ⟨fun i hi => (hω t).2.2 i hi, fun i hi => (hω t).2.1 i hi⟩
  · intro p hp hpl x hx t
    have hxo : x ∈ orthant n := fun i => le_of_lt (hx i)
    have hδP : StochKolmogorov.Persist.IsDelta0 (ExtinctGlue.toP C) γb δ₀ :=
      ⟨hδ₀.1, lt_of_lt_of_le hδ₀.2.1 (min_le_left _ _), hδ₀.2.2⟩
    have hmom := StochKolmogorov.Persist.kolmogorov_lyapunov_moment_bound (P := P)
      (C := ExtinctGlue.toP C) hn hB hA hδP hp hpl hx (hsol x hxo) t
    have hxf : x ∈ StochKolmogorov.Persist.faceOpen (Finset.univ : Finset (Fin n)) :=
      ⟨hxo, fun i hi => absurd (Finset.mem_univ i) hi, fun i _ => hx i⟩
    have hpos : ∀ᵐ ω ∂P, 0 ≤ (Vfun c p (X x t ω)) ^ δ₀ := by
      filter_upwards [hface _ x hxf] with ω hω
      have hy := ExtinctGlue.openOrthant_of_face_univ _ (hω t)
      have hnum : 0 < 1 + ∑ i, c i * X x t ω i := by
        have : 0 ≤ ∑ i, c i * X x t ω i :=
          Finset.sum_nonneg (fun i _ => mul_nonneg (le_of_lt (hA.2.2.1 i)) (le_of_lt (hy i)))
        linarith
      have hden : 0 < ∏ i, X x t ω i ^ p i :=
        Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (hy i) _)
      exact Real.rpow_nonneg (le_of_lt (div_pos hnum hden)) _
    have hmeas : AEStronglyMeasurable (fun ω => (Vfun c p (X x t ω)) ^ δ₀) P :=
      ((ExtinctGlue.measurable_Vfun_pow c p δ₀).comp ((hsol x hxo).1 t)).aestronglyMeasurable
    have hbound_nn : 0 ≤ Real.exp (δ₀ * Hconst C c γb δ₀ * (t : ℝ)) * (Vfun c p x) ^ δ₀ := by
      refine mul_nonneg (Real.exp_pos _).le ?_
      have hnum : 0 < 1 + ∑ i, c i * x i := by
        have : 0 ≤ ∑ i, c i * x i :=
          Finset.sum_nonneg (fun i _ => mul_nonneg (le_of_lt (hA.2.2.1 i)) (le_of_lt (hx i)))
        linarith
      have hden : 0 < ∏ i, x i ^ p i :=
        Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (hx i) _)
      exact Real.rpow_nonneg (le_of_lt (div_pos hnum hden)) _
    have hmom' : ∫⁻ ω, ENNReal.ofReal ((Vfun c p (X x t ω)) ^ δ₀) ∂P ≤
        ENNReal.ofReal (Real.exp (δ₀ * Hconst C c γb δ₀ * (t : ℝ)) * (Vfun c p x) ^ δ₀) :=
      hmom
    have hfin : ∫⁻ ω, ENNReal.ofReal ((Vfun c p (X x t ω)) ^ δ₀) ∂P < ∞ :=
      lt_of_le_of_lt hmom' ENNReal.ofReal_lt_top
    have hint : Integrable (fun ω => (Vfun c p (X x t ω)) ^ δ₀) P := by
      refine ⟨hmeas, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal hpos]
      exact hfin
    refine ⟨hint, ?_⟩
    rw [integral_eq_lintegral_of_nonneg_ae hpos hmeas]
    calc
      (∫⁻ ω, ENNReal.ofReal ((Vfun c p (X x t ω)) ^ δ₀) ∂P).toReal
          ≤ (ENNReal.ofReal (Real.exp (δ₀ * Hconst C c γb δ₀ * (t : ℝ)) *
              (Vfun c p x) ^ δ₀)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hmom'
      _ = Real.exp (δ₀ * Hconst C c γb δ₀ * (t : ℝ)) * (Vfun c p x) ^ δ₀ :=
        ENNReal.toReal_ofReal hbound_nn
