-- Prove2me | solution 1 for avram_ws01e_a_finite_grid_ae_stop_cylinder_identity_6e132acd
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:21:23.744911+00:00
-- url     : https://prove2.me/submissions/98964522-5aa4-464d-8a22-e4b7ee642e9a

import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

namespace Aux_cyl6e
open AvramDividend.Classical MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

lemma tail_one {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ) (t T : ℝ≥0) (htT : t ≤ T) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * (X.X T ω - X.X t ω) - ((T:ℝ) - t) * X.ψ θ)) ∂P = 1 := by
  have hid := X.stationaryIncrements t T htT
  have hc : ((T - t : ℝ≥0) : ℝ) = (T:ℝ) - t := NNReal.coe_sub htT
  have hg : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (θ * x - ((T:ℝ) - t) * X.ψ θ))) := by
    fun_prop
  have hcomp := (hid.comp hg).lintegral_eq
  simp only [Function.comp_def] at hcomp
  rw [hcomp]
  obtain ⟨hint, hval⟩ := X.laplace (T - t) θ hθ
  have h2 : (fun ω => Real.exp (θ * X.X (T - t) ω - ((T:ℝ) - t) * X.ψ θ)) =
      fun ω => Real.exp (θ * X.X (T - t) ω) * Real.exp (-(((T:ℝ) - t) * X.ψ θ)) := by
    funext ω; rw [← Real.exp_add]; ring_nf
  have hint' : Integrable (fun ω => Real.exp (θ * X.X (T - t) ω - ((T:ℝ) - t) * X.ψ θ)) P := by
    rw [h2]; exact hint.mul_const _
  rw [← ofReal_integral_eq_lintegral_ofReal hint'
    (Filter.Eventually.of_forall (fun ω => (Real.exp_pos _).le))]
  have hψ : X.ψ θ = laplaceExponent X.c X.σ X.ν θ := rfl
  have : ∫ ω, Real.exp (θ * X.X (T - t) ω - ((T:ℝ) - t) * X.ψ θ) ∂P = 1 := by
    rw [h2, integral_mul_const, hval, ← Real.exp_add, Real.exp_eq_one_iff, hc, hψ]
    ring
  rw [this, ENNReal.ofReal_one]

lemma tail {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ) (t T : ℝ≥0) (htT : t ≤ T)
    (F : Ω → ℝ≥0∞) (hF : Measurable[𝓕 t] F) :
    ∫⁻ ω, F ω * ENNReal.ofReal (Real.exp (θ * X.X T ω - (T:ℝ) * X.ψ θ)) ∂P =
      ∫⁻ ω, F ω * ENNReal.ofReal (Real.exp (θ * X.X t ω - (t:ℝ) * X.ψ θ)) ∂P := by
  have hsplit : ∀ ω, ENNReal.ofReal (Real.exp (θ * X.X T ω - (T:ℝ) * X.ψ θ)) =
      ENNReal.ofReal (Real.exp (θ * X.X t ω - (t:ℝ) * X.ψ θ)) *
        ENNReal.ofReal (Real.exp (θ * (X.X T ω - X.X t ω) - ((T:ℝ) - t) * X.ψ θ)) := by
    intro ω
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2; ring
  simp_rw [hsplit, ← mul_assoc]
  have hXT : Measurable (X.X T) := (X.adapted T).mono (𝓕.le T) le_rfl
  have hXt : Measurable (X.X t) := (X.adapted t).mono (𝓕.le t) le_rfl
  have hJ : Measurable (fun ω => X.X T ω - X.X t ω) := hXT.sub hXt
  have hg : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (θ * x - ((T:ℝ) - t) * X.ψ θ))) := by
    fun_prop
  have hgt : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (θ * x - (t:ℝ) * X.ψ θ))) := by
    fun_prop
  have hF1 : Measurable[𝓕 t] (fun ω => F ω *
      ENNReal.ofReal (Real.exp (θ * X.X t ω - (t:ℝ) * X.ψ θ))) :=
    hF.mul (hgt.comp (X.adapted t))
  have hG : Measurable[MeasurableSpace.comap (fun ω => X.X T ω - X.X t ω) inferInstance]
      (fun ω => ENNReal.ofReal (Real.exp (θ * (X.X T ω - X.X t ω) - ((T:ℝ) - t) * X.ψ θ))) :=
    hg.comp (comap_measurable _)
  rw [lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace (𝓕.le t)
    hJ.comap_le (X.indepIncrements t T htT).symm hF1 hG, tail_one X θ hθ t T htT, mul_one]

lemma setLIntegral_eq_indicator {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (S : Set Ω)
    (hS : MeasurableSet S) (f : Ω → ℝ≥0∞) :
    ∫⁻ ω in S, f ω ∂P = ∫⁻ ω, S.indicator (fun _ => (1:ℝ≥0∞)) ω * f ω ∂P := by
  rw [← lintegral_indicator hS]
  congr 1
  funext ω
  by_cases h : ω ∈ S <;> simp [h]

end Aux_cyl6e

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal BigOperators


theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (T u : ℝ≥0) (τ : Ω → ℝ≥0) (grid : Finset ℝ≥0)
    (hgrid : ∀ᵐ ω ∂(P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))), τ ω ∈ grid)
    (hT : ∀ s ∈ grid, s + u ≤ T)
    (hstop : ∀ s ∈ grid, MeasurableSet[𝓕 s] {ω : Ω | τ ω = s})
    (A : Set Ω) (hA : MeasurableSet A)
    (hHistory : ∀ s ∈ grid,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω = s}))
    (B : Set ℝ) (hB : MeasurableSet B) 
    (hfib : (let QT : Measure Ω := (P.withDensity (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))); let QU : Measure Ω := (P.withDensity (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ)))); ∀ s ∈ grid, MeasurableSet {ω : Ω | τ ω = s}))
    (hXm : (let QT : Measure Ω := (P.withDensity (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))); let QU : Measure Ω := (P.withDensity (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ)))); ∀ r, Measurable (X.X r)))
    (hinc : (let QT : Measure Ω := (P.withDensity (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))); let QU : Measure Ω := (P.withDensity (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ)))); ∀ s, MeasurableSet ((fun ω => X.X (s + u) ω -
      X.X s ω) ⁻¹' B)))
    (hAae : (let QT : Measure Ω := (P.withDensity (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))); let QU : Measure Ω := (P.withDensity (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ)))); let C : ℝ≥0 → Set Ω := fun s => A ∩ {ω : Ω | τ ω = s}; let D : ℝ≥0 → Set Ω := (fun s => C s ∩ (fun ω => X.X (s + u) ω - X.X s ω) ⁻¹' B); ∀ᵐ ω ∂QT,
      (ω ∈ A ↔ ω ∈ ⋃ s ∈ grid, C s)))
    (hEae : (let QT : Measure Ω := (P.withDensity (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))); let QU : Measure Ω := (P.withDensity (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ)))); let C : ℝ≥0 → Set Ω := fun s => A ∩ {ω : Ω | τ ω = s}; let D : ℝ≥0 → Set Ω := (fun s => C s ∩ (fun ω => X.X (s + u) ω - X.X s ω) ⁻¹' B); ∀ᵐ ω ∂QT,
      (ω ∈ A ∩ {ω : Ω | X.X (τ ω + u) ω - X.X (τ ω) ω ∈ B} ↔
       ω ∈ ⋃ s ∈ grid, D s)))
    (hCpartition : (let QT : Measure Ω := (P.withDensity (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))); let QU : Measure Ω := (P.withDensity (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ)))); let C : ℝ≥0 → Set Ω := fun s => A ∩ {ω : Ω | τ ω = s}; let D : ℝ≥0 → Set Ω := (fun s => C s ∩ (fun ω => X.X (s + u) ω - X.X s ω) ⁻¹' B); QT A = ∑ s ∈ grid, QT (C s)))
    (hDpartition : (let QT : Measure Ω := (P.withDensity (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))); let QU : Measure Ω := (P.withDensity (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ)))); let C : ℝ≥0 → Set Ω := fun s => A ∩ {ω : Ω | τ ω = s}; let D : ℝ≥0 → Set Ω := (fun s => C s ∩ (fun ω => X.X (s + u) ω - X.X s ω) ⁻¹' B); QT (A ∩
      {ω : Ω | X.X (τ ω + u) ω - X.X (τ ω) ω ∈ B}) =
      ∑ s ∈ grid, QT (D s)))
    : (let QT : Measure Ω := (P.withDensity (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))); let QU : Measure Ω := (P.withDensity (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ)))); let C : ℝ≥0 → Set Ω := fun s => A ∩ {ω : Ω | τ ω = s}; let D : ℝ≥0 → Set Ω := (fun s => C s ∩ (fun ω => X.X (s + u) ω - X.X s ω) ⁻¹' B); ∀ s ∈ grid,
      QT (D s) = QT (C s) * QU ((X.X u) ⁻¹' B)) := by
  intro QT QU C D s hs
  have hfib' : ∀ s ∈ grid, MeasurableSet {ω : Ω | τ ω = s} := hfib
  have hinc' : ∀ s, MeasurableSet ((fun ω => X.X (s + u) ω - X.X s ω) ⁻¹' B) := hinc
  have hXm' : ∀ r, Measurable (X.X r) := hXm
  have hsu : s ≤ s + u := le_self_add
  have hsuT : s + u ≤ T := hT s hs
  have hCm : MeasurableSet (C s) := hA.inter (hfib' s hs)
  have hDm : MeasurableSet (D s) := hCm.inter (hinc' s)
  have hCF : MeasurableSet[𝓕 s] (C s) := hHistory s hs
  have hIF : Measurable[𝓕 (s + u)] (fun ω => X.X (s + u) ω - X.X s ω) :=
    (X.adapted (s + u)).sub ((X.adapted s).mono (𝓕.mono hsu) le_rfl)
  have hDF : MeasurableSet[𝓕 (s + u)] (D s) :=
    (𝓕.mono hsu _ hCF).inter (hIF hB)
  -- rewrite QT (D s)
  have hQD : QT (D s) = ∫⁻ ω, (D s).indicator (fun _ => (1:ℝ≥0∞)) ω *
      ENNReal.ofReal (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)) ∂P := by
    simp only [QT]
    rw [withDensity_apply _ hDm, Aux_cyl6e.setLIntegral_eq_indicator P _ hDm]
  have hQC : QT (C s) = ∫⁻ ω, (C s).indicator (fun _ => (1:ℝ≥0∞)) ω *
      ENNReal.ofReal (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)) ∂P := by
    simp only [QT]
    rw [withDensity_apply _ hCm, Aux_cyl6e.setLIntegral_eq_indicator P _ hCm]
  have hUm : MeasurableSet ((X.X u) ⁻¹' B) := hXm' u hB
  have hQU : QU ((X.X u) ⁻¹' B) = ∫⁻ ω, B.indicator (fun _ => (1:ℝ≥0∞)) (X.X u ω) *
      ENNReal.ofReal (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ)) ∂P := by
    simp only [QU]
    rw [withDensity_apply _ hUm, Aux_cyl6e.setLIntegral_eq_indicator P _ hUm]
    rfl
  rw [hQD, hQC, hQU]
  -- tail from T to s+u
  rw [Aux_cyl6e.tail X θ hθ (s + u) T hsuT _ (measurable_const.indicator hDF)]
  rw [Aux_cyl6e.tail X θ hθ s T (hsu.trans hsuT) _ (measurable_const.indicator hCF)]
  -- split
  have hsplit : ∀ ω, (D s).indicator (fun _ => (1:ℝ≥0∞)) ω *
      ENNReal.ofReal (Real.exp (θ * X.X (s + u) ω - ((s + u : ℝ≥0) : ℝ) * X.ψ θ)) =
      ((C s).indicator (fun _ => (1:ℝ≥0∞)) ω *
        ENNReal.ofReal (Real.exp (θ * X.X s ω - (s : ℝ) * X.ψ θ))) *
      (B.indicator (fun _ => (1:ℝ≥0∞)) (X.X (s + u) ω - X.X s ω) *
        ENNReal.ofReal (Real.exp (θ * (X.X (s + u) ω - X.X s ω) - (u : ℝ) * X.ψ θ))) := by
    intro ω
    have he : ENNReal.ofReal (Real.exp (θ * X.X (s + u) ω - ((s + u : ℝ≥0) : ℝ) * X.ψ θ)) =
        ENNReal.ofReal (Real.exp (θ * X.X s ω - (s : ℝ) * X.ψ θ)) *
        ENNReal.ofReal (Real.exp (θ * (X.X (s + u) ω - X.X s ω) - (u : ℝ) * X.ψ θ)) := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2; push_cast; ring
    rw [he]
    by_cases h1 : ω ∈ C s
    · by_cases h2 : X.X (s + u) ω - X.X s ω ∈ B
      · have h3 : ω ∈ D s := ⟨h1, h2⟩
        simp only [Set.indicator_of_mem h1, Set.indicator_of_mem h2, Set.indicator_of_mem h3]
        ring
      · have h3 : ω ∉ D s := fun h => h2 h.2
        simp only [Set.indicator_of_mem h1, Set.indicator_of_notMem h2,
          Set.indicator_of_notMem h3]
        ring
    · have h3 : ω ∉ D s := fun h => h1 h.1
      simp only [Set.indicator_of_notMem h1, Set.indicator_of_notMem h3]
      ring
  simp_rw [hsplit]
  have hXs : Measurable[𝓕 s] (X.X s) := X.adapted s
  have hgs : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (θ * x - (s:ℝ) * X.ψ θ))) := by
    fun_prop
  have hgB : Measurable (fun x : ℝ => B.indicator (fun _ => (1:ℝ≥0∞)) x *
      ENNReal.ofReal (Real.exp (θ * x - (u:ℝ) * X.ψ θ))) :=
    (measurable_const.indicator hB).mul (by fun_prop)
  have hF1 : Measurable[𝓕 s] (fun ω => (C s).indicator (fun _ => (1:ℝ≥0∞)) ω *
      ENNReal.ofReal (Real.exp (θ * X.X s ω - (s : ℝ) * X.ψ θ))) :=
    (measurable_const.indicator hCF).mul (hgs.comp hXs)
  have hG : Measurable[MeasurableSpace.comap (fun ω => X.X (s + u) ω - X.X s ω) inferInstance]
      (fun ω => B.indicator (fun _ => (1:ℝ≥0∞)) (X.X (s + u) ω - X.X s ω) *
        ENNReal.ofReal (Real.exp (θ * (X.X (s + u) ω - X.X s ω) - (u : ℝ) * X.ψ θ))) :=
    hgB.comp (comap_measurable _)
  have hJ : Measurable (fun ω => X.X (s + u) ω - X.X s ω) := (hXm' _).sub (hXm' _)
  rw [ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace (𝓕.le s)
    hJ.comap_le (X.indepIncrements s (s + u) hsu).symm hF1 hG]
  congr 1
  have hid := X.stationaryIncrements s (s + u) hsu
  rw [add_tsub_cancel_left] at hid
  have := (hid.comp hgB).lintegral_eq
  simp only [Function.comp_def] at this
  exact this
