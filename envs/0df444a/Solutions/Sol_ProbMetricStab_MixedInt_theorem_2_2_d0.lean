-- Prove2me | solution 1 for ProbMetricStab.MixedInt.theorem_2_2_d0
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T00:58:39.422959+00:00
-- url     : https://prove2.me/submissions/1f3c058d-c6cf-4ba6-93c4-b0a0404810be
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ProbMetricStab_MixedInt_ObjectiveStability
import Definitions.Def_ProbMetricStab_General_Setting
import Theorems.Thm_ProbMetricStab_General_theorem_2_2
import Theorems.Thm_ProbMetricStab_General_theorem_2_2_d_zero

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbMetricStab.MixedInt.Bridge

open ProbMetricStab.MixedInt Set Metric

variable {m s : ℕ}

/-- The objective-only program `min ∫ f(ξ, x) ν(dξ)` as a `General.Model` with `d = 0`. -/
def model (Ξ : Set (EuclideanSpace ℝ (Fin s))) (X : Set (EuclideanSpace ℝ (Fin m)))
    (f : EuclideanSpace ℝ (Fin s) → EuclideanSpace ℝ (Fin m) → EReal) :
    ProbMetricStab.General.Model m s 0 :=
  ⟨X, Ξ, fun _ ξ x => f ξ.1 x⟩

/-- A measure on `ℝ^s` concentrated on `Ξ`, viewed as a measure on `Ξ`. -/
noncomputable def lift (Ξ : Set (EuclideanSpace ℝ (Fin s)))
    (ν : Measure (EuclideanSpace ℝ (Fin s))) : Measure ↥Ξ :=
  ν.comap Subtype.val

section

variable {Ξ : Set (EuclideanSpace ℝ (Fin s))} {X : Set (EuclideanSpace ℝ (Fin m))}
  {f : EuclideanSpace ℝ (Fin s) → EuclideanSpace ℝ (Fin m) → EReal}

lemma lintegral_lift (hΞ : MeasurableSet Ξ) {ν : Measure (EuclideanSpace ℝ (Fin s))}
    (hν : ν Ξᶜ = 0) (h : EuclideanSpace ℝ (Fin s) → ℝ≥0∞) :
    ∫⁻ ξ : ↥Ξ, h ξ ∂(lift Ξ ν) = ∫⁻ ξ, h ξ ∂ν := by
  rw [lift, lintegral_subtype_comap hΞ, Measure.restrict_eq_self_of_ae_mem]
  rw [ae_iff]
  exact hν

lemma expect_lift (hΞ : MeasurableSet Ξ) {ν : Measure (EuclideanSpace ℝ (Fin s))}
    (hν : ν Ξᶜ = 0) (g : EuclideanSpace ℝ (Fin s) → EReal) :
    DupacovaWets.Consistency.expect (lift Ξ ν) (fun ξ => g ξ.1) =
      DupacovaWets.Consistency.expect ν g := by
  unfold DupacovaWets.Consistency.expect
  rw [lintegral_lift hΞ hν (fun ξ => (g ξ).toENNReal),
    lintegral_lift hΞ hν (fun ξ => (-g ξ).toENNReal)]

lemma integral_lift (hΞ : MeasurableSet Ξ) {ν : Measure (EuclideanSpace ℝ (Fin s))}
    (hν : ν Ξᶜ = 0) (j : Fin 1) (x : EuclideanSpace ℝ (Fin m)) :
    (model Ξ X f).integral (lift Ξ ν) j x = intObj f ν x :=
  expect_lift hΞ hν (fun ξ => f ξ x)

lemma prob_lift (hΞ : MeasurableSet Ξ) {ν : Measure (EuclideanSpace ℝ (Fin s))}
    (hν : ν ∈ ProbOn Ξ) : IsProbabilityMeasure (lift Ξ ν) := by
  have := hν.1
  refine isProbabilityMeasure_comap Subtype.val_injective ?_ (fun t ht => hΞ.subtype_image ht)
  rw [Subtype.range_coe, ae_iff]
  exact hν.2

lemma PFU_lift (hΞ : MeasurableSet Ξ) {U : Set (EuclideanSpace ℝ (Fin m))}
    {ν : Measure (EuclideanSpace ℝ (Fin s))} (hν : ν ∈ PFU Ξ f X U) :
    lift Ξ ν ∈ (model Ξ X f).PFU U := by
  obtain ⟨hP, h1, h2⟩ := hν
  refine ⟨prob_lift hΞ hP, fun j => ⟨fun r hr => ?_, ?_⟩⟩
  · have hset : {x : EuclideanSpace ℝ (Fin m) | x ∈ X ∧ ‖x‖ ≤ r} =
        X ∩ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) r := by
      ext x; simp [mem_closedBall, dist_zero_right]
    have := h1 r hr
    change ⊥ < DupacovaWets.Consistency.expect (lift Ξ ν)
      (fun ξ => ⨅ x ∈ {x : EuclideanSpace ℝ (Fin m) | x ∈ X ∧ ‖x‖ ≤ r}, f ξ.1 x)
    rw [hset, expect_lift hΞ hP.2 (fun ξ => ⨅ x ∈ X ∩ Metric.closedBall 0 r, f ξ x)]
    exact this
  · have heq : (⨆ x ∈ (model Ξ X f).X ∩ closure U, (model Ξ X f).integral (lift Ξ ν) j x) =
        ⨆ x ∈ X ∩ closure U, intObj f ν x :=
      iSup_congr fun x => iSup_congr fun _ => integral_lift hΞ hP.2 j x
    rw [heq]; exact h2

lemma normal_lift (hf : ProbMetricStab.TwoStage.IsNormalIntegrand Ξ f) (j : Fin 1) :
    ProbMetricStab.General.IsNormalIntegrand ((model Ξ X f).f j) := by
  refine ⟨fun ω => hf.1 ω.1 ω.2, fun O hO => ?_⟩
  have h := (hf.2 O hO)
  convert measurable_subtype_coe h using 1
  ext ω
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  exact ⟨fun h' => ⟨ω.2, h'⟩, fun h' => h'.2⟩

lemma M_model (ν : Measure ↥Ξ) : (model Ξ X f).M ν = X := by
  ext x; simp [ProbMetricStab.General.Model.M, model]

lemma MU_model (U : Set (EuclideanSpace ℝ (Fin m))) (ν : Measure ↥Ξ) :
    (model Ξ X f).MU U ν = X ∩ closure U := by
  ext x; simp [ProbMetricStab.General.Model.MU, model]

variable (hΞ : MeasurableSet Ξ) {ν : Measure (EuclideanSpace ℝ (Fin s))} (hν : ν Ξᶜ = 0)
include hΞ hν

lemma v_lift : (model Ξ X f).v (lift Ξ ν) = optVal f X ν := by
  unfold ProbMetricStab.General.Model.v optVal
  rw [M_model]
  exact iInf_congr fun x => iInf_congr fun _ => integral_lift hΞ hν 0 x

lemma S_lift : (model Ξ X f).S (lift Ξ ν) = solSet f X ν := by
  ext x
  simp only [ProbMetricStab.General.Model.S, solSet, M_model, Set.mem_ofPred_eq]
  rw [v_lift hΞ hν, integral_lift hΞ hν]

lemma vU_lift (U : Set (EuclideanSpace ℝ (Fin m))) :
    (model Ξ X f).vU U (lift Ξ ν) = locOptVal f X U ν := by
  unfold ProbMetricStab.General.Model.vU locOptVal
  rw [MU_model]
  exact iInf_congr fun x => iInf_congr fun _ => integral_lift hΞ hν 0 x

lemma SU_lift (U : Set (EuclideanSpace ℝ (Fin m))) :
    (model Ξ X f).SU U (lift Ξ ν) = locSolSet f X U ν := by
  ext x
  simp only [ProbMetricStab.General.Model.SU, locSolSet, MU_model, Set.mem_ofPred_eq]
  rw [vU_lift hΞ hν, integral_lift hΞ hν]

lemma dFU_lift (U : Set (EuclideanSpace ℝ (Fin m))) {μ : Measure (EuclideanSpace ℝ (Fin s))}
    (hμ : μ Ξᶜ = 0) :
    (model Ξ X f).dFU U (lift Ξ μ) (lift Ξ ν) = dFU f X U μ ν := by
  unfold ProbMetricStab.General.Model.dFU dFU
  refine iSup_congr fun x => iSup_congr fun _ => ?_
  simp only [integral_lift hΞ hμ, integral_lift hΞ hν, iSup_const]

lemma psiInv_lift (U : Set (EuclideanSpace ℝ (Fin m))) (t : ℝ≥0∞) :
    (model Ξ X f).ψinv U (lift Ξ ν) (t : EReal) = growthInv f X U ν t := by
  have hψ : ∀ τ : ℝ≥0, (model Ξ X f).ψ U (lift Ξ ν) (τ : ℝ) = growthFn f X U ν τ := by
    intro τ
    unfold ProbMetricStab.General.Model.ψ growthFn
    rw [MU_model, S_lift hΞ hν, v_lift hΞ hν, ENNReal.ofReal_coe_nnreal]
    exact iInf_congr fun x => iInf_congr fun _ => by rw [integral_lift hΞ hν]
  unfold ProbMetricStab.General.Model.ψinv growthInv
  apply le_antisymm
  · refine iSup₂_le fun τ hτ => ?_
    have h1 := hψ τ.toNNReal
    rw [Real.coe_toNNReal _ hτ.1] at h1
    have hτ2 : growthFn f X U ν τ.toNNReal ≤ (t : EReal) := by rw [← h1]; exact hτ.2
    refine le_iSup₂_of_le (f := fun (τ : ℝ≥0) (_ : growthFn f X U ν τ ≤ (t : EReal)) =>
      (τ : ℝ≥0∞)) τ.toNNReal hτ2 ?_
    rfl
  · refine iSup₂_le fun τ hτ => ?_
    refine le_iSup₂_of_le (f := fun (τ : ℝ) (_ : τ ∈ {τ : ℝ | 0 ≤ τ ∧
      (model Ξ X f).ψ U (lift Ξ ν) τ ≤ (t : EReal)}) => ENNReal.ofReal τ) (τ : ℝ)
      ⟨τ.2, by rw [hψ τ]; exact hτ⟩ ?_
    rw [ENNReal.ofReal_coe_nnreal]

lemma Psi_lift (U : Set (EuclideanSpace ℝ (Fin m))) (η : ℝ≥0∞) :
    (model Ξ X f).Ψ U (lift Ξ ν) η = PsiThm23 f X U ν η := by
  unfold ProbMetricStab.General.Model.Ψ PsiThm23
  rw [psiInv_lift hΞ hν]

end

/-- The assumptions of Theorem 2.2 transfer to the lifted model. -/
lemma thm22_lift {Ξ : Set (EuclideanSpace ℝ (Fin s))} (hΞ : IsClosed Ξ)
    {X : Set (EuclideanSpace ℝ (Fin m))} (hX : IsClosed X) (hXne : X.Nonempty)
    {f : EuclideanSpace ℝ (Fin s) → EuclideanSpace ℝ (Fin m) → EReal}
    (hf : ProbMetricStab.TwoStage.IsNormalIntegrand Ξ f)
    {U : Set (EuclideanSpace ℝ (Fin m))} (hUo : IsOpen U) (hUb : Bornology.IsBounded U)
    {μ : Measure (EuclideanSpace ℝ (Fin s))} (hμ : μ ∈ PFU Ξ f X U)
    (hS : (solSet f X μ).Nonempty) (hSU : solSet f X μ ⊆ U) :
    (model Ξ X f).Thm22Assumptions U (lift Ξ μ) := by
  have hΞm := hΞ.measurableSet
  have hμ0 : μ Ξᶜ = 0 := hμ.1.2
  refine ⟨⟨hXne, hX, hΞ, normal_lift hf⟩, PFU_lift hΞm hμ, ?_, hUo, hUb, ?_, ?_, ?_⟩
  · rw [S_lift hΞm hμ0]; exact hS
  · rw [S_lift hΞm hμ0]; exact hSU
  · intro h; omega
  · intro xbar _
    refine ⟨0, 1, le_rfl, one_pos, fun x hx y _ => ?_⟩
    have hxM : x ∈ (model Ξ X f).My (lift Ξ μ) y := ⟨hx.1, fun i => i.elim0⟩
    rw [infEDist_zero_of_mem hxM]
    exact bot_le

end ProbMetricStab.MixedInt.Bridge

open ProbMetricStab.MixedInt ProbMetricStab.MixedInt.Bridge in
theorem solution {m s : ℕ}
    (Ξ : Set (EuclideanSpace ℝ (Fin s))) (hΞ : IsClosed Ξ)
    (X : Set (EuclideanSpace ℝ (Fin m))) (hX : IsClosed X) (hXne : X.Nonempty)
    (f : EuclideanSpace ℝ (Fin s) → EuclideanSpace ℝ (Fin m) → EReal)
    (hf : ProbMetricStab.TwoStage.IsNormalIntegrand Ξ f)
    (U : Set (EuclideanSpace ℝ (Fin m))) (hUo : IsOpen U) (hUb : Bornology.IsBounded U)
    (μ : Measure (EuclideanSpace ℝ (Fin s))) (hμ : μ ∈ PFU Ξ f X U)
    (hS : (solSet f X μ).Nonempty) (hSU : solSet f X μ ⊆ U) :
    (∀ O : Set (EuclideanSpace ℝ (Fin m)), IsOpen O → locSolSet f X U μ ⊆ O →
      ∃ ε : ℝ, 0 < ε ∧ ∀ ν ∈ PFU Ξ f X U, dFU f X U μ ν < ENNReal.ofReal ε →
        locSolSet f X U ν ⊆ O) ∧
    (∀ ν ∈ PFU Ξ f X U,
      optVal f X μ ≠ ⊤ ∧ optVal f X μ ≠ ⊥ ∧ locOptVal f X U ν ≠ ⊤ ∧ locOptVal f X U ν ≠ ⊥ ∧
      ENNReal.ofReal |(optVal f X μ).toReal - (locOptVal f X U ν).toReal| ≤ dFU f X U μ ν) ∧
    (∃ δ : ℝ, 0 < δ ∧ ∀ ν ∈ PFU Ξ f X U, dFU f X U μ ν < ENNReal.ofReal δ →
      IsCLMSet f X U ν) := by
  have hΞm := hΞ.measurableSet
  have hμ0 : μ Ξᶜ = 0 := hμ.1.2
  have hA := thm22_lift hΞ hX hXne hf hUo hUb hμ hS hSU
  obtain ⟨hBerge, L, δ, -, hδ, hmain⟩ := ProbMetricStab.General.theorem_2_2 hA
  have h0 := ProbMetricStab.General.theorem_2_2_d_zero hA
  refine ⟨fun O hO hsub => ?_, fun ν hν => ?_, ⟨δ, hδ, fun ν hν hd => ?_⟩⟩
  · rw [← SU_lift hΞm hμ0] at hsub
    obtain ⟨ε, hε, h⟩ := hBerge O hO hsub
    refine ⟨ε, hε, fun ν hν hd => ?_⟩
    have hν0 : ν Ξᶜ = 0 := hν.1.2
    rw [← dFU_lift hΞm hν0 U hμ0] at hd
    have := h (lift Ξ ν) (PFU_lift hΞm hν) hd
    rwa [SU_lift hΞm hν0] at this
  · have hν0 : ν Ξᶜ = 0 := hν.1.2
    obtain ⟨h1, h2, h3, h4, h5⟩ := h0 (lift Ξ ν) (PFU_lift hΞm hν)
    rw [v_lift hΞm hμ0] at h1 h2 h5
    rw [vU_lift hΞm hν0] at h3 h4 h5
    rw [dFU_lift hΞm hν0 U hμ0] at h5
    refine ⟨h1, h2, h3, h4, ?_⟩
    rw [← EReal.coe_toReal h1 h2, ← EReal.coe_toReal h3 h4, ← EReal.coe_sub,
      EReal.abs_def] at h5
    simpa only [EReal.toReal_coe] using h5
  · have hν0 : ν Ξᶜ = 0 := hν.1.2
    rw [← dFU_lift hΞm hν0 U hμ0] at hd
    obtain ⟨-, hne, hUo', heq, hsub⟩ := hmain (lift Ξ ν) (PFU_lift hΞm hν) hd
    rw [heq, SU_lift hΞm hν0] at hne hsub
    exact ⟨hUo', hne, hsub⟩
