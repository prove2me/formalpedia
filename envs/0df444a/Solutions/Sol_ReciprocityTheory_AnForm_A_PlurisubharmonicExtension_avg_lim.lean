-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.avg_lim
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:19:37.817183+00:00
-- url     : https://prove2.me/submissions/b35ad073-8baa-4916-8aeb-4dfafe983edb

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExtA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExtB
import Theorems.Thm_ReciprocityTheory_AnForm_A_PlurisubharmonicExtension_ii_of_bdd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Real Filter Topology MeasureTheory
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
namespace ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
theorem _root_.solution {E X : Type*} [TopologicalSpace E] {ψ : E → ℝ} {U K : Set E}
    (hψ : UpperSemicontinuousOn ψ U) (hKU : K ⊆ U) {m M : ℝ} (hm : ∀ y ∈ K, m ≤ ψ y)
    (hM : ∀ y ∈ K, ψ y ≤ M) {l : Filter X} [l.IsCountablyGenerated] (P : X → ℝ → E)
    (P0 : ℝ → E) (hPc : ∀ᶠ x in l, Continuous (P x)) (hP0c : Continuous P0)
    (hPK : ∀ᶠ x in l, ∀ θ, P x θ ∈ K) (hP0K : ∀ θ, P0 θ ∈ K)
    (hlim : ∀ θ, Tendsto (fun x => P x θ) l (𝓝 (P0 θ))) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in l, ∫ θ in (0 : ℝ)..2 * π, ψ (P x θ) ≤ (∫ θ in (0 : ℝ)..2 * π, ψ (P0 θ)) + ε := by
  have usc_comp : ∀ Q : ℝ → E, Continuous Q → (∀ θ, Q θ ∈ K) →
      UpperSemicontinuous (fun θ => ψ (Q θ)) := by
    intro Q hQ hQK θ y hy
    have h1 : Tendsto Q (𝓝 θ) (𝓝[U] (Q θ)) :=
      tendsto_nhdsWithin_iff.2 ⟨hQ.tendsto θ, Filter.Eventually.of_forall (fun θ' => hKU (hQK θ'))⟩
    exact h1.eventually (hψ (Q θ) (hKU (hQK θ)) y hy)
  have bnd : ∀ y ∈ K, |ψ y| ≤ |m| + |M| := by
    intro y hy
    rw [abs_le]
    have h1 := hm y hy
    have h2 := hM y hy
    have h3 := neg_abs_le m
    have h4 := le_abs_self M
    have h5 := abs_nonneg m
    have h6 := abs_nonneg M
    constructor <;> linarith
  have meas0 : Measurable (fun θ => ψ (P0 θ)) := (usc_comp P0 hP0c hP0K).measurable
  have bndG : ∀ x, (∀ θ, P x θ ∈ K) → ∀ θ, |max (ψ (P x θ)) (ψ (P0 θ))| ≤ |m| + |M| := by
    intro x hxK θ
    rw [abs_le]
    have h1 := abs_le.1 (bnd _ (hxK θ))
    have h2 := abs_le.1 (bnd _ (hP0K θ))
    exact ⟨le_trans h1.1 (le_max_left _ _), max_le h1.2 h2.2⟩
  have hlimG : ∀ θ, Tendsto (fun x => max (ψ (P x θ)) (ψ (P0 θ))) l (𝓝 (ψ (P0 θ))) := by
    intro θ
    rw [tendsto_order]
    refine ⟨fun a ha => Filter.Eventually.of_forall (fun x => lt_of_lt_of_le ha (le_max_right _ _)),
      fun b hb => ?_⟩
    have h1 : Tendsto (fun x => P x θ) l (𝓝[U] (P0 θ)) :=
      tendsto_nhdsWithin_iff.2 ⟨hlim θ, hPK.mono (fun x hx => hKU (hx θ))⟩
    filter_upwards [h1.eventually (hψ (P0 θ) (hKU (hP0K θ)) b hb)] with x hx
    exact max_lt hx hb
  have hT : Tendsto (fun x => ∫ θ in (0 : ℝ)..2 * π, max (ψ (P x θ)) (ψ (P0 θ))) l
      (𝓝 (∫ θ in (0 : ℝ)..2 * π, ψ (P0 θ))) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => |m| + |M|)
    · filter_upwards [hPc, hPK] with x hx hxK
      exact ((usc_comp (P x) hx hxK).measurable.max meas0).aestronglyMeasurable
    · filter_upwards [hPK] with x hxK
      exact Filter.Eventually.of_forall (fun θ _ => by
        rw [Real.norm_eq_abs]
        exact bndG x hxK θ)
    · exact intervalIntegrable_const
    · exact Filter.Eventually.of_forall (fun θ _ => hlimG θ)
  have hev := (tendsto_order.1 hT).2 _ (lt_add_of_pos_right _ hε)
  filter_upwards [hev, hPc, hPK] with x hx hxc hxK
  have hmeas := (usc_comp (P x) hxc hxK).measurable
  have hIF : IntervalIntegrable (fun θ => ψ (P x θ)) volume 0 (2 * π) :=
    ii_of_bdd hmeas (|m| + |M|) (fun θ => bnd _ (hxK θ)) 0 (2 * π)
  have hIG : IntervalIntegrable (fun θ => max (ψ (P x θ)) (ψ (P0 θ))) volume 0 (2 * π) :=
    ii_of_bdd (hmeas.max meas0) (|m| + |M|) (bndG x hxK) 0 (2 * π)
  have hle : ∫ θ in (0 : ℝ)..2 * π, ψ (P x θ) ≤ ∫ θ in (0 : ℝ)..2 * π, max (ψ (P x θ)) (ψ (P0 θ)) :=
    intervalIntegral.integral_mono_on (by positivity) hIF hIG (fun θ _ => le_max_left _ _)
  exact le_trans hle hx.le
end ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
