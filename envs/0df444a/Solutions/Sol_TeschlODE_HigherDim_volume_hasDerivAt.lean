-- Prove2me | solution 1 for TeschlODE.HigherDim.volume_hasDerivAt
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T00:34:30.597499+00:00
-- url     : https://prove2.me/submissions/3b5cc1f5-c72b-4313-a39c-2fb6e43cf8bf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_TeschlODE_HigherDim_IsIntegralCurve
import Definitions.Def_TeschlODE_HigherDim_IsMaximalFlow
import Definitions.Def_TeschlODE_HigherDim_divergence
import Theorems.Thm_TeschlODE_HigherDim_flow_spatial_c1_on_compact
import Theorems.Thm_TeschlODE_HigherDim_flow_jacobian_integral_hasDerivAt

open MeasureTheory Set Filter Topology TeschlODE.HigherDim

set_option autoImplicit false

namespace TeschlODE.HigherDim

section Flow
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : E → E} {M : Set E} {I : E → Set ℝ} {Φ : ℝ → E → E}

/-- The accepted flow-core argument, generalized to include Hamiltonian phase space. -/
theorem flow_add (hΦ : IsMaximalFlow f M I Φ) {x : E} (hx : x ∈ M)
    {s : ℝ} (hs : s ∈ I x) {t : ℝ} (ht : t + s ∈ I x) :
    t ∈ I (Φ s x) ∧ Φ t (Φ s x) = Φ (t + s) x := by
  obtain ⟨⟨hJo, hJc, hJM, hJd⟩, -, -, -⟩ := hΦ x hx
  have hyM : Φ s x ∈ M := hJM s hs
  have hcurve : IsIntegralCurve f M {τ | τ + s ∈ I x} (fun τ => Φ (τ + s) x) := by
    refine ⟨hJo.preimage (continuous_id.add continuous_const), ⟨fun a ha b hb τ hτ => ?_⟩,
      fun τ hτ => hJM _ hτ, fun τ hτ => (hJd _ hτ).comp_add_const τ s⟩
    exact hJc.out ha hb ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  obtain ⟨-, -, -, hmax⟩ := hΦ (Φ s x) hyM
  obtain ⟨hsub, heq⟩ := hmax _ _ hcurve (by simpa using hs) (by simp)
  exact ⟨hsub ht, (heq t ht).symm⟩

/-- Backward evolution inverts forward evolution wherever the latter is defined. -/
theorem flow_inverse (hΦ : IsMaximalFlow f M I Φ) {x : E} (hx : x ∈ M)
    {t : ℝ} (ht : t ∈ I x) :
    -t ∈ I (Φ t x) ∧ Φ (-t) (Φ t x) = x := by
  have h := flow_add hΦ hx ht (t := -t) (by simpa using (hΦ x hx).2.1)
  simpa [(hΦ x hx).2.2.1] using h

/-- A time slice is injective on every subset of its living domain. -/
theorem flow_injOn (hΦ : IsMaximalFlow f M I Φ) {U : Set E} (hUM : U ⊆ M)
    {t : ℝ} (ht : ∀ x ∈ U, t ∈ I x) : InjOn (Φ t) U := by
  intro x hx y hy hxy
  have hxi := (flow_inverse hΦ (hUM hx) (ht x hx)).2
  have hyi := (flow_inverse hΦ (hUM hy) (ht y hy)).2
  rw [← hxi, ← hyi, hxy]

end Flow

/-- A C¹ field has continuous divergence. -/
theorem continuous_divergence {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} (hf : ContDiff ℝ 1 f) :
    Continuous (divergence f) := by
  unfold divergence
  apply continuous_finsetSum
  intro i hi
  exact (PiLp.continuous_apply (p := 2) (β := fun _ : Fin n => ℝ) i).comp
    ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const)

/-- The divergence is integrable on any bounded set, by passing to its compact closure. -/
theorem integrableOn_divergence_bounded {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} (hf : ContDiff ℝ 1 f)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hUb : Bornology.IsBounded U) :
    IntegrableOn (divergence f) U :=
  ((continuous_divergence hf).continuousOn.integrableOn_compact hUb.isCompact_closure).mono_set
    subset_closure

end TeschlODE.HigherDim

theorem solution {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hf : ContDiff ℝ 1 f)
    (I : EuclideanSpace ℝ (Fin n) → Set ℝ)
    (Φ : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hΦ : IsMaximalFlow f Set.univ I Φ)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (t₀ : ℝ) (ht₀ : ∀ x ∈ closure U, t₀ ∈ I x) :
    volume (Φ t₀ '' U) < ⊤ ∧ IntegrableOn (divergence f) (Φ t₀ '' U) ∧
      HasDerivAt (fun t : ℝ => (volume (Φ t '' U)).toReal)
        (∫ x in Φ t₀ '' U, divergence f x) t₀ := by
  obtain ⟨ε, hε, hregular⟩ :=
    flow_spatial_c1_on_compact f hf I Φ hΦ U hU hUb t₀ ht₀
  have ht : t₀ ∈ Ioo (t₀ - ε) (t₀ + ε) := ⟨by linarith, by linarith⟩
  have hbounded : Bornology.IsBounded (Φ t₀ '' U) :=
    ((hUb.isCompact_closure.image_of_continuousOn (hregular t₀ ht).2.1).isBounded).subset
      (image_mono subset_closure)
  have hfinite : volume (Φ t₀ '' U) < ⊤ :=
    (measure_mono subset_closure).trans_lt hbounded.isCompact_closure.measure_lt_top
  have hinj : ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), InjOn (Φ t) U := by
    intro t htime
    exact flow_injOn hΦ (subset_univ U)
      (fun x hx => (hregular t htime).1 x (subset_closure hx))
  have hchange : ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), ∀ g : EuclideanSpace ℝ (Fin n) → ℝ,
      (∫ x in Φ t '' U, g x) =
      ∫ x in U, |(fderiv ℝ (Φ t) x).det| * g (Φ t x) := by
    intro t htime g
    simpa only [smul_eq_mul] using
      integral_image_eq_integral_abs_det_fderiv_smul volume hU.measurableSet
        (fun x hx => ((hregular t htime).2.2 x hx).hasFDerivAt.hasFDerivWithinAt)
        (hinj t htime) g
  have hvol : ∀ᶠ t in 𝓝 t₀,
      (∫ x in U, |(fderiv ℝ (Φ t) x).det|) = (volume (Φ t '' U)).toReal := by
    filter_upwards [Ioo_mem_nhds (by linarith : t₀ - ε < t₀)
      (by linarith : t₀ < t₀ + ε)] with t htime
    simpa [Measure.real] using (hchange t htime (fun _ => (1 : ℝ))).symm
  refine ⟨hfinite, integrableOn_divergence_bounded hf hbounded, ?_⟩
  have hderiv := flow_jacobian_integral_hasDerivAt f hf I Φ hΦ U hU hUb t₀ ht₀
  rw [← hchange t₀ ht (divergence f)] at hderiv
  exact hderiv.congr_of_eventuallyEq (Filter.EventuallyEq.symm hvol)
