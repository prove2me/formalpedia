-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Qo7.eq_zero_of_orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:34:11.247663+00:00
-- url     : https://prove2.me/submissions/84a5ef2e-f6c8-4053-9dff-43f35f91aaa8

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsFurtherExtra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

open MeasureTheory
namespace UpperTheory.Reformulated.B.Qo7
theorem _root_.solution :
    ∀ {K : Type} [inst : TopologicalSpace K] [CompactSpace K]
    [inst_2 : MeasurableSpace K] [BorelSpace K] (μ : MeasureTheory.Measure K) [MeasureTheory.IsFiniteMeasure μ]
    [μ.IsOpenPosMeasure] (S : Set C(K, ℂ)),
    (1 : C(K, ℂ)) ∈ S →
      (∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) →
        (∀ a ∈ S, Star.star a ∈ S) →
          (∀ (x y : K), x ≠ y → ∃ a ∈ S, (a : K → ℂ) x ≠ (a : K → ℂ) y) →
            ∀ (f : C(K, ℂ)), (∀ a ∈ S, ∫ (x : K), (a : K → ℂ) x * (f : K → ℂ) x ∂μ = (0 : ℂ)) → f = (0 : C(K, ℂ)) := by
  intro K _ _ _ _ μ _ _ S h1 hmul hstar hsep f hf
  have hint : ∀ g : C(K, ℂ), Integrable (fun x => g x) μ := fun g =>
    (BoundedContinuousFunction.mkOfCompact g).integrable μ
  have hint' : ∀ a : C(K, ℂ), Integrable (fun x => a x * f x) μ := fun a => hint (a * f)
  let L0 : C(K, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun a => ∫ x, a x * f x ∂μ
      map_add' := fun a b => by
        simp only [ContinuousMap.add_apply, add_mul]
        exact integral_add (hint' a) (hint' b)
      map_smul' := fun c a => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply]
        exact integral_const_mul c _ }
  have hL : Continuous L0 := by
    refine (L0.mkContinuous (‖f‖ * μ.real Set.univ) fun a => ?_).continuous
    have : ‖∫ x, a x * f x ∂μ‖ ≤ (‖a‖ * ‖f‖) * μ.real Set.univ := by
      refine norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun x => ?_)
      rw [norm_mul]
      exact mul_le_mul (a.norm_coe_le_norm x) (f.norm_coe_le_norm x) (norm_nonneg _) (norm_nonneg _)
    calc ‖L0 a‖ ≤ (‖a‖ * ‖f‖) * μ.real Set.univ := this
      _ = _ := by ring
  have hspan : ∀ a ∈ StarAlgebra.adjoin ℂ S, a ∈ Submodule.span ℂ S := by
    intro a ha
    induction ha using StarAlgebra.adjoin_induction with
    | mem x hx => exact Submodule.subset_span hx
    | algebraMap r =>
      rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (Submodule.subset_span h1)
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | mul x y _ _ hx hy =>
      have h := Submodule.mul_mem_mul hx hy
      rw [Submodule.span_mul_span] at h
      refine Submodule.span_mono ?_ h
      rintro _ ⟨u, hu, v, hv, rfl⟩
      exact hmul u hu v hv
    | star x _ hx =>
      clear * - hx hstar
      induction hx using Submodule.span_induction with
      | mem y hy => exact Submodule.subset_span (hstar y hy)
      | zero => simp
      | add y z _ _ hy hz => rw [star_add]; exact Submodule.add_mem _ hy hz
      | smul c y _ hy => rw [star_smul]; exact Submodule.smul_mem _ _ hy
  have hker : Submodule.span ℂ S ≤ LinearMap.ker L0 :=
    Submodule.span_le.2 fun a ha => hf a ha
  have hsp : (StarAlgebra.adjoin ℂ S).SeparatesPoints := by
    intro x y hxy
    obtain ⟨a, ha, hne⟩ := hsep x y hxy
    exact ⟨a, ⟨a, StarAlgebra.subset_adjoin ℂ S ha, rfl⟩, hne⟩
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ hsp
  have hall : ∀ a : C(K, ℂ), L0 a = 0 := by
    intro a
    have ha : a ∈ closure (StarAlgebra.adjoin ℂ S : Set C(K, ℂ)) := by
      have : a ∈ (StarAlgebra.adjoin ℂ S).topologicalClosure := by
        rw [htop]; exact StarSubalgebra.mem_top
      exact this
    exact closure_minimal (t := {b | L0 b = 0}) (fun b hb => hker (hspan b hb))
      (isClosed_eq hL continuous_const) ha
  have h0 : ∫ x, ‖f x‖ ^ 2 ∂μ = 0 := by
    have h := hall (star f)
    change ∫ x, (star f) x * f x ∂μ = 0 at h
    have e : (fun x => (star f) x * f x) = fun x => ((‖f x‖ ^ 2 : ℝ) : ℂ) := by
      funext x
      simp only [ContinuousMap.star_apply, RCLike.star_def]
      rw [Complex.conj_mul']
      push_cast
      rfl
    rw [e, integral_complex_ofReal] at h
    exact_mod_cast h
  have hc : Continuous fun x => ‖f x‖ ^ 2 := by fun_prop
  have hi : Integrable (fun x => ‖f x‖ ^ 2) μ :=
    (BoundedContinuousFunction.mkOfCompact ⟨_, hc⟩).integrable μ
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => by positivity) hi).1 h0
  have heq := (hc.ae_eq_iff_eq μ continuous_zero).1 hae
  ext x
  simpa using congrFun heq x
end UpperTheory.Reformulated.B.Qo7
