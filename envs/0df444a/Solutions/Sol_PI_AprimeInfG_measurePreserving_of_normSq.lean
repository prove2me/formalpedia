-- Prove2me | solution 1 for PI.AprimeInfG.measurePreserving_of_normSq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:10:37.706648+00:00
-- url     : https://prove2.me/submissions/6588717d-25d0-4be6-be6b-b9835da30042

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_PiCoord
import Theorems.Thm_PI_AprimeInfG_measurePreserving_piCurry_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AprimeInfG
open MeasureTheory Set
open scoped ENNReal
namespace PI.AprimeInfG
theorem _root_.solution {ι V : Type} [Fintype ι] [Fintype V] {α : V → Type} [∀ v, Fintype (α v)]
    (T : EuclideanSpace ℝ ι →ₗ[ℝ] (∀ v, EuclideanSpace ℝ (α v))) (hbij : Function.Bijective T)
    (hn : ∀ x, ∑ v, ‖T x v‖ ^ 2 = ‖x‖ ^ 2) :
    MeasurePreserving T volume (Measure.pi fun _ => volume) := by

  let F : (∀ v, EuclideanSpace ℝ (α v)) →ₗ[ℝ] EuclideanSpace ℝ (Σ v, α v) :=
    { toFun := fun z => WithLp.toLp 2 (fun p : Σ v, α v => z p.1 p.2)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hFn : ∀ z, ‖F z‖ ^ 2 = ∑ v, ‖z v‖ ^ 2 := by
    intro z
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [EuclideanSpace.norm_sq_eq]
    rfl
  have hF : MeasurePreserving F (Measure.pi fun v => volume) volume := by
    have h1 := measurePreserving_pi (fun v => (volume : Measure (EuclideanSpace ℝ (α v))))
      (fun v => (volume : Measure (α v → ℝ)))
      (fun v => EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (α v))
    have h2 := measurePreserving_piCurry_symm (X := fun v (_ : α v) => ℝ) (fun _ _ => (volume : Measure ℝ))
    have h3 := PiLp.volume_preserving_toLp (Σ v, α v)
    simp only [← MeasureTheory.volume_pi] at h2
    exact (h3.comp (h2.comp h1))
  have hGn : ∀ x, ‖F (T x)‖ = ‖x‖ := by
    intro x
    have := hFn (T x)
    rw [hn x] at this
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this
  let G : EuclideanSpace ℝ ι →ₗᵢ[ℝ] EuclideanSpace ℝ (Σ v, α v) := ⟨F ∘ₗ T, hGn⟩
  have hFi : Function.Injective F := by
    intro z z' h
    funext v
    ext a
    have := congrArg (fun w : EuclideanSpace ℝ (Σ v, α v) => w ⟨v, a⟩) h
    exact this
  have hFs : Function.Surjective F := by
    intro w
    exact ⟨fun v => WithLp.toLp 2 (fun a => w ⟨v, a⟩), rfl⟩
  have hGs : Function.Surjective G := (hFs.comp hbij.2)
  let Ge := LinearIsometryEquiv.ofSurjective G hGs
  have hGe : MeasurePreserving Ge volume volume := Ge.measurePreserving
  let Fe : (∀ v, EuclideanSpace ℝ (α v)) ≃ᵐ EuclideanSpace ℝ (Σ v, α v) :=
    { toEquiv := Equiv.ofBijective F ⟨hFi, hFs⟩
      measurable_toFun := hF.measurable
      measurable_invFun := by
        have : ⇑(Equiv.ofBijective F ⟨hFi, hFs⟩).symm =
            fun (w : EuclideanSpace ℝ (Σ v, α v)) (v : V) => (WithLp.toLp 2 (fun a => w ⟨v, a⟩) : EuclideanSpace ℝ (α v)) := by
          funext w
          apply (Equiv.ofBijective F ⟨hFi, hFs⟩).injective
          rw [Equiv.apply_symm_apply]
          rfl
        rw [this]
        exact measurable_pi_lambda _ fun v =>
          (PiLp.volume_preserving_toLp (α v)).measurable.comp
            (measurable_pi_lambda _ fun a => (measurable_pi_apply _).comp (PiLp.volume_preserving_ofLp _).measurable) }
  have hFe : MeasurePreserving Fe (Measure.pi fun v => volume) volume := hF
  have key := hFe.symm.comp hGe
  convert key using 1
  funext x
  show T x = Fe.symm (F (T x))
  exact (Fe.symm_apply_apply (T x)).symm
end PI.AprimeInfG
