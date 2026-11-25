-- Prove2me | solution 1 for PI.VolStabW.RestrProdA.rpTail_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:22:39.381365+00:00
-- url     : https://prove2.me/submissions/1a81591b-6d93-4de3-98e5-3d7e3eda13bd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProdSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProdA
import Theorems.Thm_PI_VolStabW_RestrProdA_hasProd_compl_of_ne_zero
import Theorems.Thm_PI_VolStabW_RestrProdA_hasProd_ofReal_of_complex
import Theorems.Thm_PI_VolStabW_PositiveNearLattice_isClopen_latV
import Theorems.Thm_PI_VolStabW_PositiveNearLattice_isSB_latV


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.RestrProdA
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct
namespace PI.VolStabW.RestrProdA
theorem _root_.solution {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    [FiniteDimensional F E] {a M d : ℕ} (b : Module.Basis (Fin d) F E)
    (m : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin a → Fin M → Fv F v ⊗[F] E))
    (hSB : ∀ v (Φ : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ), IsSB Φ → Integrable Φ (m v))
    (hmult : ∀ (Φf : (Fin a → Fin M → Af F ⊗[F] E) → ℂ)
      (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ),
      IsPureFin b Φf Φv → Multipliable (fun v => ∫ X, Φv v X ∂(m v))) :
    (∃ v, ∀ Φ : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ, IsSB Φ → ∫ X, Φ X ∂(m v) = 0) ∨
    ∀ S : Finset (HeightOneSpectrum (𝓞 F)), ∃ c : ENNReal, c ≠ ⊤ ∧
      HasProd (fun v : {v // v ∉ S} => m v.1 (latV b v.1)) c := by
  classical
  by_cases h0 : ∃ v, ∀ Φ : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ, IsSB Φ → ∫ X, Φ X ∂(m v) = 0
  · exact Or.inl h0
  refine Or.inr fun S => ?_
  push_neg at h0
  choose g hgSB hg0 using h0
  let Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ :=
    fun v => if v ∈ S then g v else (latV b v).indicator 1
  have hpure : IsPureFin b (fun Y => ∏ᶠ v, Φv v (projV v Y)) Φv := by
    refine ⟨fun v => ?_, ?_, fun Y => rfl⟩
    · by_cases hv : v ∈ S
      · simp only [Φv, hv, if_true]; exact hgSB v
      · simp only [Φv, hv, if_false]; exact PositiveNearLattice.isSB_latV b v a M
    · refine Filter.eventually_cofinite.2 (S.finite_toSet.subset fun v hv => ?_)
      by_contra h
      exact hv (if_neg h)
  have hP := (hmult _ Φv hpure).hasProd
  have hne : ∀ v ∈ S, ∫ X, Φv v X ∂(m v) ≠ 0 := fun v hv => by
    simp only [Φv, hv, if_true]; exact hg0 v
  have h1 := hasProd_compl_of_ne_zero hP S hne
  have hL : ∀ v, MeasurableSet (latV (M := M) (n := a) b v) := fun v =>
    (PositiveNearLattice.isClopen_latV b v a M).isOpen.measurableSet
  have hfin : ∀ v, m v (latV b v) ≠ ⊤ := fun v => by
    have h := hSB v _ (PositiveNearLattice.isSB_latV b v a M)
    rw [integrable_indicator_iff (hL v)] at h
    exact (((integrableOn_const_iff (C := (1 : ℂ))).1 h).resolve_left (by simp)).ne
  have e : {v | v ∉ S}.mulIndicator (fun v => ∫ X, Φv v X ∂(m v)) =
      fun v => (({v | v ∉ S}.mulIndicator (fun v => (m v (latV b v)).toReal) v : ℝ) : ℂ) := by
    funext v
    by_cases hv : v ∈ S
    · simp [Set.mulIndicator, hv]
    · simp only [Set.mulIndicator, Set.mem_setOf_eq, hv, not_false_eq_true, if_true, Φv, if_false]
      rw [integral_indicator (hL v)]
      simp [Measure.real]
  rw [e] at h1
  have h2 := hasProd_ofReal_of_complex (fun v => by
    by_cases hv : v ∈ S <;> simp [Set.mulIndicator, hv]) h1
  have e2 : (fun v => ENNReal.ofReal ({v | v ∉ S}.mulIndicator
      (fun v => (m v (latV b v)).toReal) v)) = {v | v ∉ S}.mulIndicator (fun v => m v (latV b v)) := by
    funext v
    by_cases hv : v ∈ S
    · simp [Set.mulIndicator, hv]
    · simp [Set.mulIndicator, hv, ENNReal.ofReal_toReal (hfin v)]
  rw [e2] at h2
  exact ⟨_, ENNReal.ofReal_ne_top, (hasProd_subtype_iff_mulIndicator (s := {v | v ∉ S})).2 h2⟩
end PI.VolStabW.RestrProdA
