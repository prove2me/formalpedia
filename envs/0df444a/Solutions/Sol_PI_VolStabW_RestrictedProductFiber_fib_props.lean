-- Prove2me | solution 1 for PI.VolStabW.RestrictedProductFiber.fib_props
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:14:48.757806+00:00
-- url     : https://prove2.me/submissions/fef89fbc-c650-4bff-927b-fc9e5fcaad69

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProdSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TensAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FiniteOnCompacts
import Theorems.Thm_PI_VolStabW_RestrictedProductFiber_finite_on_compacts
import Theorems.Thm_PI_VolStabW_isUnit_det_hermOf
import Theorems.Thm_PI_VolStabW_linIndep_of_isUnit_det


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Topology
open scoped TensorProduct
open PI.VolStabW.RestrictedProductFiber
namespace PI.VolStabW.RestrictedProductFiber
theorem _root_.solution {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (a : ℕ) (R : Type) [CommRing R]
    [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] (hTF : TensFacts F E σ M J a R)
    (T : Matrix (Fin a) (Fin a) E) (hT : ∀ i j, σ (T j i) = T i j) (hdet : T.det ≠ 0)
    (μ : Measure (Fin a → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ a))
    (fib : HermR R σ a → Measure (Fin a → Fin M → R ⊗[F] E))
    (h : IsFibreFamily μ (gramR R σ J) Subtype.val
      {X | LinearIndependent (R ⊗[F] E) X} ν Set.univ fib) :
    SigmaFinite (fib (hermOf R σ T hT)) ∧
    ∀ Φ : (Fin a → Fin M → R ⊗[F] E) → ℂ, Continuous Φ → HasCompactSupport Φ →
      Integrable Φ (fib (hermOf R σ T hT)) := by
  obtain ⟨h1, h2, h3, _h4, h5, _h6, h7⟩ := hTF
  have : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have : T2Space (Matrix (Fin a) (Fin a) (R ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin a → Fin a → R ⊗[F] E))
  have hC : IsClosed (gramR R σ J ⁻¹' {((hermOf R σ T hT : HermR R σ a) :
      Matrix (Fin a) (Fin a) (R ⊗[F] E))}) := isClosed_singleton.preimage h5
  have hCU : gramR R σ J ⁻¹' {((hermOf R σ T hT : HermR R σ a) :
      Matrix (Fin a) (Fin a) (R ⊗[F] E))} ⊆ {X | LinearIndependent (R ⊗[F] E) X} := by
    intro X hX
    have hX' : gramR R σ J X = ((hermOf R σ T hT : HermR R σ a) :
        Matrix (Fin a) (Fin a) (R ⊗[F] E)) := hX
    have hu := isUnit_det_hermOf R σ T hT hdet
    rw [← hX'] at hu
    exact linIndep_of_isUnit_det R σ J X hu
  have hfin := finite_on_compacts μ (gramR R σ J) Subtype.val _ h7 ν Set.univ fib h
    (hermOf R σ T hT) (Set.mem_univ _) hC hCU
  have : SigmaCompactSpace (Fin a → Fin M → R ⊗[F] E) :=
    sigmaCompactSpace_of_locallyCompact_secondCountable
  exact ⟨inferInstance, fun Φ hc hs => hc.integrable_of_hasCompactSupport hs⟩
end PI.VolStabW.RestrictedProductFiber
