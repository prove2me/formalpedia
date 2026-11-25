-- Prove2me | solution 1 for PI.VolStabW.SdTestInfW.continuous_BR_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:57:29.699887+00:00
-- url     : https://prove2.me/submissions/a5f9823d-9367-4754-88c1-9e5926f2a602

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensInfAll
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_RealCharacter
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdTestInf
import Theorems.Thm_PI_VolStabW_SdUniqW_continuous_trace_tens
import Theorems.Thm_PI_VolStabW_continuous_hR


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
open PI.VolStabW.SdTestInfW
open MeasureTheory Complex Filter Topology
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation PI.VolFromSW SdUniqW
variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [T2Space R]
namespace PI.VolStabW.SdTestInfW
theorem _root_.solution (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (Y : Fin n → Fin M → R ⊗[F] E) : Continuous fun X => BR R σ J X Y := by
  have h : ∀ a : Fin n, Continuous fun X : Fin n → Fin M → R ⊗[F] E =>
      Algebra.trace R (R ⊗[F] E) (hR R σ J (X a) (Y a)) := by
    intro a
    have h0 : Continuous fun X : Fin n → Fin M → R ⊗[F] E => (X a, Y a) :=
      (continuous_apply a).prodMk (continuous_const (y := Y a))
    have hc := continuous_hR R σ J
    have h1 := Continuous.comp (g := fun q : (Fin M → R ⊗[F] E) × (Fin M → R ⊗[F] E) =>
      hR R σ J q.1 q.2) hc h0
    have h2 : Continuous fun z : R ⊗[F] E => Algebra.trace R (R ⊗[F] E) z := continuous_trace_tens R
    exact h2.comp h1
  exact continuous_finsetSum Finset.univ fun a _ => h a
end PI.VolStabW.SdTestInfW
