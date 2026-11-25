-- Prove2me | solution 1 for PI.VolStabW.continuous_gramB_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:59:27.551294+00:00
-- url     : https://prove2.me/submissions/a91e8806-2b33-45fa-9baa-3a6b68425472

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensInfTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensInfCo
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
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Topology
open scoped TensorProduct
open PI.AdicCompletionValuation
variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [T2Space R]
namespace PI.VolStabW
theorem _root_.solution (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (a b : Fin n) : Continuous (fun p : (Fin n → Fin M → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) =>
      gramB R σ J p.1 p.2 a b) := by
  show Continuous (fun p : (Fin n → Fin M → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) =>
    hR R σ J (p.1 a) (p.2 b) + hR R σ J (p.2 a) (p.1 b))
  have hc := continuous_hR R σ J
  have e1 : Continuous (fun p : (Fin n → Fin M → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) =>
      ((p.1 a, p.2 b) : (Fin M → R ⊗[F] E) × (Fin M → R ⊗[F] E))) := by fun_prop
  have e2 : Continuous (fun p : (Fin n → Fin M → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) =>
      ((p.2 a, p.1 b) : (Fin M → R ⊗[F] E) × (Fin M → R ⊗[F] E))) := by fun_prop
  have h1 := Continuous.comp (g := fun q : (Fin M → R ⊗[F] E) × (Fin M → R ⊗[F] E) =>
      hR R σ J q.1 q.2) hc e1
  have h2 := Continuous.comp (g := fun q : (Fin M → R ⊗[F] E) × (Fin M → R ⊗[F] E) =>
      hR R σ J q.1 q.2) hc e2
  exact h1.add h2
end PI.VolStabW
