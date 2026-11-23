-- Prove2me | solution 1 for PI.FT.cont_HA_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:23.318778+00:00
-- url     : https://prove2.me/submissions/a9c00a42-d2fb-4267-9577-e7eabbe50a33

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_MemHFinInIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_InstIsModTopTens

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FT
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E}
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
namespace PI.FT
theorem _root_.solution {T : Type*} [TopologicalSpace T] {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (f : T → HA R σ J) :
    Continuous f ↔ Continuous (fun t => mt (f t)) ∧ Continuous (fun t => mtI (f t)) := by
  constructor
  · intro hf
    have h1 : Continuous (fun t => ((toHR (f t) : HR R σ J) : GL (Fin n) (R ⊗[F] E))) :=
      continuous_subtype_val.comp hf
    exact ⟨Units.continuous_val.comp h1, Units.continuous_coe_inv.comp h1⟩
  · rintro ⟨h1, h2⟩
    have h3 : Continuous (fun t => ((toHR (f t) : HR R σ J) : GL (Fin n) (R ⊗[F] E))) :=
      Units.continuous_iff.2 ⟨h1, h2⟩
    exact h3.subtype_mk (fun t => (toHR (f t)).2)
end PI.FT
