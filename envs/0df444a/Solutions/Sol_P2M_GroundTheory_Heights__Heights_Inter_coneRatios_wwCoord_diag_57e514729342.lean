-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_coneRatios_wwCoord_diag_57e514729342
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:59:26.612867+00:00
-- url     : https://prove2.me/submissions/515cf393-9c13-4fe9-bff4-6bafb254055e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StDiagRatioBasis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagRatioBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution {Ω : Type} [Field Ω] {ι ν κ : Type} {E : Type} [AddCommGroup E] [Module Ω E]
    {Φ : Type} [Field Φ] [Algebra Ω Φ] (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E)
    (φ : κ → E →ₗ[Ω] Ω) (a : Φ) (c : ∀ k, T.yyIdx ι ν κ k) :
    coneRatios (T.wwCoord x δ e φ a a) (diagChart c) = coneRatios (T.yyCoord x δ e φ a) c := by
  ext r
  constructor
  · rintro ⟨⟨k, i⟩, rfl⟩
    cases k
    · exact ⟨⟨.base, (i : ι)⟩, rfl⟩
    · exact ⟨⟨.det, (i : ν)⟩, rfl⟩
    · exact ⟨⟨.line, (i : κ)⟩, rfl⟩
    · exact ⟨⟨.line, (i : κ)⟩, rfl⟩
  · rintro ⟨⟨k, i⟩, rfl⟩
    cases k
    · exact ⟨⟨.base, (i : ι)⟩, rfl⟩
    · exact ⟨⟨.det, (i : ν)⟩, rfl⟩
    · exact ⟨⟨.line0, (i : κ)⟩, rfl⟩
end GroundTheory.Heights₂.Heights.Inter
