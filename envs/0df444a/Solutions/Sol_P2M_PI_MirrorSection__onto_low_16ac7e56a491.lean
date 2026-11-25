-- Prove2me | solution 1 for P2M_PI_MirrorSection__onto_low_16ac7e56a491
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:56:34.198215+00:00
-- url     : https://prove2.me/submissions/2b3f9805-6a3d-47ab-a90b-ac1d156cd78d

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirrorDecomposition_HpkRowEsI

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.MirrorSection₂
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
variable {k r : ℕ}
namespace PI.MirrorSection₂
theorem _root_.solution {g : B.Mat k r} (hg : g⁻¹ * g = 1) {a : ℕ} (hmaps : ∀ y ∈ lowS k r a, g *ᵥ y ∈ lowS k r a) :
    ∀ y ∈ lowS k r a, ∃ x ∈ lowS k r a, g *ᵥ x = y := by
  let f : lowS k r a →ₗ[ℂ] lowS k r a := (Matrix.mulVecLin g).restrict hmaps
  have hinj : Function.Injective f := by
    intro x x' hxx
    have h1 : g *ᵥ (x : Fin (2 * r + k + 1) → ℂ) = g *ᵥ x' := congrArg Subtype.val hxx
    have h2 := congrArg (fun v => g⁻¹ *ᵥ v) h1
    simp only [Matrix.mulVec_mulVec, hg, Matrix.one_mulVec] at h2
    exact Subtype.ext h2
  have hsurj := LinearMap.injective_iff_surjective.mp hinj
  intro y hy
  obtain ⟨x, hx⟩ := hsurj ⟨y, hy⟩
  exact ⟨x.1, x.2, congrArg Subtype.val hx⟩
end PI.MirrorSection₂
