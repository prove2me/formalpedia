-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_mem_twistA_iff_917ff1481aae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:05:58.167828+00:00
-- url     : https://prove2.me/submissions/348f3380-d197-444d-be24-7a64c5350f20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CoordIdealIsMultiProjPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_EqZeroOrIsHomogeneousOfMemPolyPiece

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
open MvPolynomial
noncomputable section
variable {S : Type} [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω] {x : Fin (N + 1) → Ω}
variable {E : Type} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
theorem _root_.solution (F : Fin (N + 1) → Submodule S E) (c : ℤ) (i : Fin (N + 1)) (z : E) :
    z ∈ IndefiniteRowSideFullHecke.Kleiman.twistA S x F c i ↔ ∃ y ∈ F i, z = x i ^ c • y := by
  constructor
  · intro hz
    induction hz using Submodule.span_induction with
    | mem z hz => obtain ⟨y, hy, rfl⟩ := hz; exact ⟨y, hy, rfl⟩
    | zero => exact ⟨0, zero_mem _, (smul_zero _).symm⟩
    | add a b _ _ ha hb =>
      obtain ⟨y, hy, rfl⟩ := ha
      obtain ⟨y', hy', rfl⟩ := hb
      exact ⟨y + y', add_mem hy hy', (smul_add _ _ _).symm⟩
    | smul s a _ ha =>
      obtain ⟨y, hy, rfl⟩ := ha
      exact ⟨s • y, Submodule.smul_mem _ s hy, smul_comm s (x i ^ c) y⟩
  · rintro ⟨y, hy, rfl⟩
    exact Submodule.subset_span ⟨y, hy, rfl⟩
end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
