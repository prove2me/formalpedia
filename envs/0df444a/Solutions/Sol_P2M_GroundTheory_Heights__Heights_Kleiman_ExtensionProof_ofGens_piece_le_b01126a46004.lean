-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_ofGens_piece_le_b01126a46004
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:01:23.29354+00:00
-- url     : https://prove2.me/submissions/1227d657-b199-4bba-98aa-c5f7dcbb1ab8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PExtension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.ExtensionProof
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E]
  [IsScalarTower S Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman.ExtensionProof
theorem _root_.solution {ι : Type} [Fintype ι] (deg : ι → ℤ) (gen : ι → E) {V : ℤ → Submodule S E}
    (hV : ∀ k, gen k ∈ V (deg k))
    (hsmul : ∀ (f : Poly S N) (d : ℕ) (c : ℤ) (m : E), f.IsHomogeneous d → m ∈ V c →
      aeval x f • m ∈ V (c + d)) (c : ℤ) : (ofGens (S := S) (x := x) deg gen).piece c ≤ V c := by
  show Submodule.span S _ ≤ V c
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨k, f, e, hf, he, rfl⟩
  have h := hsmul f e _ _ hf (hV k)
  rwa [show deg k + e = c by omega] at h
end GroundTheory.Heights₂.Heights.Kleiman.ExtensionProof
