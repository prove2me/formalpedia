-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_gen_mem_ofGens_4d3cdc5867bd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:01:19.312598+00:00
-- url     : https://prove2.me/submissions/576f87b4-3483-428d-beb6-84a269b11569

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
theorem _root_.solution {ι : Type} [Fintype ι] (deg : ι → ℤ) (gen : ι → E) (k : ι) :
    gen k ∈ (ofGens (S := S) (x := x) deg gen).piece (deg k) :=
  Submodule.subset_span ⟨k, 1, 0, isHomogeneous_one _ _, by simp, by simp⟩
end GroundTheory.Heights₂.Heights.Kleiman.ExtensionProof
