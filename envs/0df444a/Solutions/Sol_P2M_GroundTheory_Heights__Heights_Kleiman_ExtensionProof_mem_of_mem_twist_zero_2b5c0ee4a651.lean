-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_mem_of_mem_twist_zero_2b5c0ee4a651
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:37:44.412926+00:00
-- url     : https://prove2.me/submissions/ec222784-4f4c-4b3d-993a-cf35e41b8b1f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PExtension
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_mem_chartRing_of_mem_twistMod_zero_13dccf6570e9

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
omit [Module S E] [IsScalarTower S Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman.ExtensionProof
theorem _root_.solution (F : SubSystem S x E) {J : Chart x} {m : E}
    (hm : m ∈ (F.twist (twistSys S x 0)).sub J) : m ∈ F.sub J := by
  refine Submodule.span_induction (p := fun m _ => m ∈ F.sub J) ?_ ?_ ?_ ?_ hm
  · rintro _ ⟨q, hq, y, hy, rfl⟩
    have h := Submodule.smul_mem (F.sub J) (⟨q, mem_chartRing_of_mem_twistMod_zero hq⟩ :
      chartRing S x J) hy
    rwa [Subalgebra.smul_def] at h
  · exact Submodule.zero_mem _
  · intro a b _ _ ha hb; exact Submodule.add_mem _ ha hb
  · intro a m _ hm; exact Submodule.smul_mem _ a hm
end GroundTheory.Heights₂.Heights.Kleiman.ExtensionProof
