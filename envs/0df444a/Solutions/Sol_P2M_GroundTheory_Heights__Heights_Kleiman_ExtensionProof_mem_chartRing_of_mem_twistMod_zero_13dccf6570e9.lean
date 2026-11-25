-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_mem_chartRing_of_mem_twistMod_zero_13dccf6570e9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:01:20.601801+00:00
-- url     : https://prove2.me/submissions/131bbba6-f4c4-4c01-b5df-e8441eff33d8

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
theorem _root_.solution {J : Chart x} {q : Ω} (hq : q ∈ twistMod S x 0 J) :
    q ∈ chartRing S x J := by
  refine Submodule.span_induction (p := fun q _ => q ∈ chartRing S x J) ?_ ?_ ?_ ?_ hq
  · rintro _ ⟨f, s, e, e', hs, hf, hse, he, rfl⟩
    have hee : e' = e := by omega
    subst hee
    exact ⟨f, s, e', hs, hf, hse, rfl⟩
  · exact Subalgebra.zero_mem _
  · intro a b _ _ ha hb; exact Subalgebra.add_mem _ ha hb
  · intro a q _ hq
    rw [chartRing_smul_def]
    exact Subalgebra.mul_mem _ a.2 hq
end GroundTheory.Heights₂.Heights.Kleiman.ExtensionProof
