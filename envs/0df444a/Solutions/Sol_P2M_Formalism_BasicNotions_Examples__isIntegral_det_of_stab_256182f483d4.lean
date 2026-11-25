-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__isIntegral_det_of_stab_256182f483d4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:51:11.790679+00:00
-- url     : https://prove2.me/submissions/7eb02715-7096-4921-b81e-82520f2bfd2d

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_RelDetCore
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__detIdeal_smul_96d231c920a3
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__detIdeal_ne_bot_ac7c91201629
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__detIdeal_fg_86bcb276e1a7

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂
variable {E : Type*} [Field E] [NumberField E] {N : ℕ}
namespace Formalism.BasicNotions.Examples₂
theorem _root_.solution (γ : Matrix (Fin N) (Fin N) E) (L : Submodule (𝓞 E) (Fin N → E))
    (hfg : L.FG) (hsp : Submodule.span E (L : Set (Fin N → E)) = ⊤)
    (hγ : ∀ x ∈ L, γ.mulVec x ∈ L) : IsIntegral ℤ γ.det := by
  have h : IsIntegral (𝓞 E) γ.det :=
    isIntegral_of_smul_mem_submodule (detIdeal L) (detIdeal_ne_bot L hsp) (detIdeal_fg L hfg)
      γ.det (detIdeal_smul γ L hγ)
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  rw [← hy]
  exact NumberField.RingOfIntegers.isIntegral_coe y
end Formalism.BasicNotions.Examples₂
