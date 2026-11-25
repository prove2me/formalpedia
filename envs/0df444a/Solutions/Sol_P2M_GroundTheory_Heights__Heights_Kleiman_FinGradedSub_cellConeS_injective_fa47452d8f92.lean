-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_cellConeS_injective_fa47452d8f92
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:42:49.924748+00:00
-- url     : https://prove2.me/submissions/4807cd0c-dedc-4b74-95c1-413afb496b32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TildeFiniteSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechTransport
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_cellCone_of_subset_d748224c1d3f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locCone_injective_5a9f3d67e677
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locMod_subsingleton_903ca61ffd0a


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
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
variable (M : FinGradedSub (S := S) (x := x) Ω) (c : ℤ)
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace FinGradedSub
theorem _root_.solution (I : StdCell N) : Function.Injective (M.cellConeS I) := by
  by_cases h : I.1 ⊆ support x
  · change Function.Injective (M.cellCone I)
    rw [M.cellCone_of_subset h]
    exact locCone_injective M I.1 h
  · obtain ⟨i, hiI, hi⟩ : ∃ i ∈ I.1, x i = 0 := by
      by_contra hne
      push Not at hne
      exact h fun i hi => (mem_support x).mpr (hne i hi)
    have := locMod_subsingleton M hiI hi
    exact Function.injective_of_subsingleton _
end FinGradedSub
end GroundTheory.Heights₂.Heights.Kleiman
