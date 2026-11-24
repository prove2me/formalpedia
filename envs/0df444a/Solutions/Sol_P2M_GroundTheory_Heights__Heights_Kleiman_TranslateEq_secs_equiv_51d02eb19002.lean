-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_secs_equiv_51d02eb19002
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:08:45.015096+00:00
-- url     : https://prove2.me/submissions/b1e8bb4d-6d9e-4eed-a49f-28b69793f3e3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CoordIdealIsMultiProjPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_EqZeroOrIsHomogeneousOfMemPolyPiece
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_chartModule_of_ne_zero_902c51d3fd20

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
namespace secs
theorem _root_.solution (F : Kleiman.SubSystem S x E) : IndefiniteRowSideFullHecke.Kleiman.secs S x (toIndefiniteRowSideFullHecke F) = F.secs := by
  apply le_antisymm
  · intro y hy
    simp only [IndefiniteRowSideFullHecke.Kleiman.secs, Submodule.mem_iInf] at hy
    rw [Kleiman.SubSystem.secs, Submodule.mem_iInf]
    intro I
    obtain ⟨i, hi⟩ := I.2.1
    have hxi : x i ≠ 0 := (Kleiman.mem_support x).mp (I.2.2 hi)
    have h1 := hy i hxi
    rw [chartModule_of_ne_zero F hxi] at h1
    exact F.mono _ I (Finset.singleton_subset_iff.mpr hi) y h1
  · intro y hy
    rw [Kleiman.SubSystem.secs, Submodule.mem_iInf] at hy
    simp only [IndefiniteRowSideFullHecke.Kleiman.secs, Submodule.mem_iInf]
    intro i hxi
    rw [chartModule_of_ne_zero F hxi]
    exact hy _
end secs
end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
