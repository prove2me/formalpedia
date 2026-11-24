-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LinesProjLattice_proof_53be31fed3e1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:28.469856+00:00
-- url     : https://prove2.me/submissions/df4cf150-7147-44df-94e1-62a80f25bbdd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesProjLattice
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesProjLattice_coordProj_surjective_e0159a2963b4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesProjLattice_coordProj_basis_inr_8d05f19318c1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField
open scoped nonZeroDivisors
open KLinesProjLattice
namespace GroundTheory.Heights₂.Heights
namespace LinesProjLattice
theorem _root_.solution (h1 : LinesIdealLatticeFG.Statement) : LinesProjLattice.Statement := by
  intro K _ _ n m k a B τ ha hB hτ
  obtain ⟨hfg, hspan⟩ := h1 K n a ha
  refine ⟨?_, ?_, ?_⟩
  · exact (hfg.map ((coordProj B).restrictScalars (𝓞 K))).restrictScalars
  · rw [Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, hspan,
      Submodule.map_top, LinearMap.range_eq_top]
    exact coordProj_surjective B
  · intro v hv
    have hv' : ∀ j, v j ∈ (a (τ j) : Submodule (𝓞 K) K) := fun j =>
      (Submodule.mem_pi (I := Set.univ)).1 hv j (Set.mem_univ j)
    refine ⟨∑ j, v j • (Pi.single (τ j) 1 : Fin n → K), ?_, ?_⟩
    · refine (Submodule.mem_pi (I := Set.univ)).2 fun x _ => ?_
      rw [Finset.sum_apply]
      refine Submodule.sum_mem _ fun j _ => ?_
      by_cases h : τ j = x
      · subst h; simpa using hv' j
      · simp [Pi.single_eq_of_ne' h]
    · simp only [LinearMap.restrictScalars_apply, map_sum, map_smul, ← hB, coordProj_basis_inr]
      ext i
      simp [Pi.single_apply]
end LinesProjLattice
end GroundTheory.Heights₂.Heights
