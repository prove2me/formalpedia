-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isRelevant_map_relabel_iff_831acc433198
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:32.596831+00:00
-- url     : https://prove2.me/submissions/673ef627-cd3d-4d48-9a10-0b72f07a99a7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsNefRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_PNefOnFibresRelabel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_X_mem_map_relabel_iff_ae7bfbc34768

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
set_option linter.unusedSectionVars false
variable {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
  [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] (ε : K ≃ K') (h : ∀ k, ι k = ι' (ε k))
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (V : Ideal (MRing ι)) :
    IsRelevant (V.map (relabelRingEquiv ε h)) ↔ IsRelevant V := by
  constructor
  · intro hV k
    obtain ⟨i, hi⟩ := hV (ε k)
    refine ⟨cast (h k).symm i, fun hmem => hi ?_⟩
    have := (X_mem_map_relabel_iff ε h V k _).2 hmem
    simpa using this
  · intro hV k'
    obtain ⟨k, rfl⟩ := ε.surjective k'
    obtain ⟨i, hi⟩ := hV k
    exact ⟨cast (h k) i, fun hmem => hi ((X_mem_map_relabel_iff ε h V k i).1 hmem)⟩
end GroundTheory.Heights₂.Heights
