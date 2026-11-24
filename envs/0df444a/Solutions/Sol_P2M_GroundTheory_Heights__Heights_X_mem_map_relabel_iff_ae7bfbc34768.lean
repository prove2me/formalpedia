-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_X_mem_map_relabel_iff_ae7bfbc34768
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:58:50.512609+00:00
-- url     : https://prove2.me/submissions/8b59dbb1-f531-446f-86ef-4b45d519e1d9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsNefRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_PNefOnFibresRelabel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_relabelRingEquiv_X_7a46ccc5629a

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
theorem _root_.solution (V : Ideal (MRing ι)) (k : K) (i : ι k) :
    (X ⟨ε k, cast (h k) i⟩ : MRing ι') ∈ V.map (relabelRingEquiv ε h) ↔ (X ⟨k, i⟩ : MRing ι) ∈ V := by
  rw [← relabelRingEquiv_X, mem_map_ringEquiv_iff]
end GroundTheory.Heights₂.Heights
