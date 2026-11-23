-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sdd_quad_eig
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:51.476967+00:00
-- url     : https://prove2.me/submissions/8f692be2-b515-449b-a4ba-83e7be87158e

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegDA
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sdd_star_self_eig

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField
open scoped ComplexOrder MatrixOrder
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {n : ℕ} {D : Matrix (Fin n) (Fin n) ℂ} (hD : D.IsHermitian) (i : Fin n) :
    star (⇑(hD.eigenvectorBasis i)) ⬝ᵥ (D *ᵥ ⇑(hD.eigenvectorBasis i)) = (hD.eigenvalues i : ℂ) := by
  rw [hD.mulVec_eigenvectorBasis, dotProduct_smul, sdd_star_self_eig hD i]
  simp
end ReciprocityTheory.MultiplicativeHeights
