-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_relabel_X_choose_90b307a92fed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:38:52.516341+00:00
-- url     : https://prove2.me/submissions/d73a040a-6444-4eb6-897e-f396a7edf246

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsNefRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_PNefOnFibresRelabel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_choose_eq_cast_be923035bc3e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_relabelRingEquiv_X_7a46ccc5629a
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
theorem _root_.solution (V : Ideal (MRing ι)) (hV : IsRelevant V)
    (hV' : IsRelevant (V.map (relabelRingEquiv ε h))) (k : K) :
    relabelRingEquiv ε h (X ⟨k, (hV k).choose⟩) = X ⟨ε k, (hV' (ε k)).choose⟩ := by
  have hc : (hV' (ε k)).choose = cast (h k) (hV k).choose :=
    choose_eq_cast (h k) (hV k) (hV' (ε k)) fun i => not_congr (X_mem_map_relabel_iff ε h V k i)
  rw [relabelRingEquiv_X, hc]
end GroundTheory.Heights₂.Heights
