-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KRest_prod_Ioi_eq_prod_ite_27d978e0f783
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:01:23.146414+00:00
-- url     : https://prove2.me/submissions/5e79679a-5fcf-4f6e-8fba-807338ffb6aa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_RestCutBasic

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
open GroundTheory.Heights₂.Heights.KRest
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.KRest
theorem _root_.solution {R : Type*} [CommMonoid R] {m : ℕ} (g : Fin m → Fin m → R) :
    ∏ i : Fin m, ∏ j ∈ Finset.Ioi i, g i j =
      ∏ x : Fin m × Fin m, if x.1 < x.2 then g x.1 x.2 else 1 := by
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_filter]
  congr 1
  ext j
  simp
end GroundTheory.Heights₂.Heights.KRest
