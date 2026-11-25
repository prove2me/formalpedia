-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_blockSubst_eq_zero_584f1638d3d0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:29:08.025934+00:00
-- url     : https://prove2.me/submissions/696842b7-511d-4bc8-b1f1-3cf9d6376e29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Examples
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_whole_mkF_injective_f0f5f10d0d70
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_blockAddData_extMap_8a459cfaa920

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
open MvPolynomial NumberField
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (n : ι → ℕ) (k₀ : ι)
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {f : MvPolynomial (Coord (blockAddData n k₀).extSizes) ℤ}
    (hf : f ∈ (blockAddData n k₀).extIdeal) : blockSubst n k₀ f = 0 := by
  have h : (MvPolynomial.map (ArithVariety.whole n).mkF) (blockSubst n k₀ f) = 0 := by
    rw [← RingHom.comp_apply, ← blockAddData_extMap]
    exact RingHom.mem_ker.mp hf
  exact map_injective _ (ArithVariety.whole_mkF_injective n) (h.trans (map_zero _).symm)
end GroundTheory.Heights₂.Heights
