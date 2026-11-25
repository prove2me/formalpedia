-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC.isClosed_psd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:30:35.752146+00:00
-- url     : https://prove2.me/submissions/9c23c1e3-4196-45cb-90f3-94a01dd7d9ad

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExhB_cont_coord
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExhB_cont_entry
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExhB_herm_one_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExhB_zPart_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC
open Matrix Topology Filter
open scoped ComplexOrder Matrix
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
variable {f p q N' : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC
theorem _root_.solution :
    IsClosed {v : V (nD f p q + N') | ∀ k, (1 - Zof (zPart v) k * (Zof (zPart v) k)ᴴ).PosSemidef} := by
  have e : {v : V (nD f p q + N') | ∀ k, (1 - Zof (zPart v) k * (Zof (zPart v) k)ᴴ).PosSemidef} =
      ⋂ k, ⋂ x : Fin p → ℂ, {v | 0 ≤ star x ⬝ᵥ ((1 - Zof (zPart v) k * (Zof (zPart v) k)ᴴ) *ᵥ x)} := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact forall_congr' fun k => ⟨fun h => h.dotProduct_mulVec_nonneg,
      fun h => PosSemidef.of_dotProduct_mulVec_nonneg (herm_one_sub _) h⟩
  rw [e]
  refine isClosed_iInter fun k => isClosed_iInter fun x => isClosed_le continuous_const ?_
  have hc := cont_entry (fun v : V (nD f p q + N') => zPart v)
    (fun i => by simp only [zPart_apply]; exact cont_coord _) k
  simp only [dotProduct, mulVec]
  exact continuous_finsetSum _ fun i _ => continuous_const.mul
    (continuous_finsetSum _ fun j _ => (hc i j).mul continuous_const)
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC
