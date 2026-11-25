-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.DataX.discr_mul_hermitian_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:02:03.866344+00:00
-- url     : https://prove2.me/submissions/ac2cc870-23d3-4964-ad1d-9453f71404a4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MmatMulVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DiscrMulHermitianIntegral
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_herm_smul_left__eda3d1954a4c
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_smul_mem_of_int
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_d4l2_dual_int__d8f00091482c


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Module Matrix
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.DataX
variable {r : ℕ} (X : DataX E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.DataX
theorem _root_.solution {v w : Fin r → E} (hv : v ∈ X.Λ) (hw : w ∈ X.Λ) :
    IsIntegral ℤ (((NumberField.discr E).natAbs : E) * (X.ξ0 * herm X.Gm v w)) := by
  have h := d4l2_dual_int' (-(X.ξ0 * herm X.Gm v w)) (fun γ => by
    obtain ⟨k, hk⟩ := X.EF_int ((γ : E) • v) (smul_mem_of_int X.Λ (RingOfIntegers.isIntegral_coe γ) hv) w hw
    refine ⟨k, ?_⟩
    rw [← hk]
    unfold EFf
    rw [herm_smul_left']
    congr 1; ring)
  have : ((NumberField.discr E).natAbs : E) * (X.ξ0 * herm X.Gm v w) =
      -(((NumberField.discr E).natAbs : E) * -(X.ξ0 * herm X.Gm v w)) := by ring
  rw [this]; exact h.neg
end ReciprocityTheory.ChartRestriction.G.FD.DataX
