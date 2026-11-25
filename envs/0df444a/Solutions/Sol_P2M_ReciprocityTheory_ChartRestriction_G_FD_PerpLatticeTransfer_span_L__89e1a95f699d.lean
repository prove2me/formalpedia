-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_FD_PerpLatticeTransfer_span_L__89e1a95f699d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:56:06.277388+00:00
-- url     : https://prove2.me/submissions/bb3415ee-0540-4b30-a4fb-ad4960a130c3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PerpBasisExistence
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PerpLatticeTransfer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PerpLatticeTransfer
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PerpBasisExistence
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : DataX E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.PerpLatticeTransfer
theorem _root_.solution : Submodule.span E (X.L' : Set (Fin r → E)) = ⊤ := by
  rw [eq_top_iff, ← X.Λ_span, Submodule.span_le]
  intro x hx
  have h1 : (X.NA : E) • x ∈ Submodule.span E (X.L' : Set (Fin r → E)) :=
    Submodule.subset_span (X.NA_sub x hx)
  have hNA : (X.NA : E) ≠ 0 := Nat.cast_ne_zero.mpr X.NA_pos.ne'
  have h2 := Submodule.smul_mem _ ((X.NA : E)⁻¹) h1
  rwa [smul_smul, inv_mul_cancel₀ hNA, one_smul] at h2
end ReciprocityTheory.ChartRestriction.G.FD.PerpLatticeTransfer
