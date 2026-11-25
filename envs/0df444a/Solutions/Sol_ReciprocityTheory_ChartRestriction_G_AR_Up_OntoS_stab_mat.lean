-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS.stab_mat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:33:53.438251+00:00
-- url     : https://prove2.me/submissions/15cd2aaf-1023-451d-a28c-581f0f42ab57

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalFrameDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DetSubUpper
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS
theorem _root_.solution {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) :
    (γ : Matrix (Fin r) (Fin r) E)ᵀ * X.Gm * (γ : Matrix (Fin r) (Fin r) E).map cc = X.Gm := by
  have hst := (X.Γ_stab γ hγ).1
  ext i j
  have h := hst (Pi.single i 1) (Pi.single j 1)
  have hR : herm X.Gm (Pi.single i (1 : E)) (Pi.single j 1) = X.Gm i j := by
    simp [herm, Pi.single_apply, cc, apply_ite]
  have hL : herm X.Gm ((γ : Matrix (Fin r) (Fin r) E) *ᵥ Pi.single i 1)
      ((γ : Matrix (Fin r) (Fin r) E) *ᵥ Pi.single j 1) =
      ((γ : Matrix (Fin r) (Fin r) E)ᵀ * X.Gm * (γ : Matrix (Fin r) (Fin r) E).map cc) i j := by
    simp only [herm, Matrix.mulVec_single_one, Matrix.col_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [← hL, h, hR]
end ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS
