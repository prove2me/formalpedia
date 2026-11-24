-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.MI.uf_lu_eS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:13:51.886025+00:00
-- url     : https://prove2.me/submissions/949fe9a9-0997-4c5f-b3a9-c21df93644a8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfJ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfK

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open NumberField Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData Finset
open scoped ComplexConjugate
noncomputable section
attribute [local instance] Classical.propDecidable
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI
theorem _root_.solution (x : LoI X.Ψ r → ℂ) (y : UpI X.Ψ r → ℂ) :
    uf X (lu ((eS X.Ψ r).symm (x, y))) = rmul (NF X x) (UF X y) := by
  have h1 : ∀ τ : X.Ψ, 1 + sl ((eS X.Ψ r).symm (x, y)) τ = Nmat x τ := by
    intro τ
    ext a b
    by_cases h : b < a
    · have hab : a ≠ b := ne_of_gt h
      first
      | simp [sl, Nmat, Matrix.one_apply, eS, h, hab, MeasurableEquiv.piEquivPiSubtypeProd_symm_apply]
      | simp [sl, Nmat, Matrix.one_apply, eS, h, hab, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd_symm_apply]
      | simp [sl, Nmat, Matrix.one_apply, eS, h, hab, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, MeasurableEquiv.symm]
    · first
      | simp [sl, Nmat, Matrix.one_apply, eS, h, MeasurableEquiv.piEquivPiSubtypeProd_symm_apply]
      | simp [sl, Nmat, Matrix.one_apply, eS, h, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd_symm_apply]
      | simp [sl, Nmat, Matrix.one_apply, eS, h, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, MeasurableEquiv.symm]
  have h2 : ∀ τ : X.Ψ, up ((eS X.Ψ r).symm (x, y)) τ = Umat y τ := by
    intro τ
    ext a b
    by_cases h : b < a
    · first
      | simp [up, Umat, eS, h, MeasurableEquiv.piEquivPiSubtypeProd_symm_apply]
      | simp [up, Umat, eS, h, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd_symm_apply]
      | simp [up, Umat, eS, h, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, MeasurableEquiv.symm]
    · first
      | simp [up, Umat, eS, h, MeasurableEquiv.piEquivPiSubtypeProd_symm_apply]
      | simp [up, Umat, eS, h, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd_symm_apply]
      | simp [up, Umat, eS, h, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, MeasurableEquiv.symm]
  funext τ a b
  show ((1 + sl ((eS X.Ψ r).symm (x, y)) τ) * up ((eS X.Ψ r).symm (x, y)) τ) a b =
    (Nmat x τ * Umat y τ) a b
  rw [h1, h2]
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
