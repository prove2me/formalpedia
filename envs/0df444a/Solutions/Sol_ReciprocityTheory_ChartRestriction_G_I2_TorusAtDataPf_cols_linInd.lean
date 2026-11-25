-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf.cols_linInd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:09:36.552587+00:00
-- url     : https://prove2.me/submissions/9de695de-0c6f-46bf-b5b9-69fcc583f0fd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtDataPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtDataPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TorusAtDataPf_e_span


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf
theorem _root_.solution (X : Data E r) (x : Frame X.Ψ r) (A : TorusAt X x) (τ : X.Ψ) :
    LinearIndependent ℂ (X.colP x τ) := by
  have h := A.e_flag τ r le_rfl
  have h1 : (fun a : Fin r => A.e τ (Fin.castLE le_rfl a)) = A.e τ := funext fun a => rfl
  have h2 : (fun a : Fin r => col (mat x τ) (Fin.castLE le_rfl a)) = fun a => col (mat x τ) a :=
    funext fun a => rfl
  rw [h1, h2, e_span X τ (A.e τ) (A.e_orth τ)] at h
  have hcols : LinearIndependent ℂ (fun a : Fin r => col (mat x τ) a) :=
    linearIndependent_of_top_le_span_of_card_eq_finrank h.le (by simp)
  exact hcols.comp _ (Fin.castLE_injective X.p0_le)
end ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf
