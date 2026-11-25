-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.majorant_realFlow_transfer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:06:07.17557+00:00
-- url     : https://prove2.me/submissions/6d38867d-5135-4963-b878-cbe8a3d0e27c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowDomainCriterionHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ImaginaryMajorants
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMinimumLowerBoundHolds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_col_flow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlowMatrixMajorants_flowMat_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlowMatrixMajorants_flowMat_isom_real
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantConjugateTransfer_maj_transfer


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex MajorantConjugateTransfer FlowMatrixMajorants ImaginaryMajorants
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
namespace ReciprocityTheory.ChartRestriction.G.FD
theorem _root_.solution {r : ℕ} (X : Data E r) (ξ : Fin r → E) (t : X.Ψ → ℝ) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) (hz : X.flow ξ (fun τ => (t τ : ℂ)) x ∈ X.dom) (τ : X.Ψ)
    (hiso : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0) (w : Fin r → ℂ) :
    X.maj (X.flow ξ (fun τ => (t τ : ℂ)) x) τ w =
      X.maj x τ (Matrix.mulVec (X.flowMat ξ τ (-(t τ : ℂ))) w) := by

  have hcol : ∀ c, Matrix.mulVec (X.flowMat ξ τ (t τ : ℂ)) (X.colP x τ c) =
      X.colP (X.flow ξ (fun τ => (t τ : ℂ)) x) τ c := by
    intro c
    unfold Data.colP
    rw [Data.col_flow]
  refine maj_transfer (hx := hx) (hy := hz) (τ := τ) (g := X.flowMat ξ τ (t τ : ℂ))
    (g' := X.flowMat ξ τ (-(t τ : ℂ))) (hgg' := fun w => flowMat_inv (hiso := hiso) (a := _) (w := w))
    (hiso := fun u v => flowMat_isom_real (hiso := hiso) (t := t τ) (u := u) (v := v))
    (H1 := ?_) (H2 := ?_) (w := w)
  · intro c
    refine ⟨fun a => if a = c then 1 else 0, ?_⟩
    rw [hcol c]
    simp [ite_smul]
  · intro a
    refine ⟨fun c => if c = a then 1 else 0, ?_⟩
    simp [ite_smul, hcol]
end ReciprocityTheory.ChartRestriction.G.FD
