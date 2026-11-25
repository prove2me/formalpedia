-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices.eq_zero_of_Pos_Neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:36:15.044936+00:00
-- url     : https://prove2.me/submissions/cd0704a4-1e73-423f-9bf4-b7b7fea50b39

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ExistsUnitaryBasisSameFlag
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnitaryComplementMoveOfIsotropic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PositiveSpanMatrices
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveSpanMatrices_fin_cases_split
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveSpanMatrices_expand
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalPerpBasis_expand


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices
theorem _root_.solution {x : Frame X.Ψ r} (hx : X.IsOrtho x) (τ : X.Ψ) (hdet : (mat x τ).det ≠ 0)
    (y : Fin r → ℂ) (hP : Pos X x τ y = 0) (hN : Neg X x τ y = 0) : y = 0 := by
  unfold Pos at hP
  unfold Neg at hN
  have hP' : ∀ b : Fin X.p0, hermC τ.1 X.Gm y (col (mat x τ) (Fin.castLE X.p0_le b)) = 0 := by
    intro b
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
      sq_nonneg ‖hermC τ.1 X.Gm y (col (mat x τ) (Fin.castLE X.p0_le i))‖)).mp hP b (Finset.mem_univ _)
    simpa using h1
  have hN' : ∀ a : Fin (r - X.p0), hermC τ.1 X.Gm y (col (mat x τ) (kap X.p0_le a)) = 0 := by
    intro a
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
      sq_nonneg ‖hermC τ.1 X.Gm y (col (mat x τ) (kap X.p0_le i))‖)).mp hN a (Finset.mem_univ _)
    simpa using h1
  have hall : ∀ c, hermC τ.1 X.Gm y (col (mat x τ) c) = 0 := by
    intro c
    rcases fin_cases_split X.p0_le c with ⟨b, rfl⟩ | ⟨a, rfl⟩
    · exact hP' b
    · exact hN' a
  rw [expand X hx τ hdet y]
  simp [hall]
end ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices
