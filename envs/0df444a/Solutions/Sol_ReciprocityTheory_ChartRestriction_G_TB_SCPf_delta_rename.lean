-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.SCPf.delta_rename
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:40:10.574792+00:00
-- url     : https://prove2.me/submissions/b654f694-2a69-4097-9420-594b285cf588

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LiftXHasSubst
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondOrderIterateEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_sum_side
import Theorems.Thm_P2M_RH_PI_WickFormula_Gen_gdelta_apply_432825626bc43230
import Theorems.Thm_PI_WickFormula_delta_eq_gdelta
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_nablaL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.TB.SCPf.nablaL_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.SCPf
variable {k : Type} [CommRing k] {ι : Type} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.TB.SCPf
theorem _root_.solution (s : ι → Bool) (κ : ι → ι → k) (hκ : ∀ l l', κ l l' ≠ 0 → s l = true ∧ s l' = false)
    (P : MvPolynomial ι k) :
    PI.WickFormula.delta (kapE s κ) (rename (sideE s) P) = rename (sideE s) (secondOrder k κ P) := by
  have hd : ∀ (x : Fin (Fintype.card {l // s l = true}) ⊕ Fin (Fintype.card {l // ¬ s l = true}))
      (Q : MvPolynomial ι k),
      pderiv x (rename (sideE s) Q) = rename (sideE s) (pderiv ((sideE s).symm x) Q) := by
    intro x Q
    conv_lhs => rw [← (sideE s).apply_symm_apply x]
    exact pderiv_rename (sideE s).injective _ _
  rw [PI.WickFormula.delta_eq_gdelta, PI.WickFormula.Gen.gdelta_apply,
    show secondOrder k κ P = ∑ l, ∑ l', C (κ l l') * pderiv l (pderiv l' P) from rfl]
  simp only [map_sum, map_mul, rename_C]
  rw [sum_side s _ ?_]
  · refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [smul_eq_C_mul, hd, hd]
  · intro l l' hne
    apply hκ
    intro h0
    apply hne
    rw [h0, map_zero, zero_mul]
end ReciprocityTheory.ChartRestriction.G.TB.SCPf
