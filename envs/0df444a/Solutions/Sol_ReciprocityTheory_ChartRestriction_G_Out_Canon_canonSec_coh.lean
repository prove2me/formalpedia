-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.Canon.canonSec_coh
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:27:28.540862+00:00
-- url     : https://prove2.me/submissions/11dfd9e0-c419-4df1-8505-1a3170e54aa2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_CanonGenIsGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_Canon_gW_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_Canon_gW_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out.Canon
variable {X Y : Scheme.{0}} (L : LB X)
variable {L}
variable {K K' : Type} [Fintype K] [Fintype K']
variable (L)
variable {L}
variable (L)
namespace ReciprocityTheory.ChartRestriction.G.Out.Canon
theorem _root_.solution (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X))
    (ε' : K' → ℤ) (hs : LB.SameSum φ ε φ' ε') (hsub : ∀ k, ∃ k', φ' k' = φ k)
    (sc : LB.Sec (LB.LinComb L φ ε)) (j : (LB.LinComb L φ ε).ι) (j' : (LB.LinComb L φ' ε').ι)
    (hj' : LB.Coh L φ' j') (hjj' : ∀ k k', φ k = φ' k' → j k = j' k') :
    rO (inf_le_left : (LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ' ε').U j' ≤ _) (sc.f j) =
      rO (inf_le_right : (LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ' ε').U j' ≤ _)
        ((canonSec L hL φ ε φ' ε' hs hsub sc).f j') := by
  have hj : jhat φ ε φ' hsub j' = j :=
    funext fun k => (hjj' k _ (hsub k).choose_spec.symm).symm
  have hc : corrU (L := L) φ' ε' j' = 1 := by
    refine Finset.prod_eq_one fun k' _ => ?_
    have hR : R φ' j' (φ' k') ⟨k', rfl⟩ = j' k' :=
      hj' _ _ (⟨k', rfl⟩ : ∃ c, φ' c = φ' k').choose_spec
    refine (congrArg (· ^ ε' k') ((gW_congr rfl rfl hR _
      (lePI (lcle φ' ε' j' k') (lcle φ' ε' j' k'))).trans (gW_self hL _ _ _))).trans ?_
    exact one_zpow _
  subst hj
  refine (rO_rO (wchart_le_jhat φ ε φ' ε' hsub j') inf_le_right _).symm.trans
    (congrArg (rO _) ?_)
  change _ = _ * Units.val (corrU φ' ε' j')
  rw [hc, Units.val_one, mul_one]
end ReciprocityTheory.ChartRestriction.G.Out.Canon
