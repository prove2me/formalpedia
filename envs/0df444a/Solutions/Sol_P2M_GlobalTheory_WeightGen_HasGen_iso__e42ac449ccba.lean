-- Prove2me | solution 1 for P2M_GlobalTheory_WeightGen_HasGen_iso__e42ac449ccba
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:00:53.475708+00:00
-- url     : https://prove2.me/submissions/d498e5e8-8223-434c-aa56-486aa4fa412d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_NonemptyGtCoordOfIsGt
import Theorems.Thm_GlobalTheory_WeightGen_HasGen_of_local
import Theorems.Thm_GlobalTheory_WeightGen_gm_iso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.WeightGen
variable {P G B : Scheme.{0}} (q : G ⟶ B) (a p : P ⟶ G)
variable {q a p}
namespace GlobalTheory.WeightGen
namespace HasGen
theorem _root_.solution (h : a ≫ q = p ≫ q) {L M : LB B} {c : GermFn P} (hM : HasGen q a p M c)
    (cov : ∀ x, ∃ k, x ∈ M.U k) (w : LB.Iso L M) (hw : w.IsGen) : HasGen q a p L c := by
  obtain ⟨s, s₁, s₂⟩ := hM
  refine HasGen.of_local h M.U cov
    (fun k j Z r z => gm r z _ (s j) * gm (r ≫ q) z (M.U j ⊓ L.U k) (w.s (j, k)))
    (fun k j => ⟨res (V := q ⁻¹ᵁ L.U k ⊓ q ⁻¹ᵁ M.U j) inf_le_right (s j) *
      res (U := q ⁻¹ᵁ (M.U j ⊓ L.U k)) (le_inf inf_le_right inf_le_left)
      (pullU q (M.U j ⊓ L.U k) (w.s (j, k))), fun Z r z h₁ h₂ => ?_⟩)
    (fun Z r z k k' j j' h₁ h₂ h₃ h₄ => ?_) (fun Z r z j k h₁ h₂ => ?_)
  · have hm : r z ∈ q ⁻¹ᵁ L.U k ⊓ q ⁻¹ᵁ M.U j := ⟨h₁, h₂⟩
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ hm _)
      ((gm_res r z _ hm _).trans (gm_pull r q z (M.U j ⊓ L.U k) ⟨h₂, h₁⟩ _)))
  · rw [gm_iso hw (r ≫ q) z h₃ h₄ h₁ h₂, s₁ Z r z j j' h₃ h₄]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · rw [s₂ Z r z k h₂, Category.assoc, Category.assoc, h, _root_.mul_assoc]
end HasGen
end GlobalTheory.WeightGen
