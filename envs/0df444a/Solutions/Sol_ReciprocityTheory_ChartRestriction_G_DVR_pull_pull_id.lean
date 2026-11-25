-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.pull_pull_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:54:58.183881+00:00
-- url     : https://prove2.me/submissions/dd86c258-147a-4728-a4b0-cf3b1a36bbd5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullU_of_eq_id
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
namespace ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
private lemma res_pullU_res_eq_res_pullU {S T : Scheme.{0}} (h : T ⟶ S) {U V : S.Opens} {W : T.Opens} (hVU : V ≤ U)
    (hW : W ≤ h ⁻¹ᵁ V) (hW' : W ≤ h ⁻¹ᵁ U) (t : Γ(S, U)ˣ) :
    res hW (pullU h V (res hVU t)) = res hW' (pullU h U t) := by
  have hn := h.naturality (homOfLE hVU).op
  have key : S.presheaf.map (homOfLE hVU).op ≫ h.app V ≫ T.presheaf.map (homOfLE hW).op =
      h.app U ≫ T.presheaf.map (homOfLE hW').op := by
    rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp]
    rfl
  ext
  simp only [res, pullU, Units.coe_map, MonoidHom.coe_coe]
  exact congrArg (fun φ => φ.hom t.val) key
private lemma pullU_comp_lemma_3 {S T R : Scheme.{0}} (g : R ⟶ T) (f : T ⟶ S) (U : S.Opens) (x : Γ(S, U)ˣ) :
    pullU (g ≫ f) U x = pullU g (f ⁻¹ᵁ U) (pullU f U x) := by
  first
  | rfl
  | (ext; simp [pullU, Scheme.comp_app])
end ReciprocityTheory.ChartRestriction.G.DVR
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (z : Z ⟶ Y) (p : Y ⟶ Z) (hzp : z ≫ p = 𝟙 Z) {W : Y.Opens} {V : Z.Opens}
    (hW : W ≤ p ⁻¹ᵁ ⊤) (hV : V ≤ z ⁻¹ᵁ W) (c : Γ(Z, ⊤)ˣ) :
    res hV (pullU z W (res hW (pullU p ⊤ c))) = res (le_top : V ≤ ⊤) c := by
  have hV' : V ≤ z ⁻¹ᵁ (p ⁻¹ᵁ ⊤) := fun x hx => hW (hV hx)
  rw [res_pullU_res_eq_res_pullU z hW hV hV', ← pullU_comp_lemma_3]
  exact pullU_of_eq_id (z ≫ p) hzp ⊤ V hV' le_top c
end ReciprocityTheory.ChartRestriction.G.DVR
