-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.pullU_units_compat_generic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:48:29.699856+00:00
-- url     : https://prove2.me/submissions/1d0a68ba-c858-4e88-8f51-873d82243b01

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
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
private lemma res_res_lemma {S : Scheme.{0}} {U V W : S.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (x : Γ(S, U)ˣ) :
    res h2 (res h1 x) = res (h2.trans h1) x := by
  have hc : S.presheaf.map (homOfLE h1).op ≫ S.presheaf.map (homOfLE h2).op =
      S.presheaf.map (homOfLE (h2.trans h1)).op := by
    rw [← Functor.map_comp]
    rfl
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← hc]
  rfl
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
theorem _root_.solution (h : Z ⟶ Y) {Ui Uj : Y.Opens} {Wi Wj : Z.Opens} (hi : Wi ≤ h ⁻¹ᵁ Ui)
    (hj : Wj ≤ h ⁻¹ᵁ Uj) (ti : Γ(Y, Ui)ˣ) (tj : Γ(Y, Uj)ˣ) (g : Γ(Y, Ui ⊓ Uj)ˣ)
    (hc : res (inf_le_left : Ui ⊓ Uj ≤ Ui) ti = g * res (inf_le_right : Ui ⊓ Uj ≤ Uj) tj)
    (g' : Γ(Z, Wi ⊓ Wj)ˣ)
    (hg' : g' = res (le_inf (inf_le_left.trans hi) (inf_le_right.trans hj) : Wi ⊓ Wj ≤ h ⁻¹ᵁ (Ui ⊓ Uj))
      (pullU h _ g)) :
    res (inf_le_left : Wi ⊓ Wj ≤ Wi) (res hi (pullU h Ui ti)) =
      g' * res (inf_le_right : Wi ⊓ Wj ≤ Wj) (res hj (pullU h Uj tj)) := by
  subst hg'
  have hW : Wi ⊓ Wj ≤ h ⁻¹ᵁ (Ui ⊓ Uj) := le_inf (inf_le_left.trans hi) (inf_le_right.trans hj)
  have h1 : res (X := Z) (U := h ⁻¹ᵁ (Ui ⊓ Uj)) (V := Wi ⊓ Wj) hW
        (pullU h (Ui ⊓ Uj) (res (inf_le_left : Ui ⊓ Uj ≤ Ui) ti)) =
      res (X := Z) (U := h ⁻¹ᵁ (Ui ⊓ Uj)) (V := Wi ⊓ Wj) hW (pullU h (Ui ⊓ Uj) g) *
        res (X := Z) (U := h ⁻¹ᵁ (Ui ⊓ Uj)) (V := Wi ⊓ Wj) hW
          (pullU h (Ui ⊓ Uj) (res (inf_le_right : Ui ⊓ Uj ≤ Uj) tj)) := by
    rw [hc, map_mul, map_mul]
  rw [res_pullU_res_eq_res_pullU h inf_le_left hW (inf_le_left.trans hi),
    res_pullU_res_eq_res_pullU h inf_le_right hW (inf_le_right.trans hj)] at h1
  rw [res_res_lemma, res_res_lemma]
  exact h1
end ReciprocityTheory.ChartRestriction.G.DVR
