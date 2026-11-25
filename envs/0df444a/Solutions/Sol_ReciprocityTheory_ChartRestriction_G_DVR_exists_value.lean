-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.exists_value
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:17:45.359774+00:00
-- url     : https://prove2.me/submissions/45ba3238-8e64-46b0-a6c7-84025ab6e472

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen_of_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_wchart_empty
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_res_refl__cb32e03a41c1
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_res_res__b0a8af1c3378
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_fsum_empty
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gen_transport
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_sameSum_iff_fsum


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
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
open scoped Classical
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen)
    (z : Z ⟶ Y) (h0 : fsum (fun k => z ≫ φ k) ε = 0) :
    ∃ c : Γ(Z, ⊤)ˣ, ∀ j : K → L.ι, LB.Coh L (fun k => z ≫ φ k) j →
      res (le_top : LB.wchart L (fun k => z ≫ φ k) j ≤ ⊤) c = (LB.pullGen L φ ε t z).s j := by
  have hs : LB.SameSum (fun k => z ≫ φ k) ε (K' := PEmpty) PEmpty.elim PEmpty.elim := by
    rw [sameSum_iff_fsum, h0, fsum_empty]
  obtain ⟨te, -, hc⟩ := gen_transport hL hs (LB.pullGen L φ ε t z) (pullGen_isGen_of_isGen φ ε t ht z)
  let j0 : PEmpty → L.ι := PEmpty.elim
  refine ⟨res (le_of_eq (wchart_empty j0).symm) (te.s j0), fun j hj => ?_⟩
  have e := hc j j0 hj (fun k _ => k.elim) (fun _ k => k.elim)
  have hle : LB.wchart L (fun k => z ≫ φ k) j ≤ LB.wchart L (fun k => z ≫ φ k) j ⊓ LB.wchart L PEmpty.elim j0 :=
    le_inf le_rfl (by rw [wchart_empty]; exact le_top)
  have e2 := congrArg (res hle) e
  erw [res_res'] at e2
  have e3 := e2.symm
  erw [res_res', res_refl'] at e3
  erw [res_res']
  exact e3
end ReciprocityTheory.ChartRestriction.G.DVR
