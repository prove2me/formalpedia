-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.units_ext_cover
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:39.97907+00:00
-- url     : https://prove2.me/submissions/aba8a35e-29c8-446f-b166-41a9093d1a98

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_sec_glue
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_res_res__b0a8af1c3378


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
open scoped Classical
variable {X Y : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']
  (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
variable {L φ φ'}
variable (L φ φ')
variable {L φ ε φ' ε'}
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {Y : Scheme.{0}} (W : Y.Opens) {ι : Type} (V : ι → Y.Opens) (hle : ∀ i, V i ≤ W)
    (hcov : W ≤ ⨆ i, V i) (a b : Γ(Y, W)ˣ) (h : ∀ i, res (hle i) a = res (hle i) b) : a = b := by
  have hv : ∀ i j, (Y.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op).hom
        ((res (hle i) a : Γ(Y, V i)ˣ) : Γ(Y, V i)) =
      (Y.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op).hom ((res (hle j) a : Γ(Y, V j)ˣ) : Γ(Y, V j)) := by
    intro i j
    have e1 := congrArg Units.val (res_res' (hle i) (inf_le_left : V i ⊓ V j ≤ V i) a)
    have e2 := congrArg Units.val (res_res' (hle j) (inf_le_right : V i ⊓ V j ≤ V j) a)
    simp only [res, Units.coe_map, MonoidHom.coe_coe] at e1 e2 ⊢
    rw [e1, e2]
  obtain ⟨g, -, hu⟩ := sec_glue W V hle hcov (fun i => ((res (hle i) a : Γ(Y, V i)ˣ) : Γ(Y, V i))) hv
  have ea := hu a.val (fun i => rfl)
  have eb := hu b.val (fun i => by rw [h i]; rfl)
  exact Units.ext (ea.trans eb.symm)
end ReciprocityTheory.ChartRestriction.G.DVR
