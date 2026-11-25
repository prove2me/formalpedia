-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.vtf_read
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:09:46.957157+00:00
-- url     : https://prove2.me/submissions/07059fe1-0849-442a-9bce-2667a1306a57

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_VtFrRdHol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_VtFrRdA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_vtfQ_snd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_vtf_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_vtf_val_g
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_ValAt_valAt__res_9bf5469fe96a


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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Opposite
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) {x0 : Sp ℂ ⟶ S}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution {k : ℤ} (F : LB.Sec (LPow A L k (Over.mk x0))) (a : Over.mk x0 ⟶ A) (fr : L.ι → ℂ)
    (hfr : ∀ j j', ⊤ ≤ a.left ⁻¹ᵁ (L.U j ⊓ L.U j') → fr j = valAt' a.left _ (L.g j j' : Γ(A.left, L.U j ⊓ L.U j')) * fr j')
    (j j' : L.ι) (hj : ⊤ ≤ a.left ⁻¹ᵁ L.U j) (hj' : ⊤ ≤ a.left ⁻¹ᵁ L.U j') (θ : ℂ)
    (h : valAt' (vtfQ A a).left ((LPow A L k (Over.mk x0)).U (fun _ => j)) (F.f (fun _ => j)) = θ * fr j ^ k) :
    valAt' (vtfQ A a).left ((LPow A L k (Over.mk x0)).U (fun _ => j')) (F.f (fun _ => j')) = θ * fr j' ^ k := by
  have hjj : ⊤ ≤ a.left ⁻¹ᵁ (L.U j' ⊓ L.U j) := fun q hq => ⟨hj' hq, hj hq⟩
  have hp : ⊤ ≤ (vtfQ A a).left ⁻¹ᵁ ((LPow A L k (Over.mk x0)).U (fun _ => j') ⊓
      (LPow A L k (Over.mk x0)).U (fun _ => j)) :=
    fun q hq => ⟨vtf_chart A L k a _ hj' hq, vtf_chart A L k a _ hj hq⟩
  have e := congrArg (valAt' (vtfQ A a).left _) (F.compat (fun _ => j') (fun _ => j))
  rw [valAt'_mul] at e
  have e1 : valAt' (vtfQ A a).left _ (((Over.mk x0 ⊗ A).left.presheaf.map (homOfLE (inf_le_left :
      (LPow A L k (Over.mk x0)).U (fun _ => j') ⊓ (LPow A L k (Over.mk x0)).U (fun _ => j) ≤ _)).op).hom
      (F.f (fun _ => j'))) = valAt' (vtfQ A a).left _ (F.f (fun _ => j')) := by
    exact valAt'_res _ _ hp _
  have e2 : valAt' (vtfQ A a).left _ (((Over.mk x0 ⊗ A).left.presheaf.map (homOfLE (inf_le_right :
      (LPow A L k (Over.mk x0)).U (fun _ => j') ⊓ (LPow A L k (Over.mk x0)).U (fun _ => j) ≤ _)).op).hom
      (F.f (fun _ => j))) = valAt' (vtfQ A a).left _ (F.f (fun _ => j)) := by
    exact valAt'_res _ _ hp _
  rw [e1, e2, vtf_val_g A L _ _ _ hp, vtfQ_snd, h] at e
  rw [e, hfr j' j hjj, mul_zpow]
  ring
end ReciprocityTheory.ChartRestriction.G.PullbackSections
