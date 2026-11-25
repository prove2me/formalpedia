-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.vtf_twist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:15:09.717567+00:00
-- url     : https://prove2.me/submissions/944348c9-6727-4f84-9e74-a625fc251cf3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_VtFrRdHol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_VtFrRdA
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_valAt__comp_88757af08841
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
theorem _root_.solution {a b : ℤ} {ψ : Over.mk x0 ⊗ A ⟶ Over.mk x0 ⊗ A} {m : Over.mk x0 ⊗ A ⟶ A}
    {hm : ψ ≫ snd (Over.mk x0) A = m}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd (Over.mk x0) A).left, m.left] ![a, -b])}
    {s : LB.Sec (LPow A L b (Over.mk x0))} {s' : LB.Sec (LPow A L a (Over.mk x0))}
    (h : IsTwistPull A L ψ m hm a b α s s') (p : Sp ℂ ⟶ (Over.mk x0 ⊗ A).left) (j : Fin 2 → L.ι)
    (hp : ⊤ ≤ p ⁻¹ᵁ LB.wchart L ![(snd (Over.mk x0) A).left, m.left] j) :
    valAt' p ((LPow A L a (Over.mk x0)).U (fun _ => j 0)) (s'.f (fun _ => j 0)) =
      valAt' p _ (α.s j).val *
        valAt' (p ≫ ψ.left) ((LPow A L b (Over.mk x0)).U (fun _ => j 1)) (s.f (fun _ => j 1)) := by
  calc valAt' p ((LPow A L a (Over.mk x0)).U (fun _ => j 0)) (s'.f (fun _ => j 0))
      = valAt' p (LB.wchart L ![(snd (Over.mk x0) A).left, m.left] j)
          (((Over.mk x0 ⊗ A).left.presheaf.map (homOfLE (chart_le_zero A L m j)).op).hom
            (s'.f (fun _ => j 0))) := by
        exact (valAt'_res p (chart_le_zero A L m j) hp _).symm
    _ = valAt' p (LB.wchart L ![(snd (Over.mk x0) A).left, m.left] j)
          ((show Γ((Over.mk x0 ⊗ A).left, LB.wchart L ![(snd (Over.mk x0) A).left, m.left] j) from (α.s j).val) *
            ((Over.mk x0 ⊗ A).left.presheaf.map (homOfLE (chart_le_pull A L ψ m hm j)).op).hom
              ((ψ.left.app _).hom (s.f (fun _ => j 1)))) := by rw [h j]
    _ = _ := by
        rw [valAt'_mul]
        refine congrArg₂ (· * ·) rfl ?_
        calc _ = valAt' p (ψ.left ⁻¹ᵁ (LPow A L b (Over.mk x0)).U (fun _ => j 1))
              ((ψ.left.app _).hom (s.f (fun _ => j 1))) := by
              exact valAt'_res p (chart_le_pull A L ψ m hm j) hp _
          _ = _ := by exact valAt'_comp p ψ.left _ _
end ReciprocityTheory.ChartRestriction.G.PullbackSections
