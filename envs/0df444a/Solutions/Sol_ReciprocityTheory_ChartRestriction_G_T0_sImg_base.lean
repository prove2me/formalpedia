-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.sImg_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:18:04.530053+00:00
-- url     : https://prove2.me/submissions/d9a31aee-8ec8-484d-be17-37dba5a81c8d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GeneratorNeZeroOfHeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ScaleMultiHomogeneous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KerPLeOfPlace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution (j₀ : Fin (N + 1)) (x : Fin N → Ω) :
    sImg (Ω := Ω) j₀ x ((0 : Fin (D + 1)), j₀) =
      algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N) (X (Sum.inl ())) := by
  unfold sImg
  congr 1
  first
  | exact (Fin.insertNth_apply_same (α := fun _ => MvPolynomial (SVar D N) Ω) j₀ _ _).trans (if_pos rfl)
  | simp [Fin.succAboveCases]
end ReciprocityTheory.ChartRestriction.G.T0
