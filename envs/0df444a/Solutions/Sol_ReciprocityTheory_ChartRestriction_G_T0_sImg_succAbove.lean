-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.sImg_succAbove
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:32:05.95928+00:00
-- url     : https://prove2.me/submissions/3d18231e-d161-4d9d-b026-609bb93af641

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
theorem _root_.solution (j₀ : Fin (N + 1)) (x : Fin N → Ω) (i : Fin (D + 1)) (k : Fin N) :
    sImg (Ω := Ω) j₀ x (i, j₀.succAbove k) =
      algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N) (X (Sum.inr (i, k))) := by
  unfold sImg
  congr 1
  exact Fin.insertNth_apply_succAbove (α := fun _ => MvPolynomial (SVar D N) Ω) j₀ _ _ k
end ReciprocityTheory.ChartRestriction.G.T0
