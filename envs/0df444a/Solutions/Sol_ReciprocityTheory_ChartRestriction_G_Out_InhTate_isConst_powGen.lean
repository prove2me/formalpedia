-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.InhTate.isConst_powGen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:02:31.080175+00:00
-- url     : https://prove2.me/submissions/335ca492-3c8d-47c6-9bec-6b84afae97a3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_InhTate

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.InhTate
open Semi Inh
variable {X Y Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
namespace ReciprocityTheory.ChartRestriction.G.Out.InhTate
theorem _root_.solution {φ : K → (Y ⟶ X)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L φ ε)}
    {a : Γ(Y, ⊤)ˣ} (ht : IsConst t a) (n : ℕ) : IsConst (GeneratorPullback.powGen L φ ε t n) (a ^ n) := by
  intro j
  have e1 : t.s j = gv a (LB.wchart L φ j) := ht j
  show (t.s j) ^ n = gv (a ^ n) (LB.wchart L φ j)
  rw [e1]
  first
    | exact (map_pow (res le_top) a n).symm
    | simp [gv, map_pow]
end ReciprocityTheory.ChartRestriction.G.Out.InhTate
