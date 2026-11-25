-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.psiS_chiImg_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:26:21.761255+00:00
-- url     : https://prove2.me/submissions/8b2431be-95b6-48cc-ba1e-4921c16119ff

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
    psiS (chiImg j₀ x ((0 : Fin (D + 1)), j₀)) =
      algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N)
        (-∑ k, X (Sum.inr ((0 : Fin (D + 1)), k)) * C (x k)) := by
  have h1 : chiImg j₀ x ((0 : Fin (D + 1)), j₀) = -∑ k, X ((0 : Fin (D + 1)), k) * C (x k) :=
    Fin.insertNth_apply_same (α := fun _ => MvPolynomial (Fin (D + 1) × Fin N) Ω) j₀ _ _
  rw [h1]
  simp [psiS, map_neg, map_sum, map_mul, MvPolynomial.rename_X, MvPolynomial.rename_C]
end ReciprocityTheory.ChartRestriction.G.T0
