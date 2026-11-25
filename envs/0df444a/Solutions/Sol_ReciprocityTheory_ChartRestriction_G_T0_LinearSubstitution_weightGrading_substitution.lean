-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.LinearSubstitution.weightGrading_substitution
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:25:18.906138+00:00
-- url     : https://prove2.me/submissions/b9fded41-7825-4fb0-8523-1384df571f5a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_PowFirstVarDvdSubstitution
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_EvalOneBilinearSubstitution
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SubstitutionSplitIrreducibleOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_WH_psiP_eq_of_isWeightedHomogeneous


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G.T0.LinearSubstitution
variable {K : Type} [Field K] {D N : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0.LinearSubstitution
theorem _root_.solution (p : V D N → Prop) [DecidablePred p]
    (hp : ∀ t : TVar D N, WH.psiP p (gImg (K := K) t) = Polynomial.C (gImg t) * Polynomial.X)
    (F : KTp K D N) (d0 : ℕ) (hmh : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => d0) F) :
    WH.psiP p (bilinearSubstitution F) = Polynomial.C (bilinearSubstitution F) * Polynomial.X ^ ((D + 1) * d0) := by
  classical
  have hw : ∀ s ∈ F.support, WH.wt (fun _ : TVar D N => True) s = (D + 1) * d0 := by
    intro s hs
    simp only [WH.wt, ↓reduceIte]
    rw [Fintype.sum_prod_type, Finset.sum_congr rfl fun b _ => hmh s hs b]
    simp
  have e := WH.psiP_eq_of_isWeightedHomogeneous (K := K) (fun _ : TVar D N => True) ((D + 1) * d0) F hw
  have e2 := congrArg (Polynomial.mapAlgHom (aeval fun t : TVar D N => gImg (K := K) t)) e
  have h1 : WH.psiP p (bilinearSubstitution F) =
      aeval (fun t => Polynomial.C (gImg (K := K) t) * Polynomial.X) F := by
    rw [show bilinearSubstitution F = aeval (fun t => gImg (K := K) t) F from rfl, MvPolynomial.comp_aeval_apply]
    simp only [hp]
  rw [h1]
  unfold WH.psiP at e2
  rw [MvPolynomial.comp_aeval_apply] at e2
  convert e2 using 1
  · refine congrArg (fun f => aeval f F) (funext fun t => ?_)
    simp
  · rw [show bilinearSubstitution F = aeval (fun t => gImg (K := K) t) F from rfl]
    simp
end ReciprocityTheory.ChartRestriction.G.T0.LinearSubstitution
