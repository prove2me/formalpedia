-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_cycR_sub_eq_d7d83be416a3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:57:49.471876+00:00
-- url     : https://prove2.me/submissions/9ac0095d-dd38-4db3-8937-f8d9dd7d2310

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_cycR_eq_finsum_b745b6d310f8

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.Inter.DiagRAux
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.DiagRAux
theorem _root_.solution (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι)) {n : ℕ}
    (L : Fin n → HermLine ι) (f g : MRing ι) (W₀ : Ideal (MRing ι))
    (hdiv : T.toZCycle (divCycle P f) - T.toZCycle (divCycle P g) = Finsupp.single W₀ 1)
    (hW₀ : IsHorizontal W₀) : cycR I P L f - cycR I P L g = I W₀ n L := by
  rw [cycR_eq_finsum, cycR_eq_finsum, ← finsum_sub_distrib]
  · have hW : ∀ W, (divCycle P f W : ℝ) - divCycle P g W = ((Finsupp.single W₀ (1 : ℤ) W : ℤ) : ℝ) := by
      intro W
      have := congrArg (fun z => z W) hdiv
      simp only [Finsupp.coe_sub, Pi.sub_apply, T.toZCycle, Finsupp.mapRange_apply] at this
      rw [← this]
      push_cast
      ring
    have e : ∀ W, (divCycle P f W : ℝ) * cycTerm I L W - divCycle P g W * cycTerm I L W =
        ((Finsupp.single W₀ (1 : ℤ) W : ℤ) : ℝ) * cycTerm I L W := fun W => by
      rw [← hW W]; ring
    simp only [e]
    rw [finsum_eq_single _ W₀ (fun W hW => by simp [Ne.symm hW])]
    simp [cycTerm, hW₀]
  · exact (divCycle P f).hasFiniteSupport.subset fun W hW h0 => hW (by simp [h0])
  · exact (divCycle P g).hasFiniteSupport.subset fun W hW h0 => hW (by simp [h0])
end GroundTheory.Heights₂.Heights.Inter.DiagRAux
