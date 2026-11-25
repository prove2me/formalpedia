-- Prove2me | solution 1 for PositivityTheory.CW.FunctionalCalculusInner.inner_basis_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:22:27.926617+00:00
-- url     : https://prove2.me/submissions/75f8f376-bab9-4af6-be6f-bb7ad934e6a1

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusOfBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.FunctionalCalculusInner
variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type}
namespace PositivityTheory.CW.FunctionalCalculusInner
theorem _root_.solution (b : Module.Basis ι ℂ V) (hb : Orthonormal ℂ b) (i : ι) (y : V) :
    inner ℂ (b i) y = b.repr y i := by
  classical
  have key : (innerₛₗ ℂ (b i) : V →ₗ[ℂ] ℂ) = b.coord i := by
    refine b.ext fun j => ?_
    show inner ℂ (b i) (b j) = b.repr (b j) i
    rw [Module.Basis.repr_self, orthonormal_iff_ite.mp hb i j]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  exact LinearMap.congr_fun key y
end PositivityTheory.CW.FunctionalCalculusInner
