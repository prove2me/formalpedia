-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsChow_GenericFibreIdeal_finIdeal_isPrime_disjoint_5dfc671a0d1a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:45:10.323606+00:00
-- url     : https://prove2.me/submissions/5c4bf6ec-a3cb-4364-a368-460592351733

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LinFormOneZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PGenericFibreIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.ObjectsChow
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar)
open GroundTheory.Heights₂.Heights.ObjectsChow.GenericFibreIdeal
variable {n : ℕ}
attribute [local instance] MvPolynomial.algebraMvPolynomial
namespace GroundTheory.Heights₂.Heights.ObjectsChow.GenericFibreIdeal
theorem _root_.solution (n d : ℕ) (P : Ideal (MRing (PBlk n))) (hP : IsArithVar P d) :
    (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P).IsPrime ∧
      Disjoint ((intUnits n : Set (MvPolynomial (Fin n) ℤ))) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) := by
  obtain ⟨-, ⟨hprime, -, -⟩, hhor, -⟩ := hP
  refine ⟨?_, ?_⟩
  · have := hprime
    exact Ideal.comap_isPrime _ _
  · refine Set.disjoint_left.mpr ?_
    rintro _ ⟨a, ha, rfl⟩ hx
    have h1 : (C a : MRing (PBlk n)) ∈ P := by
      simpa [IndefiniteRowSideFullHecke.ArithBezout.finIdeal, Ideal.mem_comap] using hx
    have h2 : a ∈ P.comap (C : ℤ →+* MRing (PBlk n)) := h1
    rw [hhor, Ideal.mem_bot] at h2
    exact nonZeroDivisors.ne_zero ha h2
end GroundTheory.Heights₂.Heights.ObjectsChow.GenericFibreIdeal
