-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsChow_GenericFibreIdeal_genericIdeal_isHomogIdeal_b15b1d64bf07
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:29:36.722611+00:00
-- url     : https://prove2.me/submissions/fb891971-4cb4-43d5-b629-33a3b5138bac

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LinFormOneZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PGenericFibreIdeal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_GenericFibreIdeal_finIdeal_eq_map_0fa9df26c3a7

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
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GroundTheory.Heights₂.Heights.ObjectsChow.GenericFibreIdeal
theorem _root_.solution (P : Ideal (MRing (PBlk n)))
    (hP : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomogIdeal P) : IsHomogIdeal (genericIdeal P) := by
  obtain ⟨S, hS, hPS⟩ := hP
  have hH : (genericIdeal P).IsHomogeneous (homogeneousSubmodule (Fin n) ℚ) := by
    rw [genericIdeal, finIdeal_eq_map, hPS, Ideal.map_span, Ideal.map_span]
    refine Ideal.homogeneous_span _ _ ?_
    rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    obtain ⟨a, ha⟩ := hS s hs
    refine ⟨a (), (mem_homogeneousSubmodule _ _).mpr ?_⟩
    have hs' : s.IsHomogeneous (a ()) := by
      intro m hm
      change Finsupp.weight (fun _ => 1) m = a ()
      rw [← Finsupp.degree_eq_weight_one, Finsupp.degree_eq_sum, Fintype.sum_sigma]
      simpa using ha m (mem_support_iff.mpr hm) ()
    exact (IsHomogeneous.rename_isHomogeneous hs').map _
  intro f hf k
  exact homogeneousComponent_mem_of_mem hH hf k
end GroundTheory.Heights₂.Heights.ObjectsChow.GenericFibreIdeal
