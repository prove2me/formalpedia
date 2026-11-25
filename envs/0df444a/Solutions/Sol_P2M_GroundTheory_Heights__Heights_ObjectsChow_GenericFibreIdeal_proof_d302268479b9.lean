-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsChow_GenericFibreIdeal_proof_d302268479b9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:56:40.545334+00:00
-- url     : https://prove2.me/submissions/a345f11e-b06b-4437-a5d3-3441a367637b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LinFormOneZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PGenericFibreIdeal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_GenericFibreIdeal_algebraMap_eq_c626137687a0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_GenericFibreIdeal_finIdeal_isPrime_disjoint_5dfc671a0d1a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_GenericFibreIdeal_genericIdeal_isHomogIdeal_b15b1d64bf07

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
theorem _root_.solution : GenericFibreIdeal.Statement := by
  intro n d P hP
  obtain ⟨hQprime, hdisj⟩ := finIdeal_isPrime_disjoint n d P hP
  have hgen : genericIdeal P =
      (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P).map
        (algebraMap (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℚ)) := by
    rw [algebraMap_eq]; rfl
  have hsat : (genericIdeal P).comap (MvPolynomial.map (Int.castRingHom ℚ)) =
      IndefiniteRowSideFullHecke.ArithBezout.finIdeal P := by
    rw [hgen, ← algebraMap_eq]
    exact IsLocalization.under_map_of_isPrime_disjoint (intUnits n) _ hQprime hdisj
  obtain ⟨-, ⟨-, ⟨S, hS, hPS⟩, hrel⟩, -, -⟩ := hP
  refine ⟨⟨?_, ?_, ?_⟩, hsat⟩
  · rw [hgen]
    exact IsLocalization.isPrime_of_isPrime_disjoint (intUnits n) _ _ hQprime hdisj
  · exact genericIdeal_isHomogIdeal P ⟨S, hS, hPS⟩
  ·
    obtain ⟨i, hi⟩ := hrel ()
    refine ⟨i, fun hX => hi ?_⟩
    have hmem : (X i : MvPolynomial (Fin n) ℤ) ∈ IndefiniteRowSideFullHecke.ArithBezout.finIdeal P := by
      rw [← hsat, Ideal.mem_comap, map_X]
      exact hX
    simpa [IndefiniteRowSideFullHecke.ArithBezout.finIdeal, Ideal.mem_comap] using hmem
end GroundTheory.Heights₂.Heights.ObjectsChow.GenericFibreIdeal
