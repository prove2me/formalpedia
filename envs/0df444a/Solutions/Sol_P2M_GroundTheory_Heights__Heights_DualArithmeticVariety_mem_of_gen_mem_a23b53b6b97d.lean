-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DualArithmeticVariety_mem_of_gen_mem_a23b53b6b97d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:30:13.604053+00:00
-- url     : https://prove2.me/submissions/5a331e7d-ab1e-4662-b0e6-f06c4e37ba88

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegreeDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.DualArithmeticVariety
variable {K : Type} [Field K]
namespace GroundTheory.Heights₂.Heights.DualArithmeticVariety
theorem _root_.solution {m : ℕ} (E : IntermediateField K (ProjField K m))
    (h : ∀ j, algebraMap (MvPolynomial (Fin m) K) (ProjField K m) (X j) ∈ E) (z : ProjField K m) :
    z ∈ E := by
  have hp : ∀ p : MvPolynomial (Fin m) K, algebraMap _ (ProjField K m) p ∈ E := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C c =>
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
      exact E.algebraMap_mem c
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p j hp => rw [map_mul]; exact mul_mem hp (h j)
  obtain ⟨p, q, -, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (Fin m) K) z
  exact div_mem (hp p) (hp q)
end GroundTheory.Heights₂.Heights.DualArithmeticVariety
