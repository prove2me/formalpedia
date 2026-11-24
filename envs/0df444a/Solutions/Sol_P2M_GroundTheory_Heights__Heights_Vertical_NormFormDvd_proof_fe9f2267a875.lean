-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_NormFormDvd_proof_fe9f2267a875
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:56:45.430812+00:00
-- url     : https://prove2.me/submissions/e0e1f113-1c62-4732-ad48-e76ed5660e0d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PNormFormDvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial TensorProduct
noncomputable section
attribute [local instance] MvPolynomial.algebraMvPolynomial
namespace GroundTheory.Heights₂.Heights.Vertical
namespace NormFormDvd
theorem _root_.solution : NormFormDvd.Statement := by
  intro R A _ _ _ _ _ n x p hdvd
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨0, Subsingleton.elim _ _⟩
  obtain ⟨h, hh⟩ := hdvd
  let b := Module.Free.chooseBasis R A
  let bP := tensorPolyBasis b n
  have hmap : (p.map (algebraMap R A) : MvPolynomial (Fin n) A) =
      algebraMap (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) A) p := by
    rw [MvPolynomial.algebraMap_def]
  have hnorm : Algebra.norm (MvPolynomial (Fin n) R)
      (algebraMap (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) A) p) = p ^ Module.finrank R A := by
    rw [Algebra.norm_algebraMap_of_basis bP, Module.finrank_eq_card_basis b]
  refine ⟨Algebra.norm (MvPolynomial (Fin n) R) h, ?_⟩
  rw [← hnorm, ← hmap, hh, map_mul]
  rfl
end NormFormDvd
end GroundTheory.Heights₂.Heights.Vertical
