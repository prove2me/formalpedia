-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowFormDimLe_exists_prime_liesOver_ad270c783d28
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:10:06.780098+00:00
-- url     : https://prove2.me/submissions/eab13cf6-af80-4b32-a561-1a2f06875c5d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChowFormDim
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormDimLe

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChowFormDimLe
namespace GroundTheory.Heights₂.Heights.ChowFormDimLe
theorem _root_.solution {F : Type} [Field F] (K : Type) [Field K] [Algebra F K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) F)) [I.IsPrime] (hI : ∀ g ∈ I, coeff 0 g = 0) :
    ∃ P : Ideal (MvPolynomial (Fin n) K), P.IsPrime ∧
      P ≤ RingHom.ker (eval (0 : Fin n → K)) ∧
      P.comap (MvPolynomial.map (algebraMap F K)) = I := by
  let _ := MvPolynomial.algebraMvPolynomial (σ := Fin n) (R := F) (S := K)
  have : Module.Flat (MvPolynomial (Fin n) F) (MvPolynomial (Fin n) K) :=
    Module.Flat.isBaseChange F (MvPolynomial (Fin n) F) K (MvPolynomial (Fin n) K)
      (Algebra.IsPushout.out (R := F) (S := MvPolynomial (Fin n) F) (R' := K)
        (S' := MvPolynomial (Fin n) K))
  set Q : Ideal (MvPolynomial (Fin n) K) := RingHom.ker (eval (0 : Fin n → K))
  have : Q.IsMaximal := RingHom.ker_isMaximal_of_surjective _ (fun c => ⟨C c, eval_C c⟩)
  have hle : I ≤ Q.under (MvPolynomial (Fin n) F) := by
    intro g hg
    rw [Ideal.under, Ideal.mem_comap, MvPolynomial.algebraMap_def, RingHom.mem_ker, eval_map,
      eval₂_zero_apply, constantCoeff_eq, hI g hg, map_zero]
  obtain ⟨P, hPQ, hP, hPI⟩ := Ideal.exists_ideal_le_liesOver_of_le Q hle
  refine ⟨P, hP, hPQ, ?_⟩
  rw [P.over_def I]
  rfl
end GroundTheory.Heights₂.Heights.ChowFormDimLe
