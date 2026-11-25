-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Qk34.norm_le_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:51:18.627663+00:00
-- url     : https://prove2.me/submissions/2ddcc8a3-faa0-4ab2-9268-d11079a5eb95

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormLeSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qk34
theorem _root_.solution :
    ∀ (P Q : Nat) (X : UpperTheory.Reformulated.B.Qk34.MM P Q),
      @LE.le Real Real.instLE
        (@Norm.norm (UpperTheory.Reformulated.B.Qk34.MM P Q)
          (@NormedRing.toNorm (UpperTheory.Reformulated.B.Qk34.MM P Q)
            (@Matrix.linftyOpNormedRing (Sum (Fin P) (Fin Q)) Complex
              (@instFintypeSum (Fin P) (Fin Q) (Fin.fintype P) (Fin.fintype Q))
              (@CStarAlgebra.toNormedRing Complex (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
              fun (a b : Sum (Fin P) (Fin Q)) ↦
              @instDecidableEqSum (Fin P) (Fin Q) (instDecidableEqFin P) (instDecidableEqFin Q) a b))
          X)
        (∑ i : Sum (Fin P) (Fin Q), ∑ j : Sum (Fin P) (Fin Q), @Norm.norm Complex Complex.instNorm (X i j)) := by
  intro P Q X
  have h := Matrix.linfty_opNorm_def (A := X)
  refine le_trans (le_of_eq h) ?_
  have key : ((Finset.univ : Finset (Sum (Fin P) (Fin Q))).sup
      fun i => ∑ j : Sum (Fin P) (Fin Q), ‖X i j‖₊)
      ≤ ∑ i : Sum (Fin P) (Fin Q), ∑ j : Sum (Fin P) (Fin Q), ‖X i j‖₊ :=
    Finset.sup_le fun i hi =>
      Finset.single_le_sum (f := fun i => ∑ j : Sum (Fin P) (Fin Q), ‖X i j‖₊)
        (fun _ _ => by positivity) hi
  have key' := NNReal.coe_le_coe.mpr key
  simpa only [NNReal.coe_sum, coe_nnnorm] using key'
end UpperTheory.Reformulated.B.Qk34
