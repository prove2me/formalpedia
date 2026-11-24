-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Qk24.Mk_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:42:21.881855+00:00
-- url     : https://prove2.me/submissions/2ae1b13c-0133-4401-926b-724595c9bfb4

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SignActionMapComm
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
private theorem UpperTheory.Reformulated.B.Qk24.sandwich_mul {R : Type*} [Semiring R] {n k : Type*} [Fintype n] [Fintype k]
    (B C : Matrix n k R) (P Q : Matrix k n R) (X Y : Matrix k k R) :
    B * X * P * (C * Y * Q) = B * (X * (P * C * Y)) * Q := by
  simp only [Matrix.mul_assoc]
private theorem UpperTheory.Reformulated.B.Qk24.block_mul {R : Type*} [Semiring R] {n k : Type*} [Fintype n] [Fintype k]
    [DecidableEq n] (B D : Matrix n k R) (P Q : Matrix k n R) (H K : Matrix k k R)
    (h1 : P * B = H) (h2 : P * D = 0) (h3 : Q * B = 0) (h4 : Q * D = K) (X Y X' Y' : Matrix k k R) :
    (1 + B * X * P + D * Y * Q) * (1 + B * X' * P + D * Y' * Q) =
      1 + B * (X + X' + X * (H * X')) * P + D * (Y + Y' + Y * (K * Y')) * Q := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    UpperTheory.Reformulated.B.Qk24.sandwich_mul, h1, h2, h3, h4, Matrix.zero_mul, Matrix.mul_zero, add_zero]
  abel
end

set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qk24
theorem _root_.solution :
    ∀ {I : Formalism.MainNotions.S.AutInst} {k : ℕ} (b d : Fin k → UpperTheory.Reformulated.B.Qk24.VA I) (η : TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)),
      UpperTheory.Reformulated.B.Qk24.rowM I d * UpperTheory.Reformulated.B.Qk24.colM I b =
          η • (1 : Matrix (Fin k) (Fin k) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F))) →
        UpperTheory.Reformulated.B.Qk24.rowM I d * UpperTheory.Reformulated.B.Qk24.colM I d =
            (0 : Matrix (Fin k) (Fin k) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F))) →
          UpperTheory.Reformulated.B.Qk24.rowM I b * UpperTheory.Reformulated.B.Qk24.colM I b =
              (0 : Matrix (Fin k) (Fin k) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F))) →
            UpperTheory.Reformulated.B.Qk24.rowM I b * UpperTheory.Reformulated.B.Qk24.colM I d =
                (UpperTheory.Reformulated.B.Qk24.sigA I :
                            TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F) → TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F))
                    η •
                  (1 : Matrix (Fin k) (Fin k) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F))) →
              ∀ (X Y X' Y' : Matrix (Fin k) (Fin k) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F))),
                UpperTheory.Reformulated.B.Qk24.Mk I b d X Y * UpperTheory.Reformulated.B.Qk24.Mk I b d X' Y' =
                  UpperTheory.Reformulated.B.Qk24.Mk I b d
                    (X + X' + X * (η • (1 : Matrix (Fin k) (Fin k) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F))) * X'))
                    (Y + Y' +
                      Y *
                        ((UpperTheory.Reformulated.B.Qk24.sigA I :
                                      TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F) → TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F))
                              η •
                            (1 : Matrix (Fin k) (Fin k) (TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F))) *
                          Y')) := by
  intro I k b d η h1 h2 h3 h4 X Y X' Y'
  exact UpperTheory.Reformulated.B.Qk24.block_mul _ _ _ _ _ _ h1 h2 h3 h4 X Y X' Y'
end UpperTheory.Reformulated.B.Qk24
