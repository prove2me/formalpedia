-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge.directLaurentToRatFunc_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:30:00.356319+00:00
-- url     : https://prove2.me/submissions/5fdeb524-9c2e-4181-b5f1-7bc7b4f4d424

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_DirectChartCommonDenominator
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseAffinePlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_InverseChartDenominatorTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_LaurentFiniteWindow
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_TwoChartFiniteDimensionalBridge

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge
open scoped LaurentPolynomial Polynomial RatFunc
variable {k F ι : Type*}
namespace QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge
theorem _root_.solution (k : Type*) [Field k] :
    Function.Injective
      (InverseChartDenominatorTransport.directLaurentToRatFunc k) := by
  let M : Submonoid k[X] := Submonoid.powers Polynomial.X
  let N : Submonoid k[X] := nonZeroDivisors k[X]
  have hMN : M ≤ Submonoid.comap (RingHom.id k[X]) N := by
    rintro f ⟨n, rfl⟩
    simp [N]
  let f : LaurentPolynomial k →+* RatFunc k :=
    IsLocalization.map (T := N) (RatFunc k) (RingHom.id k[X]) hMN
  have hf : Function.Injective f :=
    IsLocalization.map_injective_of_injective'
      (R := Polynomial k) (S := Polynomial k) (f := RingHom.id (Polynomial k))
      (Rₘ := LaurentPolynomial k) M (RatFunc k) (N := N) hMN (by simp [N])
      Function.injective_id
  have hmap :
      InverseChartDenominatorTransport.directLaurentToRatFunc k = f := by
    apply IsLocalization.ringHom_ext M
    apply Polynomial.ringHom_ext
    · intro c
      simp [f, InverseChartDenominatorTransport.directLaurentToRatFunc,
        InverseChartDenominatorTransport.ratFuncXUnit]
    · simp [f,
        InverseChartDenominatorTransport.directLaurentToRatFunc,
        InverseChartDenominatorTransport.ratFuncXUnit]
  rw [hmap]
  exact hf
end QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge
