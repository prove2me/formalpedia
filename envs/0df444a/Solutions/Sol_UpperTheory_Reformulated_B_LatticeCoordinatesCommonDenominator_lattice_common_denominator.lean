-- Prove2me | solution 1 for UpperTheory.Reformulated.B.LatticeCoordinatesCommonDenominator.lattice_common_denominator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:42:20.629274+00:00
-- url     : https://prove2.me/submissions/c8e5536d-0f05-4895-b888-a716f3c4db96

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DenominatorOfFinitelyGenerated
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
private lemma UpperTheory.Reformulated.B.LatticeCoordinatesCommonDenominator.denom_of_fg {R K ι : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [Finite ι] (L : Submodule R (ι → K)) (hL : L.FG) :
    ∃ b : R, b ≠ 0 ∧ ∀ y ∈ L, ∀ i : ι, ∃ c : R, algebraMap R K c = algebraMap R K b * y i := by
  obtain ⟨S, rfl⟩ := hL
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R)
    (fun p : S × ι => (p.1 : ι → K) p.2)
  refine ⟨b, nonZeroDivisors.ne_zero b.2, ?_⟩
  intro y hy i
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc⟩ := hb (⟨x, hx⟩, i)
    exact ⟨c, by rw [hc, Algebra.smul_def]⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc⟩ := hx
    obtain ⟨d, hd⟩ := hy
    exact ⟨c + d, by rw [map_add, hc, hd, Pi.add_apply, mul_add]⟩
  | smul a x _ hx =>
    obtain ⟨c, hc⟩ := hx
    exact ⟨a * c, by rw [map_mul, hc, Pi.smul_apply, Algebra.smul_def]; ring⟩
end

set_option autoImplicit false

namespace UpperTheory.Reformulated.B.LatticeCoordinatesCommonDenominator
theorem _root_.solution :
    ∀ (I : Formalism.MainNotions.S.AutInst),
      ∃ (b : NumberField.RingOfIntegers I.E),
        b ≠ (0 : NumberField.RingOfIntegers I.E) ∧
          ∀ y ∈ I.L, ∀ (i : Fin I.n), ∃ (c : NumberField.RingOfIntegers I.E), (↑c : I.E) = (↑b : I.E) * y i := by
  intro I
  exact UpperTheory.Reformulated.B.LatticeCoordinatesCommonDenominator.denom_of_fg I.L I.L_fg
end UpperTheory.Reformulated.B.LatticeCoordinatesCommonDenominator
