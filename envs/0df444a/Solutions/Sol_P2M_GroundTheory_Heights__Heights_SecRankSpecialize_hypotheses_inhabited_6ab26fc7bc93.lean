-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SecRankSpecialize_hypotheses_inhabited_6ab26fc7bc93
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:08:33.359088+00:00
-- url     : https://prove2.me/submissions/746187ab-37ea-4a8a-b32a-8821366eb2b8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSecRankSpecialize

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
namespace GroundTheory.Heights₂.Heights
namespace SecRankSpecialize
theorem _root_.solution :
    letI : Algebra (PowerSeries ℚ) ℚ := (PowerSeries.constantCoeff (R := ℚ)).toAlgebra
    IsDomain (PowerSeries ℚ) ∧ IsLocalRing (PowerSeries ℚ) ∧
      IsFractionRing (PowerSeries ℚ) (FractionRing (PowerSeries ℚ)) ∧
      Function.Surjective (algebraMap (PowerSeries ℚ) ℚ) ∧
      Module.Finite (PowerSeries ℚ)
        (Vertical.SecAlg (⊥ : Ideal (MvPolynomial (Fin 1) (PowerSeries ℚ)))
          (fun _ : Vertical.Par 0 1 => (1 : PowerSeries ℚ))) := by
  letI : Algebra (PowerSeries ℚ) ℚ := (PowerSeries.constantCoeff (R := ℚ)).toAlgebra
  refine ⟨inferInstance, inferInstance, inferInstance,
    fun a => ⟨PowerSeries.C a, by simp [RingHom.algebraMap_toAlgebra]⟩, ?_⟩
  set I := Vertical.secIdeal (⊥ : Ideal (MvPolynomial (Fin 1) (PowerSeries ℚ)))
    (fun _ : Vertical.Par 0 1 => (1 : PowerSeries ℚ))
  have hX : ∀ j : Fin 1, Ideal.Quotient.mk I (X j) = 1 := by
    intro j
    rw [Fin.fin_one_eq_zero j, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk I), ← map_sub,
      Ideal.Quotient.eq_zero_iff_mem]
    refine Ideal.mem_sup_right (Ideal.subset_span ?_)
    simp [Vertical.chartForm, linForm]
  have hrange : ∀ p : MvPolynomial (Fin 1) (PowerSeries ℚ),
      Ideal.Quotient.mk I p ∈ Set.range (algebraMap (PowerSeries ℚ) (Vertical.SecAlg ⊥
        (fun _ : Vertical.Par 0 1 => (1 : PowerSeries ℚ)))) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => exact ⟨a, rfl⟩
    | add p q hp hq =>
      obtain ⟨a, ha⟩ := hp
      obtain ⟨b, hb⟩ := hq
      exact ⟨a + b, by rw [map_add, map_add, ha, hb]⟩
    | mul_X p j hp =>
      obtain ⟨a, ha⟩ := hp
      exact ⟨a, by rw [map_mul, hX, mul_one, ha]⟩
  refine Module.Finite.of_surjective (Algebra.linearMap (PowerSeries ℚ) _) ?_
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact hrange p
end SecRankSpecialize
end GroundTheory.Heights₂.Heights
