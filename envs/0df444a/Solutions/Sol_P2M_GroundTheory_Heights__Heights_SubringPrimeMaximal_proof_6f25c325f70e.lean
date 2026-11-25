-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SubringPrimeMaximal_proof_6f25c325f70e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:47:48.279854+00:00
-- url     : https://prove2.me/submissions/c0c29bf2-460e-432b-aecf-f8e88da2d007

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightSubringPrimeMaximal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PSubringPrimeMaximal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_subalgebra_isAlgebraic_int_021dcf6f6296

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
open NumberField Polynomial
namespace GroundTheory.Heights₂.Heights
namespace SubringPrimeMaximal
theorem _root_.solution : SubringPrimeMaximal.Statement := by
  intro K _ _ O q hq hq0
  obtain ⟨b, hbq, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hq0
  set J : Ideal ℤ := q.comap (algebraMap ℤ O) with hJ
  have hJ0 : J ≠ ⊥ :=
    Ideal.comap_ne_bot_of_algebraic_mem hb0 hbq (subalgebra_isAlgebraic_int O b)
  have hJp : J.IsPrime := Ideal.comap_isPrime _ _
  have hJm : J.IsMaximal := hJp.isMaximal hJ0
  let _ : Field (ℤ ⧸ J) := Ideal.Quotient.field J
  have hJtop : J ≠ ⊤ := hJm.ne_top
  have hint : Algebra.IsIntegral (ℤ ⧸ J) (O ⧸ q) := by
    constructor
    intro z
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨P, hP0, hPy⟩ := subalgebra_isAlgebraic_int O y
    set Q := P.primPart
    have hQy : aeval y Q = 0 := aeval_primPart_eq_zero hP0 hPy
    have hQmap : Q.map (Ideal.Quotient.mk J) ≠ 0 := by
      intro h
      obtain ⟨g, hg⟩ := (inferInstance : Submodule.IsPrincipal J)
      have hdvd : C g ∣ Q := by
        rw [C_dvd_iff_dvd_coeff]
        intro i
        have : Q.coeff i ∈ J := by
          rw [← Ideal.Quotient.eq_zero_iff_mem, ← coeff_map, h, coeff_zero]
        rw [hg, Submodule.mem_span_singleton] at this
        obtain ⟨a, ha⟩ := this
        exact ⟨a, by rw [← ha, smul_eq_mul, mul_comm]⟩
      have hu := isPrimitive_primPart P g hdvd
      apply hJtop
      rw [hg, Ideal.submodule_span_eq, Ideal.span_singleton_eq_top]
      exact hu
    refine IsAlgebraic.isIntegral ⟨Q.map (Ideal.Quotient.mk J), hQmap, ?_⟩
    have e : Q.map (Ideal.Quotient.mk J) = Q.map (algebraMap ℤ (ℤ ⧸ J)) := rfl
    rw [e, aeval_def, eval₂_map, show (algebraMap (ℤ ⧸ J) (O ⧸ q)).comp (algebraMap ℤ (ℤ ⧸ J)) =
      algebraMap ℤ (O ⧸ q) from RingHom.ext_int _ _, ← aeval_def]
    have := aeval_algHom_apply (Ideal.Quotient.mkₐ ℤ q) y Q
    rw [Ideal.Quotient.mkₐ_eq_mk] at this
    rw [this, hQy, map_zero]
  have hfield : IsField (ℤ ⧸ J) := Field.toIsField _
  exact Ideal.Quotient.maximal_of_isField q
    ((Algebra.IsIntegral.isField_iff_isField (RingHom.injective _)).mp hfield)
end SubringPrimeMaximal
end GroundTheory.Heights₂.Heights
