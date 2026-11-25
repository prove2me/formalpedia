-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_height_eq_of_isMaximal_mvPolynomial_fin_6b75e0ad698e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:41:58.852672+00:00
-- url     : https://prove2.me/submissions/75705896-a7b1-4ed9-91a3-f73459dcfab6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsMaxHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMaximalIdealHeightFG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (F : Type u) [Field F] :
    ∀ (n : ℕ) (M : Ideal (MvPolynomial (Fin n) F)), M.IsMaximal → M.height = n := by
  intro n
  induction n with
  | zero =>
    intro M hM
    have h := Ideal.height_le_ringKrullDim_of_ne_top hM.ne_top
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field] at h
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin, CharP.cast_eq_zero, add_zero] at h
    have h' : M.height ≤ 0 := by exact_mod_cast h
    simpa using h'
  | succ n ih =>
    intro M hM
    let e := (finSuccEquiv F n).toRingEquiv
    rw [← e.height_map M]
    set P : Ideal (Polynomial (MvPolynomial (Fin n) F)) := M.map e with hPdef
    have hP : P.IsMaximal := Ideal.map_isMaximal_of_equiv e
    have hc : (P.comap (Polynomial.C : MvPolynomial (Fin n) F →+* _)).IsMaximal :=
      Polynomial.isMaximal_comap_C_of_isJacobsonRing P
    have hlo : P.LiesOver (P.under (MvPolynomial (Fin n) F)) := ⟨rfl⟩
    rw [Polynomial.height_eq_height_add_one (P.under (MvPolynomial (Fin n) F)) P,
      ih (P.under (MvPolynomial (Fin n) F)) hc]
    norm_cast
end GroundTheory.Heights₂.Heights.NumbersDVR
