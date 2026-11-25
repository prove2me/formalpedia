-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DominantPrimitiveFibres_dim_eq_152f4491059c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:29:41.070251+00:00
-- url     : https://prove2.me/submissions/fcf49d33-a4d9-4444-b310-0200da75d7ad

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StDominantPrimitiveFibres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PDominantFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitiveElementFibres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PDominantPrimitiveFibres
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DominantFibreBound_trdeg_le_5ed0a4f11660


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ComplexSets
open GroundTheory.Heights₂.Heights.DominantPrimitiveFibres
namespace GroundTheory.Heights₂.Heights.DominantPrimitiveFibres
theorem _root_.solution (hG : GenericProjectionFinite.Statement) {n d : ℕ} (Q : Ideal (MvPolynomial (Fin n) ℂ))
    (A : Matrix (Fin d) (Fin n) ℂ) (hQ : Q.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ Q) ≤ ((d : ℕ) : WithBot ℕ∞))
    (hinj : Function.Injective (projHom Q A)) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ Q) = ((d : ℕ) : WithBot ℕ∞) := by
  have := hQ
  obtain ⟨e, he⟩ : ∃ e : ℕ, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ Q) = ((e : ℕ) : WithBot ℕ∞) := by
    have h0 := ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (Fin n) ℂ ⧸ Q)
    generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ Q) = k at h0 hdim ⊢
    induction k using WithBot.recBotCoe with
    | bot => simp at h0
    | coe k =>
      induction k using ENat.recTopCoe with
      | top => exact absurd hdim (not_le.2 (WithBot.coe_lt_coe.2 (ENat.natCast_lt_top d)))
      | coe k => exact ⟨k, rfl⟩
  obtain ⟨A', hA'⟩ := (hG n e Q hQ he).2.1
  have h1 := DominantFibreBound.trdeg_le Q A' hA'
  have hproj : projHom Q A = aeval (fun i => Ideal.Quotient.mk Q (linPoly A i)) := by
    rw [projHom, pullback, comp_aeval]
    rfl
  have hind : AlgebraicIndependent ℂ (fun i => Ideal.Quotient.mk Q (linPoly A i)) := by
    rw [algebraicIndependent_iff_injective_aeval, ← hproj]
    exact hinj
  have h2 := hind.cardinalMk_le_trdeg
  have hde : d ≤ e := by
    have := h2.trans h1
    simpa using this
  have hed : e ≤ d := by
    rw [he] at hdim
    exact_mod_cast hdim
  rw [he, le_antisymm hed hde]
end GroundTheory.Heights₂.Heights.DominantPrimitiveFibres
