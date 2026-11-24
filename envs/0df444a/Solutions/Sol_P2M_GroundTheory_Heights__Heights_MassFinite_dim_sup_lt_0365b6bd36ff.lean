-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MassFinite_dim_sup_lt_0365b6bd36ff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:57.326256+00:00
-- url     : https://prove2.me/submissions/8a888451-bf55-47f3-b702-655fbf5ad35b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalGraphMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMassFinite

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
open MvPolynomial MeasureTheory Matrix
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.MassFinite
namespace GroundTheory.Heights₂.Heights.MassFinite
theorem _root_.solution {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (hJ : J.IsPrime)
    (hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d) (f : MvPolynomial (Fin n) ℂ) (hf : f ∉ J) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {f})) < d := by
  have := hJ
  have hr : Ideal.Quotient.mk J f ∈ nonZeroDivisors (MvPolynomial (Fin n) ℂ ⧸ J) :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  have h := ringKrullDim_succ_le_of_surjective
    (Ideal.Quotient.factor (le_sup_left : J ≤ J ⊔ Ideal.span {f}))
    (Ideal.Quotient.factor_surjective _) hr
    (by
      rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  rw [hd] at h
  generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {f})) = x at h ⊢
  induction x using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe e =>
    have h' : e + 1 ≤ (d : ℕ∞) := by exact_mod_cast h
    have he : e ≠ ⊤ := fun he => by simp [he] at h'
    exact_mod_cast (ENat.add_one_le_iff he).mp h'
end GroundTheory.Heights₂.Heights.MassFinite
