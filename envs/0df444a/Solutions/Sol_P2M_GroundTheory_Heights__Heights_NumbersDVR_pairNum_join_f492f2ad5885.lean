-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_pairNum_join_f492f2ad5885
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:36:59.793738+00:00
-- url     : https://prove2.me/submissions/d9ef41c4-9962-46c3-90b3-6489dffc4fd4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBundles
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSubQuotient
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_classNum_rename_e13bf3796dec
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_rename_psumExpansion_d622675f0759

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
variable {K : Type*} [DecidableEq K] {ι : K → Type*}
  {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {r m N : ℕ} (P : Ideal (MRing ι O)) (e : Fin r ⊕ Fin m ≃ Fin N)
    (xU xU' : Fin r → K → ℤ) (xV xV' : Fin m → K → ℤ) (fU gU : Fin r → MRing ι O)
    (fV gV : Fin m → MRing ι O) (k : ℕ) (Q : List (K → ℤ)) :
    pairNum P (fun i => Sum.elim xU xV (e.symm i)) (fun i => Sum.elim xU' xV' (e.symm i))
        (fun i => Sum.elim fU fV (e.symm i)) (fun i => Sum.elim gU gV (e.symm i))
        (psumExpansion N k) Q =
      pairNum P xU xU' fU gU (psumExpansion r k) Q + pairNum P xV xV' fV gV (psumExpansion m k) Q := by
  unfold pairNum
  rw [← e.sum_comp, Fintype.sum_sum_type]
  have hl : Function.Injective (fun a : Fin r => e (Sum.inl a)) :=
    e.injective.comp Sum.inl_injective
  have hr : Function.Injective (fun b : Fin m => e (Sum.inr b)) :=
    e.injective.comp Sum.inr_injective
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Equiv.symm_apply_apply, Sum.elim_inl]
    congr 1
    funext W
    rw [← rename_psumExpansion (fun a : Fin r => e (Sum.inl a)) k a,
      classNum_rename _ (hl.sumMap hl)]
    congr 1
    funext t
    rcases t with a' | a' <;> simp
  · refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Equiv.symm_apply_apply, Sum.elim_inr]
    congr 1
    funext W
    rw [← rename_psumExpansion (fun b : Fin m => e (Sum.inr b)) k b,
      classNum_rename _ (hr.sumMap hr)]
    congr 1
    funext t
    rcases t with b' | b' <;> simp
end GroundTheory.Heights₂.Heights.NumbersDVR
