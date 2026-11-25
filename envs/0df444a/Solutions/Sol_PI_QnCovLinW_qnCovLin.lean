-- Prove2me | solution 1 for PI.QnCovLinW.qnCovLin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:31:40.385082+00:00
-- url     : https://prove2.me/submissions/e4fa0629-5bc6-48db-aa16-cac190abb0cb

import Definitions.Def_Formalism_PeriodIntegrals_ContractionsCovariantIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantLinearProduct_OfFnProdSmul
import Theorems.Thm_PI_QnCovLinW_ofFn_prod_sum
import Theorems.Thm_PI_QnCovLinW_ofFn_prod_smul
import Theorems.Thm_PI_QnCovLinW_tm_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open PI PI.QnCovLinW
open Formalism.REAL Formalism.FourierDecayAlt.Q
namespace PI.QnCovLinW
theorem _root_.solution : PI.QnCovLin := by
  intro A _ _ n t E P Q hQP a b u
  have key : ∀ σ : Equiv.Perm (Fin t),
      (List.ofFn fun k : Fin t => Tm (Econj E P Q) (u - (k : ℂ)) (a (σ k)) (b k)).prod =
        ∑ c : Fin t → Fin n, ∑ d : Fin t → Fin n,
          ((∏ k, P (c k) (a (σ k))) * ∏ k, Q (b k) (d k)) •
            (List.ofFn fun k : Fin t => Tm E (u - (k : ℂ)) (c k) (d k)).prod := by
    intro σ
    simp only [tm_conj E P Q hQP]
    rw [ofFn_prod_sum]
    have hs : ∀ c : Fin t → Fin n × Fin n,
        (List.ofFn fun k => (P (c k).1 (a (σ k)) * Q (b k) (c k).2) • Tm E (u - (k : ℂ)) (c k).1 (c k).2).prod =
        (fun p : (Fin t → Fin n) × (Fin t → Fin n) => ((∏ k, P (p.1 k) (a (σ k))) * ∏ k, Q (b k) (p.2 k)) •
            (List.ofFn fun k : Fin t => Tm E (u - (k : ℂ)) (p.1 k) (p.2 k)).prod)
          (Equiv.arrowProdEquivProdArrow (Fin t) (fun _ => Fin n) (fun _ => Fin n) c) := by
      intro c
      rw [ofFn_prod_smul, Finset.prod_mul_distrib]
      rfl
    rw [Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow (Fin t) (fun _ => Fin n) (fun _ => Fin n)) _
      (fun p : (Fin t → Fin n) × (Fin t → Fin n) => ((∏ k, P (p.1 k) (a (σ k))) * ∏ k, Q (b k) (p.2 k)) •
            (List.ofFn fun k : Fin t => Tm E (u - (k : ℂ)) (p.1 k) (p.2 k)).prod) hs,
      Fintype.sum_prod_type]
  have reidx : ∀ σ : Equiv.Perm (Fin t),
      ∑ c : Fin t → Fin n, ∑ d : Fin t → Fin n, ((Equiv.Perm.sign σ : ℤ) : A) *
        (((∏ k, P (c k) (a (σ k))) * ∏ k, Q (b k) (d k)) •
          (List.ofFn fun k : Fin t => Tm E (u - (k : ℂ)) (c k) (d k)).prod) =
      ∑ c : Fin t → Fin n, ∑ d : Fin t → Fin n, ((∏ k, P (c k) (a k)) * ∏ k, Q (b k) (d k)) •
        (((Equiv.Perm.sign σ : ℤ) : A) *
          (List.ofFn fun k : Fin t => Tm E (u - (k : ℂ)) (c (σ k)) (d k)).prod) := by
    intro σ
    rw [← (Equiv.arrowCongr σ.symm (Equiv.refl (Fin n))).sum_comp]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, Equiv.symm_symm, id]
    have hp : ∏ k, P (c (σ k)) (a (σ k)) = ∏ k, P (c k) (a k) := Equiv.prod_comp σ (fun k => P (c k) (a k))
    rw [mul_smul_comm, hp]
  simp only [qminor, key, Finset.mul_sum]
  simp only [reidx, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
end PI.QnCovLinW
