-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowFormBirational_proof_0e59d74b380d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:47:51.232074+00:00
-- url     : https://prove2.me/submissions/4261fe50-f28b-4f7a-a7a1-0b7eefbf3844

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormBirational
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_pderiv_aeval_eq_sum_be961d70ab0c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_pderiv_genSubst_db306a917fae
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_not_dvd_pderiv_of_degreeOf_pos_961cad1c5a74

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
namespace ChowFormBirational
theorem _root_.solution (h₁ : IncidenceGeneric.Statement)
    (h₂ : ChowFormMultiHomog.Statement) : ChowFormBirational.Statement := by
  intro F _ _ n k P g c hP hg hc
  have := hP.isPrime
  classical

  have hmem : ∀ h, h ∈ incIdeal P (k + 1) ↔ g ∣ h := by
    intro h
    rw [← hg.2 h, incIdeal]
    simp only [Submodule.mem_iInf, RingHom.mem_ker]
  have hg0 : aeval (genSubst (genPt P) c) g = 0 :=
    (h₁ F n (k + 1) P c hc g).1 ((hmem g).2 dvd_rfl)

  have hA : ∀ m, aeval (genSubst (genPt P) c) (pderiv (0, m) g) =
      C (genPt P m) * ∑ l, aeval (genSubst (genPt P) c) (pderiv (0, l) g) * C (c l) := by
    intro m
    have h := pderiv_aeval_eq_sum (genSubst (genPt P) c) (0, m) g
    rw [hg0, map_zero] at h
    simp only [pderiv_genSubst, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Fintype.sum_prod_type, Fin.sum_univ_succ,
      Fin.succ_ne_zero, if_false, Finset.sum_const_zero, add_zero] at h
    rw [eq_comm, sub_eq_zero] at h
    rw [h, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring

  obtain ⟨δ, hδ, hhom⟩ := h₂ F n (k + 1) P g hP hg
  obtain ⟨s, hs⟩ := support_nonempty.2 hg.1
  obtain ⟨l, hl⟩ : ∃ l, 0 < s (0, l) := by
    by_contra hcon
    push Not at hcon
    have hw := congrFun (hhom (mem_support_iff.1 hs)) 0
    have : (Finsupp.weight (groupWeight (k + 1) n) s) 0 = 0 := by
      rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
      refine Finset.sum_eq_zero fun x _ => ?_
      obtain ⟨x₁, x₂⟩ := x
      by_cases hx : x₁ = 0
      · subst hx; simp [Nat.le_zero.1 (hcon x₂)]
      · simp [groupWeight, hx]
    omega
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ∀ m, aeval (genSubst (genPt P) c) (pderiv (0, m) g) = C (genPt P m) * ρ :=
    ⟨_, hA⟩
  have hdeg : 0 < degreeOf (0, l) g := lt_of_lt_of_le hl (monomial_le_degreeOf _ hs)
  refine ⟨Pi.single l 1, ?_, fun m => ?_⟩
  · have hsum : (∑ l', C ((Pi.single l (1 : F) : Fin n → F) l') * pderiv (0, l') g) =
        pderiv (0, l) g := by
      rw [Finset.sum_eq_single l]
      · simp
      · intro b _ hb; simp [hb]
      · simp
    rw [hsum, hmem]
    exact not_dvd_pderiv_of_degreeOf_pos hg.1 hdeg
  · simp only [map_sum, map_mul, aeval_C, MvPolynomial.algebraMap_apply, hρ]
    simp only [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l' _ => ?_
    ring
end ChowFormBirational
end GroundTheory.Heights₂.Heights
