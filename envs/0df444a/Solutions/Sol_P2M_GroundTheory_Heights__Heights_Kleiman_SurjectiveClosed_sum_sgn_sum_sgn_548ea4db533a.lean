-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SurjectiveClosed_sum_sgn_sum_sgn_548ea4db533a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:35:44.969527+00:00
-- url     : https://prove2.me/submissions/554c657c-0123-4a09-b722-0aed0e1df39b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTildeVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsIdealTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSurjectiveClosed
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SurjectiveClosed_sgn_mul_sgn_erase_swap_5eea5c9c3658

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.SurjectiveClosed
variable {n : ℕ}
variable {U : Finset (Fin n)} {A : Type*} [AddCommGroup A]
namespace GroundTheory.Heights₂.Heights.Kleiman.SurjectiveClosed
theorem _root_.solution (φ : Cell U → A) (L : Cech.Idx U 2) :
    ∑ j : L.1.1, Cech.sgn L.1.1 j • ∑ k : (Cech.face L j).1.1,
      Cech.sgn (Cech.face L j).1.1 k • φ (Cech.face (Cech.face L j) k).1 = 0 := by
  classical
  let ψ : Finset (Fin n) → A := fun T => if h : T.Nonempty ∧ T ⊆ U then φ ⟨T, h⟩ else 0
  have hψ : ∀ c : Cell U, φ c = ψ c.1 := fun c => by simp only [ψ, dif_pos c.2]
  have hin : ∀ j : L.1.1, (∑ k : (Cech.face L j).1.1,
      Cech.sgn (Cech.face L j).1.1 k • φ (Cech.face (Cech.face L j) k).1) =
        ∑ k ∈ L.1.1.erase j, Cech.sgn (L.1.1.erase j) k • ψ ((L.1.1.erase j).erase k) := by
    intro j
    rw [← Finset.sum_coe_sort (L.1.1.erase j)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hψ]
    rfl
  simp only [hin]
  rw [Finset.sum_coe_sort L.1.1 (fun j => Cech.sgn L.1.1 j •
    ∑ k ∈ L.1.1.erase j, Cech.sgn (L.1.1.erase j) k • ψ ((L.1.1.erase j).erase k))]
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_sigma' L.1.1 (fun j => L.1.1.erase j)]
  refine Finset.sum_involution (fun p _ => ⟨p.2, p.1⟩) ?_ ?_ ?_ ?_
  · rintro ⟨j, k⟩ hp
    obtain ⟨hj, hk⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hkj, hk⟩ := Finset.mem_erase.mp hk
    simp only
    rw [Finset.erase_right_comm, sgn_mul_sgn_erase_swap hj hk (Ne.symm hkj), neg_smul]
    exact neg_add_cancel _
  · rintro ⟨j, k⟩ hp _ heq
    obtain ⟨-, hk⟩ := Finset.mem_sigma.mp hp
    exact (Finset.mem_erase.mp hk).1 (Sigma.mk.inj_iff.mp heq).1
  · rintro ⟨j, k⟩ hp
    obtain ⟨hj, hk⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hkj, hk⟩ := Finset.mem_erase.mp hk
    exact Finset.mem_sigma.mpr ⟨hk, Finset.mem_erase.mpr ⟨Ne.symm hkj, hj⟩⟩
  · rintro ⟨j, k⟩ _
    rfl
end GroundTheory.Heights₂.Heights.Kleiman.SurjectiveClosed
