-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_CechDSq_proof_00587d327cc8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:21:36.495623+00:00
-- url     : https://prove2.me/submissions/42334c4c-98bd-4859-8ddb-19ea79473cfa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCechDSq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDSq
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDSq_sgn_mul_sgn_swap_491f9f307a17
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDSq_restrictTo_eq_6615ffe29c1d

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
noncomputable section
universe u v
open CechDSq
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace CechDSq
theorem _root_.solution : CechDSq.Statement := by
  intro n U R _ G _ _ ρ hρ i s
  classical
  funext K
  have hcomp : ∀ (I J L : Cell U) (h₁ : I.1 ⊆ J.1) (h₂ : J.1 ⊆ L.1) (x : G I),
      ρ J L h₂ (ρ I J h₁ x) = ρ I L (h₁.trans h₂) x := fun I J L h₁ h₂ x =>
    LinearMap.congr_fun (hρ I J L h₁ h₂) x

  let f : (Σ _ : Fin n, Fin n) → G K.1 := fun p =>
    (Cech.sgn K.1.1 p.1 * Cech.sgn (K.1.1.erase p.1) p.2) •
      restrictTo (ρ := ρ) s K.1 ((K.1.1.erase p.1).erase p.2)
  have step : ∀ k : K.1.1, Cech.sgn K.1.1 k • ρ (Cech.face K k).1 K.1 (Cech.face_subset K k)
      (Cech.d G ρ i s (Cech.face K k)) = ∑ j ∈ K.1.1.erase k, f ⟨k, j⟩ := by
    intro k
    rw [Cech.d_apply, map_sum, Finset.smul_sum]
    refine Eq.trans ?_ (Finset.sum_coe_sort (K.1.1.erase k) (fun j => f ⟨k, j⟩))
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, smul_smul, hcomp, ← restrictTo_eq]
    rfl
  show Cech.d G ρ (i + 1) (Cech.d G ρ i s) K = 0
  rw [Cech.d_apply, Finset.sum_congr rfl fun k _ => step k,
    Finset.sum_coe_sort K.1.1 (fun k => ∑ j ∈ K.1.1.erase k, f ⟨k, j⟩),
    Finset.sum_sigma' K.1.1 (fun k => K.1.1.erase k) (fun k j => f ⟨k, j⟩)]
  refine Finset.sum_involution (fun p _ => ⟨p.2, p.1⟩) ?_ ?_ ?_ ?_
  · rintro ⟨k, j⟩ hp
    obtain ⟨hk, hj⟩ := Finset.mem_sigma.1 hp
    obtain ⟨hne, hj⟩ := Finset.mem_erase.1 hj
    simp only [f]
    rw [Finset.erase_right_comm, sgn_mul_sgn_swap hk hj hne, neg_smul, neg_add_cancel]
  · rintro ⟨k, j⟩ hp - h
    obtain ⟨hne, -⟩ := Finset.mem_erase.1 (Finset.mem_sigma.1 hp).2
    exact hne (congrArg Sigma.fst h)
  · rintro ⟨k, j⟩ hp
    obtain ⟨hk, hj⟩ := Finset.mem_sigma.1 hp
    obtain ⟨hne, hj⟩ := Finset.mem_erase.1 hj
    exact Finset.mem_sigma.2 ⟨hj, Finset.mem_erase.2 ⟨hne.symm, hk⟩⟩
  · rintro ⟨k, j⟩ -
    rfl
end CechDSq
end GroundTheory.Heights₂.Heights.Kleiman
