-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotAdd_proof_a5f303e24f00
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:26:30.844345+00:00
-- url     : https://prove2.me/submissions/b79dd148-9dd5-4461-8d93-c494d253f2c1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotAddSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperSubquotFiniteSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDSq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperQuotAdd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_altSum_eq_7363a236564f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_hdeg_subsingleton_d600335fc570
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_idx_isEmpty_3f8167bd3da0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_quotRes_comp_b9c0a60636d5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_quotInl_comm_79891e2026a5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_quotPr_comm_61b60b23a5db
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_quotInl_injective_dcb53ac094c3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_quotPr_quotInl_baf1d4324949
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_exists_quotInl_e9e32e11d485
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_quotPr_surjective_05066ea6fa37
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_finrank_quotH_3c5908ab69a8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDSq_proof_00587d327cc8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechExact_proof_3af6e4d7b86c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_longExact_09831fd84e20


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
universe u v w
set_option maxHeartbeats 1000000
open SnapperQuotientAdditivity
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace SnapperQuotAdd
theorem _root_.solution (hfin : SnapperSubquotFinite.Statement.{u, v, w}) :
    SnapperQuotAdd.Statement.{u, v, w} := by
  intro k _ Ω _ _ N x E _ _ _ _ F₁ F₂ F₃ hfg h21 h32
  have h31 : ∀ I, F₃.sub I ≤ F₁.sub I := fun I => (h32 I).trans (h21 I)
  have hdd := CechDSq.proof (N + 1) (support x) k
    (fun I : Chart x => F₁.sub I ⧸ SubSystem.quotSub F₁.toSubSystem F₃.toSubSystem I)
    (SubSystem.quotRes F₁.toSubSystem F₃.toSubSystem) (quotRes_comp F₁.toSubSystem F₃.toSubSystem)
  have L := Cech.longExact (R := k) (U := support x)
    (A := fun I : Chart x => F₂.sub I ⧸ SubSystem.quotSub F₂.toSubSystem F₃.toSubSystem I)
    (B := fun I : Chart x => F₁.sub I ⧸ SubSystem.quotSub F₁.toSubSystem F₃.toSubSystem I)
    (C := fun I : Chart x => F₁.sub I ⧸ SubSystem.quotSub F₁.toSubSystem F₂.toSubSystem I)
    (ρA := SubSystem.quotRes F₂.toSubSystem F₃.toSubSystem)
    (ρB := SubSystem.quotRes F₁.toSubSystem F₃.toSubSystem)
    (ρC := SubSystem.quotRes F₁.toSubSystem F₂.toSubSystem)
    (dA := fun _ => ⊤) (dB := fun _ => ⊤) (dC := fun _ => ⊤)
    (φ := quotInl F₁.toSubSystem F₂.toSubSystem F₃.toSubSystem h21)
    (ψ := quotPr F₁.toSubSystem F₂.toSubSystem F₃.toSubSystem h32)
  have L1 := L (quotInl_comm _ _ _ h21)
  have L2 := L1 (quotPr_comm _ _ _ h32)
  have L3 := L2 (fun _ _ _ => Submodule.mem_top) (fun _ _ _ => Submodule.mem_top)
  have L4 := L3 (quotInl_injective _ _ _ h21)
  have L5 := L4 (quotPr_quotInl _ _ _ h21 h32)
  have L6 := L5 (fun I m _ hm => (exists_quotInl _ _ _ h21 h32 I m hm).imp fun y hy => ⟨Submodule.mem_top, hy⟩)
  have L7 := L6 (fun I m _ => (quotPr_surjective _ _ _ h32 I m).imp fun y hy => ⟨Submodule.mem_top, hy⟩)
  have L8 := L7 (fun _ _ _ _ _ => Submodule.mem_top)
  have liftZP_newton := L8 hdd
  have h0 := liftZP_newton.1
  have hex := liftZP_newton.2
  choose δ hgδ hδf using fun i => (hex i).2
  have fin : ∀ (G₁ G₂ : SubFamily k x E), (∀ I, G₁.sub I ≤ F₁.sub I) → (∀ I, G₂.sub I ≤ G₁.sub I) → ∀ i,
      FiniteDimensional k (Cech.Hdeg (fun I : Chart x => G₁.sub I ⧸ SubSystem.quotSub G₁.toSubSystem G₂.toSubSystem I)
        (fun _ => ⊤) (SubSystem.quotRes G₁.toSubSystem G₂.toSubSystem) i) := by
    intro G₁ G₂ h1 h2 i
    have : FiniteDimensional k (Cech.H (fun I : Chart x => G₁.sub I ⧸ SubSystem.quotSub G₁.toSubSystem G₂.toSubSystem I)
        (SubSystem.quotRes G₁.toSubSystem G₂.toSubSystem) i) := hfin k Ω N x E F₁ G₁ G₂ hfg h1 h2 i
    exact (hdegTopEquiv _ _ i).symm.finiteDimensional
  have := fin F₂ F₃ h21 h32
  have := fin F₁ F₃ (fun _ => le_rfl) h31
  have := fin F₁ F₂ (fun _ => le_rfl) h21
  have key := altSum_eq _ _ _ _ _ δ h0 (fun i => (hex i).1) hgδ hδf N
  have := idx_isEmpty x
  have hsub := hdeg_subsingleton (fun I : Chart x => F₂.sub I ⧸ SubSystem.quotSub F₂.toSubSystem F₃.toSubSystem I)
    (fun _ => (⊤ : Submodule k _)) (SubSystem.quotRes F₂.toSubSystem F₃.toSubSystem) (N + 1)
  have hδN : Module.finrank k (LinearMap.range (δ N)) = 0 := by
    have hz : Module.finrank k (Cech.Hdeg (fun I : Chart x => F₂.sub I ⧸ SubSystem.quotSub F₂.toSubSystem F₃.toSubSystem I)
        (fun _ => (⊤ : Submodule k _)) (SubSystem.quotRes F₂.toSubSystem F₃.toSubSystem) (N + 1)) = 0 :=
      Module.finrank_zero_of_subsingleton
    exact Nat.eq_zero_of_le_zero ((Submodule.finrank_le (LinearMap.range (δ N))).trans hz.le)
  rw [hδN] at key
  simp only [Nat.cast_zero, mul_zero, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib] at key
  simp only [eulerCharQuot, finrank_quotH]
  linarith
end SnapperQuotAdd
end GroundTheory.Heights₂.Heights.Kleiman
