-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SnapperSubquotFinite_proof_a0fb55929bf2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:04:01.478961+00:00
-- url     : https://prove2.me/submissions/d8dc02fa-765d-413f-b8db-9e27d0735f86

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperSubquotFiniteSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperQuotAdd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperSubquotFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperSubquotientFinite_isNoetherianRing_chart_5008a51ed2a5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDSq_proof_00587d327cc8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechExact_proof_3af6e4d7b86c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_longExact_09831fd84e20
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotAdd_proof_a5f303e24f00


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
open SnapperQuotientAdditivity SnapperSubquotientFinite
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace SnapperSubquotFinite
theorem _root_.solution (hfin : SnapperFinite.Statement.{u, v, w}) :
    SnapperSubquotFinite.Statement.{u, v, w} := by
  intro k _ Ω _ _ N x E _ _ _ _ F F₁ F₂ hfg h1 h21 i
  have hfg1 : ∀ I, (F₁.sub I).FG := fun I => by
    have := isNoetherianRing_chart (S := k) I
    exact (hfg I).of_le (h1 I)
  have hfg2 : ∀ I, (F₂.sub I).FG := fun I => by
    have := isNoetherianRing_chart (S := k) I
    exact (hfg I).of_le ((h21 I).trans (h1 I))

  have hH : ∀ (G : SubFamily k x E), (∀ I, (G.sub I).FG) → ∀ j,
      FiniteDimensional k (Cech.Hdeg (fun I : Chart x => (G.sub I : Type v)) (fun _ => ⊤)
        G.toSubSystem.res j) := by
    intro G hG j
    have h := hfin k Ω N x E G hG 0 Fin.elim0 Fin.elim0 0 j
    change FiniteDimensional k ((G.toSubSystem.twist (twistSys k x 0)).H j) at h
    rw [SubSystem.twist_twistSys_zero] at h
    have : FiniteDimensional k (Cech.H (fun I : Chart x => (G.sub I : Type v)) G.toSubSystem.res j) := h
    exact (hdegTopEquiv _ _ j).symm.finiteDimensional
  have hdd := CechDSq.proof (N + 1) (support x) k (fun I : Chart x => (F₁.sub I : Type v))
    F₁.toSubSystem.res (fun _ _ _ _ _ => LinearMap.ext fun _ => rfl)
  let φ : ∀ I : Chart x, F₂.sub I →ₗ[k] F₁.sub I := fun I =>
    { toFun := fun y => ⟨y, h21 I y.2⟩, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let ψ : ∀ I : Chart x, F₁.sub I →ₗ[k] F₁.sub I ⧸ SubSystem.quotSub F₁.toSubSystem F₂.toSubSystem I :=
    fun I => (SubSystem.quotSub F₁.toSubSystem F₂.toSubSystem I).mkQ
  have L := Cech.longExact (R := k) (U := support x)
    (A := fun I : Chart x => (F₂.sub I : Type v)) (B := fun I : Chart x => (F₁.sub I : Type v))
    (C := fun I : Chart x => F₁.sub I ⧸ SubSystem.quotSub F₁.toSubSystem F₂.toSubSystem I)
    (ρA := F₂.toSubSystem.res) (ρB := F₁.toSubSystem.res)
    (ρC := SubSystem.quotRes F₁.toSubSystem F₂.toSubSystem)
    (dA := fun _ => ⊤) (dB := fun _ => ⊤) (dC := fun _ => ⊤) (φ := φ) (ψ := ψ)
  have L1 := L (fun _ _ _ _ => rfl)
  have L2 := L1 (fun _ _ _ _ => rfl)
  have L3 := L2 (fun _ _ _ => Submodule.mem_top) (fun _ _ _ => Submodule.mem_top)
  have L4 := L3 (fun I a b hab => Subtype.ext (congrArg (fun z : F₁.sub I => (z : E)) hab))
  have L5 := L4 (fun I y => (Submodule.Quotient.mk_eq_zero _).2 y.2)
  have L6 := L5 (fun I m _ hm => ⟨⟨m, (Submodule.Quotient.mk_eq_zero (SubSystem.quotSub F₁.toSubSystem F₂.toSubSystem I)).1 hm⟩, Submodule.mem_top, rfl⟩)
  have L7 := L6 (fun I z _ => (Submodule.Quotient.mk_surjective _ z).imp fun y hy => ⟨Submodule.mem_top, hy⟩)
  have L8 := L7 (fun _ _ _ _ _ => Submodule.mem_top)
  have liftZP_newton := L8 hdd
  obtain ⟨δ, hgδ, -⟩ := (liftZP_newton.2 i).2
  have := hH F₁ hfg1 i
  have := hH F₂ hfg2 (i + 1)
  have hC := Module.Finite.of_exact (f := Cech.mapHdeg _ _ ψ _ _ i) (g := δ.rangeRestrict)
    (LinearMap.exact_iff.2 (by rw [LinearMap.ker_rangeRestrict]; exact LinearMap.exact_iff.1 hgδ))
    δ.surjective_rangeRestrict
  exact (hdegTopEquiv _ _ i).finiteDimensional
end SnapperSubquotFinite
end GroundTheory.Heights₂.Heights.Kleiman
