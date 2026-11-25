-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_subsingleton_H_one_of_smul_53085ae11a31
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:59:28.820009+00:00
-- url     : https://prove2.me/submissions/7ff2a108-ed06-46cc-8ec6-b9f4cc79a1fc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PClaimVanishCech
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_subsingleton_H_one_iff_a50a0634e5b7

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
open GroundTheory.Heights₂.Heights.Kleiman.SubSystem
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.SubSystem
theorem _root_.solution (F' G : SubSystem S x Ω) (σ : Ω) (hσ : σ ≠ 0)
    (hG : ∀ I z, z ∈ G.sub I ↔ ∃ y ∈ F'.sub I, z = σ * y) (hF : Subsingleton (F'.H 1)) :
    Subsingleton (G.H 1) := by
  unfold SubSystem.H at hF ⊢
  rw [Cech.subsingleton_H_one_iff] at hF ⊢
  have hdiv : ∀ I (z : G.sub I), σ⁻¹ * (z : Ω) ∈ F'.sub I := fun I z => by
    obtain ⟨y, hy, hzy⟩ := (hG I z).mp z.2
    rw [hzy, ← mul_assoc, inv_mul_cancel₀ hσ, one_mul]
    exact hy
  let φ : ∀ I, G.sub I →ₗ[S] F'.sub I := fun I =>
    { toFun := fun z => ⟨σ⁻¹ * z, hdiv I z⟩
      map_add' := fun a b => Subtype.ext (mul_add _ _ _)
      map_smul' := fun s a => Subtype.ext (by
        show σ⁻¹ * (s • (a : Ω)) = s • (σ⁻¹ * (a : Ω))
        rw [Algebra.smul_def, Algebra.smul_def]; ring) }
  let ψ : ∀ I, F'.sub I →ₗ[S] G.sub I := fun I =>
    { toFun := fun y => ⟨σ * y, (hG I _).mpr ⟨y, y.2, rfl⟩⟩
      map_add' := fun a b => Subtype.ext (mul_add _ _ _)
      map_smul' := fun s a => Subtype.ext (by
        show σ * (s • (a : Ω)) = s • (σ * (a : Ω))
        rw [Algebra.smul_def, Algebra.smul_def]; ring) }
  have hφ : ∀ I J h m, φ J (G.res I J h m) = F'.res I J h (φ I m) := fun _ _ _ _ => rfl
  have hψ : ∀ I J h m, ψ J (F'.res I J h m) = G.res I J h (ψ I m) := fun _ _ _ _ => rfl
  have hφd := Cech.mapC_d (R := S) (G := fun I => ↥(G.sub I)) (G' := fun I => ↥(F'.sub I)) φ hφ
  have hψd := Cech.mapC_d (R := S) (G := fun I => ↥(F'.sub I)) (G' := fun I => ↥(G.sub I)) ψ hψ
  intro z hz
  obtain ⟨w, hw⟩ := hF (Cech.mapC (R := S) (G := fun I => ↥(G.sub I)) (G' := fun I => ↥(F'.sub I)) φ 1 z) (by rw [← hφd, hz, map_zero])
  refine ⟨(Cech.mapC (R := S) (G := fun I => ↥(F'.sub I)) (G' := fun I => ↥(G.sub I)) ψ 0 w), ?_⟩
  rw [← hψd, hw]
  funext J
  apply Subtype.ext
  show σ * (σ⁻¹ * ((z J : G.sub J.1) : Ω)) = ((z J : G.sub J.1) : Ω)
  rw [← mul_assoc, mul_inv_cancel₀ hσ, one_mul]
end GroundTheory.Heights₂.Heights.Kleiman.SubSystem
