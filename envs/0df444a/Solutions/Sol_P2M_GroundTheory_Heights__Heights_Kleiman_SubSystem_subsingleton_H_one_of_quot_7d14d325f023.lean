-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_subsingleton_H_one_of_quot_7d14d325f023
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:01:39.938087+00:00
-- url     : https://prove2.me/submissions/10eec2d6-87e9-4f8a-8150-fc2ccd9ec981

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PClaimVanishCech
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_subsingleton_H_one_iff_a50a0634e5b7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_d_one_d_zero_613304503aca
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_d_one_d_zero_2a2432191898

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
variable {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
set_option maxHeartbeats 1000000
namespace GroundTheory.Heights₂.Heights.Kleiman.SubSystem
theorem _root_.solution (F G : SubSystem S x E)
    (hGF : ∀ I, ∀ y ∈ G.sub I, y ∈ F.sub I) (hG : Subsingleton (G.H 1))
    (hQ : Subsingleton (quotH F G 1)) : Subsingleton (F.H 1) := by
  unfold SubSystem.H at hG ⊢
  unfold quotH at hQ
  rw [Cech.subsingleton_H_one_iff] at hG hQ ⊢
  intro z hz
  let q : ∀ I, F.sub I →ₗ[S] (F.sub I ⧸ quotSub F G I) := fun I => (quotSub F G I).mkQ
  have hq : ∀ I J h m, q J (F.res I J h m) = quotRes F G I J h (q I m) := fun _ _ _ _ => rfl
  have hqd := Cech.mapC_d (R := S) (G := fun I => ↥(F.sub I))
    (G' := fun I => ↥(F.sub I) ⧸ quotSub F G I) q hq
  obtain ⟨wb, hwb⟩ := hQ (Cech.mapC (R := S) (G := fun I => ↥(F.sub I)) (G' := fun I => ↥(F.sub I) ⧸ quotSub F G I) q 1 z) (by rw [← hqd, hz, map_zero])
  choose w hw using fun I : Cech.Idx (support x) 0 => Submodule.Quotient.mk_surjective _ (wb I)
  have hmw : (Cech.mapC (R := S) (G := fun I => ↥(F.sub I)) (G' := fun I => ↥(F.sub I) ⧸ quotSub F G I) q 0 w) = wb := funext hw
  have hr : (Cech.mapC (R := S) (G := fun I => ↥(F.sub I)) (G' := fun I => ↥(F.sub I) ⧸ quotSub F G I) q 1 (z - Cech.d (fun I => F.sub I) F.res 0 w)) = 0 := by
    rw [map_sub, hqd 0, hmw, hwb]
    exact @sub_eq_zero_of_eq (Cech.Cochain (fun I => ↥(F.sub I) ⧸ quotSub F G I) 1) _ _ _ rfl
  have hrG : ∀ J, (((z - Cech.d (fun I => F.sub I) F.res 0 w) J : F.sub J.1) : E) ∈ G.sub J.1 :=
    fun J => (Submodule.Quotient.mk_eq_zero (quotSub F G J.1)).mp (congrFun hr J)
  let ι : ∀ I, G.sub I →ₗ[S] F.sub I := fun I =>
    { toFun := fun y => ⟨y, hGF I y y.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hι : ∀ I J h m, ι J (G.res I J h m) = F.res I J h (ι I m) := fun _ _ _ _ => rfl
  have hιd := Cech.mapC_d (R := S) (G := fun I => ↥(G.sub I)) (G' := fun I => ↥(F.sub I)) ι hι
  have hιinj : ∀ i, Function.Injective (Cech.mapC (R := S) (G := fun I => ↥(G.sub I)) (G' := fun I => ↥(F.sub I)) ι i) := fun i a b hab =>
    funext fun I => Subtype.ext (congrArg (fun c => ((c I : F.sub I.1) : E)) hab)
  obtain ⟨g, hg⟩ : ∃ g : Cech.Cochain (fun I => ↥(G.sub I)) 1,
      (Cech.mapC (R := S) (G := fun I => ↥(G.sub I)) (G' := fun I => ↥(F.sub I)) ι 1 g) =
        z - Cech.d (fun I => F.sub I) F.res 0 w := ⟨fun J => ⟨_, hrG J⟩, rfl⟩
  have hdg : Cech.d (fun I => ↥(G.sub I)) G.res 1 g = 0 := by
    have h2 : (Cech.mapC (R := S) (G := fun I => ↥(G.sub I)) (G' := fun I => ↥(F.sub I)) ι (1 + 1)
        (Cech.d (fun I => ↥(G.sub I)) G.res 1 g)) = 0 := by
      rw [hιd 1 g, hg, map_sub, hz, d_one_d_zero, sub_zero]
    exact hιinj (1 + 1) (h2.trans (LinearMap.map_zero _).symm)
  obtain ⟨v, hv⟩ := hG g hdg
  refine ⟨w + (Cech.mapC (R := S) (G := fun I => ↥(G.sub I)) (G' := fun I => ↥(F.sub I)) ι 0 v), ?_⟩
  rw [map_add, ← hιd, hv, hg, add_sub_cancel]
end GroundTheory.Heights₂.Heights.Kleiman.SubSystem
