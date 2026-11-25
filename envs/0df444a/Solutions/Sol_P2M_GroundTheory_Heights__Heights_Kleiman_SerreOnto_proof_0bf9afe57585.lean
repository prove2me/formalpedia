-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SerreOnto_proof_0bf9afe57585
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:53:39.784093+00:00
-- url     : https://prove2.me/submissions/c14b9254-39a3-47cf-bcd8-1d1c993bffe9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerreOnto
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_single_one_mem_freeGraded_bff34005d702
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_GradedPMod_exists_gens_61d7d2f88479
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_freeMap_mem_9c019e288fdd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_freeMap_surjective_0efadb208268
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_cohomMap_toH0_db774a862a06
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_cohomMap_leftInverse_b296a5e4e453
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_toH0_surjective_of_exact_384eb577a921

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
universe u v w w'
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace SerreOnto
theorem _root_.solution (hC : CechExact.Statement.{u, max u v})
    (hF : SerreFree.Statement.{u, max u v}) (hV : SerreVanish.Statement.{u, max u v}) :
    SerreOnto.Statement.{u, v} := by
  intro S _ _ N M _ _ _ _ 𝓜 hM
  obtain ⟨r, g, deg, hg, hspan⟩ := 𝓜.exists_gens hM

  let eM : M ≃ₗ[Poly S N] ULift.{u} M := ULift.moduleEquiv.symm
  let eF : (Fin r → Poly S N) ≃ₗ[Poly S N] ULift.{v} (Fin r → Poly S N) := ULift.moduleEquiv.symm
  let 𝓜L := 𝓜.transport eM
  let 𝓕 := (freeGraded S N deg).transport eF
  let φ : GradedHom 𝓕 𝓜L :=
    { toLin := eM.toLinearMap ∘ₗ freeMap S N g ∘ₗ eF.symm.toLinearMap
      map_piece := by
        rintro c _ ⟨f, hf, rfl⟩
        exact ⟨freeMap S N g f, freeMap_mem 𝓜 hg c hf, by simp [eF]⟩ }
  have hφ : Function.Surjective φ.toLin := by
    change Function.Surjective (⇑eM.toLinearMap ∘ ⇑(freeMap S N g) ∘ ⇑eF.symm.toLinearMap)
    exact eM.surjective.comp ((freeMap_surjective hspan).comp eF.symm.surjective)

  have hKfin : Module.Finite (Poly S N) (LinearMap.ker φ.toLin) := by
    have : Module.Finite (Poly S N) (ULift.{v} (Fin r → Poly S N)) := Module.Finite.equiv eF
    have : IsNoetherian (Poly S N) (ULift.{v} (Fin r → Poly S N)) :=
      isNoetherian_of_isNoetherianRing_of_finite _ _
    infer_instance
  obtain ⟨c₁, hc₁⟩ := hV S N _ φ.kerGraded hKfin

  let b : Module.Basis (Fin r) (Poly S N) (ULift.{v} (Fin r → Poly S N)) :=
    (Pi.basisFun (Poly S N) (Fin r)).map eF
  have hb : ∀ j, b j ∈ 𝓕.piece (deg j) := fun j =>
    ⟨Pi.single j 1, single_one_mem_freeGraded deg j, by simp [b, eF]⟩
  have hFc := (hF S N _ 𝓕 r b deg hb).2
  refine ⟨max c₁ (∑ j, |deg j|), fun c hc => ?_⟩
  have hcd : ∀ j, deg j ≤ c := fun j => (le_abs_self _).trans
    ((Finset.single_le_sum (fun j _ => abs_nonneg (deg j)) (Finset.mem_univ j)).trans
      ((le_max_right _ _).trans hc))
  have hsurjL : Function.Surjective (toH0 𝓜L c) :=
    toH0_surjective_of_exact hC φ.kerIncl φ (LinearMap.ker φ.toLin).injective_subtype hφ
      (LinearMap.exact_subtype_ker_map _) c (hFc c hcd).2.surjective
      (hc₁ 1 le_rfl c ((le_max_left _ _).trans hc))

  intro y
  obtain ⟨z, hz⟩ := hsurjL (cohomMap (𝓜.toTransport eM) 0 c y)
  refine ⟨⟨(𝓜.ofTransport eM).toLin z, (𝓜.ofTransport eM).map_piece c z z.2⟩, ?_⟩
  rw [← cohomMap_toH0 (𝓜.ofTransport eM), hz, cohomMap_leftInverse]
  intro m
  simp [GradedPMod.toTransport, GradedPMod.ofTransport]
end SerreOnto
end GroundTheory.Heights₂.Heights.Kleiman
