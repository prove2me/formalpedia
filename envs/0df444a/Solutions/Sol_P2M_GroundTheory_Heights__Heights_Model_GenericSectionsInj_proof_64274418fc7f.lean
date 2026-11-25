-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_GenericSectionsInj_proof_64274418fc7f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:56:19.285969+00:00
-- url     : https://prove2.me/submissions/2a05f95d-8dbb-4c02-94cd-af03d82bd20d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGenericSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGenericSections
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_exists_torsion_bound_622fbf2536dc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_eq_zero_of_intCast_mul_eq_zero_44d637363897
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_flat_of_eq_zero_of_intCast_mul_4de2fa557ad9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry Opposite
noncomputable section
namespace GroundTheory.Heights₂.Heights.Model
namespace GenericSectionsInj
theorem _root_.solution : GenericSectionsInj.Statement := by
  intro X f _ _
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  choose N hNpos hN using fun U : X.affineOpens =>
    haveI := IsLocallyNoetherian.component_noetherian U
    exists_torsion_bound Γ(X, U)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun U : X.affineOpens => ((U : X.Opens) : Set X)) (fun U => (U : X.Opens).isOpen)
    (fun x _ => by
      obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
      exact Set.mem_iUnion.mpr ⟨⟨U, hU⟩, hxU⟩)
  refine ⟨∏ U ∈ t, N U, Finset.prod_pos fun U _ => hNpos U, fun k hk hmk W => ?_⟩
  have hcov : ∀ x : X, ∃ (U : X.affineOpens) (N' : ℕ), x ∈ (U : X.Opens) ∧ (N' : ℤ) ∣ k ∧
      ∀ (n : ℤ) (a : Γ(X, U)), n ≠ 0 → (n : Γ(X, U)) * a = 0 → (N' : Γ(X, U)) * a = 0 := by
    intro x
    obtain ⟨U, hUt, hxU⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact ⟨U, N U, hxU, dvd_trans (by exact_mod_cast Finset.dvd_prod_of_mem N hUt) hmk, hN U⟩
  have hflat : Flat ((invOpen f k).ι ≫ f) := flat_of_eq_zero_of_intCast_mul _ fun V n s hn hs => by
    let e := ((invOpen f k).ι.appIso V).commRingCatIsoToRingEquiv
    have h0 := eq_zero_of_intCast_mul_eq_zero f k hcov ((invOpen f k).ι_image_le V) n hn (e.symm s)
      (by rw [← map_intCast e.symm, ← map_mul, hs, map_zero])
    simpa using congrArg e h0
  let φ : Spec (CommRingCat.of ℚ) ⟶ SpecZ := Spec.map (CommRingCat.ofHom (Int.castRingHom ℚ))
  have H : IsPullback (toInvOpen f ℚ k hk) (𝟙 _ ≫ pullback.snd f φ) ((invOpen f k).ι ≫ f) φ :=
    (IsOpenImmersion.isPullback_lift_id _ _ _).paste_vert (IsPullback.of_hasPullback _ _)
  have : IsDominant φ := by
    rw [isDominant_iff]
    exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr (by
      rw [(RingHom.injective_iff_ker_eq_bot _).mp (Int.cast_injective (α := ℚ))]
      exact bot_le)
  have : IsSchemeTheoreticallyDominant φ := .of_isDominant φ
  have : IsSchemeTheoreticallyDominant (toInvOpen f ℚ k hk) := .of_isPullback H.flip
  have : QuasiCompact (toInvOpen f ℚ k hk) := MorphismProperty.of_isPullback H.flip inferInstance
  exact (toInvOpen f ℚ k hk).app_injective W
end GenericSectionsInj
end GroundTheory.Heights₂.Heights.Model
