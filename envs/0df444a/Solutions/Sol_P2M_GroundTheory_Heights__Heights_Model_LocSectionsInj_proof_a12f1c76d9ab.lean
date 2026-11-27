-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_LocSectionsInj_proof_a12f1c76d9ab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:04:13.290635+00:00
-- url     : https://prove2.me/submissions/4ce0134d-46c0-4bcf-8d42-f509eaf94900

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsLocSectionsInj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGenericSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PLocSectionsInj
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_eq_zero_of_coprime_mul_eq_zero_aedbac591ad9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_exists_coprime_mul_eq_zero_4a4cdbd8cee2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_exists_torsion_bound_622fbf2536dc


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
namespace LocSectionsInj
theorem _root_.solution : LocSectionsInj.Statement := by
  intro X f _ _ p
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
  have hP : (∏ U ∈ t, N U) ≠ 0 := (Finset.prod_pos fun U _ => hNpos U).ne'
  refine ⟨ordCompl[(p : ℕ)] (∏ U ∈ t, N U), Nat.ordCompl_pos _ hP, Nat.not_dvd_ordCompl p.2 hP,
    fun k _ hmk W hW => ?_⟩
  have hcov : ∀ x : X, ∃ (U : X.affineOpens) (N' : ℕ), x ∈ (U : X.Opens) ∧
      ((ordCompl[(p : ℕ)] N' : ℕ) : ℤ) ∣ k ∧
      ∀ (n : ℤ) (a : Γ(X, U)), n ≠ 0 → (n : Γ(X, U)) * a = 0 → (N' : Γ(X, U)) * a = 0 := by
    intro x
    obtain ⟨U, hUt, hxU⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    have hd : ordCompl[(p : ℕ)] (N U) ∣ ordCompl[(p : ℕ)] (∏ U ∈ t, N U) :=
      Nat.ordCompl_dvd_ordCompl_of_dvd (Finset.dvd_prod_of_mem N hUt) _
    exact ⟨U, N U, hxU, dvd_trans (Int.natCast_dvd_natCast.mpr hd) hmk, hN U⟩
  rw [injective_iff_map_eq_zero ((baseChangeMap f (ZLoc p)).app W).hom]
  intro s hs
  refine X.IsSheaf.section_ext fun x hx => ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx W.isOpen
  have hVW' : V ≤ W := hVW
  refine ⟨V, hVW', hxV, ?_⟩
  obtain ⟨u, hu, hus⟩ := exists_coprime_mul_eq_zero f p hV (X.presheaf.map (homOfLE hVW').op s) (by
    rw [← ConcreteCategory.comp_apply, Scheme.Hom.naturality]
    simp [hs])
  rw [map_zero]
  exact eq_zero_of_coprime_mul_eq_zero f p p.2 k hcov (hVW'.trans hW) u hu _ hus
end LocSectionsInj
end GroundTheory.Heights₂.Heights.Model
