-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SerrePoly_LaurentCohom_proof_b93810c6f4c0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:53:56.64925+00:00
-- url     : https://prove2.me/submissions/1c405134-fb90-46ad-8640-e6afd2eb182e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerrePolyLaurentCohom
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_mem_exps_3fdef6a3d557
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_sum_partC_72f412671d36
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_partC_mem_bdry_c8f9b9260b31
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_part_univ_eq_zero_4f68cd74c221
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_bnd_finite_04cd16ef5319
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_reduce_311485808135
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentCohomProof_mk_eq_e60e9069aaa5

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
universe u
open LaurentCohomProof
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace SerrePoly.LaurentCohom
theorem _root_.solution (hC : Cech.Cone.Statement.{u, u}) :
    SerrePoly.LaurentCohom.Statement.{u} := by
  intro S _ _ N
  refine ⟨fun i c => ?_, fun c hc i hi => ?_, fun c hc z hz => ?_⟩
  ·
    let B := Finsupp.supported S S (bnd (N := N) c)
    have : Finite (bnd (N := N) c) := (bnd_finite c).to_subtype
    have : Module.Finite S B := Module.Finite.equiv (Finsupp.supportedEquivFinsupp _).symm
    let T := ∀ _ : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) i, B
    let ψ : T →ₗ[S] Cech.Cochain (G S N) i :=
      LinearMap.pi fun I => B.subtype.comp (LinearMap.proj I)
    let C := Cech.cocyDeg (G S N) (laurentDeg S N c) (ρ S N) i
    let P := C.comap ψ
    have : IsNoetherian S T := isNoetherian_of_linearEquiv
      (LinearEquiv.piCongrRight fun _ => Finsupp.supportedEquivFinsupp (M := S) (R := S) (bnd c)).symm
    have : Module.Finite S P := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian P)
    let g : P →ₗ[S] laurentCohom S N i c :=
      (Submodule.mkQ _).comp (ψ.restrict (p := P) (q := C) fun _ hx => hx)
    refine Module.Finite.of_surjective g fun x => ?_
    obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.mkQ_surjective _ x
    obtain ⟨w, hw, hwB, hzw⟩ := reduce hC hz
    have hP : (fun I => (⟨w I, hwB I⟩ : B)) ∈ P := Submodule.mem_comap.mpr hw
    refine ⟨⟨_, hP⟩, ?_⟩
    exact (mk_eq hz hw hzw).symm
  ·
    obtain ⟨i, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    refine (Submodule.Quotient.subsingleton_iff).mpr (eq_top_iff.mpr fun ⟨z, hz⟩ _ => ?_)
    change z ∈ Cech.bdryDeg _ _ _ _
    have hu : partC S Finset.univ (i + 1) z = 0 := by
      funext I
      exact part_univ_eq_zero hc (hz.2 I (Set.mem_univ _))
    rw [← sum_partC (S := S) (i + 1) z, ← Finset.sum_erase_add _ _ (Finset.mem_univ Finset.univ), hu,
      add_zero]
    exact Submodule.sum_mem _ fun J hJ => partC_mem_bdry hC (Finset.ne_of_mem_erase hJ) hz
  ·
    let sg : Fin (N + 1) → Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 0 := fun k =>
      ⟨⟨{k}, Finset.singleton_nonempty k, Finset.subset_univ _⟩, Finset.card_singleton k⟩
    have hconst := (hC S (Laurent S N) N ∅).2.2 z (LinearMap.mem_ker.mp hz.1)
    refine ⟨z (sg 0), (Finsupp.mem_supported' S _).mpr fun a ha => ?_, fun I => hconst I (sg 0)⟩
    by_contra h'
    apply ha
    refine ⟨(mem_exps (hz.2 (sg 0) (Set.mem_univ _)) h').1, fun j _ => ?_⟩
    by_cases hk : ∃ k, k ≠ j
    · obtain ⟨k, hk⟩ := hk
      have h'' : z (sg k) a ≠ 0 := by rwa [hconst (sg k) (sg 0)]
      exact (mem_exps (hz.2 (sg k) (Set.mem_univ _)) h'').2 j (by simpa [sg] using hk.symm)
    · replace hk : ∀ k, k = j := fun k => by by_contra h; exact hk ⟨k, h⟩
      have hs := (mem_exps (hz.2 (sg 0) (Set.mem_univ _)) h').1
      rw [Finset.sum_eq_single j (fun k _ hkj => absurd (hk k) hkj) (by simp)] at hs
      omega
end SerrePoly.LaurentCohom
end GroundTheory.Heights₂.Heights.Kleiman
