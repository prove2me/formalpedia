-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_Extension_proof_3fa22c8847fa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:28:47.142128+00:00
-- url     : https://prove2.me/submissions/1da6c624-4c62-4b9c-b67a-e44f4d7191d1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PExtension
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_inv_smul_mem_b33911982ebf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_mem_gam_550215db2da5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_smul_mem_gam_089b125b1417
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_eventually_pow_smul_mem_db52199cafd5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_gen_mem_ofGens_4d3cdc5867bd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_ofGens_piece_le_b01126a46004

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
open ExtensionProof
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace Extension
theorem _root_.solution : Extension.Statement.{u, v, w} := by
  intro S _ _ Ω _ _ N x E _ _ _ _ F hF
  classical
  have hgen : ∀ (i : Fin (N + 1)) (hi : x i ≠ 0), ∃ (r : ℕ) (g : Fin r → E),
      Submodule.span (chartRing S x (singleChart hi)) (Set.range g) = F.sub (singleChart hi) :=
    fun i hi => Submodule.fg_iff_exists_fin_generating_family.mp (hF _)
  choose r g hg using hgen
  have hev : ∀ᶠ n : ℕ in Filter.atTop, ∀ (k : Σ i : {i // x i ≠ 0}, Fin (r i.1 i.2)) (J : Chart x),
      x k.1.1 ^ n • g k.1.1 k.1.2 k.2 ∈ (F.twist (twistSys S x (n : ℤ))).sub J := by
    rw [Filter.eventually_all]
    intro k
    rw [Filter.eventually_all]
    intro J
    refine eventually_pow_smul_mem F k.1.2 ?_ J
    rw [← hg]
    exact Submodule.subset_span ⟨k.2, rfl⟩
  obtain ⟨n, hn⟩ := hev.exists
  let M : FinGradedSub (S := S) (x := x) E :=
    ofGens (fun _ : (Σ i : {i // x i ≠ 0}, Fin (r i.1 i.2)) => (n : ℤ))
      (fun k => x k.1.1 ^ n • g k.1.1 k.1.2 k.2)
  have hpiece : ∀ c, M.piece c ≤ F.gam c := fun c =>
    ofGens_piece_le _ _ (fun k => mem_gam.mpr (hn k))
      (fun _ _ _ _ hf hm => smul_mem_gam F.toSubSystem hf hm) c
  refine ⟨M, hpiece, fun I => le_antisymm ?_ ?_⟩
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩
    exact inv_smul_mem F.toSubSystem ((mem_gam.mp (hpiece a hm)) I) hs hse (by omega)
  · intro y hy
    obtain ⟨i, hi⟩ := I.2.1
    have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
    have hsub : (singleChart hxi).1 ⊆ I.1 := by simpa [singleChart] using hi
    have hF1 : ∀ z ∈ F.sub (singleChart hxi), z ∈ M.tilde 0 I := by
      intro z hz
      rw [← hg i hxi] at hz
      refine Submodule.span_induction (p := fun z _ => z ∈ M.tilde 0 I) ?_ ?_ ?_ ?_ hz
      · rintro _ ⟨j, rfl⟩
        have hmem : x i ^ n • g i hxi j ∈ M.piece n :=
          gen_mem_ofGens _ _ (⟨⟨i, hxi⟩, j⟩ : Σ i : {i // x i ≠ 0}, Fin (r i.1 i.2))
        refine Submodule.subset_span ⟨_, X i ^ n, n, n, pow_mem (X_mem_monos hi) n,
          isHomogeneous_X_pow i n, hmem, by simp, ?_⟩
        rw [map_pow, aeval_X, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hxi), one_smul]
      · exact Submodule.zero_mem _
      · intro a b _ _ ha hb; exact Submodule.add_mem _ ha hb
      · intro a z _ hz
        have h := Submodule.smul_mem _ (chartIncl hsub a) hz
        rw [Subalgebra.smul_def] at h ⊢
        exact h
    obtain ⟨a, ⟨u, hu⟩, hay⟩ := (F.mem_iff _ I hsub y).mp hy
    have hinv : ((↑u⁻¹ : chartRing S x I) : Ω) * (a : Ω) = 1 := by
      have := congrArg Subtype.val (Units.inv_mul u)
      rw [hu] at this
      exact this
    have hy' : y = (↑u⁻¹ : chartRing S x I) • ((a : Ω) • y) := by
      rw [Subalgebra.smul_def, smul_smul, hinv, one_smul]
    rw [hy']
    exact Submodule.smul_mem _ _ (hF1 _ hay)
end Extension
end GroundTheory.Heights₂.Heights.Kleiman
