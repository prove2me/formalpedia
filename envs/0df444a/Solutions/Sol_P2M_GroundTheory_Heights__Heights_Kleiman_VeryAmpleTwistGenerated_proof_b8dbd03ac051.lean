-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleTwistGenerated_proof_b8dbd03ac051
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:40:43.588056+00:00
-- url     : https://prove2.me/submissions/133418a2-3fe2-4a2f-9656-2b5ac98db8a5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsJoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefPlusAmple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleTwistGenerated
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_isVeryAmpleBy_twist_74af083d4682
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_span_secs_le_b24ff46a355a


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
open scoped Pointwise
noncomputable section
universe u w
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace VeryAmpleTwistGenerated
theorem _root_.solution : VeryAmpleTwistGenerated.Statement.{u, w} := by
  rintro k _ Ω _ _ N x L G - hG ⟨r, h, hL⟩ hGg
  classical

  have hfin : ∀ I : Chart x, ∃ T : Finset Ω, (T : Set Ω) ⊆ G.secs ∧
      G.sub I ≤ Submodule.span (chartRing k x I) (T : Set Ω) := by
    intro I
    obtain ⟨G', hG'⟩ := hG I
    obtain ⟨F, hF⟩ := Submodule.fg_of_isUnit (IsUnit.of_mul_eq_one _ hG')
    have hsp : ∀ f ∈ F, ∃ T : Finset Ω, (T : Set Ω) ⊆ G.secs ∧
        f ∈ Submodule.span (chartRing k x I) (T : Set Ω) := fun f hf =>
      Submodule.mem_span_finite_of_mem_span (by rw [hGg I, ← hF]; exact Submodule.subset_span hf)
    choose! Tf hTf using hsp
    refine ⟨F.biUnion Tf, fun z hz => ?_, ?_⟩
    · obtain ⟨f, hf, hz⟩ := Finset.mem_biUnion.mp hz
      exact (hTf f hf).1 hz
    · rw [← hF, Submodule.span_le]
      intro f hf
      refine Submodule.span_mono (fun z hz => ?_) (hTf f hf).2
      exact Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨f, hf, hz⟩)
  choose T hTs hTg using hfin
  set U : Finset Ω := Finset.univ.biUnion T with hU
  have hUs : (U : Set Ω) ⊆ G.secs := fun z hz => by
    obtain ⟨I, -, hz⟩ := Finset.mem_biUnion.mp hz
    exact hTs I hz
  let g : Fin (U.card + 1) → Ω := Fin.cons 0 fun i => (U.equivFin.symm i : Ω)
  have hgs : ∀ j, g j ∈ G.secs := by
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [g, Fin.cons_zero]
      exact zero_mem _
    · simp only [g, Fin.cons_succ]
      exact hUs (U.equivFin.symm i).2
  have hgg : ∀ I, Submodule.span (chartRing k x I) (Set.range g) = G.sub I := by
    intro I
    apply le_antisymm
    · exact (Submodule.span_mono (by rintro _ ⟨j, rfl⟩; exact hgs j)).trans
        (SubSystem.span_secs_le G I)
    · refine (hTg I).trans (Submodule.span_mono (s := (T I : Set Ω)) (t := Set.range g) fun z hz => ?_)
      have hzU : z ∈ U := Finset.mem_biUnion.mpr ⟨I, Finset.mem_univ I, hz⟩
      exact ⟨(U.equivFin ⟨z, hzU⟩).succ, by simp [g]⟩
  have hR : (r + 1) * (U.card + 1) - 1 + 1 = (r + 1) * (U.card + 1) :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (by positivity))
  exact ⟨_, _, isVeryAmpleBy_twist hL hgs hgg ((finCongr hR).trans finProdFinEquiv.symm)⟩
end VeryAmpleTwistGenerated
end GroundTheory.Heights₂.Heights.Kleiman
