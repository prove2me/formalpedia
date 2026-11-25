-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosed_proof_1a14374dcafa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:20:49.129654+00:00
-- url     : https://prove2.me/submissions/4b590c9d-21ae-4ea0-987c-b708186b1fdc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PGraphClosedLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PGraphClosed
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_mem_sub_of_mem_secs__0f08f505c152
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_exists_fin_generators_41e46a1db7ba
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_ampleChart_twist_95103f7b6497
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_ampleRing_twist_fb592b680e04
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_ampleRing_twist_subset_4861de94ddb8

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
open GraphClosedAlt
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace GraphClosed
theorem _root_.solution : GraphClosed.Statement.{u, w} := by
  intro k _ Ω _ _ N x G H hG hH
  obtain ⟨r₁, g, hg, hgI⟩ := exists_fin_generators G hG
  obtain ⟨r₂, h, hh⟩ := hH
  have hr : (r₁ + 1) * (r₂ + 1) = (r₁ * r₂ + r₁ + r₂) + 1 := by ring
  let E : Fin (r₁ + 1) × Fin (r₂ + 1) ≃ Fin (r₁ * r₂ + r₁ + r₂ + 1) :=
    finProdFinEquiv.trans (finCongr hr)
  let pr : Fin (r₁ + 1) × Fin (r₂ + 1) → Ω := fun q => h q.2 * g q.1
  let s : Fin (r₁ * r₂ + r₁ + r₂ + 1) → Ω := fun j => pr (E.symm j)
  have hs : ∀ j, s j = h (E.symm j).2 * g (E.symm j).1 := fun j => rfl
  have hsE : ∀ b m, s (E (b, m)) = h m * g b := fun b m => by simp [s, pr]
  have hrange : Set.range s = Set.range h * Set.range g := by
    ext z
    constructor
    · rintro ⟨j, rfl⟩
      exact Set.mem_mul.mpr ⟨_, ⟨(E.symm j).2, rfl⟩, _, ⟨(E.symm j).1, rfl⟩, (hs j).symm⟩
    · intro hz
      obtain ⟨_, ⟨m, rfl⟩, _, ⟨b, rfl⟩, rfl⟩ := Set.mem_mul.mp hz
      exact ⟨E (b, m), hsE b m⟩
  refine ⟨r₁ * r₂ + r₁ + r₂, s, ?_, ?_, ?_, ?_⟩
  · intro j
    rw [hs, SubSystem.secs, Submodule.mem_iInf]
    intro I
    exact Submodule.subset_span ⟨h (E.symm j).2, mem_sub_of_mem_secs' (hh.mem_secs _) I,
      g (E.symm j).1, mem_sub_of_mem_secs' (hg _) I, (smul_eq_mul _ _).symm⟩
  · intro I
    rw [hrange, ← Submodule.span_mul_span, hh.generates I, hgI I,
      SubSystem.twist_sub_eq_mul_of_line]
  · intro j hj
    rw [hs] at hj ⊢
    refine ampleRing_twist_subset G.toSubSystem H.toSubSystem g h hgI hh hj _ fun b m => ?_
    have : h m * g b / (h (E.symm j).2 * g (E.symm j).1) = s (E (b, m)) / s j := by
      rw [hsE, hs]
    rw [this]
    exact Algebra.subset_adjoin ⟨E (b, m), rfl⟩
  · intro j hj
    rw [hs] at hj ⊢
    have hl : h (E.symm j).2 ≠ 0 := left_ne_zero_of_mul hj
    obtain ⟨n, a, b, J, ha, hb, hsum, hJ⟩ := hh.affine _ hl
    refine ⟨n, a, b, J, fun q => ampleRing_twist _ _ (hg _) (ha q),
      fun q => ampleRing_twist _ _ (hg _) (hb q), hsum, fun q I => ?_⟩
    obtain ⟨e, he⟩ := hJ q I
    exact ⟨e, ampleChart_twist _ _ I (mem_sub_of_mem_secs' (hg _) I) he⟩
end GraphClosed
end GroundTheory.Heights₂.Heights.Kleiman
