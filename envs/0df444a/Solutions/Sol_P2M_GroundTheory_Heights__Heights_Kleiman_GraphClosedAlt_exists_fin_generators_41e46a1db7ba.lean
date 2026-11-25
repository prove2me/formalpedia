-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_exists_fin_generators_41e46a1db7ba
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:03:25.552722+00:00
-- url     : https://prove2.me/submissions/8badf5fc-8a57-4e6b-8f41-34dcadef88af

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PGraphClosedLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PGraphClosed
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_mem_sub_of_mem_secs__0f08f505c152

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
open GroundTheory.Heights₂.Heights.Kleiman.GraphClosedAlt
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.GraphClosedAlt
theorem _root_.solution (G : LineBundle S x) (hG : G.toSubSystem.Generated) :
    ∃ (r : ℕ) (g : Fin (r + 1) → Ω), (∀ a, g a ∈ G.toSubSystem.secs) ∧
      ∀ I, Submodule.span (chartRing S x I) (Set.range g) = G.sub I := by
  classical
  have hloc : ∀ I : Chart x, ∃ F : Finset Ω, (F : Set Ω) ⊆ G.toSubSystem.secs ∧
      G.sub I ≤ Submodule.span (chartRing S x I) (F : Set Ω) := by
    intro I
    obtain ⟨t, ht⟩ := G.fg I
    have hy : ∀ y : Ω, ∃ T : Finset Ω, (T : Set Ω) ⊆ G.toSubSystem.secs ∧
        (y ∈ G.sub I → y ∈ Submodule.span (chartRing S x I) (T : Set Ω)) := by
      intro y
      by_cases hyI : y ∈ G.sub I
      · have : y ∈ Submodule.span (chartRing S x I) (G.toSubSystem.secs : Set Ω) := by
          rw [hG I]; exact hyI
        obtain ⟨T, hT, hyT⟩ := Submodule.mem_span_finite_of_mem_span this
        exact ⟨T, hT, fun _ => hyT⟩
      · exact ⟨∅, by simp, fun h => absurd h hyI⟩
    choose T hT hTy using hy
    refine ⟨t.biUnion T, ?_, ?_⟩
    · intro z hz
      obtain ⟨y, -, hzy⟩ := Finset.mem_biUnion.mp hz
      exact hT y hzy
    · rw [← ht, Submodule.span_le]
      intro y hyt
      have hyI : y ∈ G.sub I := by rw [← ht]; exact Submodule.subset_span hyt
      exact Submodule.span_mono (by
        intro z hz
        exact Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨y, hyt, hz⟩)) (hTy y hyI)
  choose F hF hFI using hloc
  set A := Finset.univ.biUnion F
  let g : Fin (A.card + 1) → Ω := Fin.cons 0 fun i => (A.equivFin.symm i : Ω)
  have hrange : Set.range g = insert 0 (A : Set Ω) := by
    simp only [g, Fin.range_cons]
    congr 1
    ext y
    constructor
    · rintro ⟨i, rfl⟩; exact (A.equivFin.symm i).2
    · intro hy; exact ⟨A.equivFin ⟨y, hy⟩, by simp⟩
  have hA : (A : Set Ω) ⊆ G.toSubSystem.secs := by
    intro z hz
    obtain ⟨I, -, hzI⟩ := Finset.mem_biUnion.mp hz
    exact hF I hzI
  refine ⟨A.card, g, fun a => ?_, fun I => le_antisymm ?_ ?_⟩
  · have : g a ∈ insert 0 (A : Set Ω) := hrange ▸ Set.mem_range_self a
    rcases this with h0 | hA'
    · rw [h0]; exact Submodule.zero_mem _
    · exact hA hA'
  · rw [Submodule.span_le, hrange]
    rintro z (rfl | hz)
    · exact Submodule.zero_mem _
    · exact mem_sub_of_mem_secs' (hA hz) I
  · refine (hFI I).trans (Submodule.span_mono ?_)
    rw [hrange]
    intro z hz
    exact Set.mem_insert_of_mem _ (Finset.mem_coe.mpr
      (Finset.mem_biUnion.mpr ⟨I, Finset.mem_univ I, Finset.mem_coe.mp hz⟩))
end GroundTheory.Heights₂.Heights.Kleiman.GraphClosedAlt
