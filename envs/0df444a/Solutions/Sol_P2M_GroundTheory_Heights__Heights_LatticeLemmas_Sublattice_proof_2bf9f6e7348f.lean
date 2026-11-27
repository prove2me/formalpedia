-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeLemmas_Sublattice_proof_2bf9f6e7348f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:03:30.596173+00:00
-- url     : https://prove2.me/submissions/b68560cd-cf54-4243-a58f-16d55b54fd15

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PSublattice
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_gramDet_sub_994da6b3e634
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_card_quotient_span_sub_b356f7ceefe4

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField GroundTheory.Heights₂.Heights
noncomputable section
namespace GroundTheory.Heights₂.Heights.LatticeLemmas
namespace Sublattice
theorem _root_.solution : Sublattice.Statement := by
  intro K _ _ M F hF
  have : Module.Finite (𝓞 K) F := inferInstanceAs (Module.Finite (𝓞 K) (M.sub F).carrier)
  obtain ⟨s, hs⟩ := exists_linearIndependent_fin (K := K) (E := F)
  have ht : LinearIndependent (𝓞 K) (fun i ↦ (s i : M.carrier)) :=
    hs.map' F.subtype (LinearMap.ker_eq_bot.mpr F.injective_subtype)
  have hcardF : Fintype.card (Fin (Module.finrank (𝓞 K) F)) = Module.finrank (𝓞 K) F :=
    Fintype.card_fin _
  have hcardM : Fintype.card (Fin (Module.finrank (𝓞 K) F)) = Module.finrank (𝓞 K) M.carrier := by
    rw [Fintype.card_fin, hF]
  have hdM : M.arithDegree = degreeWith M.metric (fun i ↦ (s i : M.carrier)) :=
    arithDegree_eq _ ht hcardM
  have hdF : (M.sub F).arithDegree = Real.log (Nat.card (F ⧸ Submodule.span (𝓞 K) (Set.range s))) -
      (1 / 2) * ∑ σ : K →+* ℂ, Real.log (gramDet M.metric σ (fun i ↦ (s i : M.carrier))) := by
    have h1 := arithDegree_eq (M.sub F).metric hs hcardF
    rw [HermitianBundle.arithDegree, h1]
    unfold degreeWith
    simp only [gramDet_sub]
    rfl
  have hfin := finite_quotient_span ht hcardM
  have hpos : 0 < Nat.card (M.carrier ⧸ Submodule.span (𝓞 K) (Set.range fun i ↦ (s i : M.carrier))) :=
    Nat.card_pos
  have hc := card_quotient_span_sub F s
  rw [hc] at hpos
  have ha : (0 : ℝ) < Nat.card (F ⧸ Submodule.span (𝓞 K) (Set.range s)) := by
    exact_mod_cast Nat.pos_of_mul_pos_right hpos
  have hb : (0 : ℝ) < Nat.card (M.carrier ⧸ F) := by
    exact_mod_cast Nat.pos_of_mul_pos_left hpos
  have hsum : M.arithDegree = (M.sub F).arithDegree + Real.log (Nat.card (M.carrier ⧸ F)) := by
    rw [hdM, hdF, degreeWith, hc, Nat.cast_mul, Real.log_mul ha.ne' hb.ne']
    ring
  have hlog : 0 ≤ Real.log (Nat.card (M.carrier ⧸ F)) := Real.log_natCast_nonneg _
  have hdeg : M.deg = (M.sub F).deg + Real.log (Nat.card (M.carrier ⧸ F)) / Module.finrank ℚ K := by
    simp only [HermitianBundle.deg]
    rw [hsum, add_div]
  refine ⟨hdeg, ?_⟩
  rw [hdeg]
  exact le_add_of_nonneg_right (div_nonneg hlog (Nat.cast_nonneg _))
end Sublattice
end GroundTheory.Heights₂.Heights.LatticeLemmas
