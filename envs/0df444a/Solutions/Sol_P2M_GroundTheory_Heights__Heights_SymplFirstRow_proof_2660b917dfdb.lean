-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SymplFirstRow_proof_2660b917dfdb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:54:01.122031+00:00
-- url     : https://prove2.me/submissions/4ba33b75-0267-4bdf-ab98-dcfa602dd872

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplFirstRow
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplFirstRow_intVec_ne_zero_77209a029981

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix
namespace GroundTheory.Heights₂.Heights
namespace SymplFirstRow
theorem _root_.solution (h1 : SymplMinExists.Statement) (h2 : SymplMinBound.Statement)
    (h3 : SymplOrbit.Statement) (h4 : SymplShortPrim.Statement) (h5 : SymplGramMem.Statement) :
    SymplFirstRow.Statement := by
  intro n G hG hpd
  obtain ⟨ρsq, hleast⟩ := h1 (Fin (n + 1) ⊕ Fin (n + 1)) G hpd
  have hdet : G.det = 1 := SymplecticGroup.det_eq_one hG
  have hbound := h2 (Fin (n + 1) ⊕ Fin (n + 1)) G hpd hdet ρsq hleast
  obtain ⟨v, hv0, hvρ⟩ := hleast.1
  refine ⟨ρsq, hleast, ?_, ?_, ?_⟩
  · rw [hvρ]
    have := hpd.dotProduct_mulVec_pos (PSymplFirstRow.intVec_ne_zero hv0)
    simpa [qf] using this
  · simp only [Fintype.card_sum, Fintype.card_fin] at hbound
    push_cast at hbound
    linarith
  · have hmin : ∀ u : Fin (n + 1) ⊕ Fin (n + 1) → ℤ, u ≠ 0 →
        qf G (intVec v) ≤ qf G (intVec u) := by
      intro u hu
      rw [← hvρ]
      exact hleast.2 ⟨u, hu, rfl⟩
    obtain ⟨P, hP, m, hm⟩ := h3 n v
    have hrow : ∃ P' ∈ symplecticGroup (Fin (n + 1)) ℤ, P' (Sum.inl 0) = v := by
      rcases h4 _ G hpd v (P (Sum.inl 0)) m hm hv0 hmin with h | h
      · exact ⟨P, hP, by rw [hm, h, one_smul]⟩
      · refine ⟨-P, SymplecticGroup.neg_mem hP, ?_⟩
        rw [hm, h, neg_one_smul]
        rfl
    obtain ⟨P', hP', hP'v⟩ := hrow
    refine ⟨P', hP', ?_⟩
    rw [(h5 (n + 1) P' G hP' hG hpd).2.2.2 (Sum.inl 0), hP'v, hvρ]
end SymplFirstRow
end GroundTheory.Heights₂.Heights
