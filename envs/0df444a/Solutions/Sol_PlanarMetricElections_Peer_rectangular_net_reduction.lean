-- Prove2me | solution 1 for PlanarMetricElections.Peer.rectangular_net_reduction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:19:06.766463+00:00
-- url     : https://prove2.me/submissions/3f26fd92-30e9-4e39-ad35-2c5874c1094a

import Mathlib
import Definitions.Def_PlanarMetricElections_Peer_Geometry
import Definitions.Def_PlanarMetricElections_Peer_Capture
import Definitions.Def_PlanarMetricElections_Peer_RectangularNet
import Theorems.Thm_PlanarMetricElections_Peer_dominance_separation

section
set_option autoImplicit false
open scoped Classical
noncomputable section

namespace PlanarMetricElections.Peer.Dev.DomSep
open PlanarMetricElections.Peer

section Norm

variable (M : Seminorm ℝ Plane)

end Norm

end PlanarMetricElections.Peer.Dev.DomSep

namespace PlanarMetricElections.Peer

end PlanarMetricElections.Peer
end
end

section
set_option autoImplicit false
open scoped Classical
noncomputable section

namespace PlanarMetricElections.Peer.Dev.NetRed
open PlanarMetricElections.Peer

theorem mass_nonneg (V : Finset Plane) (X : Set Plane) : 0 ≤ mass V X := by
  unfold mass; positivity

theorem mass_le_one (V : Finset Plane) (X : Set Plane) : mass V X ≤ 1 := by
  unfold mass
  apply div_le_one_of_le₀
  · exact_mod_cast Finset.card_filter_le _ _
  · positivity

theorem payoff_nonneg (d : Plane → Plane → ℝ) (V S : Finset Plane) (c : Plane) :
    0 ≤ capturePayoff d V S c := by
  unfold capturePayoff; positivity

theorem halfplane_rect (H : Set Plane) (hH : IsOpenAxisHalfPlane H) :
    ∃ I J : Set ℝ, I.OrdConnected ∧ J.OrdConnected ∧ H = I ×ˢ J := by
  obtain ⟨t, h | h | h | h⟩ := hH
  · exact ⟨Set.Iio t, Set.univ, inferInstance, inferInstance, by rw [h]; ext x; simp⟩
  · exact ⟨Set.Ioi t, Set.univ, inferInstance, inferInstance, by rw [h]; ext x; simp⟩
  · exact ⟨Set.univ, Set.Iio t, inferInstance, inferInstance, by rw [h]; ext x; simp⟩
  · exact ⟨Set.univ, Set.Ioi t, inferInstance, inferInstance, by rw [h]; ext x; simp⟩

theorem dOne_comm (x y : Plane) : dOne x y = dOne y x := by
  unfold dOne; rw [abs_sub_comm x.1, abs_sub_comm x.2]

theorem rect_cover (S : Finset Plane) (c : Plane) :
    ∃ R : Set Plane, IsRectangle R ∧ Disjoint R (↑S : Set Plane) ∧
      ∀ v : Plane, (∀ s ∈ S, dOne v c < dOne v s) → S.Nonempty → v ∈ R := by
  by_cases hc : c ∈ S
  · refine ⟨∅, ⟨∅, ∅, inferInstance, inferInstance, by simp⟩, by simp, ?_⟩
    intro v hv _
    exact absurd (hv c hc) (lt_irrefl _)
  · have hall : ∀ s : Plane, ∃ I J : Set ℝ, I.OrdConnected ∧ J.OrdConnected ∧
        (s ≠ c → dominance dOne c s ⊆ I ×ˢ J ∧ s ∉ I ×ˢ J) := by
      intro s
      by_cases hs : s = c
      · exact ⟨Set.univ, Set.univ, inferInstance, inferInstance, fun h => absurd hs h⟩
      · obtain ⟨H, hH, hsub, hnot⟩ := (dominance_separation).2 c s (Ne.symm hs)
        obtain ⟨I, J, hI, hJ, hHIJ⟩ := halfplane_rect H hH
        exact ⟨I, J, hI, hJ, fun _ => by rw [← hHIJ]; exact ⟨hsub, hnot⟩⟩
    choose I J hI hJ hIJ using hall
    refine ⟨(⋂ s ∈ S, I s) ×ˢ (⋂ s ∈ S, J s),
      ⟨_, _, Set.ordConnected_biInter (fun s _ => hI s), Set.ordConnected_biInter (fun s _ => hJ s), rfl⟩,
      ?_, ?_⟩
    · rw [Set.disjoint_left]
      intro x hx hxS
      have hxS' : x ∈ S := hxS
      have hne : x ≠ c := fun h => hc (h ▸ hxS')
      have h1 : x ∈ I x ×ˢ J x := by
        simp only [Set.mem_prod, Set.mem_iInter] at hx ⊢
        exact ⟨hx.1 x hxS', hx.2 x hxS'⟩
      exact (hIJ x hne).2 h1
    · intro v hv _
      simp only [Set.mem_prod, Set.mem_iInter]
      constructor <;> intro s hs
      · have hne : s ≠ c := fun h => hc (h ▸ hs)
        have : v ∈ dominance dOne c s := by
          show dOne c v < dOne s v
          rw [dOne_comm c v, dOne_comm s v]; exact hv s hs
        exact ((hIJ s hne).1 this).1
      · have hne : s ≠ c := fun h => hc (h ▸ hs)
        have : v ∈ dominance dOne c s := by
          show dOne c v < dOne s v
          rw [dOne_comm c v, dOne_comm s v]; exact hv s hs
        exact ((hIJ s hne).1 this).2

theorem worst_bdd (V Q : Finset Plane) :
    BddAbove {r : ℝ | ∃ R : Set Plane, IsRectangle R ∧ Disjoint R (↑Q : Set Plane) ∧ r = mass V R} :=
  ⟨1, by rintro r ⟨R, _, _, rfl⟩; exact mass_le_one V R⟩

theorem worst_ne (V Q : Finset Plane) :
    {r : ℝ | ∃ R : Set Plane, IsRectangle R ∧ Disjoint R (↑Q : Set Plane) ∧ r = mass V R}.Nonempty :=
  ⟨mass V ∅, ∅, ⟨∅, ∅, inferInstance, inferInstance, by simp⟩, by simp, rfl⟩

theorem rectWorst_nonneg (V Q : Finset Plane) : 0 ≤ rectangularWorst V Q := by
  apply Real.sSup_nonneg
  rintro r ⟨R, _, _, rfl⟩; exact mass_nonneg V R

theorem rectWorst_le_one (V Q : Finset Plane) : rectangularWorst V Q ≤ 1 :=
  csSup_le (worst_ne V Q) (by rintro r ⟨R, _, _, rfl⟩; exact mass_le_one V R)

theorem worstCapture_le (V Q S : Finset Plane) (hS : S.Nonempty)
    (hSQ : Q.Nonempty → S = Q) : worstCapture dOne V S ≤ rectangularWorst V Q := by
  apply csSup_le (Set.range_nonempty _)
  rintro r ⟨c, rfl⟩
  obtain ⟨R, hR, hdisj, hcov⟩ := rect_cover S c
  by_cases hQ : Q.Nonempty
  · have hSQ' := hSQ hQ
    subst hSQ'
    have hle : capturePayoff dOne V S c ≤ mass V R := by
      unfold capturePayoff mass
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast Finset.card_le_card (fun v hv => by
        simp only [captured, Finset.mem_filter] at hv ⊢
        exact ⟨hv.1, hcov v hv.2 hQ⟩)
    exact le_trans hle (le_csSup (worst_bdd V S) ⟨R, hR, hdisj, rfl⟩)
  · have hQ' : Q = ∅ := Finset.not_nonempty_iff_eq_empty.1 hQ
    subst hQ'
    have hle : capturePayoff dOne V S c ≤ mass V Set.univ := by
      unfold capturePayoff mass
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast Finset.card_le_card (fun v hv => by
        simp only [captured, Finset.mem_filter] at hv ⊢
        simp [hv.1])
    exact le_trans hle (le_csSup (worst_bdd V ∅)
      ⟨Set.univ, ⟨Set.univ, Set.univ, inferInstance, inferInstance, by simp⟩, by simp, rfl⟩)

theorem peerInstance_le_worst (V : Finset Plane) (hV : V.Nonempty) (k : ℕ+) (Q : Finset Plane)
    (hQV : Q ⊆ V) (hQk : Q.card ≤ k) : peerInstance dOne V k ≤ rectangularWorst V Q := by
  obtain ⟨v0, hv0⟩ := hV
  let S : Finset Plane := if Q.Nonempty then Q else {v0}
  have hSfeas : FeasibleCoalition V S k := by
    by_cases hQ : Q.Nonempty
    · simp only [S, if_pos hQ]; exact ⟨hQV, hQ, hQk⟩
    · simp only [S, if_neg hQ]
      refine ⟨by simpa using hv0, by simp, ?_⟩
      rw [Finset.card_singleton]; exact PNat.pos k
  have hSQ : Q.Nonempty → S = Q := fun hQ => by simp [S, if_pos hQ]
  have hS : S.Nonempty := hSfeas.2.1
  calc peerInstance dOne V k ≤ worstCapture dOne V S := by
        apply csInf_le
        · refine ⟨0, ?_⟩
          rintro r ⟨S', _, rfl⟩
          apply Real.sSup_nonneg
          rintro x ⟨c, rfl⟩; exact payoff_nonneg _ _ _ _
        · exact ⟨S, hSfeas, rfl⟩
    _ ≤ rectangularWorst V Q := worstCapture_le V Q S hS hSQ

theorem main (k : ℕ+) : peerFactor dOne k ≤ rectangularFactor k := by
  have hbdd : ∀ V : Finset Plane, rectangularInstance V k ≤ 1 := by
    intro V
    have hb : BddBelow {r : ℝ | ∃ Q : Finset Plane, Q ⊆ V ∧ Q.card ≤ (k : ℕ) ∧
        r = rectangularWorst V Q} := ⟨0, by rintro r ⟨Q, _, _, rfl⟩; exact rectWorst_nonneg V Q⟩
    exact le_trans (csInf_le hb (show rectangularWorst V ∅ ∈ {r : ℝ | ∃ Q : Finset Plane, Q ⊆ V ∧
      Q.card ≤ (k : ℕ) ∧ r = rectangularWorst V Q} from ⟨∅, by simp, by simp, rfl⟩))
      (rectWorst_le_one V ∅)
  have hle : ∀ V : Finset Plane, V.Nonempty → peerInstance dOne V k ≤ rectangularFactor k := by
    intro V hV
    have h1 : peerInstance dOne V k ≤ rectangularInstance V k := by
      refine le_csInf ?_ ?_
      · exact ⟨rectangularWorst V ∅, ∅, by simp, by simp, rfl⟩
      rintro r ⟨Q, hQV, hQk, rfl⟩
      exact peerInstance_le_worst V hV k Q hQV hQk
    have hb : BddAbove {r : ℝ | ∃ W : Finset Plane, W.Nonempty ∧ r = rectangularInstance W k} :=
      ⟨1, by rintro r ⟨W, _, rfl⟩; exact hbdd W⟩
    exact le_trans h1 (le_csSup hb (show rectangularInstance V k ∈ {r : ℝ | ∃ W : Finset Plane, W.Nonempty ∧ r = rectangularInstance W k} from ⟨V, hV, rfl⟩))
  refine csSup_le ?_ ?_
  · exact ⟨peerInstance dOne {0} k, {0}, by simp, rfl⟩
  rintro r ⟨V, hV, rfl⟩
  exact hle V hV

end PlanarMetricElections.Peer.Dev.NetRed

namespace PlanarMetricElections.Peer
open PlanarMetricElections.Peer.Dev.NetRed in
theorem chk_rectangular_net_reduction (k : ℕ+) :
    peerFactor dOne k ≤ rectangularFactor k := main k

end PlanarMetricElections.Peer
end
end

theorem solution : type_of% @PlanarMetricElections.Peer.chk_rectangular_net_reduction := @PlanarMetricElections.Peer.chk_rectangular_net_reduction
