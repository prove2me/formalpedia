-- Prove2me | solution 1 for PlanarMetricElections.Peer.strong_peer_three
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:24:25.026887+00:00
-- url     : https://prove2.me/submissions/24185d62-cf28-45fe-ab3e-5b61f748c3ef

import Mathlib
import Definitions.Def_PlanarMetricElections_Peer_Capture
import Theorems.Thm_PlanarMetricElections_Peer_rectangular_net_reduction
import Theorems.Thm_PlanarMetricElections_Peer_rectangular_half_net

section
set_option autoImplicit false
open scoped Classical
noncomputable section

namespace PlanarMetricElections.Peer.Dev.SP3
open PlanarMetricElections.Peer

theorem payoff_nonneg (d : Plane → Plane → ℝ) (V S : Finset Plane) (c : Plane) :
    0 ≤ capturePayoff d V S c := by
  unfold capturePayoff; positivity

theorem payoff_le_one (d : Plane → Plane → ℝ) (V S : Finset Plane) (c : Plane) :
    capturePayoff d V S c ≤ 1 := by
  unfold capturePayoff
  apply div_le_one_of_le₀
  · exact_mod_cast Finset.card_filter_le _ _
  · positivity

theorem worst_le_one (d : Plane → Plane → ℝ) (V S : Finset Plane) : worstCapture d V S ≤ 1 :=
  csSup_le (Set.range_nonempty _) (by rintro r ⟨c, rfl⟩; exact payoff_le_one d V S c)

theorem payoff_le_worst (d : Plane → Plane → ℝ) (V S : Finset Plane) (c : Plane) :
    capturePayoff d V S c ≤ worstCapture d V S :=
  le_csSup ⟨1, by rintro r ⟨c, rfl⟩; exact payoff_le_one d V S c⟩ ⟨c, rfl⟩

theorem peerInstance_le_one (V : Finset Plane) (hV : V.Nonempty) (k : ℕ+) (d : Plane → Plane → ℝ) :
    peerInstance d V k ≤ 1 := by
  obtain ⟨v0, hv0⟩ := hV
  have hfeas : FeasibleCoalition V {v0} k :=
    ⟨by simpa using hv0, by simp, by rw [Finset.card_singleton]; exact PNat.pos k⟩
  have hb : BddBelow {r : ℝ | ∃ S : Finset Plane, FeasibleCoalition V S k ∧ r = worstCapture d V S} := by
    refine ⟨0, ?_⟩
    rintro r ⟨S', _, rfl⟩
    apply Real.sSup_nonneg
    rintro x ⟨c, rfl⟩; exact payoff_nonneg _ _ _ _
  exact le_trans (csInf_le hb ⟨{v0}, hfeas, rfl⟩) (worst_le_one d V {v0})

/-- Part one: the `ℓ¹` case, from the two published siblings. -/
theorem dOne_case (V : Finset Plane) (hV : V.Nonempty) : StrongPeerGuarantee dOne V 3 (1 / 2) := by
  have hF : peerFactor dOne 3 ≤ 1 / 2 := by
    have h1 := rectangular_net_reduction 3
    have h2 := rectangular_half_net
    exact le_trans h1 h2
  have hI : peerInstance dOne V 3 ≤ 1 / 2 := by
    have hb : BddAbove {r : ℝ | ∃ W : Finset Plane, W.Nonempty ∧ r = peerInstance dOne W 3} :=
      ⟨1, by rintro r ⟨W, hW, rfl⟩; exact peerInstance_le_one W hW 3 dOne⟩
    exact le_trans (le_csSup hb (show peerInstance dOne V 3 ∈ {r : ℝ | ∃ W : Finset Plane,
      W.Nonempty ∧ r = peerInstance dOne W 3} from ⟨V, hV, rfl⟩)) hF
  set T : Set ℝ := {r : ℝ | ∃ S : Finset Plane, FeasibleCoalition V S ((3 : ℕ+) : ℕ) ∧
    r = worstCapture dOne V S} with hT
  have hTne : T.Nonempty := by
    obtain ⟨v0, hv0⟩ := hV
    exact ⟨_, {v0}, ⟨by simpa using hv0, by simp, by simp⟩, rfl⟩
  have hTfin : T.Finite := by
    apply Set.Finite.subset (Finset.finite_toSet (V.powerset.image (worstCapture dOne V)))
    rintro r ⟨S, hS, rfl⟩
    simp only [Finset.coe_image, Finset.mem_coe, Set.mem_image, Finset.mem_powerset]
    exact ⟨S, hS.1, rfl⟩
  obtain ⟨S, hS, hSeq⟩ := hTne.csInf_mem hTfin
  refine ⟨S, ⟨hS.1, hS.2.1, by simpa using hS.2.2⟩, fun c => ?_⟩
  have : worstCapture dOne V S ≤ 1 / 2 := by
    rw [← hSeq]; exact hI
  exact le_trans (payoff_le_worst _ _ _ _) this

theorem dOne_transfer (x y : Plane) : dOne (normTransfer x) (normTransfer y) = 2 * dInf x y := by
  unfold dOne dInf normTransfer
  simp only
  rcases abs_cases (x.1 - y.1) with h1 | h1 <;> rcases abs_cases (x.2 - y.2) with h2 | h2 <;>
    rcases abs_cases (x.1 + x.2 - (y.1 + y.2)) with h3 | h3 <;>
    rcases abs_cases (x.1 - x.2 - (y.1 - y.2)) with h4 | h4 <;>
    rcases max_cases |x.1 - y.1| |x.2 - y.2| with h5 | h5 <;> linarith

theorem transfer_inj : Function.Injective normTransfer := by
  intro x y h
  simp only [normTransfer, Prod.ext_iff] at h
  exact Prod.ext (by linarith [h.1, h.2]) (by linarith [h.1, h.2])

theorem dInf_case (V : Finset Plane) (hV : V.Nonempty) : StrongPeerGuarantee dInf V 3 (1 / 2) := by
  have hV' : (V.image normTransfer).Nonempty := hV.image _
  obtain ⟨S', ⟨hS'V, hS'ne, hS'k⟩, hS'c⟩ := dOne_case _ hV'
  set S : Finset Plane := V.filter (fun v => normTransfer v ∈ S') with hS
  have himg : S.image normTransfer = S' := by
    ext w
    simp only [Finset.mem_image, hS, Finset.mem_filter]
    constructor
    · rintro ⟨v, ⟨_, hv⟩, rfl⟩; exact hv
    · intro hw
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 (hS'V hw)
      exact ⟨v, ⟨hv, hw⟩, rfl⟩
  refine ⟨S, ⟨Finset.filter_subset _ _, ?_, ?_⟩, fun c => ?_⟩
  · obtain ⟨w, hw⟩ := hS'ne
    rw [← himg] at hw
    obtain ⟨v, hv, _⟩ := Finset.mem_image.1 hw
    exact ⟨v, hv⟩
  · rw [← Finset.card_image_of_injective _ transfer_inj, himg]; exact hS'k
  · have h1 := hS'c (normTransfer c)
    unfold capturePayoff at h1 ⊢
    rw [Finset.card_image_of_injective _ transfer_inj] at h1
    refine le_trans ?_ h1
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hsub : (captured dInf V S c).image normTransfer ⊆
        captured dOne (V.image normTransfer) S' (normTransfer c) := by
      intro w hw
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw
      simp only [captured, Finset.mem_filter] at hv ⊢
      refine ⟨Finset.mem_image_of_mem _ hv.1, fun s' hs' => ?_⟩
      rw [← himg] at hs'
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hs'
      rw [dOne_transfer, dOne_transfer]
      have := hv.2 s hs
      linarith
    have := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ transfer_inj] at this
    exact_mod_cast this

end PlanarMetricElections.Peer.Dev.SP3

namespace PlanarMetricElections.Peer
open PlanarMetricElections.Peer.Dev.SP3 in
theorem chk_strong_peer_three (V : Finset Plane) (hV : V.Nonempty) :
    StrongPeerGuarantee dOne V 3 (1 / 2) ∧
    StrongPeerGuarantee dInf V 3 (1 / 2) := ⟨dOne_case V hV, dInf_case V hV⟩

end PlanarMetricElections.Peer
end
end

theorem solution : type_of% @PlanarMetricElections.Peer.chk_strong_peer_three := @PlanarMetricElections.Peer.chk_strong_peer_three
