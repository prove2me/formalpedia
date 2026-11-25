-- Prove2me | solution 1 for PositivityTheory.RgUd.T.Nil.BasePf.core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:04:57.002498+00:00
-- url     : https://prove2.me/submissions/7fa853d2-824e-4ef0-9dfe-1a1970198604

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_BaseOrbits_PieceMem
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_BasePf_rel_iff
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_BasePf_comp_mem
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_BasePf_tens_mem
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_BasePf_slice_mem
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_BasePf_piece_mem
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_isCompact_support


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Set GroundTheory.Automorphic.Whittaker
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.BasePf
variable {Y W G : Type*} [TopologicalSpace Y] [T2Space Y] [TopologicalSpace W] [T2Space W]
  [Group G] [MulAction G W]
variable {ι : Type*}
open Classical
namespace PositivityTheory.RgUd.T.Nil.BasePf
theorem _root_.solution (hcomm : ∀ a b : G, a * b = b * a) (hcont : ∀ g : G, Continuous fun w : W => g • w)
    (D : (Y × W → ℂ) →ₗ[ℂ] ℂ)
    (hD : ∀ g : G, ∀ f ∈ TF (Y × W), D (fun p => f (p.1, g • p.2)) = D f)
    (S : Set W) (w0 : W) (htr : ∀ w ∈ S, ∃ g : G, g • w0 = w)
    (K : ι → Subgroup G) (hKo : ∀ i, ∀ w ∈ S, IsOpen {w' | ∃ g ∈ K i, g • w = w'})
    (hKf : ∀ f ∈ supportedIn (univ ×ˢ S : Set (Y × W)), ∃ i, ∀ g ∈ K i, ∀ p : Y × W, f (p.1, g • p.2) = f p)
    (t : G) (L : Set W) (hLc : IsCompact L) (hLo : IsOpen L) (hLK : ∀ i, ∀ g ∈ K i, ∀ w ∈ L, g • w ∈ L)
    (htL : ∀ w, t⁻¹ • w ∈ L → w ∈ L) (hLS : ∀ w ∈ L, t⁻¹ • w ∉ L → w ∈ S)
    (hne : ∃ w ∈ L, t⁻¹ • w ∉ L) :
    ∀ f ∈ supportedIn (univ ×ˢ S : Set (Y × W)), D f = 0 := by

  set tL : Set W := {w | t⁻¹ • w ∈ L} with htLdef
  have htLc : IsClopen tL := ⟨hLc.isClosed.preimage (hcont t⁻¹), hLo.preimage (hcont t⁻¹)⟩
  set B : Set W := L ∩ tLᶜ with hBdef
  have hBc : IsCompact B := hLc.inter_right htLc.compl.isClosed
  have hBo : IsOpen B := hLo.inter htLc.isClosed.isOpen_compl
  have hBS : B ⊆ S := fun w hw => hLS w hw.1 hw.2
  have hBK : ∀ i, ∀ g ∈ K i, ∀ w ∈ B, g • w ∈ B := by
    intro i g hg w hw
    refine ⟨hLK i g hg w hw.1, fun h => hw.2 ?_⟩
    have h' : g⁻¹ • (t⁻¹ • (g • w)) ∈ L := hLK i g⁻¹ ((K i).inv_mem hg) _ h
    have e : g⁻¹ • (t⁻¹ • (g • w)) = t⁻¹ • w := by
      rw [← mul_smul, ← mul_smul, hcomm g⁻¹ t⁻¹, mul_assoc, inv_mul_cancel, mul_one]
    show t⁻¹ • w ∈ L
    rwa [e] at h'

  have claimA : ∀ i, ∀ F ∈ TF (Y × W), (∀ g ∈ K i, ∀ p : Y × W, F (p.1, g • p.2) = F p) →
      (∀ p : Y × W, F p ≠ 0 → ∃ g ∈ K i, g • w0 = p.2) → D F = 0 := by
    intro i F hF hFK hFO
    set a : Y → ℂ := fun y => F (y, w0) with ha
    have haT : a ∈ TF Y := slice_mem hF w0
    set Φ : Y × W → ℂ := fun p => a p.1 * B.indicator 1 p.2 with hΦ
    have hΦT : Φ ∈ TF (Y × W) := tens_mem haT hBc hBo

    have hΦ0 : D Φ = 0 := by
      set ΦL : Y × W → ℂ := fun p => a p.1 * L.indicator 1 p.2
      have hLT : ΦL ∈ TF (Y × W) := tens_mem haT hLc hLo
      have e1 : (fun p : Y × W => ΦL (p.1, t⁻¹ • p.2)) = fun p => a p.1 * tL.indicator 1 p.2 := by
        funext p
        by_cases h : t⁻¹ • p.2 ∈ L
        · simp [ΦL, Set.indicator_of_mem h, Set.indicator_of_mem (show p.2 ∈ tL from h)]
        · simp [ΦL, Set.indicator_of_notMem h, Set.indicator_of_notMem (show p.2 ∉ tL from h)]
      have e2 : Φ = ΦL - fun p => a p.1 * tL.indicator 1 p.2 := by
        funext p
        simp only [Φ, ΦL, Pi.sub_apply, B]
        by_cases h1 : p.2 ∈ tL
        · have h2 : p.2 ∈ L := htL _ h1
          simp [Set.indicator_of_mem h1, Set.indicator_of_mem h2,
            Set.indicator_of_notMem (show p.2 ∉ L ∩ tLᶜ from fun h => h.2 h1)]
        · by_cases h2 : p.2 ∈ L
          · simp [Set.indicator_of_notMem h1, Set.indicator_of_mem h2,
              Set.indicator_of_mem (show p.2 ∈ L ∩ tLᶜ from ⟨h2, h1⟩)]
          · simp [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2,
              Set.indicator_of_notMem (show p.2 ∉ L ∩ tLᶜ from fun h => h2 h.1)]
      rw [e2, map_sub, ← e1, hD t⁻¹ ΦL hLT, sub_self]

    obtain ⟨b, hbB, hbfin, hbcov⟩ := hBc.elim_finite_subcover_image (b := B)
      (c := fun r => {w' | ∃ g ∈ K i, g • r = w'}) (fun r hr => hKo i r (hBS hr))
      (fun w hw => mem_iUnion₂.2 ⟨w, hw, 1, (K i).one_mem, one_smul _ _⟩)
    set Q : Finset (Quotient (rel (K i))) := hbfin.toFinset.image (Quotient.mk (rel (K i))) with hQ
    have hΦsum : Φ = ∑ q ∈ Q, fun p : Y × W => Φ p * if Quotient.mk (rel (K i)) p.2 = q then 1 else 0 := by
      funext p
      rw [Finset.sum_apply]
      simp only [← Finset.mul_sum, Finset.sum_ite_eq, Finset.sum_const_zero]
      by_cases hp : p.2 ∈ B
      · obtain ⟨r, hr, g, hg, hgr⟩ := mem_iUnion₂.1 (hbcov hp)
        have : Quotient.mk (rel (K i)) p.2 ∈ Q :=
          Finset.mem_image.2 ⟨r, hbfin.mem_toFinset.2 hr, ((rel_iff _ _ _).2 ⟨g, hg, hgr⟩).symm⟩
        simp [this]
      · simp [Φ, Set.indicator_of_notMem hp]
    have hpiece : ∀ q ∈ Q, D (fun p : Y × W => Φ p * if Quotient.mk (rel (K i)) p.2 = q then 1 else 0) = D F := by
      intro q hq
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hq
      have hrB : r ∈ B := hbB (hbfin.mem_toFinset.1 hr)
      obtain ⟨h, hh⟩ := htr r (hBS hrB)
      have hPT := piece_mem (K i) S (hKo i) hΦT
        (fun p hp => by simp [Φ, Set.indicator_of_notMem (fun h' => hp (hBS h'))])
        (Quotient.mk (rel (K i)) r)
      rw [← hD h _ hPT]
      congr 1
      funext p
      have key : Quotient.mk (rel (K i)) (h • p.2) = Quotient.mk (rel (K i)) r ↔ ∃ g ∈ K i, g • w0 = p.2 := by
        rw [rel_iff, ← hh]
        constructor
        · rintro ⟨g, hg, hgx⟩
          refine ⟨g, hg, ?_⟩
          have : h • (g • w0) = h • p.2 := by rw [← hgx, ← mul_smul, ← mul_smul, hcomm]
          exact smul_left_cancel h this
        · rintro ⟨g, hg, hgx⟩
          exact ⟨g, hg, by rw [← hgx, ← mul_smul, ← mul_smul, hcomm]⟩
      by_cases hp : ∃ g ∈ K i, g • w0 = p.2
      · have hk := key.2 hp
        obtain ⟨g, hg, hgx⟩ := hp
        have hhB : h • p.2 ∈ B := by
          rw [← hgx, ← mul_smul, hcomm, mul_smul, hh]
          exact hBK i g hg r hrB
        simp only [Φ, Set.indicator_of_mem hhB, hk, if_true, Pi.one_apply, mul_one, a]
        have e3 := hFK g hg (p.1, w0)
        simp only [hgx] at e3
        rw [← e3]
      · have hk : ¬ Quotient.mk (rel (K i)) (h • p.2) = Quotient.mk (rel (K i)) r := fun h' => hp (key.1 h')
        simp only [hk, if_false, mul_zero]
        by_contra h0
        exact hp (hFO p (Ne.symm h0))
    have hQne : Q.Nonempty := by
      obtain ⟨w, hwL, hwt⟩ := hne
      have hwB : w ∈ B := ⟨hwL, hwt⟩
      obtain ⟨r, hr, -⟩ := mem_iUnion₂.1 (hbcov hwB)
      exact ⟨_, Finset.mem_image.2 ⟨r, hbfin.mem_toFinset.2 hr, rfl⟩⟩
    have hsum : D Φ = (Q.card : ℂ) * D F := by
      conv_lhs => rw [hΦsum]
      rw [map_sum, Finset.sum_congr rfl hpiece, Finset.sum_const, nsmul_eq_mul]
    rw [hΦ0] at hsum
    have hc : (Q.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 hQne)
    exact (mul_eq_zero.1 hsum.symm).resolve_left hc

  intro f hf
  obtain ⟨i, hfK⟩ := hKf f hf
  have hfT : f ∈ TF (Y × W) := hf.1
  have hfS : ∀ p : Y × W, p.2 ∉ S → f p = 0 := fun p hp => by
    by_contra h
    exact hp (hf.2 h).2
  set C : Set W := Prod.snd '' Function.support f
  have hCc : IsCompact C := (isCompact_support hf.1).image continuous_snd
  have hCS : C ⊆ S := by
    rintro _ ⟨p, hp, rfl⟩
    exact (hf.2 hp).2
  obtain ⟨b, hbC, hbfin, hbcov⟩ := hCc.elim_finite_subcover_image (b := C)
    (c := fun r => {w' | ∃ g ∈ K i, g • r = w'}) (fun r hr => hKo i r (hCS hr))
    (fun w hw => mem_iUnion₂.2 ⟨w, hw, 1, (K i).one_mem, one_smul _ _⟩)
  set Q : Finset (Quotient (rel (K i))) := hbfin.toFinset.image (Quotient.mk (rel (K i))) with hQ
  have hfsum : f = ∑ q ∈ Q, fun p : Y × W => f p * if Quotient.mk (rel (K i)) p.2 = q then 1 else 0 := by
    funext p
    rw [Finset.sum_apply]
    simp only [← Finset.mul_sum, Finset.sum_ite_eq, Finset.sum_const_zero]
    by_cases hp : f p = 0
    · simp [hp]
    · obtain ⟨r, hr, g, hg, hgr⟩ := mem_iUnion₂.1 (hbcov ⟨p, hp, rfl⟩)
      have : Quotient.mk (rel (K i)) p.2 ∈ Q :=
        Finset.mem_image.2 ⟨r, hbfin.mem_toFinset.2 hr, ((rel_iff _ _ _).2 ⟨g, hg, hgr⟩).symm⟩
      simp [this]
  rw [hfsum, map_sum]
  refine Finset.sum_eq_zero fun q hq => ?_
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hq
  have hrS : r ∈ S := hCS (hbC (hbfin.mem_toFinset.1 hr))
  obtain ⟨h, hh⟩ := htr r hrS
  have hPT := piece_mem (K i) S (hKo i) hfT hfS (Quotient.mk (rel (K i)) r)
  rw [← hD h _ hPT]
  refine claimA i _ (comp_mem hPT h (hcont h) (hcont h⁻¹)) ?_ ?_
  · intro g hg p
    have e : Quotient.mk (rel (K i)) (g • h • p.2) = Quotient.mk (rel (K i)) (h • p.2) :=
      (rel_iff _ _ _).2 ⟨g, hg, rfl⟩
    have e2 : h • g • p.2 = g • h • p.2 := by rw [← mul_smul, ← mul_smul, hcomm]
    have e3 := hfK g hg (p.1, h • p.2)
    simp only at e3
    simp only [e2]
    rw [e, e3]
  · intro p hp
    have hk : Quotient.mk (rel (K i)) (h • p.2) = Quotient.mk (rel (K i)) r := by
      by_contra hk
      exact hp (by simp [hk])
    obtain ⟨g, hg, hgx⟩ := (rel_iff _ _ _).1 hk
    refine ⟨g, hg, smul_left_cancel h ?_⟩
    rw [← hgx, ← hh, ← mul_smul, ← mul_smul, hcomm]
end PositivityTheory.RgUd.T.Nil.BasePf
