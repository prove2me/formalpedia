-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SnapperSubquotientFinite_chartRing_fg_1c4b759fa1c8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:15:53.5969+00:00
-- url     : https://prove2.me/submissions/3e4a785d-1794-4362-b334-eccaef3e7438

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperSubquotFiniteSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperQuotAdd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperSubquotFinite

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
open GroundTheory.Heights₂.Heights.Kleiman.SnapperSubquotientFinite
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.SnapperSubquotientFinite
theorem _root_.solution (I : Chart x) : (chartRing S x I).FG := by
  classical
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  refine ⟨Finset.univ.image (fun l => x l / x i) ∪ I.1.image (fun j => x i / x j), ?_⟩
  apply le_antisymm
  · rw [Algebra.adjoin_le_iff]
    intro a ha
    simp only [Finset.coe_union, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_union,
      Set.mem_range, Set.mem_image, Finset.mem_coe] at ha
    rcases ha with ⟨l, rfl⟩ | ⟨j, hj, rfl⟩
    · exact ⟨X l, X i, 1, X_mem_monos hi, isHomogeneous_X S l, isHomogeneous_X S i, by simp⟩
    · exact ⟨X i, X j, 1, X_mem_monos hj, isHomogeneous_X S i, isHomogeneous_X S j, by simp⟩
  · rintro a ⟨f, s, e, hs, hf, hse, rfl⟩
    set T := Algebra.adjoin S ((Finset.univ.image (fun l => x l / x i) ∪
      I.1.image (fun j => x i / x j) : Finset Ω) : Set Ω) with hT
    have h1 : aeval x f / x i ^ e ∈ T := by
      have hc : aeval x f / x i ^ e ∈ chartRing S x (singleChart hxi) :=
        ⟨f, X i ^ e, e, pow_mem (X_mem_monos (Finset.mem_singleton_self i)) e, hf,
          isHomogeneous_X_pow _ _, by simp⟩
      refine Algebra.adjoin_mono ?_ (mem_ampleBase_of_mem_chartRing hxi hc)
      rintro _ ⟨l, rfl⟩
      simp
    have h2 : ∀ s ∈ monos (S := S) I.1, ∃ e', s.IsHomogeneous e' ∧ x i ^ e' / aeval x s ∈ T := by
      intro s hs
      induction hs using Submonoid.closure_induction with
      | mem a ha =>
        obtain ⟨j, hj, rfl⟩ := ha
        refine ⟨1, isHomogeneous_X S j, ?_⟩
        rw [aeval_X, pow_one]
        exact Algebra.subset_adjoin (by simp only [Finset.coe_union, Finset.coe_image, Set.mem_union,
          Set.mem_image, Finset.mem_coe]; exact Or.inr ⟨j, hj, rfl⟩)
      | one => exact ⟨0, isHomogeneous_one _ _, by simp⟩
      | mul a b _ _ ha hb =>
        obtain ⟨ea, ha1, ha2⟩ := ha
        obtain ⟨eb, hb1, hb2⟩ := hb
        refine ⟨ea + eb, ha1.mul hb1, ?_⟩
        rw [map_mul, pow_add, mul_div_mul_comm]
        exact T.mul_mem ha2 hb2
    obtain ⟨e', hse', h2'⟩ := h2 s hs
    have hs0 : aeval x s ≠ 0 := eval_ne_zero_of_mem_monos I hs
    have hs0' : s ≠ 0 := by rintro rfl; exact hs0 (map_zero _)
    obtain rfl : e = e' := hse.inj_right hse' hs0'
    have hxe : x i ^ e ≠ 0 := pow_ne_zero _ hxi
    have : aeval x f / aeval x s = (aeval x f / x i ^ e) * (x i ^ e / aeval x s) := by
      field_simp
    rw [this]
    exact T.mul_mem h1 h2'
end GroundTheory.Heights₂.Heights.Kleiman.SnapperSubquotientFinite
