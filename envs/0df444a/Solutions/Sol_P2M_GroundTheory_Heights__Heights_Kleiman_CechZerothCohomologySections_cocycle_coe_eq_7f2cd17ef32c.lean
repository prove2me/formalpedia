-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_CechZerothCohomologySections_cocycle_coe_eq_7f2cd17ef32c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:20:22.404709+00:00
-- url     : https://prove2.me/submissions/8b8de6e2-cca6-4c23-afed-8a6a580f818b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CechH0SectionsHypothesesLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExistsMemSupport
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechZerothCohomologySections_idx_ext_4851e327243f

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
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.CechZerothCohomologySections
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E]
  [IsScalarTower S Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman.CechZerothCohomologySections
theorem _root_.solution (F : SubSystem S x E) {s : Cech.Cochain (fun I => F.sub I) 0}
    (hs : Cech.d (fun I => F.sub I) F.res 0 s = 0) (K K' : Cech.Idx (support x) 0) :
    (s K : E) = (s K' : E) := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp K.2
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp K'.2
  by_cases hab : a = b
  · subst hab; rw [idx_ext (ha.trans hb.symm)]
  have hsub : ({a, b} : Finset (Fin (N + 1))) ⊆ support x := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact K.1.2.2 (by rw [ha]; exact Finset.mem_singleton_self _)
    · rw [Finset.mem_singleton.mp hz]
      exact K'.1.2.2 (by rw [hb]; exact Finset.mem_singleton_self _)
  let J : Cech.Idx (support x) 1 :=
    ⟨⟨{a, b}, Finset.insert_nonempty _ _, hsub⟩, Finset.card_pair hab⟩
  have ha' : a ∈ J.1.1 := Finset.mem_insert_self _ _
  have hb' : b ∈ J.1.1 := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have fa : Cech.face J ⟨a, ha'⟩ = K' := idx_ext (by
    change ({a, b} : Finset _).erase a = _
    rw [hb]; ext z
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2 | h2⟩
      · exact absurd h2 h1
      · exact h2
    · rintro rfl; exact ⟨Ne.symm hab, Or.inr rfl⟩)
  have fb : Cech.face J ⟨b, hb'⟩ = K := idx_ext (by
    change ({a, b} : Finset _).erase b = _
    rw [ha]; ext z
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2 | h2⟩
      · exact h2
      · exact absurd h2 h1
    · rintro rfl; exact ⟨hab, Or.inl rfl⟩)
  have hval : ∀ L L' : Cech.Idx (support x) 0, L = L' → (s L : E) = (s L' : E) := by
    rintro L L' rfl; rfl
  have h0 := congrArg (F.sub J.1).subtype (congrFun hs J)
  rw [Cech.d_apply, map_sum, Pi.zero_apply, map_zero] at h0
  have huniv : (Finset.univ : Finset J.1.1) = {⟨a, ha'⟩, ⟨b, hb'⟩} := by
    ext ⟨z, hz⟩
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq, true_iff]
    exact (Finset.mem_insert.mp hz).imp id Finset.mem_singleton.mp
  have hne : (⟨a, ha'⟩ : J.1.1) ≠ ⟨b, hb'⟩ := fun h => hab (congrArg Subtype.val h)
  rw [huniv, Finset.sum_pair hne, map_zsmul, map_zsmul] at h0
  have h1 : Cech.sgn ({a, b} : Finset (Fin (N + 1))) a • (s K' : E) +
      Cech.sgn ({a, b} : Finset (Fin (N + 1))) b • (s K : E) = 0 := by
    rw [← hval _ _ fa, ← hval _ _ fb]; exact h0
  have hsum := Cech.sum_sgn_of_card_two (Finset.card_pair hab)
  rw [Finset.sum_pair hab] at hsum
  have hb2 : Cech.sgn ({a, b} : Finset (Fin (N + 1))) b =
      - Cech.sgn ({a, b} : Finset (Fin (N + 1))) a := by linarith
  rw [hb2, neg_smul, ← sub_eq_add_neg, ← smul_sub] at h1
  have hsq : Cech.sgn ({a, b} : Finset (Fin (N + 1))) a *
      Cech.sgn ({a, b} : Finset (Fin (N + 1))) a = 1 := by
    unfold Cech.sgn; rw [← mul_pow]; norm_num
  have h2 : (s K' : E) - (s K : E) = 0 := by
    rw [← one_smul ℤ ((s K' : E) - (s K : E)), ← hsq, mul_smul, h1, smul_zero]
  exact (sub_eq_zero.mp h2).symm
end GroundTheory.Heights₂.Heights.Kleiman.CechZerothCohomologySections
