-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_InvertibleIndexCharP_proof_be4720698cde
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:09:24.661375+00:00
-- url     : https://prove2.me/submissions/e1155a33-1917-4fc7-8eac-ac04f8a99832

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsInvertibleIndexMulSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PInvertibleIndexCharP
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_InvertibleIndexCharP_finite_subring_fb0d73c5f47f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open GroundTheory.Heights₂.Heights
namespace GroundTheory.Heights₂.Heights.Targets
namespace InvertibleIndexCharP
theorem _root_.solution : InvertibleIndexCharP.Statement := by
  intro Ω _ B X η _ f hp hB hX hf hloc
  have hfin : Finite B := InvertibleIndexCharP.finite_subring B hp hB
  have hfield : IsField B := Finite.isField_of_domain B
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  obtain ⟨i, ⟨b₀, hb₀m, hb₀X⟩, hgen⟩ := hloc m hm

  have hunit : ∀ b : B, b ∉ m → ∃ b' : B, (b' : Ω) * b = 1 := by
    intro b hb
    have hb0 : b ≠ 0 := fun h => hb (h ▸ m.zero_mem)
    obtain ⟨b', hb'⟩ := hfield.mul_inv_cancel hb0
    refine ⟨b', ?_⟩
    have := congrArg Subtype.val hb'
    simpa [mul_comm] using this

  have hXeq : (X : Set Ω) = (fun y => f i * y) '' (B : Set Ω) := by
    ext z
    constructor
    · intro hz
      obtain ⟨b, c, hbm, hbc⟩ := hgen z hz
      obtain ⟨b', hb'⟩ := hunit b hbm
      refine ⟨((b' * c : B) : Ω), (b' * c).2, ?_⟩
      calc f i * ((b' * c : B) : Ω) = b' * (c * f i) := by push_cast; ring
        _ = b' * (b * z) := by rw [hbc]
        _ = z := by rw [← mul_assoc, hb', one_mul]
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨b', hb'⟩ := hunit b₀ hb₀m
      have hfX : f i ∈ X := by
        have := hX b' b'.2 _ hb₀X
        rwa [← mul_assoc, hb', one_mul] at this
      have := hX y hy _ hfX
      rw [mul_comm] at this
      exact this
  set A := B.toAddSubgroup with hA
  have hAfin : Finite A := hfin
  have hXfin' : (X : Set Ω).Finite := by
    rw [hXeq]; exact (Set.toFinite (B : Set Ω)).image _
  have hXfin : Finite X := hXfin'.to_subtype

  have hcard : Nat.card X = Nat.card A := by
    have h := Nat.card_image_of_injective (mul_right_injective₀ (hf i)) (B : Set Ω)
    rw [← hXeq] at h
    exact h
  have hc : Nat.card (A.addSubgroupOf X) = Nat.card (X.addSubgroupOf A) :=
    Nat.card_congr
      { toFun := fun x => ⟨⟨x.1.1, AddSubgroup.mem_addSubgroupOf.1 x.2⟩,
          AddSubgroup.mem_addSubgroupOf.2 x.1.2⟩
        invFun := fun x => ⟨⟨x.1.1, AddSubgroup.mem_addSubgroupOf.1 x.2⟩,
          AddSubgroup.mem_addSubgroupOf.2 x.1.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have k1 : Nat.card (A.addSubgroupOf X) * A.relIndex X = Nat.card X :=
    (A.addSubgroupOf X).card_mul_index
  have k2 : Nat.card (X.addSubgroupOf A) * X.relIndex A = Nat.card A :=
    (X.addSubgroupOf A).card_mul_index
  have hpos : 0 < Nat.card (A.addSubgroupOf X) := Nat.card_pos
  have hApos : 0 < Nat.card A := Nat.card_pos
  have heq : A.relIndex X = X.relIndex A := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [k1, hc, k2, hcard]
  have hne : X.relIndex A ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at k2
    omega
  unfold genIndex
  rw [heq]
  exact div_self (by exact_mod_cast hne)
end InvertibleIndexCharP
end GroundTheory.Heights₂.Heights.Targets
