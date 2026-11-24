-- Prove2me | solution 1 for PositivityTheory.RgUd.T.Nil.Orb.BModbound.relIndex_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:57:49.386847+00:00
-- url     : https://prove2.me/submissions/7b94c4a2-c593-4f82-aff6-707ac3e490f8

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_ModulusBounds_RelIndexEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb PositivityTheory.RgUd.T.Nil.Orb.BModbound
namespace PositivityTheory.RgUd.T.Nil.Orb.BModbound
theorem _root_.solution {k : Type} [Field k] {n : ℕ} (I J : AddSubgroup (Matrix (Fin n) (Fin n) k))
    (GI GJ : Subgroup (GL (Fin n) k)) (hJI : J ≤ I)
    (hGI : ∀ u : GL (Fin n) k, u ∈ GI ↔ u.val - 1 ∈ I)
    (hGJ : ∀ u : GL (Fin n) k, u ∈ GJ ↔ u.val - 1 ∈ J)
    (hsurj : ∀ x ∈ I, ∃ u : GL (Fin n) k, u.val = 1 + x)
    (hmul : ∀ u ∈ GI, ∀ y ∈ J, u.val * y ∈ J) :
    GJ.relIndex GI = J.relIndex I := by
  classical
  have hinv : ∀ x ∈ I, ∃ u : GL (Fin n) k, u ∈ GI ∧ u.val = 1 + x := fun x hx => by
    obtain ⟨u, hu⟩ := hsurj x hx
    refine ⟨u, (hGI u).2 ?_, hu⟩
    rw [hu, add_sub_cancel_left]
    exact hx
  let f : GI → I := fun u => ⟨u.1.val - 1, (hGI u.1).1 u.2⟩
  have hf_inj : Function.Injective f := by
    intro a b hab
    have h : a.1.val - 1 = b.1.val - 1 := congrArg Subtype.val hab
    exact Subtype.ext (Units.ext (sub_left_inj.mp h))
  have hf_surj : Function.Surjective f := by
    intro x
    obtain ⟨u, hu, hux⟩ := hinv x.1 x.2
    refine ⟨⟨u, hu⟩, Subtype.ext ?_⟩
    show u.val - 1 = x.1
    rw [hux, add_sub_cancel_left]
  let e : GI ≃ I := Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
  have key : ∀ a b : GI, (QuotientGroup.leftRel (GJ.subgroupOf GI)) a b ↔
      (QuotientAddGroup.leftRel (J.addSubgroupOf I)) (e a) (e b) := by
    intro a b
    rw [QuotientGroup.leftRel_apply, QuotientAddGroup.leftRel_apply, Subgroup.mem_subgroupOf,
      AddSubgroup.mem_addSubgroupOf]
    show ((a.1⁻¹ * b.1 : GL (Fin n) k)) ∈ GJ ↔ -(a.1.val - 1) + (b.1.val - 1) ∈ J
    have h1 : -(a.1.val - 1) + (b.1.val - 1) = b.1.val - a.1.val := by abel
    rw [h1, hGJ, Units.val_mul]
    have ha : a.1⁻¹ ∈ GI := GI.inv_mem a.2
    constructor
    · intro h
      have h2 := hmul a.1 a.2 _ h
      have e2 : a.1.val * ((a.1⁻¹).val * b.1.val - 1) = b.1.val - a.1.val := by
        rw [mul_sub, ← mul_assoc, Units.mul_inv, one_mul, mul_one]
      rwa [e2] at h2
    · intro h
      have h2 := hmul a.1⁻¹ ha _ h
      have e2 : (a.1⁻¹).val * (b.1.val - a.1.val) = (a.1⁻¹).val * b.1.val - 1 := by
        rw [mul_sub, Units.inv_mul]
      rwa [e2] at h2
  have hc := Nat.card_congr (Quotient.congr e key)
  exact hc
end PositivityTheory.RgUd.T.Nil.Orb.BModbound
