-- Prove2me | solution 1 for UpperTheory.cyclic_trivial_induction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:34:40.007886+00:00
-- url     : https://prove2.me/submissions/0f5eb369-837d-4187-97cf-a17a1fb6961e

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CyclicTrivialInductionRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
private theorem UpperTheory.cyclic_trivial_induction_ring {R : Type} [Ring R] (hR : ∀ c : R, ∃ m : ℤ, c = m) :
    ∀ {H : Type} [Monoid H] (n : ℕ) (P : Rep.{0, 0, 0} R H → Prop),
        (∀ C : Rep.{0, 0, 0} R H, Finite C.V → IsAddCyclic C.V →
          (∀ (g : H) (c : C.V), C.ρ g c = c) → (∀ c : C.V, n • c = 0) → P C) →
        (∀ (A B C : Rep.{0, 0, 0} R H) (f : A ⟶ B) (g : B ⟶ C),
          (∀ (h : H) (a : A.V), A.ρ h a = a) → (∀ (h : H) (c : C.V), C.ρ h c = c) →
          Function.Injective f.hom → Function.Exact f.hom g.hom → Function.Surjective g.hom →
          P A → P C → P B) →
        ∀ A : Rep.{0, 0, 0} R H, Finite A.V →
          (∀ (g : H) (a : A.V), A.ρ g a = a) → (∀ a : A.V, n • a = 0) → P A := by
  intro H _ n P hcyc hext A
  induction hk : Nat.card A.V using Nat.strong_induction_on generalizing A with
  | _ k ih =>
    intro hfin htriv htors
    by_cases hne : ∃ a : A.V, a ≠ 0
    · obtain ⟨a, ha⟩ := hne
      let B : Submodule R A.V := Submodule.span _ {a}
      let S : Rep.{0, 0, 0} R H := Rep.of (Representation.trivial R H B)
      let Q : Rep.{0, 0, 0} R H :=
        Rep.of (Representation.trivial R H (A.V ⧸ B))
      let f : S ⟶ A := Rep.ofHom (ρ := Representation.trivial R H B) (σ := A.ρ)
        (B.subtype.intertwiningMap_of_isIntertwiningMap _ _ (fun g v => by
          simpa using (htriv g v.1).symm))
      let g : A ⟶ Q := Rep.ofHom (ρ := A.ρ) (σ := Representation.trivial R H (A.V ⧸ B))
        (B.mkQ.intertwiningMap_of_isIntertwiningMap _ _ (fun g v => by
          simp [htriv g v]))
      have hlt : Nat.card (A.V ⧸ B) < Nat.card A.V := by
        by_contra hcon
        have hbij := (Submodule.mkQ_surjective B).bijective_of_nat_card_le (not_lt.mp hcon)
        have hmem : a ∈ B := Submodule.mem_span_singleton_self a
        have h0 : B.mkQ a = B.mkQ 0 := by
          simpa using (Submodule.Quotient.mk_eq_zero B).2 hmem
        exact ha (hbij.1 h0)
      have hS : P S := by
        refine hcyc S (inferInstanceAs (Finite B)) ?_ (fun _ _ => rfl) ?_
        · refine (⟨⟨⟨a, Submodule.mem_span_singleton_self a⟩, fun x => ?_⟩⟩ : IsAddCyclic B)
          obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 x.2
          obtain ⟨m, rfl⟩ := hR c
          refine AddSubgroup.mem_zmultiples_iff.2 ⟨m, Subtype.ext ?_⟩
          rw [← hc, Int.cast_smul_eq_zsmul]
          rfl
        · intro c
          exact Subtype.ext (htors c.1)
      have hQ : P Q := by
        refine ih (Nat.card (A.V ⧸ B)) (hk ▸ hlt) Q rfl
          (Finite.of_surjective B.mkQ (Submodule.mkQ_surjective B))
          (fun _ _ => rfl) ?_
        intro c
        obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective B c
        have : n • B.mkQ x = B.mkQ (n • x) := (map_nsmul B.mkQ n x).symm
        exact this.trans (by rw [htors x, map_zero])
      exact hext S A Q f g (fun _ _ => rfl) (fun _ _ => rfl) (Subtype.val_injective)
        (LinearMap.exact_subtype_mkQ B) (Submodule.mkQ_surjective B) hS hQ
    · have : Subsingleton A.V := ⟨fun x y => by
        push_neg at hne
        rw [hne x, hne y]⟩
      exact hcyc A hfin inferInstance htriv htors
end

set_option autoImplicit false

namespace UpperTheory
theorem _root_.solution :
    ∀ {H : Type} [Monoid H] (n : ℕ) (P : Rep.{0, 0, 0} (ULift.{0, 0} ℤ) H → Prop),
        (∀ C : Rep.{0, 0, 0} (ULift.{0, 0} ℤ) H, Finite C.V → IsAddCyclic C.V →
          (∀ (g : H) (c : C.V), C.ρ g c = c) → (∀ c : C.V, n • c = 0) → P C) →
        (∀ (A B C : Rep.{0, 0, 0} (ULift.{0, 0} ℤ) H) (f : A ⟶ B) (g : B ⟶ C),
          (∀ (h : H) (a : A.V), A.ρ h a = a) → (∀ (h : H) (c : C.V), C.ρ h c = c) →
          Function.Injective f.hom → Function.Exact f.hom g.hom → Function.Surjective g.hom →
          P A → P C → P B) →
        ∀ A : Rep.{0, 0, 0} (ULift.{0, 0} ℤ) H, Finite A.V →
          (∀ (g : H) (a : A.V), A.ρ g a = a) → (∀ a : A.V, n • a = 0) → P A := by
  intro H _
  exact UpperTheory.cyclic_trivial_induction_ring (R := ULift.{0, 0} ℤ) (fun c => ⟨c.down, ULift.ext _ _ (by simp)⟩)
end UpperTheory
