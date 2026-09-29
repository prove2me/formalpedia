-- Prove2me | solution 1 for Rep.nonempty_tateH0_coind_linearEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/bbbfa1d6-383e-5d83-ba62-c9a2f90748d2

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_nonempty_tateH0_coind_linearEquiv

set_option autoImplicit false
universe u
open CategoryTheory Rep
set_option maxHeartbeats 1600000

namespace P2mS26C4
open Representation

variable {k G : Type*} [CommRing k] [Group G] (S : Subgroup G)

section cosets

noncomputable def rightCosetEquiv : G ≃ Quotient (QuotientGroup.rightRel S) × S where
  toFun g := (Quotient.mk _ g, ⟨g * (Quotient.out (Quotient.mk (QuotientGroup.rightRel S) g))⁻¹, by
    have h : (QuotientGroup.rightRel S) (Quotient.out (Quotient.mk (QuotientGroup.rightRel S) g)) g :=
      Quotient.exact (Quotient.out_eq _)
    exact QuotientGroup.rightRel_apply.1 h⟩)
  invFun qs := (qs.2 : G) * Quotient.out qs.1
  left_inv g := by simp
  right_inv := by
    rintro ⟨q, s⟩
    have hq : Quotient.mk (QuotientGroup.rightRel S) ((s : G) * Quotient.out q) = q := by
      conv_rhs => rw [← Quotient.out_eq q]
      apply Quotient.sound
      exact QuotientGroup.rightRel_apply.2 (by simpa using S.inv_mem s.2)
    ext
    · exact hq
    · simp only
      rw [hq]; simp

lemma sum_eq_sum_cosets [Fintype G] [Fintype S] [Fintype (Quotient (QuotientGroup.rightRel S))]
    {M : Type*} [AddCommMonoid M] (f : G → M) :
    ∑ g, f g = ∑ q : Quotient (QuotientGroup.rightRel S), ∑ s : S, f ((s : G) * Quotient.out q) := by
  rw [← Fintype.sum_prod_type (fun qs : Quotient (QuotientGroup.rightRel S) × S => f ((qs.2 : G) * Quotient.out qs.1))]
  exact Fintype.sum_equiv (rightCosetEquiv S) _ _ (fun g => by
    show f g = f ((g * (Quotient.out (Quotient.mk (QuotientGroup.rightRel S) g))⁻¹) * Quotient.out (Quotient.mk (QuotientGroup.rightRel S) g))
    rw [inv_mul_cancel_right])
end cosets

section coind
variable {B : Type*} [AddCommGroup B] [Module k B] (ρ : Representation k S B)

lemma coind_apply_apply (g x : G) (f : coindV S.subtype ρ) :
    ((Representation.coind S.subtype ρ g f : coindV S.subtype ρ) : G → B) x = (f : G → B) (x * g) := rfl

lemma coindV_apply_mul (f : coindV S.subtype ρ) (s : S) (x : G) : (f : G → B) ((s : G) * x) = ρ s ((f : G → B) x) :=
  f.2 s x

lemma apply_eq_apply_one (f : coindV S.subtype ρ) (hf : f ∈ (Representation.coind S.subtype ρ).invariants) (x : G) :
    (f : G → B) x = (f : G → B) 1 := by
  have := congrArg (fun h : coindV S.subtype ρ => (h : G → B) 1) ((mem_invariants _ _).1 hf x)
  simpa [coind_apply_apply] using this

def const (b : ρ.invariants) : coindV S.subtype ρ :=
  ⟨fun _ => (b : B), fun s x => ((mem_invariants _ _).1 b.2 s).symm⟩

noncomputable def supp (b : B) : coindV S.subtype ρ := by
  classical
  exact ⟨fun g => if h : g ∈ S then ρ ⟨g, h⟩ b else 0, fun s x => by
    show (if h : S.subtype s * x ∈ S then ρ ⟨S.subtype s * x, h⟩ b else 0) = ρ s (if h : x ∈ S then ρ ⟨x, h⟩ b else 0)
    by_cases hx : x ∈ S
    · have hsx : (S.subtype s * x) ∈ S := S.mul_mem s.2 hx
      rw [dif_pos hsx, dif_pos hx, show (⟨S.subtype s * x, hsx⟩ : S) = s * ⟨x, hx⟩ from rfl, map_mul,
        Module.End.mul_apply]
    · have hsx : (S.subtype s * x) ∉ S := fun h => hx (by simpa using S.mul_mem (S.inv_mem s.2) h)
      rw [dif_neg hsx, dif_neg hx, map_zero]⟩

noncomputable def ev1 : (Representation.coind S.subtype ρ).invariants ≃ₗ[k] ρ.invariants where
  toFun f := ⟨((f : coindV S.subtype ρ) : G → B) 1, (mem_invariants _ _).2 fun s => by
    have h1 := coindV_apply_mul S ρ (f : coindV S.subtype ρ) s 1
    rw [mul_one, apply_eq_apply_one S ρ _ f.2] at h1
    exact h1.symm⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun b := ⟨const S ρ b, (mem_invariants _ _).2 fun g => Subtype.ext (funext fun x => rfl)⟩
  left_inv f := by
    apply Subtype.ext; apply Subtype.ext; funext x
    exact (apply_eq_apply_one S ρ _ f.2 x).symm
  right_inv b := rfl

lemma coe_ev1 (f : (Representation.coind S.subtype ρ).invariants) :
    (ev1 S ρ f : B) = ((f : coindV S.subtype ρ) : G → B) 1 := rfl

variable [Fintype G]

lemma norm_coind_apply_one (f : coindV S.subtype ρ) :
    (((Representation.coind S.subtype ρ).norm f : coindV S.subtype ρ) : G → B) 1 = ∑ g, (f : G → B) g := by
  simp only [Representation.norm, LinearMap.sum_apply, AddSubmonoidClass.coe_finsetSum, Finset.sum_apply,
    coind_apply_apply, one_mul]

end coind
end P2mS26C4

open CategoryTheory Rep

theorem solution {k G : Type*} [CommRing k] [Group G] [Fintype G]
    (S : Subgroup G) [Fintype S] (B : Rep k S) :
    Nonempty ((Rep.coind S.subtype B).tateH0 ≃ₗ[k] B.tateH0) := by
  classical
  let C := Representation.coind S.subtype B.ρ

  have hmap : Submodule.map (P2mS26C4.ev1 S B.ρ : C.invariants →ₗ[k] B.ρ.invariants) (LinearMap.range C.normBar)
      = LinearMap.range B.ρ.normBar := by
    apply le_antisymm
    · rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
      obtain ⟨f, rfl⟩ := Representation.Coinvariants.mk_surjective _ y

      refine ⟨Representation.Coinvariants.mk _ (∑ q : Quotient (QuotientGroup.rightRel S), ((f : Representation.coindV S.subtype B.ρ) : G → B) (Quotient.out q)), ?_⟩
      apply Subtype.ext
      rw [Representation.normBar_mk, Representation.coe_normToInvariants_apply, Representation.normBar_mk]
      show B.ρ.norm _ = (P2mS26C4.ev1 S B.ρ ⟨C.norm f, _⟩ : B)
      rw [P2mS26C4.coe_ev1]
      show _ = (((C.norm f : Representation.coindV S.subtype B.ρ)) : G → B) 1
      rw [P2mS26C4.norm_coind_apply_one, P2mS26C4.sum_eq_sum_cosets S, map_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      simp only [Representation.norm, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun s _ => ?_
      exact (P2mS26C4.coindV_apply_mul S B.ρ f s (Quotient.out q)).symm
    · rintro _ ⟨y, rfl⟩
      obtain ⟨b, rfl⟩ := Representation.Coinvariants.mk_surjective _ y

      refine ⟨⟨C.norm (P2mS26C4.supp S B.ρ b), Representation.norm_apply_mem_invariants C _⟩,
        ⟨Representation.Coinvariants.mk _ (P2mS26C4.supp S B.ρ b), Subtype.ext rfl⟩, ?_⟩
      apply Subtype.ext
      rw [Representation.normBar_mk, Representation.coe_normToInvariants_apply]
      show (((C.norm (P2mS26C4.supp S B.ρ b) : Representation.coindV S.subtype B.ρ)) : G → B) 1 = B.ρ.norm b
      rw [P2mS26C4.norm_coind_apply_one]
      simp only [Representation.norm, LinearMap.sum_apply]

      rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ⟨((↑) : S → G), Subtype.coe_injective⟩))
        (fun g _ hg => by
          have hgS : g ∉ S := fun h => hg (Finset.mem_map.2 ⟨⟨g, h⟩, Finset.mem_univ _, rfl⟩)
          show (if h : g ∈ S then B.ρ ⟨g, h⟩ b else 0) = 0
          rw [dif_neg hgS]),
        Finset.sum_map]
      refine Finset.sum_congr rfl fun s _ => ?_
      show (if h : (s : G) ∈ S then B.ρ ⟨s, h⟩ b else 0) = B.ρ s b
      rw [dif_pos s.2]
  exact ⟨Submodule.Quotient.equiv _ _ (P2mS26C4.ev1 S B.ρ) hmap⟩

end S_Rep_nonempty_tateH0_coind_linearEquiv
end P2MW
export P2MW.S_Rep_nonempty_tateH0_coind_linearEquiv (solution)
