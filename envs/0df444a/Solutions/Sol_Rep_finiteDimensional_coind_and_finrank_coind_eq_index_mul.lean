-- Prove2me | solution 1 for Rep.finiteDimensional_coind_and_finrank_coind_eq_index_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/35d27f01-8cea-5f80-863f-61155e2b07bf

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_finiteDimensional_coind_and_finrank_coind_eq_index_mul

set_option autoImplicit false

universe u

open CategoryTheory

theorem solution {k G : Type u} [Field k] [Group G] (S : Subgroup G) [S.FiniteIndex]
    (N : Rep.{u} k S) [FiniteDimensional k N] :
    FiniteDimensional k (Rep.coind S.subtype N) ∧
      Module.finrank k (Rep.coind S.subtype N) = S.index * Module.finrank k N := by
  classical
  let Q := Quotient (QuotientGroup.rightRel S)
  haveI : Finite Q := Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel S).symm
  letI : Fintype Q := Fintype.ofFinite Q

  let rep : G → G := fun g => (Quotient.mk (QuotientGroup.rightRel S) g).out
  have rep_spec : ∀ g : G, g * (rep g)⁻¹ ∈ S := fun g =>
    QuotientGroup.rightRel_apply.1 (Quotient.mk_out (s := QuotientGroup.rightRel S) g)
  have rep_mul : ∀ (s : S) (g : G), rep ((s : G) * g) = rep g := fun s g => by
    show (Quotient.mk _ ((s : G) * g)).out = (Quotient.mk _ g).out
    congr 1
    apply Quotient.sound
    show @Setoid.r _ (QuotientGroup.rightRel S) ((s : G) * g) g
    rw [QuotientGroup.rightRel_apply]
    simp

  have key : ∀ (a : G) (ha : a ∈ S) (v : N), a = 1 → N.ρ ⟨a, ha⟩ v = v := by
    rintro a ha v rfl
    exact congrFun (congrArg DFunLike.coe (map_one N.ρ)) v

  let e : Rep.coind S.subtype N ≃ₗ[k] (Q → N) :=
    { toFun := fun f q => (f : G → N) q.out
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun F => ⟨fun g => N.ρ ⟨g * (rep g)⁻¹, rep_spec g⟩ (F (Quotient.mk _ g)), fun s h => by
        simp only [Subgroup.coe_subtype]
        have hq : (Quotient.mk (QuotientGroup.rightRel S) ((s : G) * h)) = Quotient.mk _ h :=
          Quotient.sound (by
            show @Setoid.r _ (QuotientGroup.rightRel S) ((s : G) * h) h
            rw [QuotientGroup.rightRel_apply]; simp)
        rw [← Module.End.mul_apply, ← map_mul]
        have hmem : (s : G) * h * (rep ((s : G) * h))⁻¹ ∈ S := rep_spec _
        have : (⟨(s : G) * h * (rep ((s : G) * h))⁻¹, hmem⟩ : S) = s * ⟨h * (rep h)⁻¹, rep_spec h⟩ := by
          apply Subtype.ext
          simp only [Subgroup.coe_mul, rep_mul, mul_assoc]
        rw [show (⟨(s : G) * h * (rep ((s : G) * h))⁻¹, rep_spec _⟩ : S) = s * ⟨h * (rep h)⁻¹, rep_spec h⟩ from this,
          hq]⟩
      left_inv := fun f => by
        apply Subtype.ext
        funext g
        show N.ρ ⟨g * (rep g)⁻¹, rep_spec g⟩ ((f : G → N) (Quotient.mk (QuotientGroup.rightRel S) g).out) = (f : G → N) g
        have := f.2 ⟨g * (rep g)⁻¹, rep_spec g⟩ (rep g)
        rw [← this]
        show (f : G → N) (g * (rep g)⁻¹ * rep g) = (f : G → N) g
        rw [inv_mul_cancel_right]
      right_inv := fun F => by
        funext q
        show N.ρ ⟨q.out * (rep q.out)⁻¹, rep_spec q.out⟩ (F (Quotient.mk _ q.out)) = F q
        have hout : Quotient.mk (QuotientGroup.rightRel S) q.out = q := Quotient.out_eq q
        rw [hout]
        exact key _ _ _ (by show q.out * ((Quotient.mk (QuotientGroup.rightRel S) q.out).out)⁻¹ = 1; rw [hout, mul_inv_cancel]) }
  haveI : FiniteDimensional k (Rep.coind S.subtype N) := LinearEquiv.finiteDimensional e.symm
  refine ⟨inferInstance, ?_⟩
  rw [LinearEquiv.finrank_eq e, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Subgroup.index, ← Nat.card_eq_fintype_card,
    Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel S)]

end S_Rep_finiteDimensional_coind_and_finrank_coind_eq_index_mul
end P2MW
export P2MW.S_Rep_finiteDimensional_coind_and_finrank_coind_eq_index_mul (solution)
