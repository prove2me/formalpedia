-- Prove2me | solution 1 for Rep.nonempty_tateHneg1_coind_linearEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/665f8dfe-fc82-561a-aaf1-0b4c83ad7f90

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_nonempty_tateHneg1_coind_linearEquiv

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

namespace P2mS26C4
open Representation

variable {k G : Type*} [CommRing k] [Group G] (S : Subgroup G)

noncomputable def cosetMul (g : G) : Quotient (QuotientGroup.rightRel S) ≃ Quotient (QuotientGroup.rightRel S) where
  toFun := Quotient.map' (· * g) (fun x y h => by
    rw [QuotientGroup.rightRel_apply] at h ⊢
    simpa [mul_assoc] using h)
  invFun := Quotient.map' (· * g⁻¹) (fun x y h => by
    rw [QuotientGroup.rightRel_apply] at h ⊢
    simpa [mul_assoc] using h)
  left_inv q := by induction q using Quotient.inductionOn with | _ x => exact congrArg (Quotient.mk _) (by simp)
  right_inv q := by induction q using Quotient.inductionOn with | _ x => exact congrArg (Quotient.mk _) (by simp)

lemma out_mul_mul_inv_out_cosetMul_mem (g : G) (q : Quotient (QuotientGroup.rightRel S)) :
    Quotient.out q * g * (Quotient.out (cosetMul S g q))⁻¹ ∈ S := by
  have h1 : Quotient.mk (QuotientGroup.rightRel S) (Quotient.out (cosetMul S g q)) = cosetMul S g q := Quotient.out_eq _
  have h2 : cosetMul S g q = Quotient.mk (QuotientGroup.rightRel S) (Quotient.out q * g) := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  exact QuotientGroup.rightRel_apply.1 (Quotient.exact (h1.trans h2))

lemma out_mem_iff (q : Quotient (QuotientGroup.rightRel S)) :
    Quotient.out q ∈ S ↔ q = Quotient.mk (QuotientGroup.rightRel S) 1 := by
  constructor
  · intro h
    rw [← Quotient.out_eq q]
    apply Quotient.sound
    exact QuotientGroup.rightRel_apply.2 (by simpa using S.inv_mem h)
  · rintro rfl
    have := QuotientGroup.rightRel_apply.1 (Quotient.exact (Quotient.out_eq (Quotient.mk (QuotientGroup.rightRel S) (1 : G))))
    simpa using S.inv_mem this

variable {B : Type*} [AddCommGroup B] [Module k B] (ρ : Representation k S B)
variable [Fintype (Quotient (QuotientGroup.rightRel S))]

noncomputable def toCoinvS : coindV S.subtype ρ →ₗ[k] ρ.Coinvariants where
  toFun f := ∑ q : Quotient (QuotientGroup.rightRel S), Representation.Coinvariants.mk ρ ((f : G → B) (Quotient.out q))
  map_add' f f' := by simp [Finset.sum_add_distrib]
  map_smul' c f := by simp [Finset.smul_sum]

lemma toCoinvS_apply (f : coindV S.subtype ρ) :
    toCoinvS S ρ f = ∑ q : Quotient (QuotientGroup.rightRel S), Representation.Coinvariants.mk ρ ((f : G → B) (Quotient.out q)) := rfl

lemma toCoinvS_coind (g : G) (f : coindV S.subtype ρ) :
    toCoinvS S ρ (Representation.coind S.subtype ρ g f) = toCoinvS S ρ f := by
  rw [toCoinvS_apply, toCoinvS_apply]
  refine Fintype.sum_equiv (cosetMul S g) _ _ (fun q => ?_)
  rw [coind_apply_apply]
  have hq : Quotient.out q * g = ((⟨_, out_mul_mul_inv_out_cosetMul_mem S g q⟩ : S) : G) * Quotient.out (cosetMul S g q) := by
    simp
  rw [hq, coindV_apply_mul, Representation.Coinvariants.mk_self_apply]

noncomputable def Φ : (Representation.coind S.subtype ρ).Coinvariants →ₗ[k] ρ.Coinvariants :=
  Representation.Coinvariants.lift _ (toCoinvS S ρ) (fun g => LinearMap.ext fun f => toCoinvS_coind S ρ g f)

lemma Φ_mk (f : coindV S.subtype ρ) :
    Φ S ρ (Representation.Coinvariants.mk _ f) = ∑ q : Quotient (QuotientGroup.rightRel S), Representation.Coinvariants.mk ρ ((f : G → B) (Quotient.out q)) := by
  simp [Φ, toCoinvS_apply]

omit [Fintype (Quotient (QuotientGroup.rightRel S))] in

lemma supp_apply_eq (s : S) (b : B) :
    supp S ρ (ρ s b) = Representation.coind S.subtype ρ (s : G) (supp S ρ b) := by
  classical
  apply Subtype.ext; funext x
  rw [coind_apply_apply]
  show (if h : x ∈ S then ρ ⟨x, h⟩ (ρ s b) else 0) = (if h : x * s ∈ S then ρ ⟨x * s, h⟩ b else 0)
  by_cases hx : x ∈ S
  · have hxs : x * s ∈ S := S.mul_mem hx s.2
    rw [dif_pos hx, dif_pos hxs, show (⟨x * s, hxs⟩ : S) = ⟨x, hx⟩ * s from rfl, map_mul, Module.End.mul_apply]
  · have hxs : x * s ∉ S := fun h => hx (by simpa using S.mul_mem h (S.inv_mem s.2))
    rw [dif_neg hx, dif_neg hxs]

noncomputable def Ψ : ρ.Coinvariants →ₗ[k] (Representation.coind S.subtype ρ).Coinvariants :=
  Representation.Coinvariants.lift _ (Representation.Coinvariants.mk _ ∘ₗ
    { toFun := supp S ρ, map_add' := fun b b' => by
        classical
        apply Subtype.ext; funext x
        show (if h : x ∈ S then ρ ⟨x, h⟩ (b + b') else 0) = (if h : x ∈ S then ρ ⟨x, h⟩ b else 0) + (if h : x ∈ S then ρ ⟨x, h⟩ b' else 0)
        split_ifs <;> simp
      map_smul' := fun c b => by
        classical
        apply Subtype.ext; funext x
        show (if h : x ∈ S then ρ ⟨x, h⟩ (c • b) else 0) = c • (if h : x ∈ S then ρ ⟨x, h⟩ b else 0)
        split_ifs <;> simp })
    (fun s => LinearMap.ext fun b => by
      show Representation.Coinvariants.mk _ (supp S ρ (ρ s b)) = Representation.Coinvariants.mk _ (supp S ρ b)
      rw [supp_apply_eq, Representation.Coinvariants.mk_self_apply])

lemma Ψ_mk (b : B) : Ψ S ρ (Representation.Coinvariants.mk ρ b) = Representation.Coinvariants.mk _ (supp S ρ b) := by
  simp [Ψ]

open scoped Classical in
omit [Fintype (Quotient (QuotientGroup.rightRel S))] in
lemma supp_apply (b : B) (x : G) :
    ((supp S ρ b : coindV S.subtype ρ) : G → B) x = if h : x ∈ S then ρ ⟨x, h⟩ b else 0 := by
  show (if h : x ∈ S then ρ ⟨x, h⟩ b else 0) = _
  congr

lemma ΦΨ (y : ρ.Coinvariants) : Φ S ρ (Ψ S ρ y) = y := by
  classical
  obtain ⟨b, rfl⟩ := Representation.Coinvariants.mk_surjective _ y
  rw [Ψ_mk, Φ_mk]
  rw [Finset.sum_eq_single (Quotient.mk (QuotientGroup.rightRel S) 1)]
  · have h1 : Quotient.out (Quotient.mk (QuotientGroup.rightRel S) (1 : G)) ∈ S := (out_mem_iff S _).2 rfl
    rw [supp_apply, dif_pos h1, Representation.Coinvariants.mk_self_apply]
  · intro q _ hq
    rw [supp_apply, dif_neg (fun h => hq ((out_mem_iff S q).1 h)), map_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma eq_sum_translate_supp (f : coindV S.subtype ρ) :
    f = ∑ q : Quotient (QuotientGroup.rightRel S),
      Representation.coind S.subtype ρ (Quotient.out q)⁻¹ (supp S ρ ((f : G → B) (Quotient.out q))) := by
  classical
  apply Subtype.ext; funext x
  rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
  rw [Finset.sum_eq_single (Quotient.mk (QuotientGroup.rightRel S) x)]
  · rw [coind_apply_apply, supp_apply]
    have hx : x * (Quotient.out (Quotient.mk (QuotientGroup.rightRel S) x))⁻¹ ∈ S :=
      QuotientGroup.rightRel_apply.1 (Quotient.exact (Quotient.out_eq _))
    rw [dif_pos hx, ← coindV_apply_mul]
    congr 1
    simp
  · intro q _ hq
    rw [coind_apply_apply, supp_apply, dif_neg]
    intro h
    apply hq
    rw [← Quotient.out_eq q]
    exact Quotient.sound (QuotientGroup.rightRel_apply.2 h)
  · intro h; exact absurd (Finset.mem_univ _) h

lemma ΨΦ (z : (Representation.coind S.subtype ρ).Coinvariants) : Ψ S ρ (Φ S ρ z) = z := by
  obtain ⟨f, rfl⟩ := Representation.Coinvariants.mk_surjective _ z
  rw [Φ_mk, map_sum]
  conv_rhs => rw [eq_sum_translate_supp S ρ f, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Ψ_mk, Representation.Coinvariants.mk_self_apply]

noncomputable def coinvEquiv : (Representation.coind S.subtype ρ).Coinvariants ≃ₗ[k] ρ.Coinvariants :=
  LinearEquiv.ofLinear (Φ S ρ) (Ψ S ρ) (LinearMap.ext (ΦΨ S ρ)) (LinearMap.ext (ΨΦ S ρ))

variable [Fintype G] [Fintype S]

lemma ev1_normBar (z : (Representation.coind S.subtype ρ).Coinvariants) :
    ev1 S ρ ((Representation.coind S.subtype ρ).normBar z) = ρ.normBar (Φ S ρ z) := by
  obtain ⟨f, rfl⟩ := Representation.Coinvariants.mk_surjective _ z
  apply Subtype.ext
  rw [Representation.normBar_mk, coe_ev1, Representation.coe_normToInvariants_apply, Φ_mk, map_sum,
    norm_coind_apply_one, sum_eq_sum_cosets S, AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Representation.normBar_mk, Representation.coe_normToInvariants_apply]
  simp only [Representation.norm, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  exact coindV_apply_mul S ρ f s (Quotient.out q)

end P2mS26C4

open CategoryTheory Rep

theorem solution {k G : Type*} [CommRing k] [Group G] [Fintype G]
    (S : Subgroup G) [Fintype S] (B : Rep k S) :
    Nonempty ((Rep.coind S.subtype B).tateHneg1 ≃ₗ[k] B.tateHneg1) := by
  classical
  let C := Representation.coind S.subtype B.ρ
  refine ⟨LinearEquiv.ofSubmodules (P2mS26C4.coinvEquiv S B.ρ) (LinearMap.ker C.normBar) (LinearMap.ker B.ρ.normBar) ?_⟩
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker] at hz ⊢
    show B.ρ.normBar (P2mS26C4.Φ S B.ρ z) = 0
    rw [← P2mS26C4.ev1_normBar, hz, map_zero]
  · intro y hy
    refine ⟨(P2mS26C4.coinvEquiv S B.ρ).symm y, ?_, LinearEquiv.apply_symm_apply _ _⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker] at hy ⊢
    apply (P2mS26C4.ev1 S B.ρ).injective
    rw [P2mS26C4.ev1_normBar, map_zero]
    show B.ρ.normBar (P2mS26C4.coinvEquiv S B.ρ ((P2mS26C4.coinvEquiv S B.ρ).symm y)) = 0
    rw [LinearEquiv.apply_symm_apply]; exact hy

end S_Rep_nonempty_tateHneg1_coind_linearEquiv
end P2MW
export P2MW.S_Rep_nonempty_tateHneg1_coind_linearEquiv (solution)
