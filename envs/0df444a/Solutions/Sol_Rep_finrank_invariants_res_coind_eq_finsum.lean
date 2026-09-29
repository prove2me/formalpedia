-- Prove2me | solution 1 for Rep.finrank_invariants_res_coind_eq_finsum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/b5102cea-1092-5326-a650-3a635bdf9c5f

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_finrank_invariants_res_coind_eq_finsum

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module"
open scoped Classical TensorProduct

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace ArchMackey

open Representation

variable {k : Type} [Field k] {G : Type} [Group G] (H D : Subgroup G) (N : Rep.{0} k H)

abbrev Q : Type := Quotient (MulAction.orbitRel H (G ⧸ D))

abbrev orb (c : G ⧸ D) : Q H D := Quotient.mk (MulAction.orbitRel H (G ⧸ D)) c

noncomputable abbrev V := (Rep.res D.subtype (Rep.coind H.subtype N)).ρ.invariants

noncomputable abbrev W (q : Q H D) := (Rep.res (MulAction.stabilizer H q.out).subtype N).ρ.invariants

noncomputable def orbOfRightCoset : Quotient (QuotientGroup.rightRel H) → Q H D :=
  Quotient.lift (fun x : G => orb H D (x : G ⧸ D)) fun a b hab => by
    have hab' : b * a⁻¹ ∈ H := QuotientGroup.rightRel_apply.1 hab
    apply Quotient.sound
    change (MulAction.orbitRel H (G ⧸ D)) (a : G ⧸ D) (b : G ⧸ D)
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    refine ⟨⟨a * b⁻¹, by simpa using H.inv_mem hab'⟩, ?_⟩
    change (((a * b⁻¹) * b : G) : G ⧸ D) = (a : G ⧸ D)
    rw [inv_mul_cancel_right]

lemma orbOfRightCoset_surjective : Function.Surjective (orbOfRightCoset H D) := by
  intro q
  induction q using Quotient.inductionOn with
  | h c =>
    induction c using QuotientGroup.induction_on with
    | H x => exact ⟨Quotient.mk _ x, rfl⟩

scoped instance finiteQ [H.FiniteIndex] : Finite (Q H D) := by
  haveI : Finite (Quotient (QuotientGroup.rightRel H)) :=
    Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel H).symm
  exact Finite.of_surjective _ (orbOfRightCoset_surjective H D)

lemma exists_smul_out_eq (c : G ⧸ D) : ∃ h : H, h • (orb H D c).out = c :=
  MulAction.mem_orbit_iff.1 (MulAction.mem_orbit_symm.1 (MulAction.orbitRel_apply.1 (Quotient.mk_out c)))

noncomputable def sec (c : G ⧸ D) : H := Classical.choose (exists_smul_out_eq H D c)

lemma sec_smul_out (c : G ⧸ D) : sec H D c • (orb H D c).out = c :=
  Classical.choose_spec (exists_smul_out_eq H D c)

lemma orb_out (q : Q H D) : orb H D q.out = q := Quotient.out_eq q

variable {H D N}

lemma V_mul_left (f : V H D N) (h : H) (x : G) : f.1.1 ((h : G) * x) = N.ρ h (f.1.1 x) :=
  f.1.2 h x

lemma V_mul_right (f : V H D N) (d : D) (x : G) : f.1.1 (x * d) = f.1.1 x := by
  have := (Representation.mem_invariants _ _).1 f.2 d
  exact congrFun (congrArg Subtype.val this) x

lemma V_coset (f : V H D N) {x y : G} (hxy : (x : G ⧸ D) = (y : G ⧸ D)) : f.1.1 x = f.1.1 y := by
  rw [QuotientGroup.eq] at hxy
  have := V_mul_right f ⟨x⁻¹ * y, hxy⟩ x
  simpa using this.symm

lemma W_congr (v : ∀ q, W H D N q) {q₁ q₂ : Q H D} (hq : q₁ = q₂) : (v q₁ : N) = (v q₂ : N) := by
  subst hq; rfl

lemma W_smul_eq (v : ∀ q, W H D N q) (q : Q H D) (h₁ h₂ : H)
    (hh : h₁ • q.out = h₂ • q.out) : N.ρ h₁ (v q : N) = N.ρ h₂ (v q : N) := by
  have hs : h₂⁻¹ * h₁ ∈ MulAction.stabilizer H q.out := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, hh, ← mul_smul, inv_mul_cancel, one_smul]
  have := (Representation.mem_invariants _ _).1 (v q).2 ⟨h₂⁻¹ * h₁, hs⟩

  have e : N.ρ (h₂⁻¹ * h₁) (v q : N) = (v q : N) := this
  calc N.ρ h₁ (v q : N) = N.ρ h₂ (N.ρ (h₂⁻¹ * h₁) (v q : N)) := by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
    _ = N.ρ h₂ (v q : N) := by rw [e]

variable (H D N)

noncomputable def Φ : V H D N →ₗ[k] ∀ q, W H D N q where
  toFun f q := ⟨f.1.1 q.out.out, by
    rw [Representation.mem_invariants]
    intro s
    show N.ρ (s : H) (f.1.1 q.out.out) = f.1.1 q.out.out
    rw [← V_mul_left]
    apply V_coset
    change (s : H) • ((q.out.out : G) : G ⧸ D) = _
    rw [QuotientGroup.out_eq']
    exact MulAction.mem_stabilizer_iff.1 s.2⟩
  map_add' f g := by funext q; rfl
  map_smul' r f := by funext q; rfl

noncomputable def ΨF (v : ∀ q, W H D N q) (c : G ⧸ D) : N := N.ρ (sec H D c) (v (orb H D c) : N)

lemma ΨF_smul (v : ∀ q, W H D N q) (h : H) (c : G ⧸ D) :
    ΨF H D N v (h • c) = N.ρ h (ΨF H D N v c) := by
  unfold ΨF
  have hq : orb H D (h • c) = orb H D c := Quotient.sound (MulAction.orbitRel_apply.2 (MulAction.mem_orbit c h))
  rw [W_congr v hq, ← Module.End.mul_apply, ← map_mul]
  apply W_smul_eq
  have h1 := sec_smul_out H D (h • c)
  rw [hq] at h1
  rw [h1, mul_smul, sec_smul_out]

noncomputable def Ψfun (v : ∀ q, W H D N q) : V H D N :=
  ⟨⟨fun x => ΨF H D N v (x : G ⧸ D), fun h x => by
      show ΨF H D N v (((h : G) * x : G) : G ⧸ D) = N.ρ h (ΨF H D N v (x : G ⧸ D))
      rw [← ΨF_smul]; rfl⟩, by
    rw [Representation.mem_invariants]
    intro d
    apply Subtype.ext
    funext x
    show ΨF H D N v ((x * d : G) : G ⧸ D) = ΨF H D N v (x : G ⧸ D)
    rw [QuotientGroup.mk_mul_of_mem _ d.2]⟩

@[scoped simp] lemma Ψfun_apply (v : ∀ q, W H D N q) (x : G) :
    (Ψfun H D N v).1.1 x = ΨF H D N v (x : G ⧸ D) := rfl

noncomputable def Ψ : (∀ q, W H D N q) →ₗ[k] V H D N where
  toFun := Ψfun H D N
  map_add' v w := by
    apply Subtype.ext; apply Subtype.ext; funext x
    show ΨF H D N (v + w) x = ΨF H D N v x + ΨF H D N w x
    simp [ΨF]
  map_smul' r v := by
    apply Subtype.ext; apply Subtype.ext; funext x
    show ΨF H D N (r • v) x = r • ΨF H D N v x
    simp [ΨF]

lemma ΦΨ (v : ∀ q, W H D N q) : Φ H D N (Ψ H D N v) = v := by
  funext q
  apply Subtype.ext
  show ΨF H D N v ((q.out.out : G) : G ⧸ D) = (v q : N)
  rw [QuotientGroup.out_eq']
  unfold ΨF
  rw [W_congr v (Quotient.out_eq q)]
  have h1 := sec_smul_out H D q.out
  rw [orb_out] at h1
  have := W_smul_eq v q (sec H D q.out) 1 (by rw [h1, one_smul])
  rw [this, map_one, Module.End.one_apply]

lemma ΨΦ (f : V H D N) : Ψ H D N (Φ H D N f) = f := by
  apply Subtype.ext; apply Subtype.ext; funext x
  show ΨF H D N (Φ H D N f) (x : G ⧸ D) = f.1.1 x
  unfold ΨF
  show N.ρ (sec H D (x : G ⧸ D)) (f.1.1 (orb H D (x : G ⧸ D)).out.out) = f.1.1 x
  rw [← V_mul_left]
  apply V_coset
  change sec H D (x : G ⧸ D) • (((orb H D (x : G ⧸ D)).out.out : G) : G ⧸ D) = _
  rw [QuotientGroup.out_eq', sec_smul_out]

noncomputable def lequiv : V H D N ≃ₗ[k] ∀ q, W H D N q :=
  LinearEquiv.ofLinear (Φ H D N) (Ψ H D N)
    (LinearMap.ext (ΦΨ H D N)) (LinearMap.ext (ΨΦ H D N))

end ArchMackey
p2m_reactivate "P2MW.S_Rep_finrank_invariants_res_coind_eq_finsum.ArchMackey"

theorem solution
    {k : Type} [Field k] {G : Type} [Group G] (H D : Subgroup G) [H.FiniteIndex]
    (N : Rep.{0} k H) [FiniteDimensional k N] :
    Module.finrank k (Rep.res D.subtype (Rep.coind H.subtype N)).ρ.invariants =
      ∑ᶠ q : Quotient (MulAction.orbitRel H (G ⧸ D)),
        Module.finrank k (Rep.res (MulAction.stabilizer H q.out).subtype N).ρ.invariants := by
  letI : Fintype (ArchMackey.Q H D) := Fintype.ofFinite _
  rw [(ArchMackey.lequiv H D N).finrank_eq, finsum_eq_sum_of_fintype]
  exact Module.finrank_pi_fintype k

end S_Rep_finrank_invariants_res_coind_eq_finsum
end P2MW
export P2MW.S_Rep_finrank_invariants_res_coind_eq_finsum (solution)
