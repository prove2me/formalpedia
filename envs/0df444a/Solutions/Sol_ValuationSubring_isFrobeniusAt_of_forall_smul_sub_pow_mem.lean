-- Prove2me | solution 1 for ValuationSubring.isFrobeniusAt_of_forall_smul_sub_pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/8fffc064-e7d5-5ce9-b4c3-d647c3d3c94b

import Definitions.Def_EllipticCurve_FrobeniusTrace
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Algebra.Rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_isFrobeniusAt_of_forall_smul_sub_pow_mem

set_option autoImplicit false

open scoped NumberField Pointwise

namespace C6PortS10T3b

variable {Qt : Ideal (𝓞 (AlgebraicClosure ℚ))} {A : ValuationSubring (AlgebraicClosure ℚ)}

private def IsLoc (Qt : Ideal (𝓞 (AlgebraicClosure ℚ))) (A : ValuationSubring (AlgebraicClosure ℚ)) :
    Prop :=
  ∀ x : AlgebraicClosure ℚ, x ∈ A ↔ ∃ s : 𝓞 (AlgebraicClosure ℚ), s ∉ Qt ∧
    ∃ a : 𝓞 (AlgebraicClosure ℚ), (s : AlgebraicClosure ℚ) * x = a

private theorem coe_ne_zero_of_notMem {s : 𝓞 (AlgebraicClosure ℚ)} (hs : s ∉ Qt) :
    (s : AlgebraicClosure ℚ) ≠ 0 := by
  intro h
  exact hs ((NumberField.RingOfIntegers.coe_eq_zero_iff.mp h).symm ▸ Qt.zero_mem)

section

variable [Qt.IsMaximal] (hA : IsLoc Qt A)
include hA

private theorem coe_mem (x : 𝓞 (AlgebraicClosure ℚ)) : (x : AlgebraicClosure ℚ) ∈ A :=
  (hA x).2 ⟨1, (Ideal.ne_top_iff_one Qt).1 Ideal.IsPrime.ne_top', x, by simp⟩

private noncomputable def ψ : 𝓞 (AlgebraicClosure ℚ) →+* A :=
  (algebraMap (𝓞 (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ)).codRestrict A (coe_mem hA)

@[scoped simp] private theorem coe_ψ (x : 𝓞 (AlgebraicClosure ℚ)) :
    ((ψ hA x : A) : AlgebraicClosure ℚ) = x := rfl

private theorem isUnit_ψ {s : 𝓞 (AlgebraicClosure ℚ)} (hs : s ∉ Qt) : IsUnit (ψ hA s) := by
  have hs0 := coe_ne_zero_of_notMem hs
  have hinv : (s : AlgebraicClosure ℚ)⁻¹ ∈ A := (hA _).2 ⟨s, hs, 1, by simp [hs0]⟩
  exact IsUnit.of_mul_eq_one (b := ⟨_, hinv⟩) (Subtype.ext (mul_inv_cancel₀ hs0))

private theorem ψ_mem_maximalIdeal {z : 𝓞 (AlgebraicClosure ℚ)} (hz : z ∈ Qt) :
    ψ hA z ∈ IsLocalRing.maximalIdeal A := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rintro ⟨u, hu⟩

  have hinvA : ((u⁻¹ : Aˣ) : A).1 ∈ A := ((u⁻¹ : Aˣ) : A).2
  obtain ⟨s, hs, a, hsa⟩ := (hA _).1 hinvA
  apply hs
  have hzu : (z : AlgebraicClosure ℚ) * ((u⁻¹ : Aˣ) : A).1 = 1 := by
    have := congrArg (fun v : A => (v : AlgebraicClosure ℚ)) u.mul_inv
    simpa [hu] using this
  have hs_eq : (s : AlgebraicClosure ℚ) = z * a := by
    calc (s : AlgebraicClosure ℚ) = s * ((z : AlgebraicClosure ℚ) * ((u⁻¹ : Aˣ) : A).1) := by
          rw [hzu, mul_one]
      _ = z * ((s : AlgebraicClosure ℚ) * ((u⁻¹ : Aˣ) : A).1) := by ring
      _ = z * a := by rw [hsa]
  have : s = z * a := NumberField.RingOfIntegers.coe_injective (by simpa using hs_eq)
  exact this ▸ Qt.mul_mem_right a hz

omit [Qt.IsMaximal] in

private theorem liesOverPrime {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓQ : (ℓ : 𝓞 (AlgebraicClosure ℚ)) ∈ Qt) :
    A.LiesOverPrime ℓ := by
  rw [ValuationSubring.LiesOverPrime, ValuationSubring.mem_nonunits_iff_or]
  refine Or.inr fun hinv => ?_
  obtain ⟨s, hs, a, hsa⟩ := (hA _).1 hinv
  apply hs
  have hℓ0 : (ℓ : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  have hs_eq : (s : AlgebraicClosure ℚ) = (ℓ : AlgebraicClosure ℚ) * a := by
    rw [← hsa, mul_left_comm, mul_inv_cancel₀ hℓ0, mul_one]
  have : s = ℓ * a := NumberField.RingOfIntegers.coe_injective (by simpa using hs_eq)
  exact this ▸ Qt.mul_mem_right a hℓQ

omit [Qt.IsMaximal] in

private theorem smul_mem {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσ : ∀ x : 𝓞 (AlgebraicClosure ℚ), σ • x ∈ Qt ↔ x ∈ Qt) {x : AlgebraicClosure ℚ} (hx : x ∈ A) :
    σ • x ∈ A := by
  obtain ⟨s, hs, a, hsa⟩ := (hA x).1 hx
  refine (hA _).2 ⟨σ • s, fun h => hs ((hσ s).1 h), σ • a, ?_⟩
  have : σ • ((s : AlgebraicClosure ℚ) * x) = σ • (a : AlgebraicClosure ℚ) := by rw [hsa]
  rwa [smul_mul'] at this

omit [Qt.IsMaximal] in

private theorem mem_decompositionSubgroup {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hstab : ∀ x : 𝓞 (AlgebraicClosure ℚ), τ • x ∈ Qt ↔ x ∈ Qt) : τ ∈ A.decompositionSubgroup ℚ := by
  have hstab' : ∀ x : 𝓞 (AlgebraicClosure ℚ), τ⁻¹ • x ∈ Qt ↔ x ∈ Qt := fun x => by
    simpa using (hstab (τ⁻¹ • x)).symm
  rw [MulAction.mem_stabilizer_iff]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  exact ⟨fun h => by simpa using smul_mem hA hstab h, fun h => smul_mem hA hstab' h⟩

private theorem smul_ψ {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hτ : τ ∈ A.decompositionSubgroup ℚ)
    (x : 𝓞 (AlgebraicClosure ℚ)) :
    (⟨τ, hτ⟩ : A.decompositionSubgroup ℚ) • ψ hA x = ψ hA (τ • x) := rfl

private theorem smul_residue {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} {ℓ : ℕ}
    (hτ : τ ∈ A.decompositionSubgroup ℚ) (hfrob : ∀ x : 𝓞 (AlgebraicClosure ℚ), τ • x - x ^ ℓ ∈ Qt)
    (y : IsLocalRing.ResidueField A) :
    (⟨τ, hτ⟩ : A.decompositionSubgroup ℚ) • y = y ^ ℓ := by
  set g : A.decompositionSubgroup ℚ := ⟨τ, hτ⟩

  have key : ∀ x : 𝓞 (AlgebraicClosure ℚ),
      g • IsLocalRing.residue A (ψ hA x) = IsLocalRing.residue A (ψ hA x) ^ ℓ := fun x => by
    rw [← IsLocalRing.ResidueField.residue_smul, smul_ψ hA hτ, ← map_pow, ← map_pow, ← sub_eq_zero,
      ← map_sub, IsLocalRing.residue_eq_zero_iff, ← map_sub]
    exact ψ_mem_maximalIdeal hA (hfrob x)

  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
  change g • IsLocalRing.residue A r = IsLocalRing.residue A r ^ ℓ
  obtain ⟨s, hs, a, hsa⟩ := (hA _).1 r.2
  have hsr : ψ hA s * r = ψ hA a := Subtype.ext hsa
  have hu : IsLocalRing.residue A (ψ hA s) ≠ 0 := by
    rw [Ne, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      not_not]
    exact isUnit_ψ hA hs
  have h1 : IsLocalRing.residue A (ψ hA s) * IsLocalRing.residue A r = IsLocalRing.residue A (ψ hA a) := by
    rw [← map_mul, hsr]
  have h2 : g • (IsLocalRing.residue A (ψ hA s) * IsLocalRing.residue A r) =
      IsLocalRing.residue A (ψ hA s) ^ ℓ * g • IsLocalRing.residue A r := by
    rw [smul_mul', key]
  rw [h1, key, ← h1, mul_pow] at h2
  exact (mul_left_cancel₀ (pow_ne_zero ℓ hu) h2).symm

end

end C6PortS10T3b
p2m_reactivate "P2MW.S_ValuationSubring_isFrobeniusAt_of_forall_smul_sub_pow_mem.C6PortS10T3b"

open C6PortS10T3b in
theorem solution
    (Qt : Ideal (𝓞 (AlgebraicClosure ℚ))) [Qt.IsMaximal] (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hℓQ : (ℓ : 𝓞 (AlgebraicClosure ℚ)) ∈ Qt) (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hstab : ∀ x : 𝓞 (AlgebraicClosure ℚ), τ • x ∈ Qt ↔ x ∈ Qt)
    (hfrob : ∀ x : 𝓞 (AlgebraicClosure ℚ), τ • x - x ^ ℓ ∈ Qt)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : ∀ x : AlgebraicClosure ℚ,
      x ∈ A ↔ ∃ s : 𝓞 (AlgebraicClosure ℚ), s ∉ Qt ∧ ∃ a : 𝓞 (AlgebraicClosure ℚ), (s : AlgebraicClosure ℚ) * x = a) :
    A.LiesOverPrime ℓ ∧ A.IsFrobeniusAt τ ℓ := by
  have hA' : C6PortS10T3b.IsLoc Qt A := hA
  have hτ := mem_decompositionSubgroup hA' hstab
  exact ⟨liesOverPrime hA' hℓ hℓQ, hτ, smul_residue hA' hτ hfrob⟩

end S_ValuationSubring_isFrobeniusAt_of_forall_smul_sub_pow_mem
end P2MW
export P2MW.S_ValuationSubring_isFrobeniusAt_of_forall_smul_sub_pow_mem (solution)
