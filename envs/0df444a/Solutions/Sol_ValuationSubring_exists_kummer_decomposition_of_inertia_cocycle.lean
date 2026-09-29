-- Prove2me | solution 1 for ValuationSubring.exists_kummer_decomposition_of_inertia_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/52843a02-10cd-5931-a000-c2cd2d49b966

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_exists_inertia_fixed_kummer_generator_of_additive_character
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_kummer_decomposition_of_inertia_cocycle
p2m_attr_erase "instance" "groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity"
p2m_attr_erase "simp" "groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity"

set_option autoImplicit false

namespace ValuationSubring
p2m_export "ValuationSubring" "LiesOverPrime inertiaSubgroupIn exists_inertia_fixed_kummer_generator_of_additive_character"
namespace C3KummerDecompAux
p2m_open "ValuationSubring"

theorem directSum_nsmul_apply {ι : Type} {β : ι → Type} [∀ i, AddCommMonoid (β i)]
    (a : ℕ) (x : DirectSum ι β) (j : ι) : (a • x) j = a • x j := by
  induction a with
  | zero => rw [zero_nsmul, zero_nsmul, DirectSum.zero_apply]
  | succ a ih => rw [succ_nsmul, succ_nsmul, DirectSum.add_apply, ih]

end ValuationSubring.C3KummerDecompAux

theorem solution
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (N : ℕ)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (p ^ N))
    {M : Type} [AddCommGroup M] [Finite M] (hM : ∀ m : M, (p ^ N) • m = 0)
    (c : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → M)
    (hlev : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ s ∈ P.inertiaSubgroupIn ℚ, s ∈ F.fixingSubgroup → c (τ * s) = c τ)
    (hadd : ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ τ' ∈ P.inertiaSubgroupIn ℚ,
      (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ N = 1 → τ ξ = ξ) →
      (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ N = 1 → τ' ξ = ξ) → c (τ * τ') = c τ + c τ')
    (hconj : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ a : ℕ, σ ζ = ζ ^ a →
      ∀ τ ∈ P.inertiaSubgroupIn ℚ, (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ N = 1 → τ ξ = ξ) →
        c (σ * τ * σ⁻¹) = a • c τ) :
    ∃ (t : ℕ) (x β : Fin t → AlgebraicClosure ℚ) (a : Fin t → M),
      (∀ i, x i ≠ 0) ∧ (∀ i, ∀ σ ∈ P.inertiaSubgroupIn ℚ, σ (x i) = x i) ∧ (∀ i, β i ^ p ^ N = x i) ∧
      ∀ τ ∈ P.inertiaSubgroupIn ℚ, (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ N = 1 → τ ξ = ξ) →
        ∀ k : Fin t → ℕ, (∀ i, τ (β i) = ζ ^ (k i) * β i) → c τ = ∑ i, (k i) • a i := by
  classical

  obtain ⟨ι, _instι, q, hq, e, ⟨φ⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite M
  haveI : ∀ j : ι, NeZero (q j ^ e j) := fun j => ⟨pow_ne_zero _ (hq j).ne_zero⟩

  have hdvd : ∀ j : ι, q j ^ e j ∣ p ^ N := by
    intro j
    apply (CharP.cast_eq_zero_iff (ZMod (q j ^ e j)) (q j ^ e j) (p ^ N)).mp
    have h1 : (p ^ N) • φ.symm (DirectSum.of (fun i => ZMod (q i ^ e i)) j 1) = 0 := hM _
    rw [← map_nsmul, ← map_nsmul, map_eq_zero_iff _ φ.symm.injective] at h1
    have h2 := congrArg (fun y => y j) h1
    simpa only [DirectSum.of_eq_same, DirectSum.zero_apply, nsmul_one] using h2
  choose n hnN hqe using fun j => (Nat.dvd_prime_pow hp).mp (hdvd j)

  let χ : ∀ j : ι, (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → ZMod (p ^ n j) :=
    fun j τ => ZMod.ringEquivCongr (hqe j) (φ (c τ) j)
  have hχlev : ∀ j : ι, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ s ∈ P.inertiaSubgroupIn ℚ, s ∈ F.fixingSubgroup →
        χ j (τ * s) = χ j τ := by
    intro j
    obtain ⟨F, hF, h⟩ := hlev
    exact ⟨F, hF, fun τ hτ s hs hsF => by simp only [χ, h τ hτ s hs hsF]⟩
  have hχadd : ∀ j : ι, ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ τ' ∈ P.inertiaSubgroupIn ℚ,
      (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ N = 1 → τ ξ = ξ) →
      (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ N = 1 → τ' ξ = ξ) →
        χ j (τ * τ') = χ j τ + χ j τ' := by
    intro j τ hτ τ' hτ' h1 h2
    simp only [χ, hadd τ hτ τ' hτ' h1 h2, map_add, DirectSum.add_apply]
  have hχconj : ∀ j : ι, ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ a : ℕ, σ ζ = ζ ^ a →
      ∀ τ ∈ P.inertiaSubgroupIn ℚ, (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ N = 1 → τ ξ = ξ) →
        χ j (σ * τ * σ⁻¹) = a • χ j τ := by
    intro j σ hσ a ha τ hτ h1
    simp only [χ, hconj σ hσ a ha τ hτ h1, map_nsmul,
      ValuationSubring.C3KummerDecompAux.directSum_nsmul_apply]

  choose x γ hx0 hxI hγ hchar using fun j : ι =>
    ValuationSubring.exists_inertia_fixed_kummer_generator_of_additive_character p hp hp2 N (n j)
      (hnN j) P hP ζ hζ (χ j) (hχlev j) (hχadd j) (hχconj j)

  choose β hβ using fun j : ι => IsAlgClosed.exists_pow_nat_eq (γ j) (pow_pos hp.pos (N - n j))
  have hβN : ∀ j : ι, β j ^ p ^ N = x j := fun j => by
    rw [← hγ j, ← hβ j, ← pow_mul, ← pow_add, Nat.sub_add_cancel (hnN j)]

  let g : ι → M := fun j => φ.symm (DirectSum.of (fun i => ZMod (q i ^ e i)) j 1)
  have hval : ∀ (j : ι) (m : ℕ), ((m : ZMod (q j ^ e j)).val) • g j = m • g j := by
    intro j m
    have hper : (q j ^ e j) • g j = 0 := by
      show (q j ^ e j) • φ.symm (DirectSum.of (fun i => ZMod (q i ^ e i)) j 1) = 0
      rw [← map_nsmul, ← map_nsmul, nsmul_one, ZMod.natCast_self, map_zero, map_zero]
    rw [ZMod.val_natCast]
    conv_rhs => rw [← Nat.mod_add_div m (q j ^ e j), add_nsmul, mul_nsmul, hper, nsmul_zero,
      add_zero]

  let eι := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun i => x (eι.symm i), fun i => β (eι.symm i), fun i => g (eι.symm i),
    fun i => hx0 _, fun i σ hσ => hxI _ σ hσ, fun i => hβN _, ?_⟩
  intro τ hτ hτN k hk

  have hcoord : ∀ j : ι, χ j τ = ((k (eι j) : ℕ) : ZMod (p ^ n j)) := by
    intro j
    apply hchar j τ hτ hτN
    have hkj := hk (eι j)
    simp only [Equiv.symm_apply_apply] at hkj
    rw [← hβ j, map_pow, hkj, mul_pow, ← pow_mul, ← pow_mul, mul_comm (p ^ (N - n j)) (k (eι j))]

  have hdecomp : c τ = ∑ j, (φ (c τ) j).val • g j := by
    apply φ.injective
    rw [map_sum]
    conv_lhs => rw [← DirectSum.sum_univ_of (φ (c τ))]
    refine Finset.sum_congr rfl fun j _ => ?_
    show DirectSum.of (fun i => ZMod (q i ^ e i)) j (φ (c τ) j) = φ ((φ (c τ) j).val • g j)
    rw [map_nsmul, AddEquiv.apply_symm_apply, ← map_nsmul, nsmul_one, ZMod.natCast_zmod_val]
  rw [hdecomp]
  refine Fintype.sum_equiv eι _ _ fun j => ?_
  simp only [Equiv.symm_apply_apply]
  have hφj : φ (c τ) j = ((k (eι j) : ℕ) : ZMod (q j ^ e j)) := by
    have h := hcoord j
    simp only [χ] at h
    apply (ZMod.ringEquivCongr (hqe j)).injective
    rw [h, map_natCast]
  rw [hφj, hval]

end S_ValuationSubring_exists_kummer_decomposition_of_inertia_cocycle
end P2MW
export P2MW.S_ValuationSubring_exists_kummer_decomposition_of_inertia_cocycle (solution)
