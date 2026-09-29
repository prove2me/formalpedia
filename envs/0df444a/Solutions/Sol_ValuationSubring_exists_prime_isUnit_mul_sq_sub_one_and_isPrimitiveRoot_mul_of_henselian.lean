-- Prove2me | solution 1 for ValuationSubring.exists_prime_isUnit_mul_sq_sub_one_and_isPrimitiveRoot_mul_of_henselian
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/eaf1bb0d-5ac3-5870-9bbd-ad5ce86fe29a

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_prime_isUnit_mul_sq_sub_one_and_isPrimitiveRoot_mul_of_henselian

set_option autoImplicit false

open IsLocalRing

theorem AUXaux_exists_emb (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (m : ℕ) [NeZero m]
    (ξ : ↥k₀) (hξ : IsPrimitiveRoot ξ m) :
    ∃ ι : ↥k₀ →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / m) := by
  haveI hQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    have h := AlgebraicClosure.isAlgebraic ℚ
    convert h
    rfl
    rfl
  haveI : Algebra.IsAlgebraic ℚ ↥k₀ :=
    Algebra.IsAlgebraic.of_injective (k₀.val) (k₀.val).toRingHom.injective
  have hmin : minpoly ℚ ξ = Polynomial.cyclotomic m ℚ :=
    (Polynomial.cyclotomic_eq_minpoly_rat hξ (Nat.pos_of_ne_zero (NeZero.ne m))).symm
  have hroot : Complex.exp (2 * Real.pi * Complex.I / m) ∈ (minpoly ℚ ξ).rootSet ℂ := by
    rw [hmin, Polynomial.mem_rootSet]
    refine ⟨Polynomial.cyclotomic_ne_zero m ℚ, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact (Polynomial.isRoot_cyclotomic_iff.mpr (Complex.isPrimitiveRoot_exp m (NeZero.ne m))).eq_zero
  rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly ℂ ξ] at hroot
  obtain ⟨ψ, hψ⟩ := hroot
  exact ⟨ψ.toRingHom, hψ⟩

theorem AUXaux_mem_of_pow_eq_one {K : Type} [Field K] (A : ValuationSubring K) {x : K} {n : ℕ} (hn : 0 < n)
    (hx : x ^ n = 1) : x ∈ A := by
  rcases A.mem_or_inv_mem x with h | h
  · exact h
  · have hx0 : x ≠ 0 := by rintro rfl; rw [zero_pow hn.ne'] at hx; exact zero_ne_one hx
    have : x = (x⁻¹) ^ (n - 1) := by
      have e : x * x ^ (n - 1) = 1 := by rw [← pow_succ', Nat.sub_add_cancel hn]; exact hx
      rw [inv_pow]; exact eq_inv_of_mul_eq_one_left e
    rw [this]; exact pow_mem h _

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M']
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (ζq : ↥k₀) (hζq : IsPrimitiveRoot ((ζq : ↥k₀) : AlgebraicClosure ℚ) q)

    (ϖt : ↥k₀) (hϖtA : (ϖt : AlgebraicClosure ℚ) ∈ A)
    (hϖt : ∃ u : ↥A, IsUnit u ∧ (ϖt : AlgebraicClosure ℚ) ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ) * (u : AlgebraicClosure ℚ)) :

    (∃ u : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), IsUnit u ∧
      (⟨ϖt, hϖtA⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ^ (q ^ 2 - 1) = (q : _) * u) ∧
    ∃ (ℓ : ℕ), ℓ.Prime ∧ 3 ≤ ℓ ∧ ℓ ≠ q ∧ ¬ ℓ ∣ M' ∧
      IsUnit ((ℓ * (ℓ ^ 2 - 1) : ℕ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ∧
      ∃ ξ : ↥k₀, IsPrimitiveRoot ξ (q * ℓ) ∧ ((ξ : ↥k₀) : AlgebraicClosure ℚ) ∈ A ∧
        ∃ ι : ↥k₀ →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)) := by
  classical
  have hqp : q.Prime := Fact.out
  set R₀ := A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)) with hR₀def
  haveI := hhens

  have hqmem : ((q : ℕ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ∈ maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hu' := hu.map (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀)

    have hqA : ((q : ℕ) : ↥A) ∈ maximalIdeal ↥A := by
      have hq' : (((q : ℕ) : ↥A) : AlgebraicClosure ℚ) = (q : AlgebraicClosure ℚ) := by norm_cast
      rw [← ValuationSubring.coe_mem_nonunits_iff, hq']; exact hA
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hqA
    apply hqA
    obtain ⟨v, hv⟩ := hu
    refine isUnit_iff_exists_inv.mpr ⟨⟨(((v⁻¹ : (↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))ˣ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) : ↥k₀), ((v⁻¹ : (↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))ˣ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))).2⟩, Subtype.ext ?_⟩
    have e := congrArg (fun z : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) => (((z : ↥k₀)) : AlgebraicClosure ℚ)) v.mul_inv
    rw [hv] at e
    push_cast at e ⊢
    simpa using e
  haveI hchar : CharP (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) q := by
    have h0 : ((q : ℕ) : ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) = 0 := by
      rw [← map_natCast (IsLocalRing.residue ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))), IsLocalRing.residue_eq_zero_iff]; exact hqmem
    exact (CharP.charP_iff_prime_eq_zero hqp).mpr h0

  have hunit_of_not_dvd : ∀ n : ℕ, ¬ q ∣ n → IsUnit ((n : ℕ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) := by
    intro n hn
    by_contra hnu
    have hmem : ((n : ℕ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ∈ maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have h0 : ((n : ℕ) : ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) = 0 := by
      rw [← map_natCast (IsLocalRing.residue ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))), IsLocalRing.residue_eq_zero_iff]; exact hmem
    exact hn ((CharP.cast_eq_zero_iff (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) q n).mp h0)
  refine ⟨?_, ?_⟩
  ·
    obtain ⟨u, hu, hϖ⟩ := hϖt
    have hq0 : (q : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast hqp.ne_zero
    have huval : (u : AlgebraicClosure ℚ) = ((ϖt ^ (q ^ 2 - 1) / (q : ↥k₀) : ↥k₀) : AlgebraicClosure ℚ) := by
      push_cast
      rw [hϖ, mul_div_cancel_left₀ _ hq0]
    have huk : ((ϖt ^ (q ^ 2 - 1) / (q : ↥k₀) : ↥k₀) : AlgebraicClosure ℚ) ∈ A := by rw [← huval]; exact u.2
    obtain ⟨w, hw⟩ := hu
    have hwinv : (((w⁻¹ : (↥A)ˣ) : ↥A) : AlgebraicClosure ℚ) = ((u : AlgebraicClosure ℚ))⁻¹ := by
      rw [← hw]
      have e := congrArg (fun z : ↥A => (z : AlgebraicClosure ℚ)) w.inv_mul
      push_cast at e
      exact eq_inv_of_mul_eq_one_left e
    have huinvk : (((ϖt ^ (q ^ 2 - 1) / (q : ↥k₀))⁻¹ : ↥k₀) : AlgebraicClosure ℚ) ∈ A := by
      push_cast
      rw [← show (u : AlgebraicClosure ℚ) = (ϖt : AlgebraicClosure ℚ) ^ (q ^ 2 - 1) / (q : AlgebraicClosure ℚ) from by
        rw [huval]; push_cast; rfl, ← hwinv]
      exact ((w⁻¹ : (↥A)ˣ) : ↥A).2
    refine ⟨⟨ϖt ^ (q ^ 2 - 1) / (q : ↥k₀), huk⟩, ?_, ?_⟩
    · refine isUnit_iff_exists_inv.mpr ⟨⟨(ϖt ^ (q ^ 2 - 1) / (q : ↥k₀))⁻¹, huinvk⟩, Subtype.ext ?_⟩
      change ϖt ^ (q ^ 2 - 1) / (q : ↥k₀) * (ϖt ^ (q ^ 2 - 1) / (q : ↥k₀))⁻¹ = 1
      apply mul_inv_cancel₀
      intro h0
      have : (u : AlgebraicClosure ℚ) = 0 := by rw [huval, h0]; rfl
      exact w.ne_zero (by rw [hw]; exact Subtype.ext this)
    · apply Subtype.ext
      change ϖt ^ (q ^ 2 - 1) = (((q : ℕ) : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) : ↥k₀) * (ϖt ^ (q ^ 2 - 1) / (q : ↥k₀))
      have hqk : (q : ↥k₀) ≠ 0 := by exact_mod_cast hqp.ne_zero
      push_cast
      rw [← mul_div_assoc, mul_div_cancel_left₀ _ hqk]
  ·
    have h2unit : IsUnit ((2 : ℕ) : ZMod q) := by
      haveI : Fact (1 < q) := ⟨hqp.one_lt⟩
      rw [isUnit_iff_ne_zero, ne_eq, ZMod.natCast_eq_zero_iff]
      intro h; have := Nat.le_of_dvd two_pos h; omega
    obtain ⟨ℓ, hℓgt, hℓp, hℓmod⟩ := Nat.forall_exists_prime_gt_and_eq_mod h2unit (max M' q)
    have hℓq : ℓ ≠ q := by intro h; rw [h] at hℓgt; exact absurd hℓgt (by simp)
    have hℓM : ¬ ℓ ∣ M' := by
      intro h; have := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M')) h
      have : M' < ℓ := lt_of_le_of_lt (le_max_left _ _) hℓgt
      omega
    have hℓ3 : 3 ≤ ℓ := by
      have : q < ℓ := lt_of_le_of_lt (le_max_right _ _) hℓgt
      omega
    haveI : Fact ℓ.Prime := ⟨hℓp⟩

    have hndvd : ¬ q ∣ ℓ * (ℓ ^ 2 - 1) := by
      intro hd
      have hcast : ((ℓ * (ℓ ^ 2 - 1) : ℕ) : ZMod q) = 6 := by
        have h1 : 1 ≤ ℓ ^ 2 := Nat.one_le_pow _ _ hℓp.pos
        push_cast [h1]
        rw [hℓmod]; norm_num
      have h6 : ((6 : ℕ) : ZMod q) = 0 := by
        rw [← (ZMod.natCast_eq_zero_iff _ _).mpr hd]
        push_cast at hcast ⊢
        exact hcast.symm
      rw [ZMod.natCast_eq_zero_iff] at h6
      have := (Nat.Prime.dvd_mul hqp).mp (show q ∣ 2 * 3 from h6)
      rcases this with h | h
      · have := Nat.le_of_dvd two_pos h; omega
      · have := Nat.le_of_dvd (by norm_num) h; omega
    refine ⟨ℓ, hℓp, hℓ3, hℓq, hℓM, hunit_of_not_dvd _ hndvd, ?_⟩

    haveI : NeZero ((ℓ : ℕ) : ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) := ⟨by
      rw [Ne, CharP.cast_eq_zero_iff (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) q]
      intro h; exact hℓq ((Nat.prime_dvd_prime_iff_eq hqp hℓp).mp h).symm⟩
    obtain ⟨ab, hab⟩ : ∃ ab : ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))), (Polynomial.cyclotomic ℓ (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))).IsRoot ab :=
      IsAlgClosed.exists_root _ (by rw [Polynomial.degree_cyclotomic]; exact_mod_cast (Nat.totient_pos.mpr hℓp.pos).ne')
    obtain ⟨a₀, ha₀⟩ := IsLocalRing.residue_surjective ab
    have hf : (Polynomial.cyclotomic ℓ ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))).Monic := Polynomial.cyclotomic.monic ℓ _
    have heval : (Polynomial.cyclotomic ℓ ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))).eval a₀ ∈ maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) := by
      rw [← IsLocalRing.residue_eq_zero_iff, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, Polynomial.map_cyclotomic, ha₀]
      exact hab
    have hder : IsUnit ((Polynomial.cyclotomic ℓ ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))).derivative.eval a₀) := by
      by_contra hnu
      have hmem : (Polynomial.cyclotomic ℓ ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))).derivative.eval a₀ ∈ maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) := (IsLocalRing.mem_maximalIdeal _).mpr hnu
      rw [← IsLocalRing.residue_eq_zero_iff, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, ← Polynomial.derivative_map,
        Polynomial.map_cyclotomic, ha₀] at hmem
      have hsep := Polynomial.separable_cyclotomic ℓ (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
      exact hsep.aeval_derivative_ne_zero (x := ab) (by rw [Polynomial.coe_aeval_eq_eval]; exact hab)
        (by rw [Polynomial.coe_aeval_eq_eval]; exact hmem)
    obtain ⟨a, ha, -⟩ := HenselianLocalRing.is_henselian (Polynomial.cyclotomic ℓ ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) hf a₀ heval hder

    have haK : IsPrimitiveRoot ((a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) : ↥k₀) ℓ := by
      haveI : NeZero ((ℓ : ℕ) : ↥k₀) := ⟨by exact_mod_cast hℓp.ne_zero⟩
      rw [← Polynomial.isRoot_cyclotomic_iff]
      have := ha.map (f := algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ↥k₀)
      rwa [Polynomial.map_cyclotomic] at this

    have hζqK : IsPrimitiveRoot ζq q :=
      hζq.of_map_of_injective (f := (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (algebraMap ↥k₀ (AlgebraicClosure ℚ)).injective
    have hζqA : ((ζq : ↥k₀) : AlgebraicClosure ℚ) ∈ A := AUXaux_mem_of_pow_eq_one A hqp.pos hζq.pow_eq_one

    refine ⟨ζq * ((a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) : ↥k₀), ?_, ?_, ?_⟩
    · rw [IsPrimitiveRoot.iff_orderOf, (Commute.all _ _).orderOf_mul_eq_mul_orderOf_of_coprime]
      · rw [hζqK.eq_orderOf.symm, haK.eq_orderOf.symm]
      · rw [← hζqK.eq_orderOf, ← haK.eq_orderOf]
        exact (Nat.coprime_primes hqp hℓp).mpr hℓq.symm
    · push_cast
      exact mul_mem hζqA a.2
    · haveI : NeZero (q * ℓ) := ⟨Nat.mul_ne_zero hqp.ne_zero hℓp.ne_zero⟩
      have hprim : IsPrimitiveRoot (ζq * ((a : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) : ↥k₀)) (q * ℓ) := by
        rw [IsPrimitiveRoot.iff_orderOf, (Commute.all _ _).orderOf_mul_eq_mul_orderOf_of_coprime]
        · rw [hζqK.eq_orderOf.symm, haK.eq_orderOf.symm]
        · rw [← hζqK.eq_orderOf, ← haK.eq_orderOf]
          exact (Nat.coprime_primes hqp hℓp).mpr hℓq.symm
      obtain ⟨ι, hι⟩ := AUXaux_exists_emb k₀ (q * ℓ) _ hprim
      exact ⟨ι, by rw [hι]; simp only [Nat.cast_mul]⟩

end S_ValuationSubring_exists_prime_isUnit_mul_sq_sub_one_and_isPrimitiveRoot_mul_of_henselian
end P2MW
export P2MW.S_ValuationSubring_exists_prime_isUnit_mul_sq_sub_one_and_isPrimitiveRoot_mul_of_henselian (solution)
