-- Prove2me | solution 1 for QuaternionAlgebra.IsOrder.forall_tmul_one_mem_localBox_iff_exists_pow_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/17fb0e4d-e565-5204-ae23-8197f20cccfd

import Mathlib
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_basis_span_eq
import Theorems.Thm_Submodule_mem_localBox_iff_exists_eq_sum_basis_tmul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsOrder_forall_tmul_one_mem_localBox_iff_exists_pow_smul_mem

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

namespace LGM

local notation "Kv" v => IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v
local notation "Ov" v => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v

section Places

variable (w : HeightOneSpectrum (𝓞 ℚ))

abbrev ℓ : ℕ := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) w : ℕ)

theorem ℓ_prime : (ℓ w).Prime := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) w).2

theorem intCast_mem_asIdeal_iff (z : ℤ) : (z : 𝓞 ℚ) ∈ w.asIdeal ↔ (ℓ w : ℤ) ∣ z := by
  rw [← Ideal.apply_mem_of_equiv_iff (f := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)), map_intCast,
    ← Rat.HeightOneSpectrum.span_natGenerator, Ideal.mem_span_singleton, Int.cast_id]
  rfl

theorem natCast_mem_asIdeal_iff (n : ℕ) : (n : 𝓞 ℚ) ∈ w.asIdeal ↔ ℓ w ∣ n := by
  rw [show (n : 𝓞 ℚ) = ((n : ℤ) : 𝓞 ℚ) from (Int.cast_natCast n).symm, intCast_mem_asIdeal_iff, Int.natCast_dvd_natCast]

theorem ℓ_eq_of_prime_mem {p : ℕ} (hp : p.Prime) (hpw : (p : 𝓞 ℚ) ∈ w.asIdeal) : ℓ w = p :=
  (Nat.prime_dvd_prime_iff_eq (ℓ_prime w) hp).mp ((natCast_mem_asIdeal_iff w p).mp hpw)

theorem eq_of_ℓ_eq {w w' : HeightOneSpectrum (𝓞 ℚ)} (h : ℓ w = ℓ w') : w = w' :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective (Subtype.ext h)

theorem exists_ℓ_eq (p : ℕ) (hp : p.Prime) : ∃ w : HeightOneSpectrum (𝓞 ℚ), ℓ w = p :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hp⟩, by
    rw [ℓ, Equiv.apply_symm_apply]⟩

theorem valued_algebraMap (q : ℚ) :
    Valued.v (algebraMap ℚ (Kv w) q) = w.valuation ℚ q := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w q

theorem valuation_intCast_eq_one_iff (z : ℤ) : w.valuation ℚ (z : ℚ) = 1 ↔ ¬ (ℓ w : ℤ) ∣ z := by
  rw [show (z : ℚ) = algebraMap (𝓞 ℚ) ℚ (z : 𝓞 ℚ) from (map_intCast _ _).symm,
    HeightOneSpectrum.valuation_eq_one_iff_notMem, intCast_mem_asIdeal_iff]

theorem valuation_natCast_lt_one_iff (n : ℕ) : w.valuation ℚ (n : ℚ) < 1 ↔ ℓ w ∣ n := by
  rw [show (n : ℚ) = algebraMap (𝓞 ℚ) ℚ (n : 𝓞 ℚ) from (map_natCast _ _).symm,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_lt_one_iff_dvd,
    Ideal.dvd_span_singleton, natCast_mem_asIdeal_iff]

theorem valuation_natCast_le_one (n : ℕ) : w.valuation ℚ (n : ℚ) ≤ 1 := by
  rw [show (n : ℚ) = algebraMap (𝓞 ℚ) ℚ (n : 𝓞 ℚ) from (map_natCast _ _).symm,
    HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_le_one _ _

theorem exists_pow_mul_den_of_forall_valuation_le_one (r : ℕ) (hr : r.Prime) (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) (q : ℚ)
    (hq : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → w.valuation ℚ q ≤ 1) :
    ∃ K : ℕ, ∃ m : ℤ, ((r ^ K : ℕ) : ℚ) * q = m := by
  have hrv : ℓ v = r := ℓ_eq_of_prime_mem v hr hv

  have hden : ∀ {p : ℕ}, p.Prime → p ∣ q.den → p = r := by
    intro p hp hpd
    by_contra hpr
    obtain ⟨w, hw⟩ := exists_ℓ_eq p hp
    have hwv : w ≠ v := fun h => hpr (by rw [← hw, h, hrv])
    have h1 := hq w hwv

    have hnum : w.valuation ℚ (q.num : ℚ) = 1 := by
      rw [valuation_intCast_eq_one_iff, hw]
      intro hdvd
      have h2 : p ∣ q.num.natAbs := Int.natCast_dvd.mp hdvd
      have := Nat.dvd_gcd h2 hpd
      rw [q.reduced] at this
      exact hp.one_lt.ne' (Nat.dvd_one.mp this)
    have hden' : w.valuation ℚ (q.den : ℚ) < 1 := by
      rw [valuation_natCast_lt_one_iff, hw]; exact hpd
    have hq' : w.valuation ℚ q = w.valuation ℚ (q.num : ℚ) / w.valuation ℚ (q.den : ℚ) := by
      rw [← map_div₀, Rat.num_div_den]
    have hden0 : w.valuation ℚ (q.den : ℚ) ≠ 0 :=
      (Valuation.ne_zero_iff _).mpr (Nat.cast_ne_zero.mpr q.den_nz)
    rw [hq', hnum, one_div] at h1
    exact absurd (one_lt_inv_iff₀.mpr ⟨zero_lt_iff.mpr hden0, hden'⟩) (not_lt.mpr h1)
  have hK : q.den = r ^ q.den.primeFactorsList.length := Nat.eq_prime_pow_of_unique_prime_dvd q.den_nz hden
  refine ⟨q.den.primeFactorsList.length, q.num, ?_⟩
  rw [← hK, mul_comm, Rat.mul_den_eq_num]

end Places

section Coords

variable {a b : ℚ} (w : HeightOneSpectrum (𝓞 ℚ))

theorem coords_unique (B : Module.Basis (Fin 4) ℚ ℍ[ℚ, a, b]) (c d : Fin 4 → (Kv w))
    (h : ∑ i, B i ⊗ₜ[ℚ] c i = ∑ i, B i ⊗ₜ[ℚ] d i) : c = d := by
  classical
  have key : ∀ e : Fin 4 → (Kv w), ∀ j,
      (Algebra.TensorProduct.basis (Kv w) B).repr
        (Algebra.TensorProduct.comm ℚ ℍ[ℚ, a, b] (Kv w) (∑ i, B i ⊗ₜ[ℚ] e i)) j = e j := by
    intro e j
    rw [map_sum (Algebra.TensorProduct.comm ℚ ℍ[ℚ, a, b] (Kv w)), map_sum (Algebra.TensorProduct.basis (Kv w) B).repr,
      Finsupp.finset_sum_apply]
    simp only [Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.basis_repr_tmul,
      Module.Basis.repr_self, Finsupp.mapRange_single, map_one, Finsupp.smul_single, smul_eq_mul, mul_one,
      Finsupp.single_apply]
    simp [Finset.sum_ite_eq']
  funext j
  rw [← key c j, ← key d j, h]

theorem smul_tmul_one (q : ℚ) (z : ℍ[ℚ, a, b]) :
    (q • z) ⊗ₜ[ℚ] (1 : (Kv w)) = z ⊗ₜ[ℚ] (algebraMap ℚ (Kv w) q) := by
  rw [TensorProduct.smul_tmul, Algebra.smul_def, mul_one]

end Coords

theorem main {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsOrder Λ)
    (r : ℕ) [Fact r.Prime] (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (y : ℍ[ℚ, a, b]) :
    (∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → y ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) ∈ Submodule.localBox Λ w) ↔
      ∃ K : ℕ, ((r ^ K : ℕ) : ℚ) • y ∈ Λ := by
  classical
  have hr : r.Prime := Fact.out
  have hrv : ℓ v = r := ℓ_eq_of_prime_mem v hr hv

  have hrw : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → ∀ K : ℕ, ((r ^ K : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := by
    intro w hwv K hmem
    rw [natCast_mem_asIdeal_iff] at hmem
    have := (Nat.prime_dvd_prime_iff_eq (ℓ_prime w) hr).mp ((ℓ_prime w).dvd_of_dvd_pow hmem)
    exact hwv (eq_of_ℓ_eq (this.trans hrv.symm))
  obtain ⟨B, hBΛ, hspan⟩ := QuaternionAlgebra.IsOrder.exists_basis_span_eq hΛ
  constructor
  · intro hy

    have hcoord : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → ∀ i, w.valuation ℚ (B.repr y i) ≤ 1 := by
      intro w hwv i
      obtain ⟨c, hc, hyc⟩ := (Submodule.mem_localBox_iff_exists_eq_sum_basis_tmul B Λ hspan w _).1 (hy w hwv)
      have hy' : y ⊗ₜ[ℚ] (1 : Kv w) = ∑ i, B i ⊗ₜ[ℚ] algebraMap ℚ (Kv w) (B.repr y i) := by
        conv_lhs => rw [← B.sum_repr y]
        rw [TensorProduct.sum_tmul]
        exact Finset.sum_congr rfl fun i _ => smul_tmul_one w _ _
      have := congrFun (coords_unique w B _ _ (hy'.symm.trans hyc)) i
      rw [← valued_algebraMap, this]
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hc i)

    have hK : ∀ i, ∃ K : ℕ, ∃ m : ℤ, ((r ^ K : ℕ) : ℚ) * B.repr y i = m := fun i =>
      exists_pow_mul_den_of_forall_valuation_le_one r hr v hv _ (fun w hwv => hcoord w hwv i)
    choose K m hKm using hK
    refine ⟨∑ i, K i, ?_⟩
    rw [← B.sum_repr y, Finset.smul_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [smul_smul]

    have hle : K i ≤ ∑ j, K j := Finset.single_le_sum (fun j _ => Nat.zero_le (K j)) (Finset.mem_univ i)
    have : ((r ^ ∑ j, K j : ℕ) : ℚ) * B.repr y i = ((((r ^ (∑ j, K j - K i) : ℕ)) : ℤ) * m i : ℤ) := by
      conv_lhs => rw [← Nat.sub_add_cancel hle, pow_add, Nat.cast_mul, mul_assoc, hKm i]
      push_cast
      ring
    rw [this, Int.cast_smul_eq_zsmul]
    rw [← hspan]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rintro ⟨K, hK⟩ w hwv
    have hK0 : ((r ^ K : ℕ) : Kv w) ≠ 0 := by
      have := (map_ne_zero (algebraMap ℚ (Kv w))).mpr
        (Nat.cast_ne_zero.mpr (pow_ne_zero K hr.ne_zero) : ((r ^ K : ℕ) : ℚ) ≠ 0)
      rwa [map_natCast] at this
    have hinv : (((r ^ K : ℕ) : Kv w))⁻¹ ∈ Ov w := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀]
      have h1 : Valued.v (((r ^ K : ℕ) : Kv w)) = 1 := by
        rw [show ((r ^ K : ℕ) : Kv w) = algebraMap ℚ (Kv w) ((r ^ K : ℕ) : ℚ) from (map_natCast _ _).symm,
          valued_algebraMap, show ((r ^ K : ℕ) : ℚ) = algebraMap (𝓞 ℚ) ℚ ((r ^ K : ℕ) : 𝓞 ℚ) from (map_natCast _ _).symm]
        exact (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := ℚ) (v := w) (r := ((r ^ K : ℕ) : 𝓞 ℚ))).2 (hrw w hwv K)
      rw [h1, inv_one]
    have e : y ⊗ₜ[ℚ] (1 : Kv w) = (((r ^ K : ℕ) : ℚ) • y) ⊗ₜ[ℚ] (((r ^ K : ℕ) : Kv w))⁻¹ := by
      rw [TensorProduct.smul_tmul, Algebra.smul_def, map_natCast, mul_inv_cancel₀ hK0]
    rw [e]
    exact AddSubgroup.subset_closure ⟨_, hK, _, hinv, rfl⟩

end LGM

end

open scoped TensorProduct Quaternion NumberField
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem solution
    {a₁ b₁ : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ : IsOrder Λ)
    (r : ℕ) [Fact r.Prime] (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (y : ℍ[ℚ, a₁, b₁]) :
    (∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → y ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) ∈ Submodule.localBox Λ w) ↔
      ∃ K : ℕ, ((r ^ K : ℕ) : ℚ) • y ∈ Λ := by
  exact LGM.main Λ hΛ r v hv y

end S_QuaternionAlgebra_IsOrder_forall_tmul_one_mem_localBox_iff_exists_pow_smul_mem
end P2MW
export P2MW.S_QuaternionAlgebra_IsOrder_forall_tmul_one_mem_localBox_iff_exists_pow_smul_mem (solution)
