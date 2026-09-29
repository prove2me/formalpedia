-- Prove2me | solution 1 for QuaternionAlgebra.exists_linearMap_matrix_zmod_pow_of_isMaximalOrder_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/bd0f8303-d4e8-566a-8d73-972a5e413e1b

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_ringEquiv_mem_localBox_iff_of_isIndefiniteRamifiedExactlyAt_of_prime
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_basis_span_eq
import Theorems.Thm_Submodule_mem_localBox_iff_exists_eq_sum_basis_tmul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_exists_linearMap_matrix_zmod_pow_of_isMaximalOrder_of_ne
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open scoped Quaternion TensorProduct
open QuaternionAlgebra IsDedekindDomain NumberField

namespace ASM21
namespace T2

theorem primesEquiv_symm_coe (ℓ : ℕ) [Fact ℓ.Prime] :
    ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨ℓ, Fact.out⟩ |> Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) : ℕ) = ℓ := by
  rw [Equiv.apply_symm_apply]

theorem eq_of_natCast_mem_asIdeal (v : HeightOneSpectrum (𝓞 ℚ)) {r : ℕ} (hr : r.Prime) (h : (r : 𝓞 ℚ) ∈ v.asIdeal) :
    (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v : ℕ) = r := by
  have hdvd : Rat.HeightOneSpectrum.natGenerator v ∣ r := by
    rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff]
    have := Ideal.mem_map_of_mem (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) h
    simpa using this
  exact (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator v) hr).1 hdvd

end ASM21.T2

namespace ASM21
namespace T2

theorem coeff_eq_of_sum_tmul_eq {a b : ℚ} {ι : Type} [Fintype ι] [DecidableEq ι] (B : Module.Basis ι ℚ ℍ[ℚ, a, b])
    {K : Type} [CommRing K] [Algebra ℚ K] (c c' : ι → K)
    (h : ∑ i, B i ⊗ₜ[ℚ] c i = ∑ i, B i ⊗ₜ[ℚ] c' i) : c = c' := by
  funext i
  let T : ℍ[ℚ, a, b] ⊗[ℚ] K →ₗ[ℚ] K :=
    (TensorProduct.lid ℚ K).toLinearMap ∘ₗ TensorProduct.map (B.coord i) LinearMap.id
  have hT : ∀ (j : ι) (x : K), T (B j ⊗ₜ[ℚ] x) = if j = i then x else 0 := by
    intro j x
    simp only [T, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply, LinearEquiv.coe_toLinearMap,
      TensorProduct.lid_tmul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs with h1
    · subst h1; simp
    · simp
  have := congrArg T h
  simp only [map_sum, hT, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
  exact this

end ASM21.T2

set_option autoImplicit false

open IsDedekindDomain NumberField

namespace ASM21
namespace T2

scoped instance instFactPrimeCoeNatPrimes (q : Nat.Primes) : Fact (Nat.Prime (q : ℕ)) := ⟨q.2⟩

section RED

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "𝔭" => (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v : ℕ)

local notation "𝒪" => (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)

theorem coe_primesEquiv_eq_natGenerator :
    𝔭 = Rat.HeightOneSpectrum.natGenerator v := rfl

theorem prime_coe_primesEquiv : Nat.Prime 𝔭 := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v).2

noncomputable def red : ↥𝒪 →+* ZMod 𝔭 :=
  PadicInt.toZMod.comp
    (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv (R := 𝓞 ℚ) v).toRingEquiv.toRingHom

theorem red_apply (c : ↥𝒪) :
    red v c = PadicInt.toZMod
      ((Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv (R := 𝓞 ℚ) v).toRingEquiv c) :=
  rfl

theorem red_intCast (n : ℤ) : red v (n : ↥𝒪) = (n : ZMod 𝔭) := map_intCast (red v) n

theorem exists_intCast_red_eq (t : ZMod 𝔭) : ∃ n : ℤ, red v (n : ↥𝒪) = t := by
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective t
  exact ⟨n, red_intCast v n⟩

theorem red_eq_zero_iff (c : ↥𝒪) : red v c = 0 ↔ ∃ d : ↥𝒪, c = (𝔭 : ↥𝒪) * d := by
  set e := (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv (R := 𝓞 ℚ) v).toRingEquiv
    with he
  rw [red_apply, ← he, ← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton, show ((𝔭 : ℕ) : ℤ_[𝔭]) = e (𝔭 : ↥𝒪) from (map_natCast e _).symm,
    map_dvd_iff]
  rfl

theorem natCast_dvd_of_intCast_eq_mul (m : ℤ) (h : ∃ d : ↥𝒪, (m : ↥𝒪) = (𝔭 : ↥𝒪) * d) :
    (𝔭 : ℤ) ∣ m := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← red_intCast v m]
  exact (red_eq_zero_iff v _).2 h

theorem intCast_eq_mul_iff (m : ℤ) :
    (∃ d : ↥𝒪, (m : ↥𝒪) = (𝔭 : ↥𝒪) * d) ↔ (𝔭 : ℤ) ∣ m := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← red_intCast v m, red_eq_zero_iff]

theorem intCast_adicCompletion_eq_coe (n : ℤ) :
    (n : v.adicCompletion ℚ) = ((n : ↥𝒪) : v.adicCompletion ℚ) := by
  simp

theorem natCast_adicCompletion_eq_coe (n : ℕ) :
    (n : v.adicCompletion ℚ) = ((n : ↥𝒪) : v.adicCompletion ℚ) := by
  simp

theorem natCast_mem_asIdeal_iff {r : ℕ} (hr : r.Prime) : (r : 𝓞 ℚ) ∈ v.asIdeal ↔ 𝔭 = r := by
  have key : (r : 𝓞 ℚ) ∈ v.asIdeal ↔ Rat.HeightOneSpectrum.natGenerator v ∣ r := by
    rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff,
      ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) r, Ideal.apply_mem_of_equiv_iff]
  rw [key, coe_primesEquiv_eq_natGenerator]
  exact Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator v) hr

theorem natCast_primesEquiv_mem_asIdeal : ((𝔭 : ℕ) : 𝓞 ℚ) ∈ v.asIdeal :=
  (natCast_mem_asIdeal_iff v (prime_coe_primesEquiv v)).2 rfl

end RED

section REDof

variable (v : HeightOneSpectrum (𝓞 ℚ)) {ℓ : ℕ}
  (hℓ : (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v : ℕ) = ℓ)

local notation "𝒪" => (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)

noncomputable def redOf : ↥𝒪 →+* ZMod ℓ := (ZMod.ringEquivCongr hℓ).toRingHom.comp (red v)

theorem redOf_def : redOf v hℓ =
    (ZMod.ringEquivCongr hℓ).toRingHom.comp (PadicInt.toZMod.comp
      (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv (R := 𝓞 ℚ) v).toRingEquiv.toRingHom) :=
  rfl

theorem redOf_apply (c : ↥𝒪) : redOf v hℓ c = ZMod.ringEquivCongr hℓ (red v c) := rfl

theorem redOf_intCast (n : ℤ) : redOf v hℓ (n : ↥𝒪) = (n : ZMod ℓ) := map_intCast (redOf v hℓ) n

theorem exists_intCast_redOf_eq (t : ZMod ℓ) : ∃ n : ℤ, redOf v hℓ (n : ↥𝒪) = t := by
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective t
  exact ⟨n, redOf_intCast v hℓ n⟩

theorem redOf_eq_zero_iff (c : ↥𝒪) : redOf v hℓ c = 0 ↔ ∃ d : ↥𝒪, c = (ℓ : ↥𝒪) * d := by
  subst hℓ
  rw [redOf_apply, RingEquiv.map_eq_zero_iff, red_eq_zero_iff]

include hℓ in

theorem intCast_eq_mul_iff_of (m : ℤ) :
    (∃ d : ↥𝒪, (m : ↥𝒪) = (ℓ : ↥𝒪) * d) ↔ (ℓ : ℤ) ∣ m := by
  subst hℓ
  exact intCast_eq_mul_iff v m

include hℓ in

theorem natCast_dvd_of_intCast_eq_mul_of (m : ℤ) (h : ∃ d : ↥𝒪, (m : ↥𝒪) = (ℓ : ↥𝒪) * d) :
    (ℓ : ℤ) ∣ m :=
  (intCast_eq_mul_iff_of v hℓ m).1 h

include hℓ in

theorem natCast_mem_asIdeal_iff_of {r : ℕ} (hr : r.Prime) : (r : 𝓞 ℚ) ∈ v.asIdeal ↔ ℓ = r := by
  subst hℓ
  exact natCast_mem_asIdeal_iff v hr

include hℓ in

theorem natCast_mem_asIdeal_of : (ℓ : 𝓞 ℚ) ∈ v.asIdeal := by
  subst hℓ
  exact natCast_primesEquiv_mem_asIdeal v

include hℓ in

theorem natCast_not_mem_asIdeal_of {r : ℕ} (hr : r.Prime) (h : ℓ ≠ r) : (r : 𝓞 ℚ) ∉ v.asIdeal :=
  fun hm => h ((natCast_mem_asIdeal_iff_of v hℓ hr).1 hm)

end REDof

section REDK

variable (v : HeightOneSpectrum (𝓞 ℚ)) {ℓ : ℕ}
  (hℓ : (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v : ℕ) = ℓ)

theorem intCast_mem_adicCompletionIntegers (n : ℤ) :
    ((n : ℤ) : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ := by
  rw [intCast_adicCompletion_eq_coe v n]
  exact SetLike.coe_mem _

theorem natCast_mem_adicCompletionIntegers (n : ℕ) :
    ((n : ℕ) : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ := by
  rw [natCast_adicCompletion_eq_coe v n]
  exact SetLike.coe_mem _

theorem mk_intCast_eq (n : ℤ) (h : ((n : ℤ) : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ) :
    (⟨(n : v.adicCompletion ℚ), h⟩ : ↥(v.adicCompletionIntegers ℚ)) = (n : ↥(v.adicCompletionIntegers ℚ)) :=
  Subtype.ext (intCast_adicCompletion_eq_coe v n)

theorem mk_natCast_eq (n : ℕ) (h : ((n : ℕ) : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ) :
    (⟨(n : v.adicCompletion ℚ), h⟩ : ↥(v.adicCompletionIntegers ℚ)) = (n : ↥(v.adicCompletionIntegers ℚ)) :=
  Subtype.ext (natCast_adicCompletion_eq_coe v n)

theorem redOf_mk_intCast (n : ℤ) (h : ((n : ℤ) : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ) :
    redOf v hℓ ⟨(n : v.adicCompletion ℚ), h⟩ = (n : ZMod ℓ) := by
  rw [mk_intCast_eq v n h, redOf_intCast]

theorem redOf_mk_natCast (n : ℕ) (h : ((n : ℕ) : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ) :
    redOf v hℓ ⟨(n : v.adicCompletion ℚ), h⟩ = (n : ZMod ℓ) := by
  rw [mk_natCast_eq v n h, map_natCast]

theorem redOf_mk_self (h : ((ℓ : ℕ) : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ) :
    redOf v hℓ ⟨(ℓ : v.adicCompletion ℚ), h⟩ = 0 := by
  rw [redOf_mk_natCast, ZMod.natCast_self]

theorem redOf_mk_eq_zero_iff (t : v.adicCompletion ℚ) (ht : t ∈ v.adicCompletionIntegers ℚ) :
    redOf v hℓ ⟨t, ht⟩ = 0 ↔
      ∃ d : v.adicCompletion ℚ, d ∈ v.adicCompletionIntegers ℚ ∧ t = (ℓ : v.adicCompletion ℚ) * d := by
  rw [redOf_eq_zero_iff]
  constructor
  · rintro ⟨d, hd⟩
    refine ⟨(d : v.adicCompletion ℚ), d.2, ?_⟩
    have := congrArg Subtype.val hd
    push_cast at this
    exact this
  · rintro ⟨d, hd, rfl⟩
    exact ⟨⟨d, hd⟩, Subtype.ext (by push_cast; rfl)⟩

include hℓ in

theorem natCast_dvd_of_intCast_eq_mul_K (m : ℤ) (d : v.adicCompletion ℚ)
    (hd : d ∈ v.adicCompletionIntegers ℚ)
    (h : ((m : ℤ) : v.adicCompletion ℚ) = (ℓ : v.adicCompletion ℚ) * d) : (ℓ : ℤ) ∣ m :=
  natCast_dvd_of_intCast_eq_mul_of v hℓ m ⟨⟨d, hd⟩, Subtype.ext (by push_cast; exact h)⟩

include hℓ in

theorem intCast_eq_mul_iff_K (m : ℤ) :
    (∃ d : v.adicCompletion ℚ, d ∈ v.adicCompletionIntegers ℚ ∧
        ((m : ℤ) : v.adicCompletion ℚ) = (ℓ : v.adicCompletion ℚ) * d) ↔ (ℓ : ℤ) ∣ m := by
  rw [← redOf_mk_eq_zero_iff v hℓ _ (intCast_mem_adicCompletionIntegers v m), redOf_mk_intCast,
    ZMod.intCast_zmod_eq_zero_iff_dvd]

include hℓ in

theorem exists_int_add_mul_of_mem (t : v.adicCompletion ℚ) (ht : t ∈ v.adicCompletionIntegers ℚ) :
    ∃ (k : ℤ) (d : v.adicCompletion ℚ), d ∈ v.adicCompletionIntegers ℚ ∧
      t = ((k : ℤ) : v.adicCompletion ℚ) + (ℓ : v.adicCompletion ℚ) * d := by
  obtain ⟨k, hk⟩ := exists_intCast_redOf_eq v hℓ (redOf v hℓ ⟨t, ht⟩)
  have h0 : redOf v hℓ (⟨t, ht⟩ - (k : ↥(v.adicCompletionIntegers ℚ))) = 0 := by
    rw [map_sub, hk, sub_self]
  obtain ⟨d, hd⟩ := (redOf_eq_zero_iff v hℓ _).1 h0
  refine ⟨k, (d : v.adicCompletion ℚ), d.2, ?_⟩
  have := congrArg Subtype.val hd
  push_cast at this
  linear_combination this

theorem exists_eq_intCast_add_mul_of_redOf_eq (t : v.adicCompletion ℚ)
    (ht : t ∈ v.adicCompletionIntegers ℚ) (k : ℤ) (hk : redOf v hℓ ⟨t, ht⟩ = (k : ZMod ℓ)) :
    ∃ d : v.adicCompletion ℚ, d ∈ v.adicCompletionIntegers ℚ ∧
      t = ((k : ℤ) : v.adicCompletion ℚ) + (ℓ : v.adicCompletion ℚ) * d := by
  have h0 : redOf v hℓ (⟨t, ht⟩ - (k : ↥(v.adicCompletionIntegers ℚ))) = 0 := by
    rw [map_sub, hk, redOf_intCast, sub_self]
  obtain ⟨d, hd⟩ := (redOf_eq_zero_iff v hℓ _).1 h0
  refine ⟨(d : v.adicCompletion ℚ), d.2, ?_⟩
  have := congrArg Subtype.val hd
  push_cast at this
  linear_combination this

end REDK

end ASM21.T2
p2m_reactivate "P2MW.S_QuaternionAlgebra_exists_linearMap_matrix_zmod_pow_of_isMaximalOrder_of_ne.ASM21 P2MW.S_QuaternionAlgebra_exists_linearMap_matrix_zmod_pow_of_isMaximalOrder_of_ne.ASM21.T2"
p2m_reactivate "P2MW.S_QuaternionAlgebra_exists_linearMap_matrix_zmod_pow_of_isMaximalOrder_of_ne.ASM21"

namespace ASM21
namespace T2P
open ASM21.T2

section REDPOW

variable (v : HeightOneSpectrum (𝓞 ℚ)) {ℓ : ℕ}
  (hℓ : (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v : ℕ) = ℓ) (m : ℕ)

local notation "𝔭" => (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v : ℕ)
local notation "𝒪" => (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v)

noncomputable def redP : ↥𝒪 →+* ZMod (𝔭 ^ m) :=
  (PadicInt.toZModPow m).comp
    (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv (R := 𝓞 ℚ) v).toRingEquiv.toRingHom

theorem redP_apply (c : ↥𝒪) :
    redP v m c = PadicInt.toZModPow m
      ((Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv (R := 𝓞 ℚ) v).toRingEquiv c) := rfl

theorem redP_eq_zero_iff (c : ↥𝒪) : redP v m c = 0 ↔ ∃ d : ↥𝒪, c = ((𝔭 ^ m : ℕ) : ↥𝒪) * d := by
  set e := (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv (R := 𝓞 ℚ) v).toRingEquiv with he
  rw [redP_apply, ← he, ← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton,
    show ((𝔭 : ℕ) : ℤ_[𝔭]) ^ m = e ((𝔭 ^ m : ℕ) : ↥𝒪) by rw [map_natCast, Nat.cast_pow], map_dvd_iff]
  rfl

noncomputable def redPow : ↥𝒪 →+* ZMod (ℓ ^ m) :=
  (ZMod.ringEquivCongr (by rw [hℓ])).toRingHom.comp (redP v m)

theorem redPow_apply (c : ↥𝒪) : redPow v hℓ m c = ZMod.ringEquivCongr (by rw [hℓ]) (redP v m c) := rfl

theorem redPow_intCast (n : ℤ) : redPow v hℓ m (n : ↥𝒪) = (n : ZMod (ℓ ^ m)) := map_intCast _ n

theorem redPow_eq_zero_iff (c : ↥𝒪) : redPow v hℓ m c = 0 ↔ ∃ d : ↥𝒪, c = ((ℓ ^ m : ℕ) : ↥𝒪) * d := by
  subst hℓ
  rw [redPow_apply, RingEquiv.map_eq_zero_iff, redP_eq_zero_iff]

theorem redPow_mk_intCast (n : ℤ) (h : ((n : ℤ) : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ) :
    redPow v hℓ m ⟨(n : v.adicCompletion ℚ), h⟩ = (n : ZMod (ℓ ^ m)) := by
  rw [mk_intCast_eq v n h, redPow_intCast]

theorem redPow_mk_eq_zero_iff (t : v.adicCompletion ℚ) (ht : t ∈ v.adicCompletionIntegers ℚ) :
    redPow v hℓ m ⟨t, ht⟩ = 0 ↔
      ∃ d : v.adicCompletion ℚ, d ∈ v.adicCompletionIntegers ℚ ∧ t = ((ℓ ^ m : ℕ) : v.adicCompletion ℚ) * d := by
  rw [redPow_eq_zero_iff]
  constructor
  · rintro ⟨d, hd⟩
    refine ⟨(d : v.adicCompletion ℚ), d.2, ?_⟩
    have := congrArg Subtype.val hd
    push_cast at this
    rw [this]; push_cast; rfl
  · rintro ⟨d, hd, rfl⟩
    exact ⟨⟨d, hd⟩, Subtype.ext (by push_cast; rfl)⟩

include hℓ in

theorem pow_dvd_of_intCast_eq_mul_K (k : ℤ) (d : v.adicCompletion ℚ)
    (hd : d ∈ v.adicCompletionIntegers ℚ)
    (h : ((k : ℤ) : v.adicCompletion ℚ) = ((ℓ ^ m : ℕ) : v.adicCompletion ℚ) * d) : ((ℓ ^ m : ℕ) : ℤ) ∣ k := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← redPow_mk_intCast v hℓ m k (intCast_mem_adicCompletionIntegers v k),
    redPow_mk_eq_zero_iff]
  exact ⟨d, hd, h⟩

end REDPOW
p2m_reactivate "P2MW.S_QuaternionAlgebra_exists_linearMap_matrix_zmod_pow_of_isMaximalOrder_of_ne.ASM21 P2MW.S_QuaternionAlgebra_exists_linearMap_matrix_zmod_pow_of_isMaximalOrder_of_ne.ASM21.T2"
end ASM21.T2P
p2m_reactivate "P2MW.S_QuaternionAlgebra_exists_linearMap_matrix_zmod_pow_of_isMaximalOrder_of_ne.ASM21 P2MW.S_QuaternionAlgebra_exists_linearMap_matrix_zmod_pow_of_isMaximalOrder_of_ne.ASM21.T2"
p2m_reactivate "P2MW.S_QuaternionAlgebra_exists_linearMap_matrix_zmod_pow_of_isMaximalOrder_of_ne.ASM21 P2MW.S_QuaternionAlgebra_exists_linearMap_matrix_zmod_pow_of_isMaximalOrder_of_ne.ASM21.T2"

namespace ASM21
namespace T2
theorem exists_M {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ))
    (φv : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (hint : ∀ (z : ↥Λ) (i j : Fin 2), φv ((z : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)) i j ∈ v.adicCompletionIntegers ℚ) :
    ∃ M : ↥Λ → Matrix (Fin 2) (Fin 2) ↥(v.adicCompletionIntegers ℚ),
      (∀ (z : ↥Λ) (i j : Fin 2), ((M z i j : ↥(v.adicCompletionIntegers ℚ)) : v.adicCompletion ℚ) =
          φv ((z : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)) i j) ∧
      (∀ x y : ↥Λ, M (x + y) = M x + M y) ∧
      (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ), M ⟨_, h⟩ = M x * M y) ∧
      (∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, M ⟨1, h⟩ = 1) := by
  classical
  refine ⟨fun z => Matrix.of fun i j => ⟨_, hint z i j⟩, fun z i j => rfl, ?_, ?_, ?_⟩
  · intro x y; ext i j
    simp only [Matrix.of_apply, Matrix.add_apply, AddMemClass.coe_add]
    rw [TensorProduct.add_tmul, RingEquiv.map_add, Matrix.add_apply]
  · intro x y h; ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply]
    push_cast
    rw [← Matrix.mul_apply, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  · intro h; ext i j
    simp only [Matrix.of_apply]
    rw [show ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)) = 1 from rfl, map_one, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
end ASM21.T2
p2m_reactivate "P2MW.S_QuaternionAlgebra_exists_linearMap_matrix_zmod_pow_of_isMaximalOrder_of_ne.ASM21 P2MW.S_QuaternionAlgebra_exists_linearMap_matrix_zmod_pow_of_isMaximalOrder_of_ne.ASM21.T2"
p2m_reactivate "P2MW.S_QuaternionAlgebra_exists_linearMap_matrix_zmod_pow_of_isMaximalOrder_of_ne.ASM21 P2MW.S_QuaternionAlgebra_exists_linearMap_matrix_zmod_pow_of_isMaximalOrder_of_ne.ASM21.T2"

namespace ASM21
namespace T2G

section pieces

theorem htmul_aux {a b : ℚ} (v : HeightOneSpectrum (𝓞 ℚ)) (B : Module.Basis (Fin 4) ℚ ℍ[ℚ, a, b]) (m : Fin 4 → ℤ) :
    (∑ i, m i • B i) ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ) = ∑ i, B i ⊗ₜ[ℚ] ((m i : ℤ) : v.adicCompletion ℚ) := by
  rw [TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  calc (m i • B i) ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ) = ((m i : ℚ) • B i) ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ) := by
        rw [Int.cast_smul_eq_zsmul]
    _ = B i ⊗ₜ[ℚ] ((m i : ℚ) • (1 : v.adicCompletion ℚ)) := by
        rw [TensorProduct.smul_tmul, TensorProduct.tmul_smul]
    _ = B i ⊗ₜ[ℚ] ((m i : ℤ) : v.adicCompletion ℚ) := by
        rw [Algebra.smul_def, mul_one, map_intCast]

theorem hsum_mul_aux {a b : ℚ} (v : HeightOneSpectrum (𝓞 ℚ)) (B : Module.Basis (Fin 4) ℚ ℍ[ℚ, a, b])
    (d : Fin 4 → v.adicCompletion ℚ) (r : v.adicCompletion ℚ) :
    ∑ i, B i ⊗ₜ[ℚ] (d i * r) = (∑ i, B i ⊗ₜ[ℚ] d i) * ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) := by
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl (fun i _ => by rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one])

theorem hφscal_aux {a b : ℚ} (v : HeightOneSpectrum (𝓞 ℚ))
    (φv : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (hφv1 : ∀ r : v.adicCompletion ℚ,
      φv ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))
    (x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) (r : v.adicCompletion ℚ) (i j : Fin 2) :
    φv (x * ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r)) i j = φv x i j * r := by
  rw [map_mul, hφv1, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_apply, smul_eq_mul, mul_comm]

theorem surj_aux
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) (ℓ : ℕ)
    (φv : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (hφv1 : ∀ r : v.adicCompletion ℚ,
      φv ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))
    (hbox : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ,
      x ∈ Submodule.localBox Λ v ↔ ∀ i j, φv x i j ∈ v.adicCompletionIntegers ℚ)
    (B : Module.Basis (Fin 4) ℚ ℍ[ℚ, a, b]) (hBΛ : ∀ i, B i ∈ Λ) (hspan : Submodule.span ℤ (Set.range B) = Λ)
    (red : ↥(v.adicCompletionIntegers ℚ) →+* ZMod ℓ)
    (hK1 : ∀ n : ℤ, ((n : ℤ) : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ)
    (hK2 : ∀ (n : ℤ) (h : ((n : ℤ) : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ),
      red ⟨(n : v.adicCompletion ℚ), h⟩ = (n : ZMod ℓ))
    (hK3 : ∀ (t : v.adicCompletion ℚ) (ht : t ∈ v.adicCompletionIntegers ℚ), red ⟨t, ht⟩ = 0 ↔
      ∃ d : v.adicCompletion ℚ, d ∈ v.adicCompletionIntegers ℚ ∧ t = (ℓ : v.adicCompletion ℚ) * d)
    (hK4 : ∀ (m : ℤ) (d : v.adicCompletion ℚ), d ∈ v.adicCompletionIntegers ℚ →
      ((m : ℤ) : v.adicCompletion ℚ) = (ℓ : v.adicCompletion ℚ) * d → (ℓ : ℤ) ∣ m)
    (hint : ∀ (z : ↥Λ) (i j : Fin 2),
      φv ((z : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)) i j ∈ v.adicCompletionIntegers ℚ)
    (M : ↥Λ → Matrix (Fin 2) (Fin 2) ↥(v.adicCompletionIntegers ℚ))
    (hMcoe : ∀ (z : ↥Λ) (i j : Fin 2), ((M z i j : ↥(v.adicCompletionIntegers ℚ)) : v.adicCompletion ℚ) =
      φv ((z : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)) i j) :
    ∀ T : Matrix (Fin 2) (Fin 2) (ZMod ℓ), ∃ z : ↥Λ, red.mapMatrix (M z) = T := by
  classical
  have hcomb : ∀ m : Fin 4 → ℤ, (∑ i, m i • B i) ∈ Λ := fun m =>
    Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (hBΛ i))
  intro T
  choose n hn using fun (i j : Fin 2) => ZMod.intCast_surjective (T i j)
  obtain ⟨Nz, hNzdef⟩ : ∃ Nz : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ),
      ∀ i j, Nz i j = ((n i j : ℤ) : v.adicCompletion ℚ) :=
    ⟨Matrix.of fun i j => ((n i j : ℤ) : v.adicCompletion ℚ), fun i j => rfl⟩
  have hNz : ∀ i j, Nz i j ∈ v.adicCompletionIntegers ℚ := fun i j => by rw [hNzdef]; exact hK1 _
  obtain ⟨x, hφx⟩ : ∃ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, φv x = Nz := ⟨φv.symm Nz, φv.apply_symm_apply Nz⟩
  have hx : x ∈ Submodule.localBox Λ v := (hbox x).2 (by intro i j; rw [hφx]; exact hNz i j)
  obtain ⟨c, hc, hxc⟩ := (Submodule.mem_localBox_iff_exists_eq_sum_basis_tmul B Λ hspan v x).1 hx
  have hk : ∀ i, ∃ (k : ℤ) (d : v.adicCompletion ℚ), d ∈ v.adicCompletionIntegers ℚ ∧
      c i = ((k : ℤ) : v.adicCompletion ℚ) + (ℓ : v.adicCompletion ℚ) * d := by
    intro i
    obtain ⟨k, hk⟩ := ZMod.intCast_surjective (red ⟨c i, hc i⟩)
    have hsub : c i - ((k : ℤ) : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ := sub_mem (hc i) (hK1 k)
    have h0 : red ⟨c i - ((k : ℤ) : v.adicCompletion ℚ), hsub⟩ = 0 := by
      have : (⟨c i - ((k : ℤ) : v.adicCompletion ℚ), hsub⟩ : ↥(v.adicCompletionIntegers ℚ)) =
          ⟨c i, hc i⟩ - ⟨((k : ℤ) : v.adicCompletion ℚ), hK1 k⟩ := rfl
      rw [this, map_sub, hK2 k (hK1 k), hk, sub_self]
    obtain ⟨d, hd, hcd⟩ := (hK3 _ hsub).1 h0
    exact ⟨k, d, hd, by rw [← hcd]; ring⟩
  choose k d hd hkd using hk
  refine ⟨⟨∑ i, k i • B i, hcomb k⟩, ?_⟩
  have hy : (∑ i, B i ⊗ₜ[ℚ] d i) ∈ Submodule.localBox Λ v :=
    (Submodule.mem_localBox_iff_exists_eq_sum_basis_tmul B Λ hspan v _).2 ⟨d, hd, rfl⟩
  have hzx : ((⟨∑ i, k i • B i, hcomb k⟩ : ↥Λ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ) =
      x - (∑ i, B i ⊗ₜ[ℚ] d i) * ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (ℓ : v.adicCompletion ℚ)) := by
    rw [← hsum_mul_aux, hxc, ← Finset.sum_sub_distrib]
    show (∑ i, k i • B i) ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ) = _
    rw [htmul_aux]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← TensorProduct.tmul_sub, hkd, mul_comm, add_sub_cancel_right]
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply]
  have hdiff : red (M ⟨∑ i, k i • B i, hcomb k⟩ i j - ⟨Nz i j, hNz i j⟩) = 0 := by
    have hmem' : φv (((⟨∑ i, k i • B i, hcomb k⟩ : ↥Λ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)) i j - Nz i j
        ∈ v.adicCompletionIntegers ℚ := sub_mem (hint _ i j) (hNz i j)
    have : M ⟨∑ i, k i • B i, hcomb k⟩ i j - ⟨Nz i j, hNz i j⟩ = ⟨_, hmem'⟩ := by
      apply Subtype.ext
      show ((M ⟨∑ i, k i • B i, hcomb k⟩ i j : ↥(v.adicCompletionIntegers ℚ)) : v.adicCompletion ℚ) - Nz i j = _
      rw [hMcoe]
    rw [this, (hK3 _ hmem').2]
    refine ⟨-(φv (∑ i, B i ⊗ₜ[ℚ] d i) i j), neg_mem ((hbox _).1 hy i j), ?_⟩
    rw [hzx, RingEquiv.map_sub, Matrix.sub_apply, hφscal_aux v φv hφv1, hφx]
    ring
  rw [map_sub, sub_eq_zero] at hdiff
  have hNz' : (⟨Nz i j, hNz i j⟩ : ↥(v.adicCompletionIntegers ℚ)) = ⟨((n i j : ℤ) : v.adicCompletion ℚ), hK1 (n i j)⟩ :=
    Subtype.ext (hNzdef i j)
  rw [hdiff, hNz', hK2 (n i j) (hK1 (n i j)), hn]

theorem ker_aux
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) (ℓ : ℕ)
    (φv : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (hφv1 : ∀ r : v.adicCompletion ℚ,
      φv ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))
    (hbox : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ,
      x ∈ Submodule.localBox Λ v ↔ ∀ i j, φv x i j ∈ v.adicCompletionIntegers ℚ)
    (B : Module.Basis (Fin 4) ℚ ℍ[ℚ, a, b]) (hBΛ : ∀ i, B i ∈ Λ) (hspan : Submodule.span ℤ (Set.range B) = Λ)
    (red : ↥(v.adicCompletionIntegers ℚ) →+* ZMod ℓ)
    (hK1 : ∀ n : ℤ, ((n : ℤ) : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ)
    (hK2 : ∀ (n : ℤ) (h : ((n : ℤ) : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ),
      red ⟨(n : v.adicCompletion ℚ), h⟩ = (n : ZMod ℓ))
    (hK3 : ∀ (t : v.adicCompletion ℚ) (ht : t ∈ v.adicCompletionIntegers ℚ), red ⟨t, ht⟩ = 0 ↔
      ∃ d : v.adicCompletion ℚ, d ∈ v.adicCompletionIntegers ℚ ∧ t = (ℓ : v.adicCompletion ℚ) * d)
    (hK4 : ∀ (m : ℤ) (d : v.adicCompletion ℚ), d ∈ v.adicCompletionIntegers ℚ →
      ((m : ℤ) : v.adicCompletion ℚ) = (ℓ : v.adicCompletion ℚ) * d → (ℓ : ℤ) ∣ m)
    (hint : ∀ (z : ↥Λ) (i j : Fin 2),
      φv ((z : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)) i j ∈ v.adicCompletionIntegers ℚ)
    (M : ↥Λ → Matrix (Fin 2) (Fin 2) ↥(v.adicCompletionIntegers ℚ))
    (hMcoe : ∀ (z : ↥Λ) (i j : Fin 2), ((M z i j : ↥(v.adicCompletionIntegers ℚ)) : v.adicCompletion ℚ) =
      φv ((z : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)) i j) :
    ∀ z : ↥Λ, red.mapMatrix (M z) = 0 ↔ ∃ y : ↥Λ, (z : ℍ[ℚ, a, b]) = (ℓ : ℚ) • (y : ℍ[ℚ, a, b]) := by
  classical
  have hcomb : ∀ m : Fin 4 → ℤ, (∑ i, m i • B i) ∈ Λ := fun m =>
    Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (hBΛ i))
  have hcoord : ∀ z : ↥Λ, ∃ m : Fin 4 → ℤ, (z : ℍ[ℚ, a, b]) = ∑ i, m i • B i := by
    intro z
    have hz : (z : ℍ[ℚ, a, b]) ∈ Submodule.span ℤ (Set.range B) := by rw [hspan]; exact z.2
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hz
    exact ⟨c, hc.symm⟩
  intro z
  constructor
  · intro hz0
    obtain ⟨m, hm⟩ := hcoord z
    have hent : ∀ i j, ∃ e : v.adicCompletion ℚ, e ∈ v.adicCompletionIntegers ℚ ∧
        φv ((z : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)) i j = (ℓ : v.adicCompletion ℚ) * e := by
      intro i j
      have h0 : red (M z i j) = 0 := by
        have := congrFun (congrFun hz0 i) j
        rw [RingHom.mapMatrix_apply, Matrix.map_apply] at this
        exact this
      have hM' : M z i j = ⟨_, hint z i j⟩ := Subtype.ext (hMcoe z i j)
      rw [hM'] at h0
      exact (hK3 _ _).1 h0
    choose e he hφe using hent
    obtain ⟨E, hEdef⟩ : ∃ E : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ), ∀ i j, E i j = e i j :=
      ⟨Matrix.of fun i j => e i j, fun i j => rfl⟩
    obtain ⟨y, hφy⟩ : ∃ y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, φv y = E := ⟨φv.symm E, φv.apply_symm_apply E⟩
    have hy : y ∈ Submodule.localBox Λ v := (hbox y).2 (by intro i j; rw [hφy, hEdef]; exact he i j)
    obtain ⟨dd, hdd, hydd⟩ := (Submodule.mem_localBox_iff_exists_eq_sum_basis_tmul B Λ hspan v y).1 hy
    have hzy : ((z : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)) = y * ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (ℓ : v.adicCompletion ℚ)) := by
      apply φv.injective
      ext i j
      rw [hφscal_aux v φv hφv1, hφy, hEdef, hφe, mul_comm]
    rw [hm, htmul_aux, hydd, ← hsum_mul_aux] at hzy
    have hcoef := ASM21.T2.coeff_eq_of_sum_tmul_eq B _ _ hzy
    have hdiv : ∀ i, (ℓ : ℤ) ∣ m i := fun i =>
      hK4 (m i) (dd i) (hdd i) (by rw [congrFun hcoef i, mul_comm])
    choose kq hkq using hdiv
    refine ⟨⟨∑ i, kq i • B i, hcomb kq⟩, ?_⟩
    show (z : ℍ[ℚ, a, b]) = (ℓ : ℚ) • ∑ i, kq i • B i
    rw [hm, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hkq i, ← Int.cast_smul_eq_zsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ (kq i), smul_smul]
    push_cast
    rfl
  · rintro ⟨y, hy⟩
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply]
    have hM' : M z i j = ⟨_, hint z i j⟩ := Subtype.ext (hMcoe z i j)
    rw [hM', Matrix.zero_apply, (hK3 _ _).2]
    refine ⟨φv ((y : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)) i j, hint y i j, ?_⟩
    have ht : ((ℓ : ℚ) • (y : ℍ[ℚ, a, b])) ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ) =
        ((y : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)) * ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (ℓ : v.adicCompletion ℚ)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, TensorProduct.smul_tmul, Algebra.smul_def, mul_one, map_natCast]
    rw [mul_comm, ← hφscal_aux v φv hφv1, hy, ht]

end pieces
p2m_reactivate "P2MW.S_QuaternionAlgebra_exists_linearMap_matrix_zmod_pow_of_isMaximalOrder_of_ne.ASM21 P2MW.S_QuaternionAlgebra_exists_linearMap_matrix_zmod_pow_of_isMaximalOrder_of_ne.ASM21.T2"

end ASM21.T2G
p2m_reactivate "P2MW.S_QuaternionAlgebra_exists_linearMap_matrix_zmod_pow_of_isMaximalOrder_of_ne.ASM21 P2MW.S_QuaternionAlgebra_exists_linearMap_matrix_zmod_pow_of_isMaximalOrder_of_ne.ASM21.T2"
p2m_reactivate "P2MW.S_QuaternionAlgebra_exists_linearMap_matrix_zmod_pow_of_isMaximalOrder_of_ne.ASM21 P2MW.S_QuaternionAlgebra_exists_linearMap_matrix_zmod_pow_of_isMaximalOrder_of_ne.ASM21.T2"

theorem solution
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q') (m : ℕ) [NeZero m] :
    ∃ φ : ↥Λ →ₗ[ℤ] Matrix (Fin 2) (Fin 2) (ZMod (ℓ ^ m)),
      (∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, φ ⟨1, h⟩ = 1) ∧
      (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
          φ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = φ x * φ y) ∧
      Function.Surjective φ ∧
      (∀ x : ↥Λ, φ x = 0 ↔ ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = ((ℓ ^ m : ℕ) : ℚ) • (y : ℍ[ℚ, a, b])) := by
  classical
  haveI : NeZero (ℓ ^ m) := ⟨pow_ne_zero m (Fact.out : ℓ.Prime).ne_zero⟩
  obtain ⟨v, hvℓ⟩ : ∃ v : HeightOneSpectrum (𝓞 ℚ), (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v : ℕ) = ℓ :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨ℓ, Fact.out⟩, by rw [Equiv.apply_symm_apply]⟩
  have hqv : (q : 𝓞 ℚ) ∉ v.asIdeal := fun h =>
    hℓq (hvℓ.symm.trans (ASM21.T2.eq_of_natCast_mem_asIdeal v Fact.out h))
  have hq'v : (q' : 𝓞 ℚ) ∉ v.asIdeal := fun h =>
    hℓq' (hvℓ.symm.trans (ASM21.T2.eq_of_natCast_mem_asIdeal v Fact.out h))
  obtain ⟨φv, hφv1, hbox⟩ :=
    QuaternionAlgebra.IsMaximalOrder.exists_ringEquiv_mem_localBox_iff_of_isIndefiniteRamifiedExactlyAt_of_prime hB hΛ v hqv hq'v
  obtain ⟨B, hBΛ, hspan⟩ := QuaternionAlgebra.IsOrder.exists_basis_span_eq hΛ.isOrder
  have hmem : ∀ z : ↥Λ, ((z : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)) ∈ Submodule.localBox Λ v := fun z =>
    AddSubgroup.subset_closure ⟨z, z.2, 1, (v.adicCompletionIntegers ℚ).one_mem, rfl⟩
  have hint : ∀ (z : ↥Λ) (i j : Fin 2), φv ((z : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)) i j ∈ v.adicCompletionIntegers ℚ :=
    fun z => (hbox _).1 (hmem z)
  obtain ⟨M, hMcoe, hMadd, hMmul, hMone⟩ := ASM21.T2.exists_M Λ v φv hint
  have hK1 : ∀ n : ℤ, ((n : ℤ) : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ :=
    fun n => ASM21.T2.intCast_mem_adicCompletionIntegers v n
  have hK2 := fun (n : ℤ) (h : ((n : ℤ) : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ) =>
    ASM21.T2P.redPow_mk_intCast v hvℓ m n h
  have hK3 := fun (t : v.adicCompletion ℚ) (ht : t ∈ v.adicCompletionIntegers ℚ) =>
    ASM21.T2P.redPow_mk_eq_zero_iff v hvℓ m t ht
  have hK4 : ∀ (k : ℤ) (d : v.adicCompletion ℚ), d ∈ v.adicCompletionIntegers ℚ →
      ((k : ℤ) : v.adicCompletion ℚ) = ((ℓ ^ m : ℕ) : v.adicCompletion ℚ) * d → ((ℓ ^ m : ℕ) : ℤ) ∣ k :=
    fun k d hd h => ASM21.T2P.pow_dvd_of_intCast_eq_mul_K v hvℓ m k d hd h
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ↥Λ →ₗ[ℤ] Matrix (Fin 2) (Fin 2) (ZMod (ℓ ^ m)),
      ∀ z : ↥Λ, Φ z = (ASM21.T2P.redPow v hvℓ m).mapMatrix (M z) :=
    ⟨(AddMonoidHom.mk' (fun z : ↥Λ => (ASM21.T2P.redPow v hvℓ m).mapMatrix (M z))
        (fun x y => by simp only [hMadd, map_add])).toIntLinearMap, fun z => rfl⟩
  refine ⟨Φ, ?_, ?_, ?_, ?_⟩
  · intro h
    simp only [hΦ, hMone h, map_one]
  · intro x y h
    simp only [hΦ, hMmul x y h, map_mul]
  · intro T
    obtain ⟨z, hz⟩ := ASM21.T2G.surj_aux Λ v (ℓ ^ m) φv hφv1 hbox B hBΛ hspan (ASM21.T2P.redPow v hvℓ m) hK1 hK2 hK3 hK4 hint M hMcoe T
    exact ⟨z, (hΦ z).trans hz⟩
  · intro z
    rw [hΦ]
    exact ASM21.T2G.ker_aux Λ v (ℓ ^ m) φv hφv1 hbox B hBΛ hspan (ASM21.T2P.redPow v hvℓ m) hK1 hK2 hK3 hK4 hint M hMcoe z

end S_QuaternionAlgebra_exists_linearMap_matrix_zmod_pow_of_isMaximalOrder_of_ne
end P2MW
export P2MW.S_QuaternionAlgebra_exists_linearMap_matrix_zmod_pow_of_isMaximalOrder_of_ne (solution)
