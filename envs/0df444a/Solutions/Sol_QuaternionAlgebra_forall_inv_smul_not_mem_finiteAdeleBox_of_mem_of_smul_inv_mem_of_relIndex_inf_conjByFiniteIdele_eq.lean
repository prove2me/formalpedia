-- Prove2me | solution 1 for QuaternionAlgebra.forall_inv_smul_not_mem_finiteAdeleBox_of_mem_of_smul_inv_mem_of_relIndex_inf_conjByFiniteIdele_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/459db21f-b07a-58b8-86b8-01c50d5c85af

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_KernelIdeal
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_Submodule_relIndex_toAddSubgroup_eq_finprod_relIndex_localBox
import Theorems.Thm_Submodule_localBox_inf
import Theorems.Thm_Submodule_mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox
import Theorems.Thm_Submodule_mem_localBox_conjByFiniteIdele_iff
import Theorems.Thm_Submodule_ofFiniteIdele_one
import Theorems.Thm_QuaternionAlgebra_IsOrder_conjByFiniteIdele
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_conjByFiniteIdele
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_pair_localBox_iff_conj_diagonal_pow_mem_adicCompletionIntegers
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_localBox_eq_localBox_of_forall_isUnit
import Theorems.Thm_Matrix_relIndex_inf_conj_diagonal_pow_eq
import Theorems.Thm_Matrix_GeneralLinearGroup_exists_forall_inv_mul_apply_mem_and_mul_inv_apply_mem_of_forall_conj_apply_mem
import Theorems.Thm_QuaternionAlgebra_forall_tensorProduct_adicCompletion_isUnit_iff_forall_normForm_eq_zero
import Theorems.Thm_QuaternionAlgebra_nonempty_algEquiv_matrix_of_normForm_eq_zero
import Theorems.Thm_QuaternionAlgebra_exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_forall_inv_smul_not_mem_finiteAdeleBox_of_mem_of_smul_inv_mem_of_relIndex_inf_conjByFiniteIdele_eq
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "LocalGL2.swapUnit_val QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

noncomputable section

namespace QPrim

local notation "HOS" => HeightOneSpectrum (𝓞 ℚ)

section Padic

scoped instance instCharZeroAdicCompletion (v : HOS) : CharZero (v.adicCompletion ℚ) :=
  charZero_of_injective_algebraMap (algebraMap ℚ (v.adicCompletion ℚ)).injective

theorem pz_valued_natCast_eq_one {n : ℕ} (v : HOS) (hn : (n : 𝓞 ℚ) ∉ v.asIdeal) :
    Valued.v (n : v.adicCompletion ℚ) = 1 := by
  have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) v (n : 𝓞 ℚ)
  rw [(HeightOneSpectrum.valuation_eq_one_iff_notMem (K := ℚ) (v := v)).mpr hn] at h
  change Valued.v (algebraMap (𝓞 ℚ) (v.adicCompletion ℚ) n) = 1 at h
  rwa [map_natCast] at h

theorem pz_natCast_ne_zero_of_notMem {n : ℕ} (v : HOS) (hn : (n : 𝓞 ℚ) ∉ v.asIdeal) :
    (n : v.adicCompletion ℚ) ≠ 0 := by
  intro h
  have := pz_valued_natCast_eq_one v hn
  rw [h, map_zero] at this
  exact zero_ne_one this

theorem pz_natCast_inv_mem_integers {n : ℕ} (v : HOS) (hn : (n : 𝓞 ℚ) ∉ v.asIdeal) :
    (n : v.adicCompletion ℚ)⁻¹ ∈ v.adicCompletionIntegers ℚ := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, pz_valued_natCast_eq_one v hn, inv_one]

theorem pz_natCast_mem_integers (v : HOS) (n : ℕ) : (n : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ := by
  have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) v (n : 𝓞 ℚ)
  change Valued.v (algebraMap (𝓞 ℚ) (v.adicCompletion ℚ) n) = _ at h
  rw [map_natCast] at h
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, h]
  exact HeightOneSpectrum.valuation_le_one v _

theorem pz_valued_intCast (v : HOS) (k : ℤ) :
    Valued.v (k : v.adicCompletion ℚ) = v.valuation ℚ (algebraMap (𝓞 ℚ) ℚ (k : 𝓞 ℚ)) := by
  have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) v (k : 𝓞 ℚ)
  change Valued.v (algebraMap (𝓞 ℚ) (v.adicCompletion ℚ) k) = _ at h
  rwa [map_intCast] at h

theorem pz_valued_intCast_lt_one_iff (v : HOS) (k : ℤ) :
    Valued.v (k : v.adicCompletion ℚ) < 1 ↔ (k : 𝓞 ℚ) ∈ v.asIdeal := by
  rw [pz_valued_intCast]; exact HeightOneSpectrum.valuation_lt_one_iff_mem v _

theorem pz_intCast_mem_iff {ℓ : ℕ} (hℓ : ℓ.Prime) {v : HOS} (hv : (ℓ : 𝓞 ℚ) ∈ v.asIdeal) (k : ℤ) :
    (k : 𝓞 ℚ) ∈ v.asIdeal ↔ (ℓ : ℤ) ∣ k := by
  constructor
  · intro hk
    by_contra hnd
    have hcopN : ℓ.Coprime k.natAbs :=
      (Nat.Prime.coprime_iff_not_dvd hℓ).mpr (fun hd => hnd (Int.natCast_dvd.mpr hd))
    have hcop : IsCoprime (ℓ : ℤ) k := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      exact hcopN
    obtain ⟨u, w, huw⟩ := hcop
    have h1 : (u : 𝓞 ℚ) * ℓ + (w : 𝓞 ℚ) * k = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 ℚ) huw
    have : (1 : 𝓞 ℚ) ∈ v.asIdeal := by
      rw [← h1]
      exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hv) (v.asIdeal.mul_mem_left _ hk)
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr this)
  · rintro ⟨t, rfl⟩
    push_cast
    exact v.asIdeal.mul_mem_right _ hv

theorem pz_natCast_mem_iff {ℓ : ℕ} (hℓ : ℓ.Prime) {v : HOS} (hv : (ℓ : 𝓞 ℚ) ∈ v.asIdeal) (n : ℕ) :
    (n : 𝓞 ℚ) ∈ v.asIdeal ↔ ℓ ∣ n := by
  have h := pz_intCast_mem_iff hℓ hv (n : ℤ)
  rw [Int.cast_natCast] at h
  rw [h, Int.natCast_dvd_natCast]

theorem pz_prime_eq_of_mem {ℓ ℓ' : ℕ} (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) {v : HOS}
    (hv : (ℓ : 𝓞 ℚ) ∈ v.asIdeal) (hv' : (ℓ' : 𝓞 ℚ) ∈ v.asIdeal) : ℓ = ℓ' :=
  (Nat.prime_dvd_prime_iff_eq hℓ hℓ').mp ((pz_natCast_mem_iff hℓ hv ℓ').mp hv')

theorem pz_exists_prime_mem (v : HOS) : ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : 𝓞 ℚ) ∈ v.asIdeal := by
  classical
  let e := Rat.ringOfIntegersEquiv
  let P : Ideal ℤ := Ideal.map e v.asIdeal
  have hP : P.IsPrime := Ideal.map_isPrime_of_equiv e
  have hP0 : P ≠ ⊥ := fun h => v.ne_bot ((Ideal.map_eq_bot_iff_of_injective e.injective).mp h)
  have hg : P = Ideal.span {Submodule.IsPrincipal.generator P} := (Ideal.span_singleton_generator P).symm
  set g := Submodule.IsPrincipal.generator P with hgdef
  have hg0 : g ≠ 0 := fun h0 => hP0 (by rw [hg, h0, Ideal.span_singleton_eq_bot])
  have hgp : Prime g := (Ideal.span_singleton_prime hg0).mp (hg ▸ hP)
  refine ⟨g.natAbs, Int.prime_iff_natAbs_prime.mp hgp, ?_⟩
  have hmem : ((g.natAbs : ℕ) : ℤ) ∈ P := by
    rw [hg, Ideal.mem_span_singleton]
    exact Int.dvd_natAbs.mpr (dvd_refl g)
  have hmem' : ((g.natAbs : ℕ) : ℤ) ∈ Ideal.comap e.symm v.asIdeal := by
    rwa [← Ideal.map_comap_of_equiv]
  rw [Ideal.mem_comap, map_natCast] at hmem'
  exact hmem'

theorem pz_exists_place {ℓ : ℕ} (hℓ : ℓ.Prime) : ∃ v : HOS, (ℓ : 𝓞 ℚ) ∈ v.asIdeal := by
  classical
  have hnu : ¬ IsUnit ((ℓ : 𝓞 ℚ)) := by
    intro hu
    have h := hu.map Rat.ringOfIntegersEquiv
    rw [map_natCast, Int.isUnit_iff] at h
    rcases h with h | h
    · exact hℓ.one_lt.ne' (by exact_mod_cast h)
    · have : (0 : ℤ) ≤ ℓ := Int.natCast_nonneg _
      omega
  have hne : Ideal.span {(ℓ : 𝓞 ℚ)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]; exact hnu
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hℓM : (ℓ : 𝓞 ℚ) ∈ M := hle (Ideal.mem_span_singleton_self _)
  have hM0 : M ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hℓM
    exact hℓ.ne_zero (by exact_mod_cast hℓM)
  exact ⟨⟨M, hM.isPrime, hM0⟩, hℓM⟩

theorem pz_eq_of_mem {ℓ : ℕ} (hℓ : ℓ.Prime) {v w : HOS} (hv : (ℓ : 𝓞 ℚ) ∈ v.asIdeal)
    (hw : (ℓ : 𝓞 ℚ) ∈ w.asIdeal) : w = v := by
  let e := Rat.ringOfIntegersEquiv
  have key : ∀ u : HOS, (ℓ : 𝓞 ℚ) ∈ u.asIdeal → Ideal.map e u.asIdeal = Ideal.span {(ℓ : ℤ)} := by
    intro u hu
    have hP : (Ideal.map e u.asIdeal).IsPrime := Ideal.map_isPrime_of_equiv e
    have hmax : (Ideal.span {(ℓ : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hℓ).irreducible
    have hle : Ideal.span {(ℓ : ℤ)} ≤ Ideal.map e u.asIdeal := by
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
      have := Ideal.mem_map_of_mem e hu
      rwa [map_natCast] at this
    exact (hmax.eq_of_le hP.ne_top hle).symm
  apply HeightOneSpectrum.ext
  have h := (key w hw).trans (key v hv).symm
  have := congrArg (Ideal.comap e) h
  rwa [Ideal.comap_map_of_bijective e e.bijective, Ideal.comap_map_of_bijective e e.bijective] at this

theorem pz_valued_prime_lt_one {ℓ : ℕ} (v : HOS) (hv : (ℓ : 𝓞 ℚ) ∈ v.asIdeal) :
    Valued.v (ℓ : v.adicCompletion ℚ) < 1 := by
  have := (pz_valued_intCast_lt_one_iff v (ℓ : ℤ)).mpr (by push_cast; exact hv)
  rwa [Int.cast_natCast] at this

theorem pz_natCast_ne_zero {ℓ : ℕ} (hℓ : ℓ.Prime) (v : HOS) : (ℓ : v.adicCompletion ℚ) ≠ 0 := by
  rw [show (ℓ : v.adicCompletion ℚ) = algebraMap ℚ (v.adicCompletion ℚ) (ℓ : ℚ) by rw [map_natCast]]
  exact (map_ne_zero (algebraMap ℚ (v.adicCompletion ℚ))).mpr (Nat.cast_ne_zero.mpr hℓ.ne_zero)

theorem pz_inv_prime_notMem {ℓ : ℕ} (hℓ : ℓ.Prime) (v : HOS) (hv : (ℓ : 𝓞 ℚ) ∈ v.asIdeal) :
    (ℓ : v.adicCompletion ℚ)⁻¹ ∉ v.adicCompletionIntegers ℚ := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, not_le]
  exact one_lt_inv₀ ((Valuation.pos_iff _).mpr (pz_natCast_ne_zero hℓ v)) |>.mpr (pz_valued_prime_lt_one v hv)

theorem pz_pow_dvd_of_mul_inv_mem {ℓ : ℕ} (hℓ : ℓ.Prime) (v : HOS) (hv : (ℓ : 𝓞 ℚ) ∈ v.asIdeal) :
    ∀ (e N : ℕ), (N : v.adicCompletion ℚ) * ((ℓ : v.adicCompletion ℚ) ^ e)⁻¹ ∈ v.adicCompletionIntegers ℚ →
      ℓ ^ e ∣ N := by
  have hℓ0 := pz_natCast_ne_zero hℓ v
  intro e
  induction e with
  | zero => intro N _; simp
  | succ e ih =>
    intro N hN

    have hdiv : ℓ ∣ N := by
      by_contra hnd
      have hNu : (N : v.adicCompletion ℚ)⁻¹ ∈ v.adicCompletionIntegers ℚ :=
        pz_natCast_inv_mem_integers v (fun h => hnd ((pz_natCast_mem_iff hℓ hv N).mp h))
      have hN0 : (N : v.adicCompletion ℚ) ≠ 0 :=
        pz_natCast_ne_zero_of_notMem v (fun h => hnd ((pz_natCast_mem_iff hℓ hv N).mp h))
      have hmem : (ℓ : v.adicCompletion ℚ)⁻¹ ∈ v.adicCompletionIntegers ℚ := by
        have h := mul_mem (mul_mem hNu hN) (pow_mem (pz_natCast_mem_integers v ℓ) e)
        convert h using 1
        field_simp
        ring
      exact pz_inv_prime_notMem hℓ v hv hmem
    obtain ⟨N', rfl⟩ := hdiv
    have h' : (N' : v.adicCompletion ℚ) * ((ℓ : v.adicCompletion ℚ) ^ e)⁻¹ ∈ v.adicCompletionIntegers ℚ := by
      convert hN using 1
      push_cast
      field_simp
      ring
    rw [pow_succ']
    exact Nat.mul_dvd_mul_left ℓ (ih N' h')

end Padic

section Denominators

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

theorem exists_den_bound (Λ : Submodule ℤ V) (hfg : Λ.FG) (f : V →ₗ[ℚ] ℚ) :
    ∃ D : ℕ, D ≠ 0 ∧ ∀ z ∈ Λ, ∃ n : ℤ, (D : ℚ) * f z = n := by
  classical
  obtain ⟨s, hs⟩ := hfg
  refine ⟨∏ z ∈ s, (f z).den, Finset.prod_ne_zero_iff.mpr fun z _ => (f z).den_ne_zero, fun z hz => ?_⟩
  rw [← hs] at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun z => (f z).den) hz
    refine ⟨(k : ℤ) * (f z).num, ?_⟩
    rw [hk, Nat.cast_mul, mul_comm ((f z).den : ℚ), mul_assoc, Rat.den_mul_eq_num]
    push_cast; ring
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm⟩ := hx; obtain ⟨n, hn⟩ := hy
    exact ⟨m + n, by rw [map_add, mul_add, hm, hn]; push_cast; ring⟩
  | smul c x _ hx =>
    obtain ⟨m, hm⟩ := hx
    refine ⟨c * m, ?_⟩
    rw [LinearMap.map_smul_of_tower, zsmul_eq_mul, mul_left_comm, hm]; push_cast; ring

theorem apply_eq_zero_of_forall_inv_pow_smul_mem (Λ : Submodule ℤ V) (hfg : Λ.FG) {p : ℕ} (hp : 1 < p)
    {x : V} (hx : ∀ k : ℕ, ((p : ℚ) ^ k)⁻¹ • x ∈ Λ) (f : V →ₗ[ℚ] ℚ) : f x = 0 := by
  obtain ⟨D, hD, hΛ⟩ := exists_den_bound Λ hfg f
  by_contra hfx
  set q : ℚ := (D : ℚ) * f x with hq
  have hq0 : q ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.mpr hD) hfx

  have hint : ∀ k : ℕ, ∃ n : ℤ, q / (p : ℚ) ^ k = n := fun k => by
    obtain ⟨n, hn⟩ := hΛ _ (hx k)
    refine ⟨n, ?_⟩
    rw [← hn, LinearMap.map_smul, smul_eq_mul, hq]; ring

  obtain ⟨k, hk⟩ := exists_nat_gt |q|
  obtain ⟨n, hn⟩ := hint k
  have hp0 : (0 : ℚ) < (p : ℚ) ^ k := by positivity
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [Int.cast_zero, div_eq_zero_iff] at hn
    exact hn.elim hq0 hp0.ne'
  have h1 : (1 : ℚ) ≤ |(n : ℚ)| := by exact_mod_cast Int.one_le_abs hn0
  have hlt : ((k : ℕ) : ℚ) < (p : ℚ) ^ k := by exact_mod_cast Nat.lt_pow_self hp
  have key : |q| = |(n : ℚ)| * (p : ℚ) ^ k := by
    rw [← hn, abs_div, abs_of_pos hp0, div_mul_cancel₀ _ hp0.ne']
  have : (p : ℚ) ^ k ≤ |q| := by
    rw [key]; exact le_mul_of_one_le_left hp0.le h1
  linarith

theorem exists_natCast_smul_mem_of_mem_span (Λ : Submodule ℤ V) {y : V}
    (hy : y ∈ Submodule.span ℚ (Λ : Set V)) : ∃ n : ℕ, n ≠ 0 ∧ ((n : ℕ) : ℤ) • y ∈ Λ := by
  induction hy using Submodule.span_induction with
  | mem z hz => exact ⟨1, one_ne_zero, by simpa using hz⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨m, hm, hmu⟩ := hu
    obtain ⟨n, hn, hnv⟩ := hv
    refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [Nat.cast_mul, mul_comm, mul_smul]; exact Submodule.smul_mem _ _ hmu
    · rw [Nat.cast_mul, mul_smul]; exact Submodule.smul_mem _ _ hnv
  | smul c u _ hu =>
    obtain ⟨n, hn, hnu⟩ := hu
    refine ⟨c.den * n, mul_ne_zero c.den_ne_zero hn, ?_⟩
    have : (((c.den * n : ℕ) : ℤ)) • c • u = c.num • (((n : ℕ) : ℤ) • u) := by
      rw [← Int.cast_smul_eq_zsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ c.num,
        ← Int.cast_smul_eq_zsmul ℚ ((n : ℕ) : ℤ), smul_smul, smul_smul]
      congr 1
      push_cast
      rw [← Rat.mul_den_eq_num c]
      ring
    rw [this]
    exact Submodule.smul_mem _ _ hnu

end Denominators

section NoMaximal

variable {A : Type*} [Ring A] [Algebra ℚ A]

theorem exists_larger_order (J : Submodule ℚ A)
    (hJl : ∀ (x : A) {y : A}, y ∈ J → x * y ∈ J) (hJr : ∀ (x : A) {y : A}, y ∈ J → y * x ∈ J)
    (hJJ : ∀ {y y' : A}, y ∈ J → y' ∈ J → y * y' = 0) {y₀ : A} (hy₀J : y₀ ∈ J) (hy₀ : y₀ ≠ 0)
    (Λ : Submodule ℤ A) (h1 : (1 : A) ∈ Λ) (hmul : ∀ {x y : A}, x ∈ Λ → y ∈ Λ → x * y ∈ Λ)
    (hsp : Submodule.span ℚ (Λ : Set A) = ⊤) (hfg : Λ.FG) :
    ∃ Λ' : Submodule ℤ A, (1 : A) ∈ Λ' ∧ (∀ {x y : A}, x ∈ Λ' → y ∈ Λ' → x * y ∈ Λ') ∧
      Submodule.span ℚ (Λ' : Set A) = ⊤ ∧ Λ'.FG ∧ Λ ≤ Λ' ∧ Λ' ≠ Λ := by
  classical

  let hf : A →ₗ[ℤ] A := (LinearMap.lsmul ℚ A (2⁻¹ : ℚ)).restrictScalars ℤ
  have hf_apply : ∀ x : A, hf x = (2⁻¹ : ℚ) • x := fun x => rfl
  let M : Submodule ℤ A := Λ ⊓ J.restrictScalars ℤ
  let Λ' : Submodule ℤ A := Λ ⊔ M.map hf
  have hle : Λ ≤ Λ' := le_sup_left
  have hMfg : M.FG := Submodule.FG.of_le hfg inf_le_left
  refine ⟨Λ', hle h1, ?_, ?_, Submodule.FG.sup hfg (hMfg.map _), hle, ?_⟩
  ·
    intro x y hx hy
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp hy
    obtain ⟨u, ⟨huΛ, huJ⟩, rfl⟩ := Submodule.mem_map.mp hx₂
    obtain ⟨w, ⟨hwΛ, hwJ⟩, rfl⟩ := Submodule.mem_map.mp hy₂
    have huJ' : u ∈ J := huJ
    have hwJ' : w ∈ J := hwJ
    have expand : (x₁ + hf u) * (y₁ + hf w) = x₁ * y₁ + hf (x₁ * w + u * y₁) := by
      simp only [hf_apply, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, smul_add, hJJ huJ' hwJ',
        smul_zero, add_zero]
      abel
    rw [expand]
    refine Submodule.mem_sup.mpr ⟨x₁ * y₁, hmul hx₁ hy₁, hf (x₁ * w + u * y₁),
      Submodule.mem_map_of_mem ⟨?_, ?_⟩, rfl⟩
    · exact Λ.add_mem (hmul hx₁ hwΛ) (hmul huΛ hy₁)
    · exact J.add_mem (hJl x₁ hwJ') (hJr y₁ huJ')
  ·
    refine top_unique ?_
    rw [← hsp]
    exact Submodule.span_mono hle
  ·
    intro heq
    have hhalf : ∀ u ∈ M, hf u ∈ M := by
      intro u hu
      refine ⟨?_, ?_⟩
      · rw [← heq]; exact Submodule.mem_sup_right (Submodule.mem_map_of_mem hu)
      · show (2⁻¹ : ℚ) • u ∈ J
        exact J.smul_mem _ hu.2
    have hpow : ∀ u ∈ M, ∀ k : ℕ, ((2 : ℚ) ^ k)⁻¹ • u ∈ Λ := by
      intro u hu k
      suffices h : ((2 : ℚ) ^ k)⁻¹ • u ∈ M from h.1
      induction k with
      | zero => simpa using hu
      | succ k ih =>
        have := hhalf _ ih
        rw [hf_apply, smul_smul] at this
        convert this using 2
        rw [pow_succ, mul_inv, mul_comm]

    obtain ⟨n, hn, hny⟩ : ∃ n : ℕ, n ≠ 0 ∧ ((n : ℕ) : ℤ) • y₀ ∈ Λ :=
      exists_natCast_smul_mem_of_mem_span Λ (by rw [hsp]; trivial)
    have hnyM : ((n : ℕ) : ℤ) • y₀ ∈ M := ⟨hny, (J.restrictScalars ℤ).smul_mem _ hy₀J⟩
    have hzero : ((n : ℕ) : ℤ) • y₀ = 0 := by

      have hall : ∀ f : A →ₗ[ℚ] ℚ, f (((n : ℕ) : ℤ) • y₀) = 0 := fun f =>
        apply_eq_zero_of_forall_inv_pow_smul_mem Λ hfg one_lt_two (hpow _ hnyM) f
      exact (Module.forall_dual_apply_eq_zero_iff ℚ _).mp hall
    rw [← Int.cast_smul_eq_zsmul ℚ, smul_eq_zero] at hzero
    rcases hzero with h | h
    · exact hn (by exact_mod_cast h)
    · exact hy₀ h

end NoMaximal

section Quaternion

variable {a b : ℚ}

theorem ne_zero_of_isMaximalOrder {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsMaximalOrder Λ) :
    a ≠ 0 ∧ b ≠ 0 := by
  have hO := hΛ.1

  have absurd_of : ∀ (J : Submodule ℚ ℍ[ℚ, a, b]),
      (∀ (x : ℍ[ℚ, a, b]) {y : ℍ[ℚ, a, b]}, y ∈ J → x * y ∈ J) →
      (∀ (x : ℍ[ℚ, a, b]) {y : ℍ[ℚ, a, b]}, y ∈ J → y * x ∈ J) →
      (∀ {y y' : ℍ[ℚ, a, b]}, y ∈ J → y' ∈ J → y * y' = 0) →
      ∀ {y₀ : ℍ[ℚ, a, b]}, y₀ ∈ J → y₀ ≠ 0 → False := by
    intro J hJl hJr hJJ y₀ hy₀J hy₀
    obtain ⟨Λ', h1', hmul', hsp', hfg', hle', hne'⟩ :=
      exists_larger_order J hJl hJr hJJ hy₀J hy₀ Λ hO.one_mem (fun hx hy => hO.mul_mem hx hy) hO.spanTop hO.fg
    exact hne' (hΛ.2 Λ' ⟨h1', fun _ _ hx hy => hmul' hx hy, hsp', hfg'⟩ hle')
  constructor
  · rintro rfl

    let J : Submodule ℚ ℍ[ℚ, 0, b] :=
      LinearMap.ker (QuaternionAlgebra.reₗ 0 0 b) ⊓ LinearMap.ker (QuaternionAlgebra.imJₗ 0 0 b)
    have hJmem : ∀ y : ℍ[ℚ, 0, b], y ∈ J ↔ y.re = 0 ∧ y.imJ = 0 := fun y => Iff.rfl
    refine absurd_of J ?_ ?_ ?_ (y₀ := ⟨0, 1, 0, 0⟩) ((hJmem _).mpr ⟨rfl, rfl⟩) ?_
    · intro x y hy
      obtain ⟨h1, h2⟩ := (hJmem y).mp hy
      refine (hJmem _).mpr ⟨?_, ?_⟩ <;>
        simp [QuaternionAlgebra.re_mul, QuaternionAlgebra.imJ_mul, h1, h2]
    · intro x y hy
      obtain ⟨h1, h2⟩ := (hJmem y).mp hy
      refine (hJmem _).mpr ⟨?_, ?_⟩ <;>
        simp [QuaternionAlgebra.re_mul, QuaternionAlgebra.imJ_mul, h1, h2]
    · intro y y' hy hy'
      obtain ⟨h1, h2⟩ := (hJmem y).mp hy
      obtain ⟨h1', h2'⟩ := (hJmem y').mp hy'
      ext <;> simp [QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul,
        QuaternionAlgebra.imK_mul, h1, h2, h1', h2']
    · intro h
      have := congrArg QuaternionAlgebra.imI h
      simp at this
  · rintro rfl

    let J : Submodule ℚ ℍ[ℚ, a, 0] :=
      LinearMap.ker (QuaternionAlgebra.reₗ a 0 0) ⊓ LinearMap.ker (QuaternionAlgebra.imIₗ a 0 0)
    have hJmem : ∀ y : ℍ[ℚ, a, 0], y ∈ J ↔ y.re = 0 ∧ y.imI = 0 := fun y => Iff.rfl
    refine absurd_of J ?_ ?_ ?_ (y₀ := ⟨0, 0, 1, 0⟩) ((hJmem _).mpr ⟨rfl, rfl⟩) ?_
    · intro x y hy
      obtain ⟨h1, h2⟩ := (hJmem y).mp hy
      refine (hJmem _).mpr ⟨?_, ?_⟩ <;>
        simp [QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul, h1, h2]
    · intro x y hy
      obtain ⟨h1, h2⟩ := (hJmem y).mp hy
      refine (hJmem _).mpr ⟨?_, ?_⟩ <;>
        simp [QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul, h1, h2]
    · intro y y' hy hy'
      obtain ⟨h1, h2⟩ := (hJmem y).mp hy
      obtain ⟨h1', h2'⟩ := (hJmem y').mp hy'
      ext <;> simp [QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul,
        QuaternionAlgebra.imK_mul, h1, h2, h1', h2']
    · intro h
      have := congrArg QuaternionAlgebra.imJ h
      simp at this

end Quaternion

section Box

variable {D : Type*} [Ring D] [Algebra ℚ D]

theorem tmul_mem_localBox {Λ : Submodule ℤ D} {z : D} (hz : z ∈ Λ) (w : HOS) {c : w.adicCompletion ℚ}
    (hc : c ∈ w.adicCompletionIntegers ℚ) : z ⊗ₜ[ℚ] c ∈ Submodule.localBox Λ w :=
  AddSubgroup.subset_closure ⟨z, hz, c, hc, rfl⟩

theorem tmul_one_mem_localBox {Λ : Submodule ℤ D} {z : D} (hz : z ∈ Λ) (w : HOS) :
    z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) ∈ Submodule.localBox Λ w :=
  tmul_mem_localBox hz w (one_mem _)

theorem one_mem_localBox {Λ : Submodule ℤ D} (h1 : (1 : D) ∈ Λ) (w : HOS) :
    (1 : D ⊗[ℚ] w.adicCompletion ℚ) ∈ Submodule.localBox Λ w := by
  rw [Algebra.TensorProduct.one_def]; exact tmul_one_mem_localBox h1 w

theorem one_tmul_mul_mem_localBox (Λ : Submodule ℤ D) (w : HOS) {c : w.adicCompletion ℚ}
    (hc : c ∈ w.adicCompletionIntegers ℚ) {x : D ⊗[ℚ] w.adicCompletion ℚ}
    (hx : x ∈ Submodule.localBox Λ w) :
    (1 : D) ⊗ₜ[ℚ] c * x ∈ Submodule.localBox Λ w := by
  have h : Submodule.localBox Λ w ≤
      (Submodule.localBox Λ w).comap (AddMonoidHom.mulLeft ((1 : D) ⊗ₜ[ℚ] c)) := by
    unfold Submodule.localBox
    refine (AddSubgroup.closure_le _).mpr ?_
    rintro _ ⟨z, hz, c', hc', rfl⟩
    show (1 : D) ⊗ₜ[ℚ] c * z ⊗ₜ[ℚ] c' ∈ AddSubgroup.closure _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    exact AddSubgroup.subset_closure ⟨z, hz, _, mul_mem hc hc', rfl⟩
  exact h hx

theorem mul_mem_localBox (Λ : Submodule ℤ D) (hmul : ∀ ⦃x y : D⦄, x ∈ Λ → y ∈ Λ → x * y ∈ Λ) (w : HOS)
    {x y : D ⊗[ℚ] w.adicCompletion ℚ} (hx : x ∈ Submodule.localBox Λ w)
    (hy : y ∈ Submodule.localBox Λ w) : x * y ∈ Submodule.localBox Λ w := by

  have h1 : ∀ z ∈ Λ, ∀ c ∈ w.adicCompletionIntegers ℚ, ∀ x' ∈ Submodule.localBox Λ w,
      x' * z ⊗ₜ[ℚ] c ∈ Submodule.localBox Λ w := by
    intro z hz c hc x' hx'
    have h : Submodule.localBox Λ w ≤
        (Submodule.localBox Λ w).comap (AddMonoidHom.mulRight (z ⊗ₜ[ℚ] c)) := by
      unfold Submodule.localBox
      refine (AddSubgroup.closure_le _).mpr ?_
      rintro _ ⟨z', hz', c', hc', rfl⟩
      show z' ⊗ₜ[ℚ] c' * z ⊗ₜ[ℚ] c ∈ AddSubgroup.closure _
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact AddSubgroup.subset_closure ⟨_, hmul hz' hz, _, mul_mem hc' hc, rfl⟩
    exact h hx'

  have h2 : Submodule.localBox Λ w ≤ (Submodule.localBox Λ w).comap (AddMonoidHom.mulLeft x) := by
    conv_lhs => unfold Submodule.localBox
    refine (AddSubgroup.closure_le _).mpr ?_
    rintro _ ⟨z, hz, c, hc, rfl⟩
    exact h1 z hz c hc x hx
  exact h2 hy

theorem mem_iff_forall_tmul_one_mem_localBox (Λ : Submodule ℤ D) (hfg : Λ.FG)
    (hspan : Submodule.span ℚ (Λ : Set D) = ⊤) (z : D) :
    z ∈ Λ ↔ ∀ w : HOS, z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) ∈ Submodule.localBox Λ w := by
  have h1 := Submodule.ofFiniteIdele_one Λ hfg hspan
  constructor
  · intro hz w; exact tmul_one_mem_localBox hz w
  · intro hz
    rw [← h1, Submodule.mem_ofFiniteIdele_iff]
    refine ⟨z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ), ?_, by simp⟩
    rw [SetLike.mem_coe,
      Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox Λ hfg hspan]
    intro w
    rw [Submodule.finiteAdeleEvalAt_tmul]
    exact hz w

theorem rat_smul_eq_one_tmul_mul (w : HOS) (c : ℚ) (x : D ⊗[ℚ] w.adicCompletion ℚ) :
    c • x = (1 : D) ⊗ₜ[ℚ] (c : w.adicCompletion ℚ) * x := by
  haveI : CharZero (w.adicCompletion ℚ) :=
    charZero_of_injective_algebraMap (algebraMap ℚ (w.adicCompletion ℚ)).injective
  calc c • x = algebraMap ℚ _ c * x := Algebra.smul_def c x
    _ = _ := by rw [Algebra.TensorProduct.algebraMap_apply', eq_ratCast]

end Box

section Split

variable {a b : ℚ}

theorem dichotomy (ha : a ≠ 0) (hb : b ≠ 0) (w : HOS) :
    (∀ x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ, x ≠ 0 → IsUnit x) ∨
    ∃ φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ),
      ∀ r : w.adicCompletion ℚ,
        φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) := by
  by_cases hdiv : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ, x ≠ 0 → IsUnit x
  · exact Or.inl hdiv
  right
  haveI : CharZero (w.adicCompletion ℚ) :=
    charZero_of_injective_algebraMap (algebraMap ℚ (w.adicCompletion ℚ)).injective
  rw [QuaternionAlgebra.forall_tensorProduct_adicCompletion_isUnit_iff_forall_normForm_eq_zero] at hdiv
  simp only [not_forall] at hdiv
  obtain ⟨x₀, x₁, x₂, x₃, h0, hx⟩ := hdiv
  have ha' : (a : w.adicCompletion ℚ) ≠ 0 := by exact_mod_cast ha
  have hb' : (b : w.adicCompletion ℚ) ≠ 0 := by exact_mod_cast hb
  obtain ⟨ψ⟩ := QuaternionAlgebra.nonempty_algEquiv_matrix_of_normForm_eq_zero (w.adicCompletion ℚ) two_ne_zero
    (a : w.adicCompletion ℚ) (b : w.adicCompletion ℚ) ha' hb' x₀ x₁ x₂ x₃ hx h0
  obtain ⟨φ, hφ, -⟩ := QuaternionAlgebra.exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
    (R := ℚ) (S := w.adicCompletion ℚ) (c₁ := a) (c₂ := (0 : ℚ)) (c₃ := b)
    (d₁ := (a : w.adicCompletion ℚ)) (d₂ := (0 : w.adicCompletion ℚ)) (d₃ := (b : w.adicCompletion ℚ))
    (eq_ratCast _ a) (by simp) (eq_ratCast _ b) ψ
  exact ⟨φ, hφ⟩

end Split

section MatrixLetters

variable {K : Type*} [Field K] (𝒪 : ValuationSubring K)

def IsInt (X : Matrix (Fin 2) (Fin 2) K) : Prop := ∀ i j, X i j ∈ 𝒪

theorem isInt_mul {X Y : Matrix (Fin 2) (Fin 2) K} (hX : IsInt 𝒪 X) (hY : IsInt 𝒪 Y) : IsInt 𝒪 (X * Y) :=
  fun i j => by
    rw [Matrix.mul_apply]
    exact sum_mem fun k _ => mul_mem (hX i k) (hY k j)

theorem mul_mul_inv_mem_of_conj_iff (Mm Mi : Matrix (Fin 2) (Fin 2) K) (hMM : Mm * Mi = 1) (hMM' : Mi * Mm = 1)
    {π : K} (hπ : π ≠ 0) (hπO : π ∈ 𝒪)
    (hiff : ∀ Y : Matrix (Fin 2) (Fin 2) K,
      IsInt 𝒪 (Mi * Y * Mm) ↔ IsInt 𝒪 (Matrix.diagonal ![(1 : K), π⁻¹] * Y * Matrix.diagonal ![(1 : K), π]))
    (t s : K) (ht : IsInt 𝒪 (t • Mi)) (hs : IsInt 𝒪 (s • Mm)) : s * t * π⁻¹ ∈ 𝒪 := by
  classical
  set d : Matrix (Fin 2) (Fin 2) K := Matrix.diagonal ![(1 : K), π] with hd
  set dinv : Matrix (Fin 2) (Fin 2) K := Matrix.diagonal ![(1 : K), π⁻¹] with hdinv
  have hdd : d * dinv = 1 := by
    rw [hd, hdinv, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i; fin_cases i <;> simp [hπ]
  have hdd' : dinv * d = 1 := by
    rw [hd, hdinv, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i; fin_cases i <;> simp [hπ]
  have hd00 : d 0 0 = 1 := by simp [hd]
  have hdinv11 : dinv 1 1 = π⁻¹ := by simp [hdinv]

  let g : GL (Fin 2) K :=
    ⟨Mi * d, dinv * Mm,
      by rw [Matrix.mul_assoc, ← Matrix.mul_assoc d, hdd, Matrix.one_mul, hMM'],
      by rw [Matrix.mul_assoc, ← Matrix.mul_assoc Mm, hMM, Matrix.one_mul, hdd']⟩
  have hgval : (g : Matrix (Fin 2) (Fin 2) K) = Mi * d := rfl
  have hginv : ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = dinv * Mm := rfl
  have hg : ∀ M : Matrix (Fin 2) (Fin 2) K, (∀ i j, M i j ∈ 𝒪) →
      ∀ i j, ((g : Matrix (Fin 2) (Fin 2) K) * M * ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) i j ∈ 𝒪 := by
    intro M hM
    have h1 : (g : Matrix (Fin 2) (Fin 2) K) * M * ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        Mi * (d * M * dinv) * Mm := by
      rw [hgval, hginv]; simp only [Matrix.mul_assoc]
    rw [h1]
    refine (hiff _).mpr ?_
    have h2 : dinv * (d * M * dinv) * d = M := by
      calc dinv * (d * M * dinv) * d = (dinv * d) * M * (dinv * d) := by simp only [Matrix.mul_assoc]
        _ = M := by rw [hdd', Matrix.one_mul, Matrix.mul_one]
    rw [h2]; exact hM
  obtain ⟨c, hc1, hc2⟩ :=
    Matrix.GeneralLinearGroup.exists_forall_inv_mul_apply_mem_and_mul_inv_apply_mem_of_forall_conj_apply_mem
      𝒪 g hg
  rw [hgval] at hc1
  rw [hginv] at hc2
  have hK1 : IsInt 𝒪 (((c⁻¹ : Kˣ) : K) • (Mi * d)) := fun i j => by
    rw [Matrix.smul_apply, smul_eq_mul]; exact hc1 i j
  have hK2 : IsInt 𝒪 ((c : K) • (dinv * Mm)) := fun i j => by
    rw [Matrix.smul_apply, smul_eq_mul]; exact hc2 i j

  have hγ : s * ((c⁻¹ : Kˣ) : K) ∈ 𝒪 := by
    have h := isInt_mul 𝒪 hs hK1 0 0
    have e1 : (s • Mm) * (((c⁻¹ : Kˣ) : K) • (Mi * d)) = (s * ((c⁻¹ : Kˣ) : K)) • d := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Matrix.mul_assoc, hMM, Matrix.one_mul]
    rwa [e1, Matrix.smul_apply, smul_eq_mul, hd00, mul_one] at h

  have hβ : (c : K) * t * π⁻¹ ∈ 𝒪 := by
    have h := isInt_mul 𝒪 hK2 ht 1 1
    have e2 : ((c : K) • (dinv * Mm)) * (t • Mi) = ((c : K) * t) • dinv := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, hMM, Matrix.mul_one]
    rwa [e2, Matrix.smul_apply, smul_eq_mul, hdinv11] at h
  have e3 : s * t * π⁻¹ = (s * ((c⁻¹ : Kˣ) : K)) * ((c : K) * t * π⁻¹) := by
    rw [Units.val_inv_eq_inv_val]
    field_simp
  rw [e3]
  exact mul_mem hγ hβ

end MatrixLetters

section SplitPlace

variable {a b : ℚ}

theorem split_place {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsMaximalOrder Λ)
    (m : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (w : HOS) {p : ℕ} (hp : p.Prime)
    (hpw : (p : 𝓞 ℚ) ∈ w.asIdeal)
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ))
    (hφ : ∀ r : w.adicCompletion ℚ,
      φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ))) :
    ∃ e : ℕ,
      (Submodule.localBox Λ w ⊓ Submodule.localBox (Submodule.conjByFiniteIdele Λ m) w).relIndex
          (Submodule.localBox Λ w) = p ^ e ∧
      ∀ t s : w.adicCompletion ℚ,
        (1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] t * Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w
            ((m⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈
          Submodule.localBox Λ w →
        (1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] s * Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w
            ((m : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈
          Submodule.localBox Λ w →
        s * t * ((p : w.adicCompletion ℚ) ^ e)⁻¹ ∈ w.adicCompletionIntegers ℚ := by
  classical
  have hΛ' : QuaternionAlgebra.IsMaximalOrder (Submodule.conjByFiniteIdele Λ m) := hΛ.conjByFiniteIdele m
  have hO := hΛ.isOrder
  obtain ⟨e, ⟨h, hΛw, hΛ'w⟩, -⟩ :=
    QuaternionAlgebra.IsMaximalOrder.exists_pair_localBox_iff_conj_diagonal_pow_mem_adicCompletionIntegers
      hΛ hΛ' w p hp hpw φ hφ
  refine ⟨e, Matrix.relIndex_inf_conj_diagonal_pow_eq w p hp hpw φ hφ h e _ _ hΛw hΛ'w, ?_⟩
  intro t s ht hs

  set mw := Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w
    ((m : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) with hmw
  set mwi := Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w
    ((m⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) with hmwi
  have hmm : mw * mwi = 1 := by rw [hmw, hmwi, ← map_mul, Units.mul_inv, map_one]
  have hmm' : mwi * mw = 1 := by rw [hmw, hmwi, ← map_mul, Units.inv_mul, map_one]
  set hM : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ) := (h : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ))
    with hhM
  set hMi : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ) :=
    ((h⁻¹ : GL (Fin 2) (w.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) with hhMi
  have hhh : hM * hMi = 1 := Units.mul_inv h
  have hhh' : hMi * hM = 1 := Units.inv_mul h

  let ψ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ → Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ) :=
    fun x => hMi * φ x * hM
  have hψ : ∀ x, ψ x = hMi * φ x * hM := fun x => rfl
  have hψmul : ∀ x y, ψ (x * y) = ψ x * ψ y := by
    intro x y
    rw [hψ, hψ, hψ, φ.map_mul]
    calc hMi * (φ x * φ y) * hM = hMi * φ x * (hM * hMi) * φ y * hM := by
          rw [hhh, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hψone : ψ 1 = 1 := by rw [hψ, φ.map_one, Matrix.mul_one, hhh']
  have hψscal : ∀ (r : w.adicCompletion ℚ) (x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ),
      ψ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r * x) = r • ψ x := by
    intro r x
    rw [hψmul, hψ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r), hφ, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hhh',
      Matrix.smul_mul, Matrix.one_mul]
  have hψsurj : ∀ Y : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ), ψ (φ.symm (hM * Y * hMi)) = Y := by
    intro Y
    simp only [hψ, RingEquiv.apply_symm_apply]
    calc hMi * (hM * Y * hMi) * hM = (hMi * hM) * Y * (hMi * hM) := by simp only [Matrix.mul_assoc]
      _ = Y := by rw [hhh', Matrix.one_mul, Matrix.mul_one]
  set Mm := ψ mw with hMm
  set Mi := ψ mwi with hMi_def
  have hMM : Mm * Mi = 1 := by rw [hMm, hMi_def, ← hψmul, hmm, hψone]
  have hMM' : Mi * Mm = 1 := by rw [hMm, hMi_def, ← hψmul, hmm', hψone]

  have hiff : ∀ Y : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ),
      IsInt (w.adicCompletionIntegers ℚ) (Mi * Y * Mm) ↔
        IsInt (w.adicCompletionIntegers ℚ)
          (Matrix.diagonal ![(1 : w.adicCompletion ℚ), ((p : w.adicCompletion ℚ) ^ e)⁻¹] * Y *
            Matrix.diagonal ![(1 : w.adicCompletion ℚ), (p : w.adicCompletion ℚ) ^ e]) := by
    intro Y
    set x := φ.symm (hM * Y * hMi) with hx
    have hY : ψ x = Y := hψsurj Y
    have h1 : x ∈ Submodule.localBox (Submodule.conjByFiniteIdele Λ m) w ↔
        mwi * x * mw ∈ Submodule.localBox Λ w := by
      rw [Submodule.mem_localBox_conjByFiniteIdele_iff Λ hO.fg hO.spanTop m w x]
      constructor
      · rintro ⟨y, hy, hxy⟩
        rw [hxy]
        have : mwi * (mw * y * mwi) * mw = y := by
          calc mwi * (mw * y * mwi) * mw = (mwi * mw) * y * (mwi * mw) := by simp only [mul_assoc]
            _ = y := by rw [hmm', one_mul, mul_one]
        rw [this]; exact hy
      · intro hx'
        refine ⟨mwi * x * mw, hx', ?_⟩
        calc x = (mw * mwi) * x * (mw * mwi) := by rw [hmm, one_mul, mul_one]
          _ = mw * (mwi * x * mw) * mwi := by simp only [mul_assoc]
    have h2 : mwi * x * mw ∈ Submodule.localBox Λ w ↔ IsInt (w.adicCompletionIntegers ℚ) (Mi * Y * Mm) := by
      rw [hΛw]
      change IsInt (w.adicCompletionIntegers ℚ) (ψ (mwi * x * mw)) ↔ _
      rw [hψmul, hψmul, hY]
    have h3 : x ∈ Submodule.localBox (Submodule.conjByFiniteIdele Λ m) w ↔
        IsInt (w.adicCompletionIntegers ℚ)
          (Matrix.diagonal ![(1 : w.adicCompletion ℚ), ((p : w.adicCompletion ℚ) ^ e)⁻¹] * Y *
            Matrix.diagonal ![(1 : w.adicCompletion ℚ), (p : w.adicCompletion ℚ) ^ e]) := by
      rw [hΛ'w]
      have : Matrix.diagonal ![(1 : w.adicCompletion ℚ), ((p : w.adicCompletion ℚ) ^ e)⁻¹] * hMi * φ x * hM *
            Matrix.diagonal ![(1 : w.adicCompletion ℚ), (p : w.adicCompletion ℚ) ^ e] =
          Matrix.diagonal ![(1 : w.adicCompletion ℚ), ((p : w.adicCompletion ℚ) ^ e)⁻¹] * ψ x *
            Matrix.diagonal ![(1 : w.adicCompletion ℚ), (p : w.adicCompletion ℚ) ^ e] := by
        simp only [hψ, Matrix.mul_assoc]
      rw [this, hY]
      rfl
    rw [← h2, ← h1, h3]

  have ht' : IsInt (w.adicCompletionIntegers ℚ) (t • Mi) := by
    have h0 := (hΛw _).mp ht
    change IsInt (w.adicCompletionIntegers ℚ) (ψ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] t * mwi)) at h0
    rwa [hψscal] at h0
  have hs' : IsInt (w.adicCompletionIntegers ℚ) (s • Mm) := by
    have h0 := (hΛw _).mp hs
    change IsInt (w.adicCompletionIntegers ℚ) (ψ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] s * mw)) at h0
    rwa [hψscal] at h0
  exact mul_mul_inv_mem_of_conj_iff (w.adicCompletionIntegers ℚ) Mm Mi hMM hMM'
    (pow_ne_zero e (pz_natCast_ne_zero hp w)) (pow_mem (pz_natCast_mem_integers w p) e) hiff t s ht' hs'

end SplitPlace

section AnyPlace

variable {a b : ℚ}

theorem dvd_of_local_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hO : QuaternionAlgebra.IsOrder Λ)
    (m : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) {ℓ : ℕ} (hℓ : ℓ.Prime) (v : HOS)
    (hv : (ℓ : 𝓞 ℚ) ∈ v.asIdeal) (N : ℕ)
    (hN : (1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (N : v.adicCompletion ℚ) * Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v
        ((m⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈
      Submodule.localBox Λ v)
    (hℓm : (1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (ℓ : v.adicCompletion ℚ)⁻¹ * Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v
        ((m : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈
      Submodule.localBox Λ v) :
    ℓ ∣ N := by
  by_contra hnd
  set mv := Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v
    ((m : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) with hmv
  set mvi := Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v
    ((m⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) with hmvi
  have hmm : mv * mvi = 1 := by rw [hmv, hmvi, ← map_mul, Units.mul_inv, map_one]
  have hNv : (N : 𝓞 ℚ) ∉ v.asIdeal := fun h => hnd ((pz_natCast_mem_iff hℓ hv N).mp h)
  have hmvi : mvi ∈ Submodule.localBox Λ v := by
    have h := one_tmul_mul_mem_localBox Λ v (pz_natCast_inv_mem_integers v hNv) hN
    rwa [← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      inv_mul_cancel₀ (pz_natCast_ne_zero_of_notMem v hNv), ← Algebra.TensorProduct.one_def, one_mul] at h
  have hℓinv : (1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (ℓ : v.adicCompletion ℚ)⁻¹ ∈ Submodule.localBox Λ v := by
    have h := mul_mem_localBox Λ hO.mul_mem v hℓm hmvi
    rwa [mul_assoc, hmm, mul_one] at h
  have hpow : ∀ k : ℕ, (1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((ℓ : v.adicCompletion ℚ) ^ k)⁻¹ ∈ Submodule.localBox Λ v := by
    intro k
    induction k with
    | zero => rw [pow_zero, inv_one, ← Algebra.TensorProduct.one_def]; exact one_mem_localBox hO.one_mem v
    | succ k ih =>
      have h := mul_mem_localBox Λ hO.mul_mem v ih hℓinv
      rwa [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← mul_inv, ← pow_succ] at h

  have hglob : ∀ k : ℕ, ((ℓ : ℚ) ^ k)⁻¹ • (1 : ℍ[ℚ, a, b]) ∈ Λ := by
    intro k
    rw [mem_iff_forall_tmul_one_mem_localBox Λ hO.fg hO.spanTop]
    intro w
    have e1 : (((ℓ : ℚ) ^ k)⁻¹ • (1 : ℍ[ℚ, a, b])) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) =
        (1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((ℓ : w.adicCompletion ℚ) ^ k)⁻¹ := by
      rw [← TensorProduct.smul_tmul', rat_smul_eq_one_tmul_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        mul_one, Rat.cast_inv, Rat.cast_pow, Rat.cast_natCast]
    rw [e1]
    by_cases hw : w = v
    · subst hw; exact hpow k
    · have hℓw : (ℓ : 𝓞 ℚ) ∉ w.asIdeal := fun h' => hw (pz_eq_of_mem hℓ hv h')
      have hint : ((ℓ : w.adicCompletion ℚ) ^ k)⁻¹ ∈ w.adicCompletionIntegers ℚ := by
        rw [← inv_pow]; exact pow_mem (pz_natCast_inv_mem_integers w hℓw) k
      exact tmul_mem_localBox hO.one_mem w hint
  have h0 := apply_eq_zero_of_forall_inv_pow_smul_mem Λ hO.fg hℓ.one_lt hglob (QuaternionAlgebra.reₗ a 0 b)
  simp at h0

end AnyPlace

section Assembly

theorem prod_dvd_of_pairwise_coprime {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℕ) (n : ℕ)
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (f i).Coprime (f j)) (hd : ∀ i ∈ s, f i ∣ n) :
    ∏ i ∈ s, f i ∣ n := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ (hd i (Finset.mem_insert_self i s))
      (ih (fun j hj k hk hjk => hcop j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hjk)
        (fun j hj => hd j (Finset.mem_insert_of_mem hj)))
    exact Nat.Coprime.prod_right fun j hj =>
      hcop i (Finset.mem_insert_self i s) j (Finset.mem_insert_of_mem hj) (fun h => hi (h ▸ hj))

end Assembly

end QPrim
p2m_reactivate "P2MW.S_QuaternionAlgebra_forall_inv_smul_not_mem_finiteAdeleBox_of_mem_of_smul_inv_mem_of_relIndex_inf_conjByFiniteIdele_eq.QPrim"

end
p2m_reactivate "P2MW.S_QuaternionAlgebra_forall_inv_smul_not_mem_finiteAdeleBox_of_mem_of_smul_inv_mem_of_relIndex_inf_conjByFiniteIdele_eq.QPrim"

open QPrim in
theorem solution
    {a b : ℚ} (Λ₁ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ₁ : QuaternionAlgebra.IsMaximalOrder Λ₁)
    (N : ℕ) [NeZero N]
    (m : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hm₁ : ((m : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ₁)
    (hmN : ((N : ℕ) : ℚ) • ((m⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ₁)
    (hRN : (Λ₁ ⊓ Submodule.conjByFiniteIdele Λ₁ m).toAddSubgroup.relIndex Λ₁.toAddSubgroup = N) :
    ∀ ℓ : ℕ, ℓ.Prime → ((ℓ : ℚ)⁻¹ • ((m : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ))) ∉ Submodule.finiteAdeleBox Λ₁ := by
  intro ℓ hℓ habs
  classical
  have hO : QuaternionAlgebra.IsOrder Λ₁ := hΛ₁.isOrder
  obtain ⟨ha, hb⟩ := ne_zero_of_isMaximalOrder hΛ₁
  set Λ' : Submodule ℤ ℍ[ℚ, a, b] := Submodule.conjByFiniteIdele Λ₁ m with hΛ'def
  have hΛ' : QuaternionAlgebra.IsMaximalOrder Λ' := hΛ₁.conjByFiniteIdele m
  have hO' : QuaternionAlgebra.IsOrder Λ' := hΛ'.isOrder
  have hR : QuaternionAlgebra.IsOrder (Λ₁ ⊓ Λ') := hO.inf hO'

  have hbox := fun x =>
    Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox (D := ℍ[ℚ, a, b]) Λ₁ hO.fg hO.spanTop x
  have hm_w : ∀ w : HeightOneSpectrum (𝓞 ℚ), Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w
      ((m : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈
        Submodule.localBox Λ₁ w :=
    fun w => (hbox _).mp hm₁ w
  have hN_w : ∀ w : HeightOneSpectrum (𝓞 ℚ), (1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (N : w.adicCompletion ℚ) *
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w
        ((m⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈
        Submodule.localBox Λ₁ w := by
    intro w
    have h := (hbox _).mp hmN w
    rwa [map_smul, rat_smul_eq_one_tmul_mul, Rat.cast_natCast] at h
  obtain ⟨v, hv⟩ := pz_exists_place hℓ
  have hℓ_v : (1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (ℓ : v.adicCompletion ℚ)⁻¹ *
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v
        ((m : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈
        Submodule.localBox Λ₁ v := by
    have h := (hbox _).mp habs v
    rwa [map_smul, rat_smul_eq_one_tmul_mul, Rat.cast_inv, Rat.cast_natCast] at h

  set idx : HeightOneSpectrum (𝓞 ℚ) → ℕ :=
    fun w => (Submodule.localBox (Λ₁ ⊓ Λ') w).relIndex (Submodule.localBox Λ₁ w) with hidx_def
  have hidx : ∀ w, idx w =
      (Submodule.localBox Λ₁ w ⊓ Submodule.localBox Λ' w).relIndex (Submodule.localBox Λ₁ w) := fun w => by
    rw [hidx_def]
    simp only
    rw [Submodule.localBox_inf Λ₁ Λ' hO.fg hO.spanTop hO'.fg hO'.spanTop w]
  have hprod : ∏ᶠ w, idx w = N := by
    rw [hidx_def, ← Submodule.relIndex_toAddSubgroup_eq_finprod_relIndex_localBox Λ₁ (Λ₁ ⊓ Λ') hO.fg
      hO.spanTop hR.fg hR.spanTop inf_le_left]
    exact hRN

  have hloc : ∀ w : HeightOneSpectrum (𝓞 ℚ), ∃ p e : ℕ, p.Prime ∧ (p : 𝓞 ℚ) ∈ w.asIdeal ∧ idx w = p ^ e ∧
      p ^ e ∣ N ∧ (w = v → p ^ (e + 1) ∣ N) := by
    intro w
    obtain ⟨p, hp, hpw⟩ := pz_exists_prime_mem w
    rcases dichotomy ha hb w with hdiv | ⟨φ, hφ⟩
    ·
      refine ⟨p, 0, hp, hpw, ?_, by simp, ?_⟩
      · rw [hidx, QuaternionAlgebra.IsMaximalOrder.localBox_eq_localBox_of_forall_isUnit w hdiv hΛ' hΛ₁,
          inf_idem, AddSubgroup.relIndex_self, pow_zero]
      · rintro rfl
        obtain rfl : p = ℓ := (pz_prime_eq_of_mem hℓ hp hv hpw).symm
        rw [zero_add, pow_one]
        exact dvd_of_local_mem hO m hp w hpw N (hN_w w) hℓ_v
    ·
      obtain ⟨e, he, hts⟩ := split_place hΛ₁ m w hp hpw φ hφ
      refine ⟨p, e, hp, hpw, by rw [hidx, he], ?_, ?_⟩
      · refine pz_pow_dvd_of_mul_inv_mem hp w hpw e N ?_
        have h := hts (N : w.adicCompletion ℚ) 1 (hN_w w)
          (by rw [← Algebra.TensorProduct.one_def, one_mul]; exact hm_w w)
        rwa [one_mul] at h
      · rintro rfl
        obtain rfl : p = ℓ := (pz_prime_eq_of_mem hℓ hp hv hpw).symm
        refine pz_pow_dvd_of_mul_inv_mem hp w hpw (e + 1) N ?_
        have h := hts (N : w.adicCompletion ℚ) ((p : w.adicCompletion ℚ)⁻¹) (hN_w w) hℓ_v
        have hp0 := pz_natCast_ne_zero hp w
        convert h using 1
        rw [pow_succ, mul_inv]
        ring

  have hℓN : ℓ ∣ N := by
    obtain ⟨p, e, hp, hpw, -, -, h⟩ := hloc v
    have h' := h rfl
    rw [pz_prime_eq_of_mem hp hℓ hpw hv] at h'
    exact dvd_trans (dvd_pow_self ℓ (Nat.succ_ne_zero e)) h'
  have hN0 : N ≠ 0 := NeZero.ne N
  have hN1 : 1 < N := lt_of_lt_of_le hℓ.one_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hℓN)
  have hfin : (Function.mulSupport idx).Finite := by
    by_contra hinf
    rw [finprod_of_infinite_mulSupport hinf] at hprod
    omega
  let s : Finset (HeightOneSpectrum (𝓞 ℚ)) := hfin.toFinset ∪ {v}
  have hsub : Function.mulSupport idx ⊆ (s : Set (HeightOneSpectrum (𝓞 ℚ))) := fun w hw =>
    Finset.mem_coe.mpr (Finset.mem_union_left _ (hfin.mem_toFinset.mpr hw))
  have hprod' : ∏ w ∈ s, idx w = N := by
    rw [← finprod_eq_prod_of_mulSupport_subset idx hsub]; exact hprod
  have hvs : v ∈ s := Finset.mem_union_right _ (Finset.mem_singleton_self v)

  choose p e hp hpw hidxw hdvd hdvdv using hloc
  have hpv : p v = ℓ := (pz_prime_eq_of_mem hℓ (hp v) hv (hpw v)).symm
  let idx' : HeightOneSpectrum (𝓞 ℚ) → ℕ := fun w => if w = v then ℓ * idx w else idx w
  have hprod'' : ∏ w ∈ s, idx' w = ℓ * N := by
    rw [← Finset.mul_prod_erase s idx' hvs, ← hprod', ← Finset.mul_prod_erase s idx hvs]
    have h1 : idx' v = ℓ * idx v := if_pos rfl
    rw [h1, mul_assoc]
    congr 1
    congr 1
    exact Finset.prod_congr rfl fun w hw => if_neg (Finset.ne_of_mem_erase hw)
  have hpow' : ∀ w, ∃ k, idx' w = p w ^ k := by
    intro w
    by_cases hw : w = v
    · refine ⟨e w + 1, ?_⟩
      show (if w = v then ℓ * idx w else idx w) = p w ^ (e w + 1)
      rw [if_pos hw, hidxw w, pow_succ', hw, hpv]
    · exact ⟨e w, by show (if w = v then ℓ * idx w else idx w) = p w ^ e w; rw [if_neg hw, hidxw w]⟩
  have hdvd' : ∀ w ∈ s, idx' w ∣ N := by
    intro w _
    by_cases hw : w = v
    · show (if w = v then ℓ * idx w else idx w) ∣ N
      rw [if_pos hw, hidxw w, hw, ← hpv, ← pow_succ']
      exact hdvdv v rfl
    · show (if w = v then ℓ * idx w else idx w) ∣ N
      rw [if_neg hw, hidxw w]
      exact hdvd w
  have hcop : ∀ w ∈ s, ∀ w' ∈ s, w ≠ w' → (idx' w).Coprime (idx' w') := by
    intro w _ w' _ hne
    have hpp : p w ≠ p w' := by
      intro h
      exact hne ((pz_eq_of_mem (hp w') (hpw w') (h ▸ hpw w)))
    obtain ⟨k, hk⟩ := hpow' w
    obtain ⟨k', hk'⟩ := hpow' w'
    rw [hk, hk']
    exact Nat.coprime_pow_primes _ _ (hp w) (hp w') hpp
  have key : ∏ w ∈ s, idx' w ∣ N := prod_dvd_of_pairwise_coprime s idx' N hcop hdvd'
  rw [hprod''] at key
  have hle : ℓ * N ≤ 1 * N := by rw [one_mul]; exact Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) key
  have hℓ1 : ℓ ≤ 1 := Nat.le_of_mul_le_mul_right hle (Nat.pos_of_ne_zero hN0)
  exact absurd hℓ.one_lt (not_lt.mpr hℓ1)

end S_QuaternionAlgebra_forall_inv_smul_not_mem_finiteAdeleBox_of_mem_of_smul_inv_mem_of_relIndex_inf_conjByFiniteIdele_eq
end P2MW
export P2MW.S_QuaternionAlgebra_forall_inv_smul_not_mem_finiteAdeleBox_of_mem_of_smul_inv_mem_of_relIndex_inf_conjByFiniteIdele_eq (solution)
