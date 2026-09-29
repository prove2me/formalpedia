-- Prove2me | solution 1 for QuaternionAlgebra.IsEichlerOrder.exists_mem_forall_pow_smul_star_mul_mul_ne_smul_of_forall_pow_smul_mul_mul_star_ne_smul_of_inf_eq_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/fdc1f89a-113c-5318-a2f7-b9553d8b54f5

import Mathlib
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_QuaternionAlgebra_IsOrder_forall_tmul_one_mem_localBox_iff_exists_pow_smul_mem
import Theorems.Thm_Submodule_exists_mem_add_one_tmul_pow_mul_of_mem_localBox
import Theorems.Thm_Submodule_localBox_inf
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_ringEquiv_generalLinearGroup_forall_mem_localBox_iff_of_inf_eq_of_dvd_of_squarefree
import Theorems.Thm_Matrix_exists_iwahori_conj_diagonal_not_mem_of_exists_iwahori_conj_not_mem
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_mem_forall_pow_smul_star_mul_mul_ne_smul_of_forall_pow_smul_mul_mul_star_ne_smul_of_inf_eq_of_dvd
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open scoped TensorProduct Quaternion NumberField
open IsDedekindDomain NumberField QuaternionAlgebra

noncomputable section

namespace NormEllTypeFlip

local notation "Kv" w => IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ w
local notation "Ov" w => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ w

section places

variable (w : HeightOneSpectrum (𝓞 ℚ))

abbrev pl : ℕ := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) w : ℕ)

theorem pl_prime : (pl w).Prime := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) w).2

theorem intCast_mem_asIdeal_iff (z : ℤ) : (z : 𝓞 ℚ) ∈ w.asIdeal ↔ (pl w : ℤ) ∣ z := by
  rw [← Ideal.apply_mem_of_equiv_iff (f := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)), map_intCast,
    ← Rat.HeightOneSpectrum.span_natGenerator, Ideal.mem_span_singleton, Int.cast_id]
  rfl

theorem natCast_mem_asIdeal_iff (n : ℕ) : (n : 𝓞 ℚ) ∈ w.asIdeal ↔ pl w ∣ n := by
  rw [show (n : 𝓞 ℚ) = ((n : ℤ) : 𝓞 ℚ) from (Int.cast_natCast n).symm, intCast_mem_asIdeal_iff, Int.natCast_dvd_natCast]

theorem pl_eq_of_prime_mem {p : ℕ} (hp : p.Prime) (hpw : (p : 𝓞 ℚ) ∈ w.asIdeal) : pl w = p :=
  (Nat.prime_dvd_prime_iff_eq (pl_prime w) hp).mp ((natCast_mem_asIdeal_iff w p).mp hpw)

theorem eq_of_pl_eq {w w' : HeightOneSpectrum (𝓞 ℚ)} (h : pl w = pl w') : w = w' :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective (Subtype.ext h)

theorem exists_pl_eq (p : ℕ) (hp : p.Prime) : ∃ w : HeightOneSpectrum (𝓞 ℚ), pl w = p :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hp⟩, by rw [pl, Equiv.apply_symm_apply]⟩

theorem natCast_notMem_of_prime_mem {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hqw : (q : 𝓞 ℚ) ∈ w.asIdeal) : (p : 𝓞 ℚ) ∉ w.asIdeal := fun hpw =>
  hpq ((pl_eq_of_prime_mem w hp hpw).symm.trans (pl_eq_of_prime_mem w hq hqw))

theorem valued_algebraMap (q : ℚ) : Valued.v (algebraMap ℚ (Kv w) q) = w.valuation ℚ q := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w q

theorem inv_natCast_mem_integers {n : ℕ} (hn : (n : 𝓞 ℚ) ∉ w.asIdeal) : ((n : Kv w))⁻¹ ∈ Ov w := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀]
  have h1 : Valued.v ((n : Kv w)) = 1 := by
    rw [show ((n : ℕ) : Kv w) = algebraMap ℚ (Kv w) ((n : ℕ) : ℚ) from (map_natCast _ _).symm, valued_algebraMap,
      show ((n : ℕ) : ℚ) = algebraMap (𝓞 ℚ) ℚ ((n : ℕ) : 𝓞 ℚ) from (map_natCast _ _).symm]
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := ℚ) (v := w) (r := ((n : ℕ) : 𝓞 ℚ))).2 hn
  rw [h1, inv_one]

theorem algebraMap_inv_natCast_mem_integers {n : ℕ} (hn : (n : 𝓞 ℚ) ∉ w.asIdeal) :
    algebraMap ℚ (Kv w) ((n : ℚ)⁻¹) ∈ Ov w := by
  rw [map_inv₀, map_natCast]; exact inv_natCast_mem_integers w hn

theorem natCast_ne_zero_Kv {n : ℕ} (hn : n ≠ 0) : ((n : Kv w)) ≠ 0 := by
  have := (map_ne_zero (algebraMap ℚ (Kv w))).mpr (Nat.cast_ne_zero.mpr hn : ((n : ℕ) : ℚ) ≠ 0)
  rwa [map_natCast] at this

end places

section box

variable {a b : ℚ} (w : HeightOneSpectrum (𝓞 ℚ))

theorem tmul_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} {z : ℍ[ℚ, a, b]} (hz : z ∈ Λ) {c : Kv w} (hc : c ∈ Ov w) :
    z ⊗ₜ[ℚ] c ∈ Submodule.localBox Λ w :=
  AddSubgroup.subset_closure ⟨z, hz, c, hc, rfl⟩

theorem localBox_mono {Λ Λ' : Submodule ℤ ℍ[ℚ, a, b]} (h : Λ ≤ Λ') : Submodule.localBox Λ w ≤ Submodule.localBox Λ' w := by
  apply AddSubgroup.closure_mono
  rintro _ ⟨z, hz, c, hc, rfl⟩
  exact ⟨z, h hz, c, hc, rfl⟩

theorem mul_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hmul : ∀ x y : ℍ[ℚ, a, b], x ∈ Λ → y ∈ Λ → x * y ∈ Λ)
    {X Y : ℍ[ℚ, a, b] ⊗[ℚ] Kv w} (hX : X ∈ Submodule.localBox Λ w) (hY : Y ∈ Submodule.localBox Λ w) :
    X * Y ∈ Submodule.localBox Λ w := by

  have h1 : ∀ (z' : ℍ[ℚ, a, b]) (_ : z' ∈ Λ) (c' : Kv w) (_ : c' ∈ Ov w),
      Submodule.localBox Λ w ≤ (Submodule.localBox Λ w).comap (AddMonoidHom.mulRight (z' ⊗ₜ[ℚ] c')) := by
    intro z' hz' c' hc'
    unfold Submodule.localBox
    rw [AddSubgroup.closure_le]
    rintro _ ⟨z, hz, c, hc, rfl⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_comap, AddMonoidHom.coe_mulRight]
    show z ⊗ₜ[ℚ] c * z' ⊗ₜ[ℚ] c' ∈ _
    rw [Algebra.TensorProduct.tmul_mul_tmul]
    exact AddSubgroup.subset_closure ⟨_, hmul _ _ hz hz', _, mul_mem hc hc', rfl⟩

  have h2 : Submodule.localBox Λ w ≤ (Submodule.localBox Λ w).comap (AddMonoidHom.mulLeft X) := by
    unfold Submodule.localBox
    rw [AddSubgroup.closure_le]
    rintro _ ⟨z', hz', c', hc', rfl⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_comap, AddMonoidHom.coe_mulLeft]
    show X * z' ⊗ₜ[ℚ] c' ∈ _
    exact h1 z' hz' c' hc' hX
  exact h2 hY

theorem smul_tmul_one_eq' (q : ℚ) (m : ℍ[ℚ, a, b]) :
    (q • m) ⊗ₜ[ℚ] (1 : Kv w) = m ⊗ₜ[ℚ] algebraMap ℚ (Kv w) q := by
  rw [TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]

theorem smul_tmul_one_eq (q : ℚ) (m : ℍ[ℚ, a, b]) :
    (q • m) ⊗ₜ[ℚ] (1 : Kv w) = (m ⊗ₜ[ℚ] (1 : Kv w)) * ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ (Kv w) q) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]

end box

section globalToLocal

variable {a b : ℚ}

theorem local_of_global (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsOrder Λ) (hR : IsOrder R) (hRΛ : R ≤ Λ)
    (r : ℕ) [Fact r.Prime] (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓr : ℓ ≠ r)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hℓv : ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (s : ℍ[ℚ, a, b]) (hsR : ∃ c : ℕ, ((r ^ c : ℕ) : ℚ) • s ∈ R) (hsR' : ∃ c : ℕ, ((r ^ c : ℕ) : ℚ) • star s ∈ R)
    (z : ℍ[ℚ, a, b]) (hz : z ∈ R)
    (hne : ∀ (c : ℕ) (y : ℍ[ℚ, a, b]), y ∈ Λ → ((r ^ c : ℕ) : ℚ) • (s * z * star s) ≠ (ℓ : ℚ) • y) :
    ((ℓ : ℚ)⁻¹ • (s * z * star s)) ⊗ₜ[ℚ] (1 : Kv v) ∉ Submodule.localBox Λ v := by
  intro hmem
  have hr : r.Prime := Fact.out
  obtain ⟨vr, hvr⟩ := exists_pl_eq r hr
  have hvr' : ((r : ℕ) : 𝓞 ℚ) ∈ vr.asIdeal := (natCast_mem_asIdeal_iff vr r).mpr (by rw [hvr])

  have hs : ∀ w, w ≠ vr → s ⊗ₜ[ℚ] (1 : Kv w) ∈ Submodule.localBox R w :=
    (IsOrder.forall_tmul_one_mem_localBox_iff_exists_pow_smul_mem R hR r vr hvr' s).mpr hsR
  have hs' : ∀ w, w ≠ vr → star s ⊗ₜ[ℚ] (1 : Kv w) ∈ Submodule.localBox R w :=
    (IsOrder.forall_tmul_one_mem_localBox_iff_exists_pow_smul_mem R hR r vr hvr' (star s)).mpr hsR'

  set q : ℍ[ℚ, a, b] := (ℓ : ℚ)⁻¹ • (s * z * star s) with hq
  have hall : ∀ w, w ≠ vr → q ⊗ₜ[ℚ] (1 : Kv w) ∈ Submodule.localBox Λ w := by
    intro w hwr
    by_cases hwv : w = v
    · subst hwv; exact hmem
    · have hℓw : ((ℓ : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := fun h =>
        hwv (eq_of_pl_eq ((pl_eq_of_prime_mem w hℓ h).trans (pl_eq_of_prime_mem v hℓ hℓv).symm))
      rw [hq, smul_tmul_one_eq]
      refine mul_mem_localBox w hΛ.mul_mem ?_ (tmul_mem_localBox w hΛ.one_mem (algebraMap_inv_natCast_mem_integers w hℓw))
      rw [show (s * z * star s) ⊗ₜ[ℚ] (1 : Kv w) =
          (s ⊗ₜ[ℚ] (1 : Kv w)) * (z ⊗ₜ[ℚ] (1 : Kv w)) * (star s ⊗ₜ[ℚ] (1 : Kv w)) from by
        rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one]]
      refine mul_mem_localBox w hΛ.mul_mem (mul_mem_localBox w hΛ.mul_mem ?_ ?_) ?_
      · exact localBox_mono w hRΛ (hs w hwr)
      · exact localBox_mono w hRΛ (tmul_mem_localBox w hz (one_mem _))
      · exact localBox_mono w hRΛ (hs' w hwr)
  obtain ⟨K, hK⟩ := (IsOrder.forall_tmul_one_mem_localBox_iff_exists_pow_smul_mem Λ hΛ r vr hvr' q).mp hall
  refine hne K _ hK ?_
  rw [hq, smul_smul, mul_comm, ← smul_smul, smul_inv_smul₀ (Nat.cast_ne_zero.mpr hℓ.ne_zero)]

theorem global_of_local (Λ : Submodule ℤ ℍ[ℚ, a, b])
    (r : ℕ) (hr : r.Prime) (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓr : ℓ ≠ r)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hℓv : ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) (t : ℍ[ℚ, a, b])
    (hloc : ((ℓ : ℚ)⁻¹ • t) ⊗ₜ[ℚ] (1 : Kv v) ∉ Submodule.localBox Λ v) :
    ∀ (c : ℕ) (y : ℍ[ℚ, a, b]), y ∈ Λ → ((r ^ c : ℕ) : ℚ) • t ≠ (ℓ : ℚ) • y := by
  intro c y hy heq
  apply hloc
  have hrc : ((r ^ c : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (pow_ne_zero c hr.ne_zero)
  have hℓ0 : (ℓ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hℓ.ne_zero
  have h1 : t = ((r ^ c : ℕ) : ℚ)⁻¹ • ((ℓ : ℚ) • y) := by rw [← heq, inv_smul_smul₀ hrc]
  have ht : (ℓ : ℚ)⁻¹ • t = ((r ^ c : ℕ) : ℚ)⁻¹ • y := by
    rw [h1, smul_comm ((ℓ : ℚ)⁻¹), inv_smul_smul₀ hℓ0]
  rw [ht, smul_tmul_one_eq']
  have hrv : ((r ^ c : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := by
    intro h
    rw [natCast_mem_asIdeal_iff] at h
    have h1 := (Nat.prime_dvd_prime_iff_eq (pl_prime v) hr).mp ((pl_prime v).dvd_of_dvd_pow h)
    exact hℓr ((pl_eq_of_prime_mem v hℓ hℓv).symm.trans h1)
  exact tmul_mem_localBox v hy (algebraMap_inv_natCast_mem_integers v hrv)

end globalToLocal

section density

variable {a b : ℚ}

theorem exists_global_of_local (R Λ' : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsOrder R) (hΛ' : IsOrder Λ') (hRΛ' : R ≤ Λ')
    (ℓ : ℕ) (hℓ : ℓ.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hℓv : ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (s : ℍ[ℚ, a, b]) (hs : s ⊗ₜ[ℚ] (1 : Kv v) ∈ Submodule.localBox R v)
    (hs' : star s ⊗ₜ[ℚ] (1 : Kv v) ∈ Submodule.localBox R v)
    (X : ℍ[ℚ, a, b] ⊗[ℚ] Kv v) (hX : X ∈ Submodule.localBox R v)
    (hXne : (((ℓ : ℚ)⁻¹ • star s) ⊗ₜ[ℚ] (1 : Kv v)) * X * (s ⊗ₜ[ℚ] (1 : Kv v)) ∉ Submodule.localBox Λ' v) :
    ∃ x ∈ R, ((ℓ : ℚ)⁻¹ • (star s * x * s)) ⊗ₜ[ℚ] (1 : Kv v) ∉ Submodule.localBox Λ' v := by
  obtain ⟨z, hz, E, hE, hXeq⟩ :=
    Submodule.exists_mem_add_one_tmul_pow_mul_of_mem_localBox R hR.fg hR.spanTop ℓ hℓ v hℓv 1 hX
  refine ⟨z, hz, fun hmem => hXne ?_⟩
  have hℓ0 : ((ℓ : Kv v)) ≠ 0 := natCast_ne_zero_Kv v hℓ.ne_zero
  have hℓinv : algebraMap ℚ (Kv v) ((ℓ : ℚ)⁻¹) = ((ℓ : Kv v))⁻¹ := by rw [map_inv₀, map_natCast]

  have h1 : (((ℓ : ℚ)⁻¹ • star s) ⊗ₜ[ℚ] (1 : Kv v)) * (z ⊗ₜ[ℚ] (1 : Kv v)) * (s ⊗ₜ[ℚ] (1 : Kv v)) =
      ((ℓ : ℚ)⁻¹ • (star s * z * s)) ⊗ₜ[ℚ] (1 : Kv v) := by
    rw [smul_tmul_one_eq', smul_tmul_one_eq', Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      mul_one, mul_one]

  have h2 : (((ℓ : ℚ)⁻¹ • star s) ⊗ₜ[ℚ] (1 : Kv v)) * (((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((ℓ : Kv v) ^ 1)) * E) *
      (s ⊗ₜ[ℚ] (1 : Kv v)) = (star s ⊗ₜ[ℚ] (1 : Kv v)) * E * (s ⊗ₜ[ℚ] (1 : Kv v)) := by
    rw [smul_tmul_one_eq', hℓinv, pow_one, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      inv_mul_cancel₀ hℓ0]
  rw [hXeq, mul_add, add_mul, h1, h2]
  refine AddSubgroup.add_mem _ hmem ?_
  exact mul_mem_localBox v hΛ'.mul_mem
    (mul_mem_localBox v hΛ'.mul_mem (localBox_mono v hRΛ' hs') (localBox_mono v hRΛ' hE)) (localBox_mono v hRΛ' hs)

end density

section translate

variable {a b : ℚ}

theorem tmul_one_mem_localBox_of_pow_smul_mem (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsOrder R)
    (r : ℕ) [Fact r.Prime] (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓr : ℓ ≠ r)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hℓv : ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (s : ℍ[ℚ, a, b]) (hsR : ∃ c : ℕ, ((r ^ c : ℕ) : ℚ) • s ∈ R) :
    s ⊗ₜ[ℚ] (1 : Kv v) ∈ Submodule.localBox R v := by
  have hr : r.Prime := Fact.out
  obtain ⟨vr, hvr⟩ := exists_pl_eq r hr
  have hvr' : ((r : ℕ) : 𝓞 ℚ) ∈ vr.asIdeal := (natCast_mem_asIdeal_iff vr r).mpr (by rw [hvr])
  have hvvr : v ≠ vr := fun h =>
    hℓr ((pl_eq_of_prime_mem v hℓ hℓv).symm.trans (h ▸ hvr : pl v = r))
  exact (IsOrder.forall_tmul_one_mem_localBox_iff_exists_pow_smul_mem R hR r vr hvr' s).mpr hsR v hvvr

theorem localBox_eq_inf (Λ₁ R₁ Λ₁s : Submodule ℤ ℍ[ℚ, a, b]) (hΛ₁ : IsOrder Λ₁) (hΛ₁s : IsOrder Λ₁s)
    (htwin : Λ₁ ⊓ Λ₁s = R₁) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Submodule.localBox R₁ v = Submodule.localBox Λ₁ v ⊓ Submodule.localBox Λ₁s v := by
  rw [← htwin]
  exact Submodule.localBox_inf Λ₁ Λ₁s hΛ₁.fg hΛ₁.spanTop hΛ₁s.fg hΛ₁s.spanTop v

end translate

section frame

variable {a b : ℚ} (v : HeightOneSpectrum (𝓞 ℚ))
  (φ : (ℍ[ℚ, a, b] ⊗[ℚ] (Kv v)) ≃+* Matrix (Fin 2) (Fin 2) (Kv v))
  (hφ : ∀ c : Kv v, φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) = c • (1 : Matrix (Fin 2) (Fin 2) (Kv v)))
  (h : GL (Fin 2) (Kv v))

def M (x : ℍ[ℚ, a, b] ⊗[ℚ] Kv v) : Matrix (Fin 2) (Fin 2) (Kv v) :=
  ((h⁻¹ : GL (Fin 2) (Kv v)) : Matrix (Fin 2) (Fin 2) (Kv v)) * φ x * (h : Matrix (Fin 2) (Fin 2) (Kv v))

theorem M_def (x : ℍ[ℚ, a, b] ⊗[ℚ] Kv v) :
    M v φ h x = ((h⁻¹ : GL (Fin 2) (Kv v)) : Matrix (Fin 2) (Fin 2) (Kv v)) * φ x * (h : Matrix (Fin 2) (Fin 2) (Kv v)) :=
  rfl

theorem M_mul (x y : ℍ[ℚ, a, b] ⊗[ℚ] Kv v) : M v φ h (x * y) = M v φ h x * M v φ h y := by
  rw [M_def, M_def, M_def, φ.map_mul]
  simp only [Matrix.mul_assoc]
  rw [Units.mul_inv_cancel_left]

include hφ in
theorem M_one_tmul (c : Kv v) : M v φ h ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) = c • (1 : Matrix (Fin 2) (Fin 2) (Kv v)) := by
  rw [M_def, hφ, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Units.inv_mul]

include hφ in
theorem M_smul_tmul_one (q : ℚ) (m : ℍ[ℚ, a, b]) :
    M v φ h ((q • m) ⊗ₜ[ℚ] (1 : Kv v)) = algebraMap ℚ (Kv v) q • M v φ h (m ⊗ₜ[ℚ] (1 : Kv v)) := by
  rw [smul_tmul_one_eq, M_mul, M_one_tmul v φ hφ h, Matrix.mul_smul, Matrix.mul_one]

theorem M_symm (X : Matrix (Fin 2) (Fin 2) (Kv v)) :
    M v φ h (φ.symm ((h : Matrix (Fin 2) (Fin 2) (Kv v)) * X * ((h⁻¹ : GL (Fin 2) (Kv v)) : Matrix (Fin 2) (Fin 2) (Kv v)))) = X := by
  simp only [M, RingEquiv.apply_symm_apply, Matrix.mul_assoc]
  rw [Units.inv_mul, Matrix.mul_one, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]

theorem conjDiag_apply (ℓ : Kv v) (A : Matrix (Fin 2) (Fin 2) (Kv v)) (i j : Fin 2) :
    (Matrix.diagonal ![(1 : Kv v), ℓ⁻¹] * A * Matrix.diagonal ![(1 : Kv v), ℓ]) i j = ![(1 : Kv v), ℓ⁻¹] i * A i j * ![(1 : Kv v), ℓ] j := by
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem iwahori_iff (ℓ : ℕ) (hℓ0 : ((ℓ : Kv v)) ≠ 0) (A : Matrix (Fin 2) (Fin 2) (Kv v)) (hA : ∀ i j, A i j ∈ Ov v) :
    (∀ i j, (Matrix.diagonal ![(1 : Kv v), ((ℓ : Kv v))⁻¹] * A * Matrix.diagonal ![(1 : Kv v), (ℓ : Kv v)]) i j ∈ Ov v) ↔
      ((ℓ : Kv v))⁻¹ * A 1 0 ∈ Ov v := by
  have hℓO : ((ℓ : Kv v)) ∈ Ov v := by
    rw [show ((ℓ : ℕ) : Kv v) = algebraMap ℚ (Kv v) ((ℓ : ℕ) : ℚ) from (map_natCast _ _).symm,
      HeightOneSpectrum.mem_adicCompletionIntegers, valued_algebraMap,
      show ((ℓ : ℕ) : ℚ) = algebraMap (𝓞 ℚ) ℚ ((ℓ : ℕ) : 𝓞 ℚ) from (map_natCast _ _).symm,
      HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_le_one _ _
  simp only [conjDiag_apply, Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    one_mul, mul_one]
  constructor
  · rintro ⟨⟨-, -⟩, h10, -⟩; exact h10
  · intro h10
    refine ⟨⟨hA 0 0, mul_mem (hA 0 1) hℓO⟩, h10, ?_⟩
    rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ hℓ0, one_mul]
    exact hA 1 1

end frame

section assembly

theorem main {a₁ b₁ : ℚ}
    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrN : ¬ r ∣ N) (hrbarN : ¬ rbar ∣ N) (hN : Squarefree N)
    (hdef : IsDefiniteRamifiedExactlyAt (a := a₁) (b := b₁) rbar)
    (Λ₁ R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ₁ : IsMaximalOrder Λ₁) (hR₁ : IsEichlerOrder R₁ N) (hRΛ₁ : R₁ ≤ Λ₁)
    (Λ₁s : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ₁s : IsMaximalOrder Λ₁s) (hR₁Λ₁s : R₁ ≤ Λ₁s) (htwin : Λ₁ ⊓ Λ₁s = R₁)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N)
    (s : ℍ[ℚ, a₁, b₁]) (hns : nrd s = (ℓ : ℚ))
    (hsR : ∃ c : ℕ, ((r ^ c : ℕ) : ℚ) • s ∈ R₁) (hsR' : ∃ c : ℕ, ((r ^ c : ℕ) : ℚ) • star s ∈ R₁)
    (hz : ∃ z : ℍ[ℚ, a₁, b₁], z ∈ R₁ ∧ ∀ (c : ℕ) (y : ℍ[ℚ, a₁, b₁]), y ∈ Λ₁ →
      ((r ^ c : ℕ) : ℚ) • (s * z * star s) ≠ (ℓ : ℚ) • y) :
    ∃ x : ℍ[ℚ, a₁, b₁], x ∈ R₁ ∧ ∀ (c : ℕ) (y : ℍ[ℚ, a₁, b₁]), y ∈ Λ₁s →
      ((r ^ c : ℕ) : ℚ) • (star s * x * s) ≠ (ℓ : ℚ) • y := by
  have hr : r.Prime := Fact.out
  have hℓr : ℓ ≠ r := fun h => hrN (h ▸ hℓN)
  have hOΛ₁ : IsOrder Λ₁ := hΛ₁.isOrder
  have hOΛ₁s : IsOrder Λ₁s := hΛ₁s.isOrder
  have hOR₁ : IsOrder R₁ := hR₁.isOrder
  obtain ⟨v, hv⟩ := exists_pl_eq ℓ hℓ
  have hℓv : ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := (natCast_mem_asIdeal_iff v ℓ).mpr (by rw [hv])
  have hℓ0 : ((ℓ : Kv v)) ≠ 0 := natCast_ne_zero_Kv v hℓ.ne_zero
  have hℓq0 : (ℓ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hℓ.ne_zero
  have hℓinv : algebraMap ℚ (Kv v) ((ℓ : ℚ)⁻¹) = ((ℓ : Kv v))⁻¹ := by rw [map_inv₀, map_natCast]

  obtain ⟨z, hzR, hzne⟩ := hz
  have hZloc := local_of_global Λ₁ R₁ hOΛ₁ hOR₁ hRΛ₁ r ℓ hℓ hℓr v hℓv s hsR hsR' z hzR hzne

  have hs := tmul_one_mem_localBox_of_pow_smul_mem R₁ hOR₁ r ℓ hℓ hℓr v hℓv s hsR
  have hs' := tmul_one_mem_localBox_of_pow_smul_mem R₁ hOR₁ r ℓ hℓ hℓr v hℓv (star s) hsR'
  have hzv : z ⊗ₜ[ℚ] (1 : Kv v) ∈ Submodule.localBox R₁ v := tmul_mem_localBox v hzR (one_mem _)

  have hprod1 : (s ⊗ₜ[ℚ] (1 : Kv v)) * (z ⊗ₜ[ℚ] (1 : Kv v)) * (((ℓ : ℚ)⁻¹ • star s) ⊗ₜ[ℚ] (1 : Kv v)) =
      ((ℓ : ℚ)⁻¹ • (s * z * star s)) ⊗ₜ[ℚ] (1 : Kv v) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one, mul_smul_comm]
  have hprod2 : (((ℓ : ℚ)⁻¹ • s) ⊗ₜ[ℚ] (1 : Kv v)) * (z ⊗ₜ[ℚ] (1 : Kv v)) * (star s ⊗ₜ[ℚ] (1 : Kv v)) =
      ((ℓ : ℚ)⁻¹ • (s * z * star s)) ⊗ₜ[ℚ] (1 : Kv v) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one, smul_mul_assoc,
      smul_mul_assoc]

  obtain ⟨φ, h, hφ, hΛ₁v, hΛ₁sv⟩ :=
    IsMaximalOrder.exists_ringEquiv_generalLinearGroup_forall_mem_localBox_iff_of_inf_eq_of_dvd_of_squarefree
      hrbarN hN hdef Λ₁ R₁ hΛ₁ hR₁ hRΛ₁ Λ₁s hΛ₁s hR₁Λ₁s htwin ℓ hℓ hℓN v hℓv

  have hR₁v : ∀ x, x ∈ Submodule.localBox R₁ v ↔
      (∀ i j, M v φ h x i j ∈ Ov v) ∧ ((ℓ : Kv v))⁻¹ * M v φ h x 1 0 ∈ Ov v := by
    intro x
    have hre : Matrix.diagonal ![(1 : Kv v), ((ℓ : Kv v))⁻¹] *
        ((h⁻¹ : GL (Fin 2) (Kv v)) : Matrix (Fin 2) (Fin 2) (Kv v)) * φ x * (h : Matrix (Fin 2) (Fin 2) (Kv v)) *
        Matrix.diagonal ![(1 : Kv v), (ℓ : Kv v)] =
        Matrix.diagonal ![(1 : Kv v), ((ℓ : Kv v))⁻¹] * M v φ h x * Matrix.diagonal ![(1 : Kv v), (ℓ : Kv v)] := by
      simp only [M, Matrix.mul_assoc]
    rw [localBox_eq_inf Λ₁ R₁ Λ₁s hOΛ₁ hOΛ₁s htwin v, AddSubgroup.mem_inf, hΛ₁v x, hΛ₁sv x, hre]
    exact ⟨fun hh => ⟨hh.1, (iwahori_iff v ℓ hℓ0 _ hh.1).mp hh.2⟩, fun hh => ⟨hh.1, (iwahori_iff v ℓ hℓ0 _ hh.1).mpr hh.2⟩⟩

  set Y := M v φ h (s ⊗ₜ[ℚ] (1 : Kv v)) with hY
  set Yi := M v φ h (((ℓ : ℚ)⁻¹ • star s) ⊗ₜ[ℚ] (1 : Kv v)) with hYi
  have hM1 : M v φ h (1 : ℍ[ℚ, a₁, b₁] ⊗[ℚ] Kv v) = 1 := by
    rw [Algebra.TensorProduct.one_def, M_one_tmul v φ hφ h, one_smul]
  have h1 : Y * Yi = 1 := by
    rw [hY, hYi, ← M_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_smul_comm, mul_star_eq_coe_nrd, hns,
      QuaternionAlgebra.smul_coe, inv_mul_cancel₀ hℓq0, QuaternionAlgebra.coe_one, ← Algebra.TensorProduct.one_def, hM1]
  have h2 : Yi * Y = 1 := by
    rw [hY, hYi, ← M_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, smul_mul_assoc, star_mul_eq_coe_nrd, hns,
      QuaternionAlgebra.smul_coe, inv_mul_cancel₀ hℓq0, QuaternionAlgebra.coe_one, ← Algebra.TensorProduct.one_def, hM1]
  obtain ⟨hYint, hY10⟩ := (hR₁v _).mp hs
  have hℓYi : ((ℓ : Kv v)) • Yi = M v φ h (star s ⊗ₜ[ℚ] (1 : Kv v)) := by
    rw [hYi, M_smul_tmul_one v φ hφ h, hℓinv, smul_smul, mul_inv_cancel₀ hℓ0, one_smul]
  obtain ⟨hpYi, hpYi10⟩ : (∀ i j, (((ℓ : Kv v)) • Yi) i j ∈ Ov v) ∧ ((ℓ : Kv v))⁻¹ * (((ℓ : Kv v)) • Yi) 1 0 ∈ Ov v := by
    rw [hℓYi]; exact (hR₁v _).mp hs'
  have hYi_not : ¬ ((∀ i j, Yi i j ∈ Ov v) ∧ ((ℓ : Kv v))⁻¹ * Yi 1 0 ∈ Ov v) := by
    intro hh
    have hmem : (((ℓ : ℚ)⁻¹ • star s) ⊗ₜ[ℚ] (1 : Kv v)) ∈ Submodule.localBox R₁ v := (hR₁v _).mpr hh
    apply hZloc
    rw [← hprod1]
    exact localBox_mono v hRΛ₁ (mul_mem_localBox v hOR₁.mul_mem (mul_mem_localBox v hOR₁.mul_mem hs hzv) hmem)
  have hℓY : ((ℓ : Kv v))⁻¹ • Y = M v φ h (((ℓ : ℚ)⁻¹ • s) ⊗ₜ[ℚ] (1 : Kv v)) := by
    rw [hY, M_smul_tmul_one v φ hφ h, hℓinv]
  have hpY_not : ¬ ((∀ i j, ((((ℓ : Kv v))⁻¹ • Y) i j ∈ Ov v)) ∧
      ((ℓ : Kv v))⁻¹ * ((((ℓ : Kv v))⁻¹ • Y) 1 0) ∈ Ov v) := by
    rw [hℓY]
    intro hh
    have hmem : (((ℓ : ℚ)⁻¹ • s) ⊗ₜ[ℚ] (1 : Kv v)) ∈ Submodule.localBox R₁ v := (hR₁v _).mpr hh
    apply hZloc
    rw [← hprod2]
    exact localBox_mono v hRΛ₁ (mul_mem_localBox v hOR₁.mul_mem (mul_mem_localBox v hOR₁.mul_mem hmem hzv) hs')

  obtain ⟨hZint, hZ10⟩ := (hR₁v _).mp hzv
  have hZ : ∃ Z : Matrix (Fin 2) (Fin 2) (Kv v), (∀ i j, Z i j ∈ Ov v) ∧ (((ℓ : Kv v))⁻¹ * Z 1 0 ∈ Ov v) ∧
      ¬ ∀ i j, (Y * Z * Yi) i j ∈ Ov v := by
    refine ⟨M v φ h (z ⊗ₜ[ℚ] (1 : Kv v)), hZint, hZ10, fun hh => hZloc ?_⟩
    rw [hY, hYi, ← M_mul, ← M_mul, hprod1] at hh
    exact (hΛ₁v _).mpr hh

  obtain ⟨X, hXint, hX10, hXne⟩ :=
    Matrix.exists_iwahori_conj_diagonal_not_mem_of_exists_iwahori_conj_not_mem ℓ hℓ v hℓv Y Yi h1 h2 hYint hY10
      hpYi hpYi10 hYi_not hpY_not hZ

  set Xh : ℍ[ℚ, a₁, b₁] ⊗[ℚ] Kv v :=
    φ.symm ((h : Matrix (Fin 2) (Fin 2) (Kv v)) * X * ((h⁻¹ : GL (Fin 2) (Kv v)) : Matrix (Fin 2) (Fin 2) (Kv v))) with hXh
  have hMXh : M v φ h Xh = X := M_symm v φ h X
  have hXhR : Xh ∈ Submodule.localBox R₁ v := (hR₁v _).mpr (by rw [hMXh]; exact ⟨hXint, hX10⟩)
  have hW : (((ℓ : ℚ)⁻¹ • star s) ⊗ₜ[ℚ] (1 : Kv v)) * Xh * (s ⊗ₜ[ℚ] (1 : Kv v)) ∉ Submodule.localBox Λ₁s v := by
    intro hmem
    apply hXne
    have := (hΛ₁sv _).mp hmem
    have key : Matrix.diagonal ![(1 : Kv v), ((ℓ : Kv v))⁻¹] * ((h⁻¹ : GL (Fin 2) (Kv v)) : Matrix (Fin 2) (Fin 2) (Kv v)) *
        φ ((((ℓ : ℚ)⁻¹ • star s) ⊗ₜ[ℚ] (1 : Kv v)) * Xh * (s ⊗ₜ[ℚ] (1 : Kv v))) * (h : Matrix (Fin 2) (Fin 2) (Kv v)) *
        Matrix.diagonal ![(1 : Kv v), (ℓ : Kv v)] =
        Matrix.diagonal ![(1 : Kv v), ((ℓ : Kv v))⁻¹] * (Yi * X * Y) * Matrix.diagonal ![(1 : Kv v), (ℓ : Kv v)] := by
      rw [hY, hYi, ← hMXh, ← M_mul, ← M_mul]
      simp only [M, Matrix.mul_assoc]
    rwa [key] at this

  obtain ⟨x, hxR, hxloc⟩ := exists_global_of_local R₁ Λ₁s hOR₁ hOΛ₁s hR₁Λ₁s ℓ hℓ v hℓv s hs hs' Xh hXhR hW
  exact ⟨x, hxR, global_of_local Λ₁s r hr ℓ hℓ hℓr v hℓv (star s * x * s) hxloc⟩

end assembly

end NormEllTypeFlip

end

open scoped TensorProduct Quaternion NumberField
open QuaternionAlgebra
open scoped Quaternion

theorem solution
    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrN : ¬ r ∣ N) (hrbarN : ¬ rbar ∣ N) (hN : Squarefree N)
    {a₁ b₁ : ℚ} (hdef : IsDefiniteRamifiedExactlyAt (a := a₁) (b := b₁) rbar)
    (Λ₁ R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ₁ : IsMaximalOrder Λ₁) (hR₁ : IsEichlerOrder R₁ N) (hRΛ₁ : R₁ ≤ Λ₁)
    (Λ₁s : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ₁s : IsMaximalOrder Λ₁s) (hR₁Λ₁s : R₁ ≤ Λ₁s) (htwin : Λ₁ ⊓ Λ₁s = R₁)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N)
    (s : ℍ[ℚ, a₁, b₁]) (hns : nrd s = (ℓ : ℚ))
    (hsR : ∃ c : ℕ, ((r ^ c : ℕ) : ℚ) • s ∈ R₁) (hsR' : ∃ c : ℕ, ((r ^ c : ℕ) : ℚ) • star s ∈ R₁)
    (hz : ∃ z : ℍ[ℚ, a₁, b₁], z ∈ R₁ ∧ ∀ (c : ℕ) (y : ℍ[ℚ, a₁, b₁]), y ∈ Λ₁ →
      ((r ^ c : ℕ) : ℚ) • (s * z * star s) ≠ (ℓ : ℚ) • y) :
    ∃ x : ℍ[ℚ, a₁, b₁], x ∈ R₁ ∧ ∀ (c : ℕ) (y : ℍ[ℚ, a₁, b₁]), y ∈ Λ₁s →
      ((r ^ c : ℕ) : ℚ) • (star s * x * s) ≠ (ℓ : ℚ) • y := by
  exact NormEllTypeFlip.main hrN hrbarN hN hdef Λ₁ R₁ hΛ₁ hR₁ hRΛ₁ Λ₁s hΛ₁s hR₁Λ₁s htwin ℓ hℓ hℓN s hns hsR hsR' hz

end S_QuaternionAlgebra_IsEichlerOrder_exists_mem_forall_pow_smul_star_mul_mul_ne_smul_of_forall_pow_smul_mul_mul_star_ne_smul_of_inf_eq_of_dvd
end P2MW
export P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_mem_forall_pow_smul_star_mul_mul_ne_smul_of_forall_pow_smul_mul_mul_star_ne_smul_of_inf_eq_of_dvd (solution)
