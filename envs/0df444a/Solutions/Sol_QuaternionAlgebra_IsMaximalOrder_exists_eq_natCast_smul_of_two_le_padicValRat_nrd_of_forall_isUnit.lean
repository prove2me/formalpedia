-- Prove2me | solution 1 for QuaternionAlgebra.IsMaximalOrder.exists_eq_natCast_smul_of_two_le_padicValRat_nrd_of_forall_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/abe15098-2f53-539a-95da-e26719fea280

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_mem_localBox_iff_nrd_mem_adicCompletionIntegers_of_forall_isUnit
import Theorems.Thm_QuaternionAlgebra_exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
import Theorems.Thm_QuaternionAlgebra_forall_tensorProduct_adicCompletion_isUnit_iff_forall_normForm_eq_zero
import Theorems.Thm_Submodule_mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox
import Theorems.Thm_Submodule_ofFiniteIdele_one
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_eq_natCast_smul_of_two_le_padicValRat_nrd_of_forall_isUnit
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 3200000

open scoped TensorProduct Quaternion NumberField Pointwise
open IsDedekindDomain NumberField

noncomputable section

namespace RamPSq

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "HOS" => HeightOneSpectrum (𝓞 ℚ)

section Places

open Rat.HeightOneSpectrum

theorem natCast_mem_asIdeal_iff (w : HOS) (n : ℕ) :
    (n : 𝓞 ℚ) ∈ w.asIdeal ↔ natGenerator w ∣ n := by
  rw [natGenerator_dvd_iff, ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n, Ideal.apply_mem_of_equiv_iff]

theorem natGenerator_eq_of_mem {q : ℕ} (hq : q.Prime) (w : HOS) (hw : (q : 𝓞 ℚ) ∈ w.asIdeal) :
    natGenerator w = q :=
  (Nat.prime_dvd_prime_iff_eq (prime_natGenerator w) hq).mp ((natCast_mem_asIdeal_iff w q).mp hw)

theorem eq_of_natCast_mem {q : ℕ} (hq : q.Prime) {v w : HOS} (hv : (q : 𝓞 ℚ) ∈ v.asIdeal)
    (hw : (q : 𝓞 ℚ) ∈ w.asIdeal) : w = v := by
  apply (primesEquiv (R := 𝓞 ℚ)).injective
  apply Subtype.ext
  show natGenerator w = natGenerator v
  rw [natGenerator_eq_of_mem hq w hw, natGenerator_eq_of_mem hq v hv]

theorem natCast_notMem_of_ne {q : ℕ} (hq : q.Prime) {v : HOS} (hv : (q : 𝓞 ℚ) ∈ v.asIdeal) {w : HOS}
    (hw : w ≠ v) : (q : 𝓞 ℚ) ∉ w.asIdeal := fun h => hw (eq_of_natCast_mem hq hv h)

theorem valued_natCast_eq_one {n : ℕ} (w : HOS) (hn : (n : 𝓞 ℚ) ∉ w.asIdeal) :
    Valued.v (n : w.adicCompletion ℚ) = 1 := by
  have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) w (n : 𝓞 ℚ)
  rw [(HeightOneSpectrum.valuation_eq_one_iff_notMem (K := ℚ) (v := w)).mpr hn] at h
  change Valued.v (algebraMap (𝓞 ℚ) (w.adicCompletion ℚ) n) = 1 at h
  rwa [map_natCast] at h

theorem natCast_inv_mem_integers {n : ℕ} (w : HOS) (hn : (n : 𝓞 ℚ) ∉ w.asIdeal) :
    (n : w.adicCompletion ℚ)⁻¹ ∈ w.adicCompletionIntegers ℚ := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, valued_natCast_eq_one w hn, inv_one]

theorem natCast_mem_integers (w : HOS) (n : ℕ) : (n : w.adicCompletion ℚ) ∈ w.adicCompletionIntegers ℚ := by
  have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) w (n : 𝓞 ℚ)
  change Valued.v (algebraMap (𝓞 ℚ) (w.adicCompletion ℚ) n) = _ at h
  rw [map_natCast] at h
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, h]
  exact HeightOneSpectrum.valuation_le_one w _

variable (v : HOS)

theorem asIdeal_eq_span : v.asIdeal = Ideal.span {(natGenerator v : 𝓞 ℚ)} := by
  have h := span_natGenerator (R := 𝓞 ℚ) v
  have h2 : v.asIdeal = Ideal.map ((Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm : ℤ →+* 𝓞 ℚ)
      (Ideal.map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) : 𝓞 ℚ →+* ℤ) v.asIdeal) := by
    rw [Ideal.map_map]
    have : ((Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm : ℤ →+* 𝓞 ℚ).comp
        (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) : 𝓞 ℚ →+* ℤ) = RingHom.id _ := by
      ext x; simp
    rw [this, Ideal.map_id]
  rw [h2]
  erw [← h]
  rw [Ideal.map_span, Set.image_singleton]
  congr 2
  simp

theorem valuation_natGenerator : v.valuation ℚ (natGenerator v : ℚ) = WithZero.exp (-1) := by
  rw [show (natGenerator v : ℚ) = algebraMap (𝓞 ℚ) ℚ (natGenerator v) from (map_natCast _ _).symm,
    HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_singleton v (by exact_mod_cast (prime_natGenerator v).ne_zero)
    (asIdeal_eq_span v)

theorem valued_algebraMap (r : ℚ) : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) r) = v.valuation ℚ r := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v r

theorem valuation_eq_exp_neg_padicValRat {q : ℕ} [hq : Fact q.Prime] (hvq : natGenerator v = q) (r : ℚ) (hr : r ≠ 0) :
    v.valuation ℚ r = WithZero.exp (-padicValRat q r) := by

  have hpe : primesEquiv (R := 𝓞 ℚ) v = ⟨q, hq.out⟩ := Subtype.ext hvq
  have hiso : (v.valuation ℚ).IsEquiv (Rat.padicValuation q) := by
    have h := valuation_equiv_padicValuation (R := 𝓞 ℚ) v
    rw [hpe] at h
    exact h
  have hVq : v.valuation ℚ (q : ℚ) = WithZero.exp (-1) := by rw [← hvq]; exact valuation_natGenerator v
  have hPq : Rat.padicValuation q (q : ℚ) = WithZero.exp (-1) := Rat.padicValuation_self q
  have hP : Rat.padicValuation q r = WithZero.exp (-padicValRat q r) := by
    simp only [Rat.padicValuation, Valuation.coe_mk, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, if_neg hr]
  have hq0 : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq.out.ne_zero
  have hVpow : ∀ j : ℤ, v.valuation ℚ ((q : ℚ) ^ j) = WithZero.exp (-j) := fun j => by
    rw [map_zpow₀, hVq, ← WithZero.exp_zsmul, smul_neg, zsmul_one, Int.cast_id]
  have hPpow : ∀ j : ℤ, Rat.padicValuation q ((q : ℚ) ^ j) = WithZero.exp (-j) := fun j => by
    rw [map_zpow₀, hPq, ← WithZero.exp_zsmul, smul_neg, zsmul_one, Int.cast_id]
  have hV0 : v.valuation ℚ r ≠ 0 := (Valuation.ne_zero_iff _).mpr hr
  set m := WithZero.log (v.valuation ℚ r) with hm
  have hVr : v.valuation ℚ r = WithZero.exp m := (WithZero.exp_log hV0).symm
  set t := padicValRat q r

  have h1 : -t ≤ m := by
    have := (hiso.le_iff_le (x := r) (y := (q : ℚ) ^ (-m))).mp (by rw [hVr, hVpow, neg_neg])
    rw [hP, hPpow, neg_neg, WithZero.exp_le_exp] at this
    exact this
  have h2 : m ≤ -t := by
    have := (hiso.le_iff_le (x := r) (y := (q : ℚ) ^ t)).mpr (by rw [hP, hPpow])
    rw [hVr, hVpow, WithZero.exp_le_exp] at this
    exact this
  rw [hVr, le_antisymm h2 h1]

end Places

section PlaceDef

open Rat.HeightOneSpectrum

def place (q : ℕ) (hq : q.Prime) : HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨q, hq⟩

variable (q : ℕ) (hq : q.Prime)

local notation "𝔳" => place q hq

theorem primesEquiv_place : Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) 𝔳 = ⟨q, hq⟩ := by
  simp [place]

theorem natGenerator_place : Rat.HeightOneSpectrum.natGenerator 𝔳 = q :=
  congrArg Subtype.val (primesEquiv_place q hq)

theorem q_mem_asIdeal_place : (q : 𝓞 ℚ) ∈ (𝔳).asIdeal := by
  rw [natCast_mem_asIdeal_iff, natGenerator_place]

end PlaceDef

section LocalBox

variable {D : Type*} [Ring D] [Algebra ℚ D]

theorem tmul_one_mem_localBox {Λ : Submodule ℤ D} {z : D} (hz : z ∈ Λ) (w : HOS) :
    z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) ∈ Submodule.localBox Λ w :=
  AddSubgroup.subset_closure ⟨z, hz, 1, (w.adicCompletionIntegers ℚ).one_mem, rfl⟩

theorem gen_mul_mem_localBox (Λ : Submodule ℤ D)
    (hmul : ∀ x y : D, x ∈ Λ → y ∈ Λ → x * y ∈ Λ) (w : HOS)
    {z : D} (hz : z ∈ Λ) {c : w.adicCompletion ℚ} (hc : c ∈ w.adicCompletionIntegers ℚ)
    {y : D ⊗[ℚ] w.adicCompletion ℚ} (hy : y ∈ Submodule.localBox Λ w) :
    (z ⊗ₜ[ℚ] c) * y ∈ Submodule.localBox Λ w := by
  unfold Submodule.localBox at hy ⊢
  refine AddSubgroup.closure_induction (p := fun y _ => (z ⊗ₜ[ℚ] c) * y ∈ _) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨z', hz', c', hc', rfl⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul]
    exact AddSubgroup.subset_closure ⟨z * z', hmul z z' hz hz', c * c', mul_mem hc hc', rfl⟩
  · show z ⊗ₜ[ℚ] c * 0 ∈ _
    rw [mul_zero]; exact AddSubgroup.zero_mem _
  · intro x y _ _ hx hy
    rw [mul_add]; exact AddSubgroup.add_mem _ hx hy
  · intro x _ hx
    convert AddSubgroup.neg_mem _ hx using 1
    exact mul_neg (z ⊗ₜ[ℚ] c) x

theorem rat_smul_eq_one_tmul_mul (w : HOS) (q : ℚ) (x : D ⊗[ℚ] w.adicCompletion ℚ) :
    q • x = ((1 : D) ⊗ₜ[ℚ] (algebraMap ℚ (w.adicCompletion ℚ) q)) * x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [smul_zero, mul_zero]
  | tmul z s =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← Algebra.smul_def, TensorProduct.smul_tmul',
      TensorProduct.smul_tmul]
  | add x y hx hy => rw [smul_add, mul_add, hx, hy]

variable (Λ : Submodule ℤ D) (v : HeightOneSpectrum (𝓞 ℚ))

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ v
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ v

theorem tmul_mem_localBox {z : D} (hz : z ∈ Λ) {c : 𝕂} (hc : c ∈ 𝓞v) :
    z ⊗ₜ[ℚ] c ∈ Submodule.localBox Λ v :=
  AddSubgroup.subset_closure ⟨z, hz, c, hc, rfl⟩

theorem one_tmul_mul_mem_localBox {x : D ⊗[ℚ] 𝕂} (hx : x ∈ Submodule.localBox Λ v) {c : 𝕂}
    (hc : c ∈ 𝓞v) : ((1 : D) ⊗ₜ[ℚ] c) * x ∈ Submodule.localBox Λ v := by
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨z, hz, c', hc', rfl⟩ := hy
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    exact tmul_mem_localBox Λ v hz (mul_mem hc hc')
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => exact (mul_neg _ x).symm ▸ neg_mem hx

theorem mul_mem_localBox (hmul : ∀ x y : D, x ∈ Λ → y ∈ Λ → x * y ∈ Λ)
    {x y : D ⊗[ℚ] 𝕂} (hx : x ∈ Submodule.localBox Λ v) (hy : y ∈ Submodule.localBox Λ v) :
    x * y ∈ Submodule.localBox Λ v := by
  induction hy using AddSubgroup.closure_induction with
  | mem y' hy' =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hy'
    induction hx using AddSubgroup.closure_induction with
    | mem x' hx' =>
      obtain ⟨z', hz', c', hc', rfl⟩ := hx'
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact tmul_mem_localBox Λ v (hmul _ _ hz' hz) (mul_mem hc' hc)
    | zero => rw [zero_mul]; exact zero_mem _
    | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
    | neg x _ hx => exact (neg_mul x _).symm ▸ neg_mem hx
  | zero => rw [mul_zero]; exact zero_mem _
  | add x' y' _ _ hx' hy' => rw [mul_add]; exact add_mem hx' hy'
  | neg x' _ hx' => exact (mul_neg _ x').symm ▸ neg_mem hx'

omit [Algebra ℚ D] in

theorem one_tmul_comm' {S : Type*} [CommRing S] [Algebra ℚ S] [Algebra ℚ D] (c : S) (x : D ⊗[ℚ] S) :
    ((1 : D) ⊗ₜ[ℚ] c) * x = x * ((1 : D) ⊗ₜ[ℚ] c) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [mul_zero, zero_mul]
  | tmul z d => rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, mul_comm]
  | add x y hx hy => rw [mul_add, add_mul, hx, hy]

end LocalBox

section Quaternion

variable {a b : ℚ}

theorem mem_iff_forall_tmul_one_mem_localBox (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsOrder Λ)
    (z : ℍ[ℚ, a, b]) : z ∈ Λ ↔ ∀ w : HOS, z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) ∈ Submodule.localBox Λ w := by
  have h1 := Submodule.ofFiniteIdele_one Λ hΛ.fg hΛ.spanTop
  constructor
  · intro hz w; exact tmul_one_mem_localBox hz w
  · intro hz
    rw [← h1, Submodule.mem_ofFiniteIdele_iff]
    refine ⟨z ⊗ₜ[ℚ] (1 : 𝔸f), ?_, by simp⟩
    rw [SetLike.mem_coe, Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox Λ hΛ.fg hΛ.spanTop]
    intro w
    rw [Submodule.finiteAdeleEvalAt_tmul]
    exact hz w

section RamifiedPlace

open QuaternionAlgebra Rat.HeightOneSpectrum

theorem nrd_mul' {K : Type*} [CommRing K] {α β : K} (x y : ℍ[K, α, β]) : nrd (x * y) = nrd x * nrd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x; obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_mul_mk, nrd_mk]; ring

theorem nrd_smul' {K : Type*} [CommRing K] {α β : K} (c : K) (x : ℍ[K, α, β]) : nrd (c • x) = c ^ 2 * nrd x := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  simp only [QuaternionAlgebra.smul_mk, nrd_mk, smul_eq_mul]; ring

variable (v : HeightOneSpectrum (𝓞 ℚ))
  (φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+*
      ℍ[v.adicCompletion ℚ, algebraMap ℚ (v.adicCompletion ℚ) a, algebraMap ℚ (v.adicCompletion ℚ) b])
  (hφ : ∀ (z : ℍ[ℚ, a, b]) (r : v.adicCompletion ℚ),
      φ (z ⊗ₜ[ℚ] r) = r • (⟨algebraMap ℚ (v.adicCompletion ℚ) z.re, algebraMap ℚ (v.adicCompletion ℚ) z.imI,
        algebraMap ℚ (v.adicCompletion ℚ) z.imJ, algebraMap ℚ (v.adicCompletion ℚ) z.imK⟩ :
          ℍ[v.adicCompletion ℚ, algebraMap ℚ (v.adicCompletion ℚ) a, algebraMap ℚ (v.adicCompletion ℚ) b]))

include hφ in
theorem nrd_φ_tmul (z : ℍ[ℚ, a, b]) (c : v.adicCompletion ℚ) :
    nrd (φ (z ⊗ₜ[ℚ] c)) = c ^ 2 * algebraMap ℚ (v.adicCompletion ℚ) (nrd z) := by
  rw [hφ, nrd_smul']
  congr 1
  obtain ⟨z₀, z₁, z₂, z₃⟩ := z
  simp only [nrd_mk, map_add, map_sub, map_mul, map_pow]

include hφ in
theorem nrd_φ_one_tmul (c : v.adicCompletion ℚ) : nrd (φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c)) = c ^ 2 := by
  rw [nrd_φ_tmul v φ hφ, nrd_one, map_one, mul_one]

theorem nrd_φ_mul (x y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) : nrd (φ (x * y)) = nrd (φ x) * nrd (φ y) := by
  rw [map_mul, nrd_mul']

abbrev VN (y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) : WithZero (Multiplicative ℤ) := Valued.v (nrd (φ y))

theorem VN_mul (x y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) : VN v φ (x * y) = VN v φ x * VN v φ y := by
  rw [VN, nrd_φ_mul, map_mul]

theorem VN_one : VN v φ 1 = 1 := by
  rw [VN, map_one, nrd_one, map_one]

theorem VN_units_ne_zero (u : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : VN v φ (u : _) ≠ 0 := by
  have h : VN v φ (u : _) * VN v φ ((u⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : _) = 1 := by
    rw [← VN_mul, Units.mul_inv, VN_one]
  exact left_ne_zero_of_mul_eq_one h

theorem VN_units_inv (u : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) :
    VN v φ ((u⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : _) = (VN v φ (u : _))⁻¹ := by
  have h : VN v φ (u : _) * VN v φ ((u⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : _) = 1 := by
    rw [← VN_mul, Units.mul_inv, VN_one]
  exact (eq_inv_of_mul_eq_one_right h)

include hφ in
theorem VN_one_tmul (c : v.adicCompletion ℚ) : VN v φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) = (Valued.v c) ^ 2 := by
  rw [VN, nrd_φ_one_tmul v φ hφ, map_pow]

include hφ in

theorem VN_tmul_one {q : ℕ} [Fact q.Prime] (hvq : natGenerator v = q) (z : ℍ[ℚ, a, b]) (hz : nrd z ≠ 0) :
    VN v φ (z ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)) = WithZero.exp (-padicValRat q (nrd z)) := by
  rw [VN, nrd_φ_tmul v φ hφ, one_pow, one_mul, valued_algebraMap, valuation_eq_exp_neg_padicValRat v hvq _ hz]

include hφ in
theorem VN_one_tmul_algebraMap (r : ℚ) : VN v φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ (v.adicCompletion ℚ) r) =
    (v.valuation ℚ r) ^ 2 := by
  rw [VN_one_tmul v φ hφ, valued_algebraMap]

end RamifiedPlace

def Aniso (a b : ℚ) : Prop :=
  ∀ x₀ x₁ x₂ x₃ : ℚ, x₀ ^ 2 - a * x₁ ^ 2 - b * x₂ ^ 2 + a * b * x₃ ^ 2 = 0 → x₀ = 0 ∧ x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0

theorem aniso_of_forall_isUnit (v : HOS) (hdiv : ∀ y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, y ≠ 0 → IsUnit y) :
    Aniso a b := by
  intro x₀ x₁ x₂ x₃ h
  set K := v.adicCompletion ℚ
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  have hK : (x₀ : K) ^ 2 - (a : K) * (x₁ : K) ^ 2 - (b : K) * (x₂ : K) ^ 2 + (a : K) * (b : K) * (x₃ : K) ^ 2 = 0 := by
    have := congrArg (fun r : ℚ => (r : K)) h
    simpa using this
  obtain ⟨h0, h1, h2, h3⟩ :=
    (QuaternionAlgebra.forall_tensorProduct_adicCompletion_isUnit_iff_forall_normForm_eq_zero a b v).mp hdiv
      (x₀ : K) (x₁ : K) (x₂ : K) (x₃ : K) hK
  exact ⟨by exact_mod_cast h0, by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3⟩

theorem ne_zero_left_of_aniso (hA : Aniso a b) : a ≠ 0 := by
  intro ha
  have := (hA 0 1 0 0 (by rw [ha]; ring)).2.1
  exact one_ne_zero this

theorem ne_zero_right_of_aniso (hA : Aniso a b) : b ≠ 0 := by
  intro hb
  have := (hA 0 0 1 0 (by rw [hb]; ring)).2.2.1
  exact one_ne_zero this

theorem nrd_ne_zero_of_ne_zero (hA : Aniso a b) {h : ℍ[ℚ, a, b]} (h0 : h ≠ 0) :
    QuaternionAlgebra.nrd h ≠ 0 := by
  intro hn
  apply h0
  obtain ⟨h₀, h₁, h₂, h₃⟩ := h
  simp only [QuaternionAlgebra.nrd_mk] at hn
  obtain ⟨f0, f1, f2, f3⟩ := hA h₀ h₁ h₂ h₃ hn
  subst f0; subst f1; subst f2; subst f3
  rfl

theorem natCast_tmul_one {S : Type*} [CommRing S] [Algebra ℚ S] (M : ℕ) :
    ((M : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : S)) = ((M : ℕ) : ℍ[ℚ, a, b] ⊗[ℚ] S) := by
  rw [Algebra.TensorProduct.natCast_def]

theorem star_mem_of_isOrder {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) {t : ℍ[ℚ, a, b]}
    (ht : t ∈ Λ) : star t ∈ Λ := by
  obtain ⟨-, tt, htt⟩ := QuaternionAlgebra.IsOrder.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hΛ ht
  have h1 : star t = ((QuaternionAlgebra.trd t : ℚ) : ℍ[ℚ, a, b]) - t := by
    rw [← QuaternionAlgebra.add_star_eq_coe_trd t]; abel
  have h2 : ((tt : ℤ) : ℍ[ℚ, a, b]) = ((tt : ℚ) : ℍ[ℚ, a, b]) := by ext <;> simp
  rw [h1, ← htt, ← h2, ← zsmul_one]
  exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hΛ.one_mem) ht

section Main

open QuaternionAlgebra Rat.HeightOneSpectrum

theorem smul_tmul_one {S : Type*} [CommRing S] [Algebra ℚ S] (r : ℚ) (z : ℍ[ℚ, a, b]) :
    ((r • z) ⊗ₜ[ℚ] (1 : S)) = ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ S r) * (z ⊗ₜ[ℚ] (1 : S)) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← Algebra.smul_def, TensorProduct.smul_tmul]

theorem main (p : ℕ) [hp : Fact p.Prime] (v : HOS) (hpv : (p : 𝓞 ℚ) ∈ v.asIdeal)
    (hdiv : ∀ y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, y ≠ 0 → IsUnit y)
    {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsMaximalOrder Λ)
    {h : ℍ[ℚ, a, b]} (hh : h ∈ Λ) (hv : h = 0 ∨ 2 ≤ padicValRat p (QuaternionAlgebra.nrd h)) :
    ∃ h' ∈ Λ, h = (p : ℤ) • h' := by
  classical
  have hpp : p.Prime := hp.out
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hpp.ne_zero
  have hp1 : 1 < p := hpp.one_lt
  have hO : IsOrder Λ := hΛ.1

  by_cases hh0 : h = 0
  · exact ⟨0, zero_mem _, by rw [hh0, smul_zero]⟩
  have hv2 : 2 ≤ padicValRat p (nrd h) := hv.resolve_left hh0

  have hvdef : v = place p hpp := (eq_of_natCast_mem hpp (q_mem_asIdeal_place p hpp) hpv)
  subst hvdef
  have hA : Aniso a b := aniso_of_forall_isUnit (place p hpp) hdiv
  have hnrdh : nrd h ≠ 0 := nrd_ne_zero_of_ne_zero hA hh0
  have hvq : natGenerator (place p hpp) = p := natGenerator_place p hpp
  set v : HOS := place p hpp with hvdef
  set K := v.adicCompletion ℚ with hK
  obtain ⟨φ, -, hφ⟩ := QuaternionAlgebra.exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
    (R := ℚ) (S := K) (c₁ := a) (c₂ := (0 : ℚ)) (c₃ := b)
    (d₁ := algebraMap ℚ K a) (d₂ := (0 : K)) (d₃ := algebraMap ℚ K b) rfl (map_zero _) rfl AlgEquiv.refl
  have hφ' : ∀ (z : ℍ[ℚ, a, b]) (r : K),
      φ (z ⊗ₜ[ℚ] r) = r • (⟨algebraMap ℚ K z.re, algebraMap ℚ K z.imI, algebraMap ℚ K z.imJ, algebraMap ℚ K z.imK⟩ :
          ℍ[K, algebraMap ℚ K a, algebraMap ℚ K b]) :=
    fun z r => by rw [hφ]; simp only [AlgEquiv.coe_refl, id_eq]
  have hVle : ∀ y : ℍ[ℚ, a, b] ⊗[ℚ] K, y ∈ Submodule.localBox Λ v ↔ VN v φ y ≤ 1 := fun y => by
    rw [hΛ.mem_localBox_iff_nrd_mem_adicCompletionIntegers_of_forall_isUnit v hdiv φ hφ' y,
      HeightOneSpectrum.mem_adicCompletionIntegers]

  set c : ℚ := (p : ℚ)⁻¹ with hc
  have hc0 : c ≠ 0 := inv_ne_zero hp0
  set h' : ℍ[ℚ, a, b] := c • h with hh'
  refine ⟨h', ?_, ?_⟩
  swap
  · rw [hh', ← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast, smul_smul, hc, mul_inv_cancel₀ hp0, one_smul]

  rw [mem_iff_forall_tmul_one_mem_localBox Λ hO h']
  intro w
  rw [hh', smul_tmul_one]
  by_cases hw : w = v
  · subst hw
    rw [hVle, VN_mul, VN_one_tmul_algebraMap v φ hφ', VN_tmul_one v φ hφ' hvq h hnrdh, valuation_eq_exp_neg_padicValRat v hvq c hc0,
      hc, padicValRat.inv, padicValRat.self hp1, pow_two, ← WithZero.exp_add, ← WithZero.exp_add,
      ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  · have hn := natCast_notMem_of_ne hpp hpv hw
    have hcw : algebraMap ℚ (w.adicCompletion ℚ) c ∈ w.adicCompletionIntegers ℚ := by
      rw [hc, map_inv₀, map_natCast]
      exact natCast_inv_mem_integers w hn
    exact one_tmul_mul_mem_localBox Λ w (tmul_one_mem_localBox hh w) hcw

end Main

end Quaternion

end RamPSq

open scoped Quaternion TensorProduct
open IsDedekindDomain NumberField QuaternionAlgebra

theorem solution
    {a b : ℚ} (p : ℕ) [Fact p.Prime] (v : HeightOneSpectrum (𝓞 ℚ)) (hpv : (p : 𝓞 ℚ) ∈ v.asIdeal)
    (hdiv : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x)
    {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsMaximalOrder Λ)
    {h : ℍ[ℚ, a, b]} (hh : h ∈ Λ) (hv : h = 0 ∨ 2 ≤ padicValRat p (QuaternionAlgebra.nrd h)) :
    ∃ h' ∈ Λ, h = (p : ℤ) • h' :=
  RamPSq.main p v hpv hdiv hΛ hh hv

end
end S_QuaternionAlgebra_IsMaximalOrder_exists_eq_natCast_smul_of_two_le_padicValRat_nrd_of_forall_isUnit
end P2MW
export P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_eq_natCast_smul_of_two_le_padicValRat_nrd_of_forall_isUnit (solution)
