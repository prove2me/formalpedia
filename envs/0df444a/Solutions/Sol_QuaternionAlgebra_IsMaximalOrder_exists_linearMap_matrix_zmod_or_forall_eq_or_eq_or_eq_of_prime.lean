-- Prove2me | solution 1 for QuaternionAlgebra.IsMaximalOrder.exists_linearMap_matrix_zmod_or_forall_eq_or_eq_or_eq_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/a26b9b91-4e7e-5228-9059-c0b9c8d5e448

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_mem_padicValRat_nrd_eq_one_of_forall_isUnit
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_eq_natCast_smul_of_two_le_padicValRat_nrd_of_forall_isUnit
import Theorems.Thm_QuaternionAlgebra_forall_tensorProduct_adicCompletion_isUnit_iff_forall_normForm_eq_zero
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_ne_zero_and_ne_zero
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_localBox_iff_generalLinearGroup_conj_mem_adicCompletionIntegers
import Theorems.Thm_QuaternionAlgebra_exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
import Theorems.Thm_QuaternionAlgebra_nonempty_algEquiv_matrix_of_ne_zero_of_not_isUnit
import Theorems.Thm_Submodule_exists_mem_add_one_tmul_pow_mul_of_mem_localBox
import Theorems.Thm_Submodule_mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox
import Theorems.Thm_Submodule_ofFiniteIdele_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_linearMap_matrix_zmod_or_forall_eq_or_eq_or_eq_of_prime
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 3200000

open scoped TensorProduct Quaternion NumberField Pointwise
open IsDedekindDomain NumberField

noncomputable section

namespace P2mKcLocalStructure

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

def place (q : ℕ) (hq : q.Prime) : HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨q, hq⟩

theorem primesEquiv_place (q : ℕ) (hq : q.Prime) : Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) (place q hq) = ⟨q, hq⟩ := by
  simp [place]

theorem natGenerator_place (q : ℕ) (hq : q.Prime) : Rat.HeightOneSpectrum.natGenerator (place q hq) = q :=
  congrArg Subtype.val (primesEquiv_place q hq)

theorem q_mem_asIdeal_place (q : ℕ) (hq : q.Prime) : (q : 𝓞 ℚ) ∈ (place q hq).asIdeal := by
  rw [natCast_mem_asIdeal_iff, natGenerator_place]

end Places

section LocalBox

variable {D : Type*} [Ring D] [Algebra ℚ D]

theorem tmul_one_mem_localBox {Λ : Submodule ℤ D} {z : D} (hz : z ∈ Λ) (w : HOS) :
    z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) ∈ Submodule.localBox Λ w :=
  AddSubgroup.subset_closure ⟨z, hz, 1, (w.adicCompletionIntegers ℚ).one_mem, rfl⟩

variable (Λ : Submodule ℤ D) (v : HeightOneSpectrum (𝓞 ℚ))

theorem tmul_mem_localBox {z : D} (hz : z ∈ Λ) {c : v.adicCompletion ℚ} (hc : c ∈ v.adicCompletionIntegers ℚ) :
    z ⊗ₜ[ℚ] c ∈ Submodule.localBox Λ v :=
  AddSubgroup.subset_closure ⟨z, hz, c, hc, rfl⟩

theorem one_tmul_mul_mem_localBox {x : D ⊗[ℚ] v.adicCompletion ℚ} (hx : x ∈ Submodule.localBox Λ v)
    {c : v.adicCompletion ℚ} (hc : c ∈ v.adicCompletionIntegers ℚ) :
    ((1 : D) ⊗ₜ[ℚ] c) * x ∈ Submodule.localBox Λ v := by
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨z, hz, c', hc', rfl⟩ := hy
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    exact tmul_mem_localBox Λ v hz (mul_mem hc hc')
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => exact (mul_neg _ x).symm ▸ neg_mem hx

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

end Quaternion

section Small

open QuaternionAlgebra

variable {a b : ℚ}

theorem nrd_mul' {K : Type*} [CommRing K] {α β : K} (x y : ℍ[K, α, β]) : nrd (x * y) = nrd x * nrd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x; obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_mul_mk, nrd_mk]; ring

theorem nrd_zsmul (r : ℤ) (y : ℍ[ℚ, a, b]) : nrd (r • y) = (r : ℚ) ^ 2 * nrd y := by
  rw [← Int.cast_smul_eq_zsmul ℚ, show (r : ℚ) • y = ((r : ℚ) : ℍ[ℚ, a, b]) * y from (QuaternionAlgebra.coe_mul_eq_smul _ _).symm,
    nrd_mul', nrd_coe]

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

theorem nrd_ne_zero_of_ne_zero (hA : Aniso a b) {h : ℍ[ℚ, a, b]} (h0 : h ≠ 0) :
    QuaternionAlgebra.nrd h ≠ 0 := by
  intro hn
  apply h0
  obtain ⟨h₀, h₁, h₂, h₃⟩ := h
  simp only [QuaternionAlgebra.nrd_mk] at hn
  obtain ⟨f0, f1, f2, f3⟩ := hA h₀ h₁ h₂ h₃ hn
  subst f0; subst f1; subst f2; subst f3
  rfl

theorem star_mem_of_isOrder {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) {t : ℍ[ℚ, a, b]}
    (ht : t ∈ Λ) : star t ∈ Λ := by
  obtain ⟨-, tt, htt⟩ := QuaternionAlgebra.IsOrder.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hΛ ht
  have h1 : star t = ((QuaternionAlgebra.trd t : ℚ) : ℍ[ℚ, a, b]) - t := by
    rw [← QuaternionAlgebra.add_star_eq_coe_trd t]; abel
  have h2 : ((tt : ℤ) : ℍ[ℚ, a, b]) = ((tt : ℚ) : ℍ[ℚ, a, b]) := by ext <;> simp
  rw [h1, ← htt, ← h2, ← zsmul_one]
  exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hΛ.one_mem) ht

theorem exists_int_nrd {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) {x : ℍ[ℚ, a, b]}
    (hx : x ∈ Λ) : ∃ N : ℤ, nrd x = N := by
  obtain ⟨⟨N, hN⟩, -⟩ := QuaternionAlgebra.IsOrder.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hΛ hx
  exact ⟨N, hN.symm⟩

theorem exists_eq_mul_iff_dvd (r : ℕ) (N : ℤ) : (∃ n : ℤ, (N : ℚ) = (r : ℚ) * n) ↔ (r : ℤ) ∣ N := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, by exact_mod_cast hn⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n, by push_cast; ring⟩

theorem dvd_iff_one_le_padicValRat (r : ℕ) [hr : Fact r.Prime] {N : ℤ} (hN : N ≠ 0) :
    (r : ℤ) ∣ N ↔ 1 ≤ padicValRat r (N : ℚ) := by
  rw [padicValRat.of_int]
  have := padicValInt_dvd_iff (p := r) 1 N
  rw [pow_one] at this
  rw [this]
  constructor
  · rintro (h | h)
    · exact absurd h hN
    · exact_mod_cast h
  · intro h; right; exact_mod_cast h

theorem sq_dvd_iff_two_le_padicValRat (r : ℕ) [hr : Fact r.Prime] {N : ℤ} (hN : N ≠ 0) :
    (r : ℤ) ^ 2 ∣ N ↔ 2 ≤ padicValRat r (N : ℚ) := by
  rw [padicValRat.of_int]
  have := padicValInt_dvd_iff (p := r) 2 N
  rw [this]
  constructor
  · rintro (h | h)
    · exact absurd h hN
    · exact_mod_cast h
  · intro h; right; exact_mod_cast h

theorem padicValRat_intCast_nonneg (r : ℕ) (N : ℤ) : 0 ≤ padicValRat r (N : ℚ) := by
  rw [padicValRat.of_int]; exact_mod_cast Nat.zero_le _

theorem exists_bezout_of_not_dvd (r : ℕ) (hr : r.Prime) {N : ℤ} (hN : ¬ (r : ℤ) ∣ N) :
    ∃ u w : ℤ, u * r + w * N = 1 := by
  have hcop : IsCoprime (r : ℤ) N := (Nat.prime_iff_prime_int.mp hr).irreducible.coprime_iff_not_dvd.mpr hN
  obtain ⟨u, w, h⟩ := hcop
  exact ⟨u, w, h⟩

end Small

section Lattices

open QuaternionAlgebra

variable {a b : ℚ}

def P (Λ : Submodule ℤ ℍ[ℚ, a, b]) (r : ℕ) : Set ℍ[ℚ, a, b] := {x | x ∈ Λ ∧ ∃ n : ℤ, nrd x = (r : ℚ) * n}

theorem mem_P_iff (Λ : Submodule ℤ ℍ[ℚ, a, b]) (r : ℕ) (x : ℍ[ℚ, a, b]) :
    x ∈ P Λ r ↔ x ∈ Λ ∧ ∃ n : ℤ, nrd x = (r : ℚ) * n := Iff.rfl

theorem ratCast_smul_eq_zsmul (r : ℕ) (y : ℍ[ℚ, a, b]) : (r : ℚ) • y = (r : ℤ) • y := by
  rw [← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast]

theorem span_smul_eq_map (Λ : Submodule ℤ ℍ[ℚ, a, b]) (r : ℕ) :
    Submodule.span ℤ ((r : ℚ) • (Λ : Set ℍ[ℚ, a, b])) = Λ.map ((r : ℤ) • (LinearMap.id : ℍ[ℚ, a, b] →ₗ[ℤ] ℍ[ℚ, a, b])) := by
  have h : ((r : ℚ) • (Λ : Set ℍ[ℚ, a, b])) = (Λ.map ((r : ℤ) • (LinearMap.id : ℍ[ℚ, a, b] →ₗ[ℤ] ℍ[ℚ, a, b])) : Set ℍ[ℚ, a, b]) := by
    ext x
    simp only [Set.mem_smul_set, Submodule.map_coe, Set.mem_image, LinearMap.smul_apply, LinearMap.id_coe, id_eq,
      SetLike.mem_coe]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, (ratCast_smul_eq_zsmul r y).symm⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, ratCast_smul_eq_zsmul r y⟩
  rw [h, Submodule.span_eq]

theorem mem_span_smul_iff (Λ : Submodule ℤ ℍ[ℚ, a, b]) (r : ℕ) (x : ℍ[ℚ, a, b]) :
    x ∈ Submodule.span ℤ ((r : ℚ) • (Λ : Set ℍ[ℚ, a, b])) ↔ ∃ y ∈ Λ, x = (r : ℤ) • y := by
  rw [span_smul_eq_map, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩

theorem zsmul_mem_span_smul (Λ : Submodule ℤ ℍ[ℚ, a, b]) (r : ℕ) {y : ℍ[ℚ, a, b]} (hy : y ∈ Λ) :
    (r : ℤ) • y ∈ Submodule.span ℤ ((r : ℚ) • (Λ : Set ℍ[ℚ, a, b])) :=
  (mem_span_smul_iff Λ r _).mpr ⟨y, hy, rfl⟩

variable {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hO : IsOrder Λ) (r : ℕ) [hr : Fact r.Prime]
include hO

theorem two_le_padicValRat_of_mem_span_smul (hA : Aniso a b) {x : ℍ[ℚ, a, b]}
    (hx : x ∈ Submodule.span ℤ ((r : ℚ) • (Λ : Set ℍ[ℚ, a, b]))) (hx0 : x ≠ 0) : 2 ≤ padicValRat r (nrd x) := by
  obtain ⟨y, hy, rfl⟩ := (mem_span_smul_iff Λ r x).mp hx
  have hy0 : y ≠ 0 := by rintro rfl; exact hx0 (smul_zero _)
  have hny : nrd y ≠ 0 := nrd_ne_zero_of_ne_zero hA hy0
  obtain ⟨M, hM⟩ := exists_int_nrd hO hy
  have hr0 : ((r : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hr.out.ne_zero
  rw [nrd_zsmul, padicValRat.mul (pow_ne_zero _ hr0) hny, padicValRat.pow, Int.cast_natCast, padicValRat.self hr.out.one_lt,
    hM]
  have := padicValRat_intCast_nonneg r M
  omega

variable (hA : Aniso a b) (hP2 : ∀ x ∈ Λ, (x = 0 ∨ 2 ≤ padicValRat r (nrd x)) → ∃ x' ∈ Λ, x = (r : ℤ) • x')
include hA hP2

theorem eq_top_of_exists_not_mem_P (J : Submodule ℤ ℍ[ℚ, a, b]) (hJ : ∀ x ∈ Λ, ∀ y ∈ J, x * y ∈ J)
    (hrJ : Submodule.span ℤ ((r : ℚ) • (Λ : Set ℍ[ℚ, a, b])) ≤ J) (hJΛ : J ≤ Λ)
    {x : ℍ[ℚ, a, b]} (hxJ : x ∈ J) (hxP : x ∉ P Λ r) : J = Λ := by
  have hxΛ : x ∈ Λ := hJΛ hxJ
  obtain ⟨N, hN⟩ := exists_int_nrd hO hxΛ
  have hndvd : ¬ (r : ℤ) ∣ N := by
    intro hd
    exact hxP ⟨hxΛ, (exists_eq_mul_iff_dvd r N).mpr hd |>.imp fun n hn => by rw [hN, hn]⟩
  obtain ⟨u, w, huw⟩ := exists_bezout_of_not_dvd r hr.out hndvd

  have hNJ : ((N : ℚ) : ℍ[ℚ, a, b]) ∈ J := by
    have := hJ (star x) (star_mem_of_isOrder hO hxΛ) x hxJ
    rwa [QuaternionAlgebra.star_mul_eq_coe_nrd, hN] at this
  have hrJ' : ((r : ℤ) • (1 : ℍ[ℚ, a, b])) ∈ J := hrJ (zsmul_mem_span_smul Λ r hO.one_mem)

  have h1 : (1 : ℍ[ℚ, a, b]) = u • ((r : ℤ) • (1 : ℍ[ℚ, a, b])) + w • ((N : ℚ) : ℍ[ℚ, a, b]) := by
    have e1 : ((N : ℚ) : ℍ[ℚ, a, b]) = (N : ℤ) • (1 : ℍ[ℚ, a, b]) := by
      rw [zsmul_one]; ext <;> simp
    rw [e1, smul_smul, smul_smul, ← add_smul, huw, one_smul]
  have h1J : (1 : ℍ[ℚ, a, b]) ∈ J := by
    rw [h1]; exact J.add_mem (J.smul_mem _ hrJ') (J.smul_mem _ hNJ)
  refine le_antisymm hJΛ fun y hy => ?_
  have := hJ y hy 1 h1J
  rwa [mul_one] at this

theorem P_subset_of_forall_mem_P (J : Submodule ℤ ℍ[ℚ, a, b]) (hJ : ∀ x ∈ Λ, ∀ y ∈ J, x * y ∈ J)
    (hrJ : Submodule.span ℤ ((r : ℚ) • (Λ : Set ℍ[ℚ, a, b])) ≤ J) (hJΛ : J ≤ Λ)
    {x : ℍ[ℚ, a, b]} (hxJ : x ∈ J) (hxr : x ∉ Submodule.span ℤ ((r : ℚ) • (Λ : Set ℍ[ℚ, a, b])))
    (hxP : x ∈ P Λ r) : P Λ r ⊆ (J : Set ℍ[ℚ, a, b]) := by
  have hrp : r.Prime := hr.out
  have hr0q : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hrp.ne_zero
  have hxΛ : x ∈ Λ := hJΛ hxJ
  have hx0 : x ≠ 0 := by rintro rfl; exact hxr (zero_mem _)
  have hnx : nrd x ≠ 0 := nrd_ne_zero_of_ne_zero hA hx0

  obtain ⟨-, m, hm⟩ := hxP
  have hm0 : m ≠ 0 := by rintro rfl; apply hnx; rw [hm]; simp
  have hlt : padicValRat r (nrd x) < 2 := by
    by_contra hge
    push Not at hge
    obtain ⟨x', hx', hxx'⟩ := hP2 x hxΛ (Or.inr hge)
    exact hxr ((mem_span_smul_iff Λ r x).mpr ⟨x', hx', hxx'⟩)
  have hvm : ¬ (r : ℤ) ∣ m := by
    intro hd
    have h1 := (dvd_iff_one_le_padicValRat r hm0).mp hd
    have : padicValRat r (nrd x) = 1 + padicValRat r (m : ℚ) := by
      rw [hm, padicValRat.mul hr0q (Int.cast_ne_zero.mpr hm0), padicValRat.self hrp.one_lt]
    omega
  obtain ⟨u, w, huw⟩ := exists_bezout_of_not_dvd r hrp hvm

  intro y hy
  obtain ⟨hyΛ, n', hn'⟩ := hy

  set z : ℍ[ℚ, a, b] := y * star x with hz
  have hzΛ : z ∈ Λ := hO.mul_mem hyΛ (star_mem_of_isOrder hO hxΛ)
  have hnz : nrd z = ((r : ℚ) * r) * (n' * m) := by
    rw [hz, nrd_mul', nrd_star, hn', hm]; ring
  have hz2 : z = 0 ∨ 2 ≤ padicValRat r (nrd z) := by
    by_cases hz0 : z = 0
    · exact Or.inl hz0
    · right
      have hnz0 : nrd z ≠ 0 := nrd_ne_zero_of_ne_zero hA hz0
      have hnm0 : ((n' : ℚ) * m) ≠ 0 := by
        intro h0; apply hnz0; rw [hnz, h0, mul_zero]
      rw [hnz, padicValRat.mul (mul_ne_zero hr0q hr0q) hnm0, padicValRat.mul hr0q hr0q, padicValRat.self hrp.one_lt,
        show ((n' : ℚ) * m) = ((n' * m : ℤ) : ℚ) by push_cast; ring]
      have := padicValRat_intCast_nonneg r (n' * m)
      omega
  obtain ⟨z', hz'Λ, hzz'⟩ := hP2 z hzΛ hz2

  have hz'x : z' * x ∈ J := hJ z' hz'Λ x hxJ
  have key : ((r : ℤ) : ℚ) • ((m : ℚ) • y) = ((r : ℤ) : ℚ) • (z' * x) := by
    have e1 : z * x = ((r : ℚ) * m) • y := by
      rw [hz, mul_assoc, QuaternionAlgebra.star_mul_eq_coe_nrd, hm, QuaternionAlgebra.mul_coe_eq_smul]
    have e2 : z * x = ((r : ℤ) : ℚ) • (z' * x) := by
      rw [hzz', ← Int.cast_smul_eq_zsmul ℚ, smul_mul_assoc]
    rw [← e2, e1, smul_smul, Int.cast_natCast]
  have hmy : (m : ℤ) • y ∈ J := by
    have hr0' : ((r : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hrp.ne_zero
    have := smul_right_injective ℍ[ℚ, a, b] hr0' key
    rw [← Int.cast_smul_eq_zsmul ℚ, this]
    exact hz'x
  have hry : (r : ℤ) • y ∈ J := hrJ (zsmul_mem_span_smul Λ r hyΛ)
  have hy1 : y = w • ((m : ℤ) • y) + u • ((r : ℤ) • y) := by
    rw [smul_smul, smul_smul, ← add_smul, show w * m + u * r = 1 by linear_combination huw, one_smul]
  rw [SetLike.mem_coe, hy1]
  exact J.add_mem (J.smul_mem _ hmy) (J.smul_mem _ hry)

theorem trichotomy (J : Submodule ℤ ℍ[ℚ, a, b]) (hJ : ∀ x ∈ Λ, ∀ y ∈ J, x * y ∈ J)
    (hrJ : Submodule.span ℤ ((r : ℚ) • (Λ : Set ℍ[ℚ, a, b])) ≤ J) (hJΛ : J ≤ Λ) :
    J = Submodule.span ℤ ((r : ℚ) • (Λ : Set ℍ[ℚ, a, b])) ∨ (J : Set ℍ[ℚ, a, b]) = P Λ r ∨ J = Λ := by
  classical
  by_cases hA' : ∃ x ∈ J, x ∉ P Λ r
  · obtain ⟨x, hxJ, hxP⟩ := hA'
    exact Or.inr (Or.inr (eq_top_of_exists_not_mem_P hO r hA hP2 J hJ hrJ hJΛ hxJ hxP))
  · push Not at hA'
    by_cases hB' : ∃ x ∈ J, x ∉ Submodule.span ℤ ((r : ℚ) • (Λ : Set ℍ[ℚ, a, b]))
    · obtain ⟨x, hxJ, hxr⟩ := hB'
      refine Or.inr (Or.inl (Set.Subset.antisymm (fun y hy => hA' y hy) ?_))
      exact P_subset_of_forall_mem_P hO r hA hP2 J hJ hrJ hJΛ hxJ hxr (hA' x hxJ)
    · push Not at hB'
      exact Or.inl (le_antisymm (fun x hx => hB' x hx) hrJ)

end Lattices

section Splitting

open QuaternionAlgebra Rat.HeightOneSpectrum

variable {a b : ℚ}

theorem exists_split (ha : a ≠ 0) (hb : b ≠ 0) (v : HOS)
    (hnd : ¬ ∀ y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, y ≠ 0 → IsUnit y) :
    ∃ φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ),
      ∀ r : v.adicCompletion ℚ, φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := by
  set K := v.adicCompletion ℚ with hK
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  haveI : NeZero (2 : K) := ⟨two_ne_zero⟩

  obtain ⟨φ₀, hφ₀1, hφ₀⟩ := QuaternionAlgebra.exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
    (R := ℚ) (S := K) (c₁ := a) (c₂ := (0 : ℚ)) (c₃ := b)
    (d₁ := algebraMap ℚ K a) (d₂ := (0 : K)) (d₃ := algebraMap ℚ K b) rfl (map_zero _) rfl AlgEquiv.refl

  push Not at hnd
  obtain ⟨y, hy0, hyu⟩ := hnd
  have hy0' : φ₀ y ≠ 0 := fun h => hy0 (by simpa using congrArg φ₀.symm h)
  have hyu' : ¬ IsUnit (φ₀ y) := fun h => hyu (by simpa using h.map φ₀.symm)
  have haK : algebraMap ℚ K a ≠ 0 := by rwa [Ne, map_eq_zero_iff _ (algebraMap ℚ K).injective]
  have hbK : algebraMap ℚ K b ≠ 0 := by rwa [Ne, map_eq_zero_iff _ (algebraMap ℚ K).injective]
  obtain ⟨ψ⟩ := QuaternionAlgebra.nonempty_algEquiv_matrix_of_ne_zero_of_not_isUnit haK hbK (φ₀ y) hy0' hyu'
  obtain ⟨φ, hφ1, -⟩ := QuaternionAlgebra.exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
    (R := ℚ) (S := K) (c₁ := a) (c₂ := (0 : ℚ)) (c₃ := b)
    (d₁ := algebraMap ℚ K a) (d₂ := (0 : K)) (d₃ := algebraMap ℚ K b) rfl (map_zero _) rfl ψ
  exact ⟨φ, hφ1⟩

def conjEquiv {K : Type*} [CommRing K] (h : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K ≃+* Matrix (Fin 2) (Fin 2) K where
  toFun A := ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * A * (h : Matrix (Fin 2) (Fin 2) K)
  invFun A := (h : Matrix (Fin 2) (Fin 2) K) * A * ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
  left_inv A := by
    show (h : Matrix (Fin 2) (Fin 2) K) * (((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * A *
      (h : Matrix (Fin 2) (Fin 2) K)) * ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = A
    rw [← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one]
  right_inv A := by
    show ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * ((h : Matrix (Fin 2) (Fin 2) K) * A *
      ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) * (h : Matrix (Fin 2) (Fin 2) K) = A
    rw [← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, mul_assoc, Units.inv_mul, mul_one]
  map_mul' A B := by
    show ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (A * B) * (h : Matrix (Fin 2) (Fin 2) K) =
      ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * A * (h : Matrix (Fin 2) (Fin 2) K) *
        (((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * B * (h : Matrix (Fin 2) (Fin 2) K))
    rw [show ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * A * (h : Matrix (Fin 2) (Fin 2) K) *
        (((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * B * (h : Matrix (Fin 2) (Fin 2) K)) =
      ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * A * ((h : Matrix (Fin 2) (Fin 2) K) *
        ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) * B * (h : Matrix (Fin 2) (Fin 2) K) by
          simp only [mul_assoc]]
    rw [Units.mul_inv, mul_one]
    simp only [mul_assoc]
  map_add' A B := by
    show ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (A + B) * (h : Matrix (Fin 2) (Fin 2) K) =
      ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * A * (h : Matrix (Fin 2) (Fin 2) K) +
        ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * B * (h : Matrix (Fin 2) (Fin 2) K)
    rw [mul_add, add_mul]

theorem conjEquiv_apply {K : Type*} [CommRing K] (h : GL (Fin 2) K) (A : Matrix (Fin 2) (Fin 2) K) :
    conjEquiv h A = ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * A * (h : Matrix (Fin 2) (Fin 2) K) := rfl

theorem conjEquiv_smul_one {K : Type*} [CommRing K] (h : GL (Fin 2) K) (r : K) :
    conjEquiv h (r • (1 : Matrix (Fin 2) (Fin 2) K)) = r • (1 : Matrix (Fin 2) (Fin 2) K) := by
  rw [conjEquiv_apply, Matrix.mul_smul, mul_one, Matrix.smul_mul, Units.inv_mul]

theorem exists_split_localBox_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsMaximalOrder Λ) (ha : a ≠ 0) (hb : b ≠ 0) (v : HOS)
    (hnd : ¬ ∀ y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, y ≠ 0 → IsUnit y) :
    ∃ φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ),
      (∀ r : v.adicCompletion ℚ, φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) ∧
      ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ,
        x ∈ Submodule.localBox Λ v ↔ ∀ i j, φ x i j ∈ v.adicCompletionIntegers ℚ := by
  obtain ⟨φ, hφ1⟩ := exists_split ha hb v hnd
  obtain ⟨h, hh⟩ := hΛ.exists_localBox_iff_generalLinearGroup_conj_mem_adicCompletionIntegers v φ hφ1
  refine ⟨φ.trans (conjEquiv h), fun r => ?_, fun x => ?_⟩
  · rw [RingEquiv.trans_apply, hφ1, conjEquiv_smul_one]
  · rw [hh x]
    simp only [RingEquiv.trans_apply, conjEquiv_apply]

end Splitting

section Reduction

open QuaternionAlgebra Rat.HeightOneSpectrum

variable {a b : ℚ} (v : HOS)

abbrev pv : Nat.Primes := primesEquiv (R := 𝓞 ℚ) v

scoped instance factPrime_pv : Fact (pv v : ℕ).Prime := ⟨(pv v).2⟩

theorem natGenerator_eq_pv : natGenerator v = (pv v : ℕ) := rfl

theorem pv_mem_asIdeal : ((pv v : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
  rw [natCast_mem_asIdeal_iff, natGenerator_eq_pv]

def eR : v.adicCompletionIntegers ℚ ≃+* ℤ_[(pv v : ℕ)] :=
  (adicCompletionIntegers.padicIntEquiv (R := 𝓞 ℚ) v).toAlgEquiv.toRingEquiv

def res : v.adicCompletionIntegers ℚ →+* ZMod (pv v : ℕ) :=
  (PadicInt.toZMod (p := (pv v : ℕ))).comp (eR v).toRingHom

theorem res_apply (t : v.adicCompletionIntegers ℚ) : res v t = PadicInt.toZMod (eR v t) := rfl

theorem res_surjective : Function.Surjective (res v) := by
  intro c
  refine ⟨(c.val : v.adicCompletionIntegers ℚ), ?_⟩
  rw [res_apply, map_natCast, map_natCast, ZMod.natCast_zmod_val]

theorem res_natCast_pv : res v ((pv v : ℕ) : v.adicCompletionIntegers ℚ) = 0 := by
  rw [res_apply, map_natCast, map_natCast, ZMod.natCast_self]

theorem exists_eq_mul_of_res_eq_zero {t : v.adicCompletionIntegers ℚ} (ht : res v t = 0) :
    ∃ t' : v.adicCompletionIntegers ℚ, t = ((pv v : ℕ) : v.adicCompletionIntegers ℚ) * t' := by
  have h1 : (eR v t : ℤ_[(pv v : ℕ)]) ∈ RingHom.ker (PadicInt.toZMod (p := (pv v : ℕ))) := ht
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h1
  obtain ⟨c, hc⟩ := h1
  refine ⟨(eR v).symm c, ?_⟩
  apply (eR v).injective
  rw [map_mul, map_natCast, RingEquiv.apply_symm_apply]
  exact hc

variable (φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
  (hφ1 : ∀ r : v.adicCompletion ℚ, φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))
  {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hO : IsOrder Λ)
  (hΛv : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ,
    x ∈ Submodule.localBox Λ v ↔ ∀ i j, φ x i j ∈ v.adicCompletionIntegers ℚ)

def liftM (X : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) (hX : ∀ i j, X i j ∈ v.adicCompletionIntegers ℚ) :
    Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers ℚ) :=
  fun i j => ⟨X i j, hX i j⟩

theorem liftM_mapMatrix (X : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) (hX : ∀ i j, X i j ∈ v.adicCompletionIntegers ℚ) :
    ((v.adicCompletionIntegers ℚ).subtype).mapMatrix (liftM v X hX) = X := by
  ext i j; rfl

theorem mapMatrix_val_injective :
    Function.Injective (((v.adicCompletionIntegers ℚ).subtype).mapMatrix :
      Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers ℚ) → Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := by
  intro A B h
  refine Matrix.ext fun i j => Subtype.ext ?_
  have := congrFun (congrFun h i) j
  exact this

theorem liftM_congr {X Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)} (h : X = Y)
    (hX : ∀ i j, X i j ∈ v.adicCompletionIntegers ℚ) (hY : ∀ i j, Y i j ∈ v.adicCompletionIntegers ℚ) :
    liftM v X hX = liftM v Y hY := by
  subst h; rfl

theorem liftM_add (X Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) (hX : ∀ i j, X i j ∈ v.adicCompletionIntegers ℚ)
    (hY : ∀ i j, Y i j ∈ v.adicCompletionIntegers ℚ) (hXY : ∀ i j, (X + Y) i j ∈ v.adicCompletionIntegers ℚ) :
    liftM v (X + Y) hXY = liftM v X hX + liftM v Y hY := by
  ext i j; rfl

theorem liftM_mul (X Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) (hX : ∀ i j, X i j ∈ v.adicCompletionIntegers ℚ)
    (hY : ∀ i j, Y i j ∈ v.adicCompletionIntegers ℚ) (hXY : ∀ i j, (X * Y) i j ∈ v.adicCompletionIntegers ℚ) :
    liftM v (X * Y) hXY = liftM v X hX * liftM v Y hY := by
  apply mapMatrix_val_injective v
  rw [map_mul, liftM_mapMatrix, liftM_mapMatrix, liftM_mapMatrix]

theorem liftM_one (h1 : ∀ i j, (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈ v.adicCompletionIntegers ℚ) :
    liftM v 1 h1 = 1 := by
  apply mapMatrix_val_injective v
  rw [liftM_mapMatrix, map_one]

theorem liftM_zero (h0 : ∀ i j, (0 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈ v.adicCompletionIntegers ℚ) :
    liftM v 0 h0 = 0 := by
  apply mapMatrix_val_injective v
  rw [liftM_mapMatrix, map_zero]

include hΛv in
theorem mem_int (z : ↥Λ) (i j : Fin 2) :
    φ ((z : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)) i j ∈ v.adicCompletionIntegers ℚ :=
  (hΛv _).mp (tmul_one_mem_localBox (Λ := Λ) z.2 v) i j

def ρ₀ : ↥Λ →+ Matrix (Fin 2) (Fin 2) (ZMod (pv v : ℕ)) where
  toFun z := (res v).mapMatrix (liftM v (φ ((z : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ))) (mem_int v φ hΛv z))
  map_zero' := by
    have h0 : ∀ i j, (0 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈ v.adicCompletionIntegers ℚ :=
      fun i j => zero_mem _
    have e : φ (((0 : ↥Λ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)) = 0 := by
      rw [ZeroMemClass.coe_zero, TensorProduct.zero_tmul, map_zero]
    rw [liftM_congr v e _ h0, liftM_zero, map_zero]
  map_add' z z' := by
    have e : φ (((z + z' : ↥Λ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)) =
        φ ((z : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)) + φ ((z' : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)) := by
      rw [Submodule.coe_add, TensorProduct.add_tmul, map_add]
    have hs : ∀ i j, (φ ((z : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)) +
        φ ((z' : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ))) i j ∈ v.adicCompletionIntegers ℚ :=
      fun i j => add_mem (mem_int v φ hΛv z i j) (mem_int v φ hΛv z' i j)
    rw [liftM_congr v e _ hs, liftM_add v _ _ (mem_int v φ hΛv z) (mem_int v φ hΛv z') hs, map_add]

theorem ρ₀_apply (z : ↥Λ) :
    ρ₀ v φ hΛv z = (res v).mapMatrix (liftM v (φ ((z : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ))) (mem_int v φ hΛv z)) := rfl

theorem ρ₀_apply_apply (z : ↥Λ) (i j : Fin 2) :
    ρ₀ v φ hΛv z i j = res v (liftM v (φ ((z : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ))) (mem_int v φ hΛv z) i j) := rfl

include hO in
theorem ρ₀_mul {z z' : ℍ[ℚ, a, b]} (hz : z ∈ Λ) (hz' : z' ∈ Λ) (hzz' : z * z' ∈ Λ) :
    ρ₀ v φ hΛv ⟨z * z', hzz'⟩ = ρ₀ v φ hΛv ⟨z, hz⟩ * ρ₀ v φ hΛv ⟨z', hz'⟩ := by
  rw [ρ₀_apply, ρ₀_apply, ρ₀_apply, ← map_mul]
  congr 1
  have e : φ ((z * z') ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)) =
      φ (z ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)) * φ (z' ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)) := by
    rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  have hs : ∀ i j, (φ (z ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)) * φ (z' ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ))) i j ∈
      v.adicCompletionIntegers ℚ := by
    intro i j; rw [← e]; exact mem_int v φ hΛv ⟨z * z', hzz'⟩ i j
  exact (liftM_congr v e _ hs).trans
    (liftM_mul v _ _ (mem_int v φ hΛv ⟨z, hz⟩) (mem_int v φ hΛv ⟨z', hz'⟩) hs)

include hφ1 in
theorem ρ₀_one (h1Λ : (1 : ℍ[ℚ, a, b]) ∈ Λ) : ρ₀ v φ hΛv ⟨1, h1Λ⟩ = 1 := by
  rw [ρ₀_apply]
  have e : φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)) = 1 := by rw [hφ1, one_smul]
  have h1 : ∀ i j, (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈ v.adicCompletionIntegers ℚ := by
    intro i j; rw [← e]; exact mem_int v φ hΛv ⟨1, h1Λ⟩ i j
  rw [liftM_congr v e _ h1, liftM_one, map_one]

theorem smul_tmul_one {S : Type*} [CommRing S] [Algebra ℚ S] (r : ℚ) (z : ℍ[ℚ, a, b]) :
    ((r • z) ⊗ₜ[ℚ] (1 : S)) = ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ S r) * (z ⊗ₜ[ℚ] (1 : S)) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← Algebra.smul_def, TensorProduct.smul_tmul]

include hO hφ1 in

theorem exists_eq_smul_of_ρ₀_eq_zero (z : ↥Λ) (hz : ρ₀ v φ hΛv z = 0) :
    ∃ y ∈ Λ, (z : ℍ[ℚ, a, b]) = ((pv v : ℕ) : ℚ) • y := by
  set ℓ : ℕ := (pv v : ℕ) with hℓ
  have hℓp : ℓ.Prime := (pv v).2
  set K := v.adicCompletion ℚ
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  have hℓK : (ℓ : K) ≠ 0 := Nat.cast_ne_zero.mpr hℓp.ne_zero

  have hent : ∀ i j, ∃ c : v.adicCompletionIntegers ℚ,
      φ ((z : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : K)) i j = (ℓ : K) * (c : K) := by
    intro i j
    have h0 : res v (liftM v (φ ((z : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : K))) (mem_int v φ hΛv z) i j) = 0 := by
      rw [← ρ₀_apply_apply v φ hΛv, hz]; rfl
    obtain ⟨c, hc⟩ := exists_eq_mul_of_res_eq_zero v h0
    refine ⟨c, ?_⟩
    have := congrArg ((v.adicCompletionIntegers ℚ).subtype) hc
    rw [map_mul, map_natCast] at this
    exact this
  choose c hc using hent

  set y : ℍ[ℚ, a, b] := ((ℓ : ℚ)⁻¹) • (z : ℍ[ℚ, a, b]) with hy
  refine ⟨y, ?_, ?_⟩
  swap
  · rw [hy, smul_smul, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hℓp.ne_zero), one_smul]
  rw [mem_iff_forall_tmul_one_mem_localBox Λ hO y]
  intro w
  rw [hy, smul_tmul_one]
  by_cases hw : w = v
  · subst hw
    rw [hΛv]
    intro i j
    rw [map_mul, hφ1, Matrix.smul_mul, one_mul, Matrix.smul_apply, hc i j, map_inv₀, map_natCast, smul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ hℓK, one_mul]
    exact (c i j).2
  · have hn : ((ℓ : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := natCast_notMem_of_ne hℓp (pv_mem_asIdeal v) hw
    have hcw : algebraMap ℚ (w.adicCompletion ℚ) ((ℓ : ℚ)⁻¹) ∈ w.adicCompletionIntegers ℚ := by
      rw [map_inv₀, map_natCast]
      exact natCast_inv_mem_integers w hn
    exact one_tmul_mul_mem_localBox Λ w (tmul_one_mem_localBox (Λ := Λ) z.2 w) hcw

include hO hφ1 in

theorem ρ₀_surjective : Function.Surjective (ρ₀ v φ hΛv) := by
  set ℓ : ℕ := (pv v : ℕ) with hℓ
  have hℓp : ℓ.Prime := (pv v).2
  set K := v.adicCompletion ℚ
  intro T

  choose c hc using fun i j => res_surjective v (T i j)
  set C : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers ℚ) := fun i j => c i j with hC
  set Y : Matrix (Fin 2) (Fin 2) K := ((v.adicCompletionIntegers ℚ).subtype).mapMatrix C with hY
  set y : ℍ[ℚ, a, b] ⊗[ℚ] K := φ.symm Y with hy
  have hyv : y ∈ Submodule.localBox Λ v := by
    rw [hΛv]
    intro i j
    rw [hy, RingEquiv.apply_symm_apply, hY, RingHom.mapMatrix_apply, Matrix.map_apply]
    exact (C i j).2

  obtain ⟨z, hz, E, hE, hyz⟩ := Submodule.exists_mem_add_one_tmul_pow_mul_of_mem_localBox Λ hO.fg hO.spanTop ℓ hℓp v
    (pv_mem_asIdeal v) 1 hyv
  refine ⟨⟨z, hz⟩, ?_⟩
  have hEint : ∀ i j, φ E i j ∈ v.adicCompletionIntegers ℚ := (hΛv E).mp hE

  have hφz : φ (z ⊗ₜ[ℚ] (1 : K)) = Y - (ℓ : K) • φ E := by
    have := congrArg φ hyz
    rw [hy, RingEquiv.apply_symm_apply, map_add, map_mul, pow_one, hφ1, Matrix.smul_mul, one_mul] at this
    rw [this]; abel
  ext i j
  rw [ρ₀_apply_apply]
  have hentry : liftM v (φ (z ⊗ₜ[ℚ] (1 : K))) (mem_int v φ hΛv ⟨z, hz⟩) i j =
      C i j - ((ℓ : ℕ) : v.adicCompletionIntegers ℚ) * ⟨φ E i j, hEint i j⟩ := by
    apply Subtype.ext
    show φ (z ⊗ₜ[ℚ] (1 : K)) i j = _
    rw [hφz, Matrix.sub_apply, Matrix.smul_apply, hY, RingHom.mapMatrix_apply, Matrix.map_apply, smul_eq_mul]
    rfl
  rw [hentry, map_sub, map_mul, res_natCast_pv, zero_mul, sub_zero]
  exact hc i j

end Reduction

section SplitCase

open QuaternionAlgebra Rat.HeightOneSpectrum

variable {a b : ℚ}

theorem split_case (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (ℓ : ℕ) [hℓ : Fact ℓ.Prime]
    (hnd : ¬ ∀ y : ℍ[ℚ, a, b] ⊗[ℚ] (place ℓ hℓ.out).adicCompletion ℚ, y ≠ 0 → IsUnit y) :
    ∃ φ : ↥Λ →ₗ[ℤ] Matrix (Fin 2) (Fin 2) (ZMod ℓ),
      (∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, φ ⟨1, h⟩ = 1) ∧
      (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
          φ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = φ x * φ y) ∧
      Function.Surjective φ ∧
      (∀ x : ↥Λ, φ x = 0 ↔ ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (ℓ : ℚ) • (y : ℍ[ℚ, a, b])) := by
  have hO : IsOrder Λ := hΛ.1
  obtain ⟨ha, hb⟩ := QuaternionAlgebra.IsMaximalOrder.ne_zero_and_ne_zero hΛ
  set v : HOS := place ℓ hℓ.out with hv
  obtain ⟨ψ, hψ1, hΛv⟩ := exists_split_localBox_iff hΛ ha hb v hnd

  have hpv : (pv v : ℕ) = ℓ := natGenerator_place ℓ hℓ.out

  set e : Matrix (Fin 2) (Fin 2) (ZMod (pv v : ℕ)) ≃+* Matrix (Fin 2) (Fin 2) (ZMod ℓ) :=
    (ZMod.ringEquivCongr hpv).mapMatrix with he
  set ρ : ↥Λ →+ Matrix (Fin 2) (Fin 2) (ZMod ℓ) := e.toAddMonoidHom.comp (ρ₀ v ψ hΛv) with hρ
  have hρapp : ∀ z : ↥Λ, ρ z = e (ρ₀ v ψ hΛv z) := fun z => rfl
  refine ⟨ρ.toIntLinearMap, ?_, ?_, ?_, ?_⟩
  · intro h1
    rw [AddMonoidHom.coe_toIntLinearMap, hρapp, ρ₀_one v ψ hψ1 hΛv h1, map_one]
  · intro x y hxy
    rw [AddMonoidHom.coe_toIntLinearMap, hρapp, hρapp, hρapp, ← map_mul]
    congr 1
    exact ρ₀_mul v ψ hO hΛv x.2 y.2 hxy
  · rw [AddMonoidHom.coe_toIntLinearMap]
    exact e.surjective.comp (ρ₀_surjective v ψ hψ1 hO hΛv)
  · intro x
    rw [AddMonoidHom.coe_toIntLinearMap, hρapp, EmbeddingLike.map_eq_zero_iff]
    constructor
    · intro hx
      obtain ⟨y, hy, hxy⟩ := exists_eq_smul_of_ρ₀_eq_zero v ψ hψ1 hO hΛv x hx
      exact ⟨⟨y, hy⟩, by rw [hpv] at hxy; exact hxy⟩
    · rintro ⟨y, hxy⟩
      have hxℓ : x = ℓ • y := by
        apply Subtype.ext
        rw [hxy, Submodule.coe_smul_of_tower, Nat.cast_smul_eq_nsmul]
      rw [hxℓ, map_nsmul, ← hpv, ← Nat.cast_smul_eq_nsmul (ZMod (pv v : ℕ)), ZMod.natCast_self, zero_smul]

end SplitCase

section RamifiedCase

open QuaternionAlgebra Rat.HeightOneSpectrum

variable {a b : ℚ}

theorem ramified_case (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (ℓ : ℕ) [hℓ : Fact ℓ.Prime]
    (hdiv : ∀ y : ℍ[ℚ, a, b] ⊗[ℚ] (place ℓ hℓ.out).adicCompletion ℚ, y ≠ 0 → IsUnit y) :
    (∀ J : Submodule ℤ ℍ[ℚ, a, b], (∀ x ∈ Λ, ∀ y ∈ J, x * y ∈ J) →
        Submodule.span ℤ ((ℓ : ℚ) • (Λ : Set ℍ[ℚ, a, b])) ≤ J → J ≤ Λ →
          J = Submodule.span ℤ ((ℓ : ℚ) • (Λ : Set ℍ[ℚ, a, b])) ∨
            (J : Set ℍ[ℚ, a, b]) = {x | x ∈ Λ ∧ ∃ n : ℤ, nrd x = (ℓ : ℚ) * n} ∨ J = Λ) ∧
      (∃ x ∈ Λ, (∃ n : ℤ, nrd x = (ℓ : ℚ) * n) ∧ ¬ (∃ n : ℤ, nrd x = (ℓ : ℚ) ^ 2 * n)) := by
  have hO : IsOrder Λ := hΛ.1
  have hℓp : ℓ.Prime := hℓ.out
  set v : HOS := place ℓ hℓp with hv
  have hℓv : (ℓ : 𝓞 ℚ) ∈ v.asIdeal := q_mem_asIdeal_place ℓ hℓp
  have hA : Aniso a b := aniso_of_forall_isUnit v hdiv

  obtain ⟨π, hπΛ, hπ0, hπ1⟩ :=
    QuaternionAlgebra.IsMaximalOrder.exists_mem_padicValRat_nrd_eq_one_of_forall_isUnit ℓ v hℓv hdiv Λ hΛ
  have hP2 : ∀ x ∈ Λ, (x = 0 ∨ 2 ≤ padicValRat ℓ (nrd x)) → ∃ x' ∈ Λ, x = (ℓ : ℤ) • x' := fun x hx hvx =>
    QuaternionAlgebra.IsMaximalOrder.exists_eq_natCast_smul_of_two_le_padicValRat_nrd_of_forall_isUnit ℓ v hℓv hdiv hΛ hx hvx
  refine ⟨fun J hJ hrJ hJΛ => trichotomy hO ℓ hA hP2 J hJ hrJ hJΛ, ?_⟩

  obtain ⟨N, hN⟩ := exists_int_nrd hO hπΛ
  have hN0 : N ≠ 0 := by
    rintro rfl; apply nrd_ne_zero_of_ne_zero hA hπ0; rw [hN]; simp
  have hdvd : (ℓ : ℤ) ∣ N := (dvd_iff_one_le_padicValRat ℓ hN0).mpr (by rw [← hN, hπ1])
  refine ⟨π, hπΛ, ((exists_eq_mul_iff_dvd ℓ N).mpr hdvd).imp fun n hn => by rw [hN, hn], ?_⟩
  rintro ⟨n, hn⟩
  have hsq : (ℓ : ℤ) ^ 2 ∣ N := ⟨n, by exact_mod_cast hN.symm.trans hn⟩
  have h2 := (sq_dvd_iff_two_le_padicValRat ℓ hN0).mp hsq
  rw [← hN, hπ1] at h2
  omega

end RamifiedCase

section Assembly

open QuaternionAlgebra

variable {a b : ℚ}

theorem main (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (ℓ : ℕ) [hℓ : Fact ℓ.Prime] :
    (∃ φ : ↥Λ →ₗ[ℤ] Matrix (Fin 2) (Fin 2) (ZMod ℓ),
      (∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, φ ⟨1, h⟩ = 1) ∧
      (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
          φ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = φ x * φ y) ∧
      Function.Surjective φ ∧
      (∀ x : ↥Λ, φ x = 0 ↔ ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (ℓ : ℚ) • (y : ℍ[ℚ, a, b]))) ∨
    ((∀ J : Submodule ℤ ℍ[ℚ, a, b], (∀ x ∈ Λ, ∀ y ∈ J, x * y ∈ J) →
        Submodule.span ℤ ((ℓ : ℚ) • (Λ : Set ℍ[ℚ, a, b])) ≤ J → J ≤ Λ →
          J = Submodule.span ℤ ((ℓ : ℚ) • (Λ : Set ℍ[ℚ, a, b])) ∨
            (J : Set ℍ[ℚ, a, b]) = {x | x ∈ Λ ∧ ∃ n : ℤ, nrd x = (ℓ : ℚ) * n} ∨ J = Λ) ∧
      (∃ x ∈ Λ, (∃ n : ℤ, nrd x = (ℓ : ℚ) * n) ∧ ¬ (∃ n : ℤ, nrd x = (ℓ : ℚ) ^ 2 * n))) := by
  by_cases hdiv : ∀ y : ℍ[ℚ, a, b] ⊗[ℚ] (place ℓ hℓ.out).adicCompletion ℚ, y ≠ 0 → IsUnit y
  · exact Or.inr (ramified_case Λ hΛ ℓ hdiv)
  · exact Or.inl (split_case Λ hΛ ℓ hdiv)

end Assembly

end P2mKcLocalStructure
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_linearMap_matrix_zmod_or_forall_eq_or_eq_or_eq_of_prime.P2mKcLocalStructure"

end
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_linearMap_matrix_zmod_or_forall_eq_or_eq_or_eq_of_prime.P2mKcLocalStructure"

open scoped Quaternion Pointwise
open QuaternionAlgebra

theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (ℓ : ℕ) [Fact ℓ.Prime] :
    (∃ φ : ↥Λ →ₗ[ℤ] Matrix (Fin 2) (Fin 2) (ZMod ℓ),
      (∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, φ ⟨1, h⟩ = 1) ∧
      (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
          φ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = φ x * φ y) ∧
      Function.Surjective φ ∧
      (∀ x : ↥Λ, φ x = 0 ↔ ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (ℓ : ℚ) • (y : ℍ[ℚ, a, b]))) ∨
    ((∀ J : Submodule ℤ ℍ[ℚ, a, b], (∀ x ∈ Λ, ∀ y ∈ J, x * y ∈ J) →
        Submodule.span ℤ ((ℓ : ℚ) • (Λ : Set ℍ[ℚ, a, b])) ≤ J → J ≤ Λ →
          J = Submodule.span ℤ ((ℓ : ℚ) • (Λ : Set ℍ[ℚ, a, b])) ∨
            (J : Set ℍ[ℚ, a, b]) = {x | x ∈ Λ ∧ ∃ n : ℤ, nrd x = (ℓ : ℚ) * n} ∨ J = Λ) ∧
      (∃ x ∈ Λ, (∃ n : ℤ, nrd x = (ℓ : ℚ) * n) ∧ ¬ (∃ n : ℤ, nrd x = (ℓ : ℚ) ^ 2 * n))) :=
  P2mKcLocalStructure.main Λ hΛ ℓ

end S_QuaternionAlgebra_IsMaximalOrder_exists_linearMap_matrix_zmod_or_forall_eq_or_eq_or_eq_of_prime
end P2MW
export P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_linearMap_matrix_zmod_or_forall_eq_or_eq_or_eq_of_prime (solution)
