-- Prove2me | solution 1 for QuaternionAlgebra.IsMaximalOrder.exists_eq_natCast_smul_of_two_le_padicValRat_nrd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/c3a3359b-1718-5295-bb86-92427fa35e6a

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_QuaternionAlgebra_Order
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_ringEquiv_coe_localBox_eq_setOf_norm_nrd_le_one_of_forall_isUnit
import Theorems.Thm_Submodule_mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox
import Theorems.Thm_Submodule_ofFiniteIdele_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_eq_natCast_smul_of_two_le_padicValRat_nrd
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false
open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra

namespace RamifiedHecke

section Local

variable {p : ℕ} [Fact p.Prime] {α β : ℚ_[p]}

theorem nrd_mul (x y : ℍ[ℚ_[p], α, β]) : nrd (x * y) = nrd x * nrd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_mul_mk, nrd_mk]
  ring

noncomputable def N (x : ℍ[ℚ_[p], α, β]) : ℝ := ‖nrd x‖

theorem N_mul (x y : ℍ[ℚ_[p], α, β]) : N (x * y) = N x * N y := by
  unfold N; rw [nrd_mul, norm_mul]

theorem N_one : N (1 : ℍ[ℚ_[p], α, β]) = 1 := by unfold N; rw [nrd_one, norm_one]

theorem N_nonneg (x : ℍ[ℚ_[p], α, β]) : 0 ≤ N x := norm_nonneg _

theorem N_coe (r : ℚ_[p]) : N ((r : ℚ_[p]) : ℍ[ℚ_[p], α, β]) = ‖r‖ ^ 2 := by
  unfold N; rw [nrd_coe, norm_pow]

theorem nrd_ne_zero (hdiv : ∀ x : ℍ[ℚ_[p], α, β], x ≠ 0 → IsUnit x) {x : ℍ[ℚ_[p], α, β]} (hx : x ≠ 0) :
    nrd x ≠ 0 := by
  intro h0
  have hsx : star x ≠ 0 := fun h => hx (by rw [← star_star x, h, star_zero])
  have hu : IsUnit (x * star x) := (hdiv x hx).mul (hdiv _ hsx)
  rw [mul_star_eq_coe_nrd, h0] at hu
  simp at hu

theorem N_pos (hdiv : ∀ x : ℍ[ℚ_[p], α, β], x ≠ 0 → IsUnit x) {x : ℍ[ℚ_[p], α, β]} (hx : x ≠ 0) :
    0 < N x := norm_pos_iff.mpr (nrd_ne_zero hdiv hx)

theorem N_inv (hdiv : ∀ x : ℍ[ℚ_[p], α, β], x ≠ 0 → IsUnit x) (u : (ℍ[ℚ_[p], α, β])ˣ) :
    N ((u⁻¹ : (ℍ[ℚ_[p], α, β])ˣ) : ℍ[ℚ_[p], α, β]) = (N (u : ℍ[ℚ_[p], α, β]))⁻¹ := by
  have h : N (u : ℍ[ℚ_[p], α, β]) * N ((u⁻¹ : (ℍ[ℚ_[p], α, β])ˣ) : ℍ[ℚ_[p], α, β]) = 1 := by
    rw [← N_mul, Units.mul_inv, N_one]
  have h0 : N (u : ℍ[ℚ_[p], α, β]) ≠ 0 := (N_pos hdiv u.ne_zero).ne'
  field_simp
  linarith [h]

theorem N_eq_zpow (hdiv : ∀ x : ℍ[ℚ_[p], α, β], x ≠ 0 → IsUnit x) {x : ℍ[ℚ_[p], α, β]} (hx : x ≠ 0) :
    ∃ m : ℤ, N x = (p : ℝ) ^ m := by
  refine ⟨-(nrd x).valuation, ?_⟩
  unfold N
  rw [Padic.norm_eq_zpow_neg_valuation (nrd_ne_zero hdiv hx)]

end Local

end RamifiedHecke

namespace RamifiedHecke

section LocalB

variable {p : ℕ} [hp : Fact p.Prime] {α β : ℚ_[p]}

theorem N_smul (r : ℚ_[p]) (x : ℍ[ℚ_[p], α, β]) : N (r • x) = ‖r‖ ^ 2 * N x := by
  rw [← QuaternionAlgebra.coe_mul_eq_smul, N_mul, N_coe]

theorem one_lt_p : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt

theorem p_pos : (0 : ℝ) < p := lt_trans zero_lt_one one_lt_p

theorem N_unit_eq_one_iff (hdiv : ∀ x : ℍ[ℚ_[p], α, β], x ≠ 0 → IsUnit x) (u : (ℍ[ℚ_[p], α, β])ˣ) :
    (N (u : ℍ[ℚ_[p], α, β]) ≤ 1 ∧ N ((u⁻¹ : (ℍ[ℚ_[p], α, β])ˣ) : ℍ[ℚ_[p], α, β]) ≤ 1) ↔
      N (u : ℍ[ℚ_[p], α, β]) = 1 := by
  rw [N_inv hdiv]
  have h0 := N_pos hdiv u.ne_zero
  constructor
  · rintro ⟨h1, h2⟩
    have : 1 ≤ N (u : ℍ[ℚ_[p], α, β]) := by rwa [inv_le_one₀ h0] at h2
    linarith
  · intro h
    rw [h, inv_one]
    exact ⟨le_rfl, le_rfl⟩

theorem N_conj (hdiv : ∀ x : ℍ[ℚ_[p], α, β], x ≠ 0 → IsUnit x) (π : (ℍ[ℚ_[p], α, β])ˣ) (x : ℍ[ℚ_[p], α, β]) :
    N ((π : ℍ[ℚ_[p], α, β]) * x * ((π⁻¹ : (ℍ[ℚ_[p], α, β])ˣ) : ℍ[ℚ_[p], α, β])) = N x := by
  rw [N_mul, N_mul, N_inv hdiv]
  have h0 := (N_pos hdiv π.ne_zero).ne'
  field_simp

theorem hecke_conditions_iff (hdiv : ∀ x : ℍ[ℚ_[p], α, β], x ≠ 0 → IsUnit x) (h : (ℍ[ℚ_[p], α, β])ˣ) :
    (N (h : ℍ[ℚ_[p], α, β]) ≤ 1 ∧
      N ((p : ℚ_[p]) • ((h⁻¹ : (ℍ[ℚ_[p], α, β])ˣ) : ℍ[ℚ_[p], α, β])) ≤ 1 ∧
      ¬ N ((h⁻¹ : (ℍ[ℚ_[p], α, β])ˣ) : ℍ[ℚ_[p], α, β]) ≤ 1 ∧
      ¬ N ((p : ℚ_[p])⁻¹ • (h : ℍ[ℚ_[p], α, β])) ≤ 1) ↔
    N (h : ℍ[ℚ_[p], α, β]) = (p : ℝ) ^ (-1 : ℤ) := by
  obtain ⟨m, hm⟩ := N_eq_zpow hdiv h.ne_zero
  have hP : (p : ℝ) ≠ 0 := p_pos.ne'
  have h1p := one_lt_p (p := p)
  have e1 : N ((h⁻¹ : (ℍ[ℚ_[p], α, β])ˣ) : ℍ[ℚ_[p], α, β]) = (p : ℝ) ^ (-m) := by
    rw [N_inv hdiv, hm, zpow_neg]
  have e2 : N ((p : ℚ_[p]) • ((h⁻¹ : (ℍ[ℚ_[p], α, β])ˣ) : ℍ[ℚ_[p], α, β])) = (p : ℝ) ^ (-2 - m) := by
    rw [N_smul, e1, Padic.norm_p, zpow_sub₀ hP, zpow_neg, zpow_neg, zpow_two, inv_pow]
    ring
  have e3 : N ((p : ℚ_[p])⁻¹ • (h : ℍ[ℚ_[p], α, β])) = (p : ℝ) ^ (2 + m) := by
    rw [N_smul, hm, norm_inv, Padic.norm_p, inv_inv, zpow_add₀ hP, zpow_two]
    ring
  rw [hm, e1, e2, e3, ← zpow_zero (p : ℝ), zpow_le_zpow_iff_right₀ h1p, zpow_le_zpow_iff_right₀ h1p,
    zpow_le_zpow_iff_right₀ h1p, zpow_le_zpow_iff_right₀ h1p, (zpow_right_injective₀ p_pos h1p.ne').eq_iff]
  omega

theorem N_inv_p_smul_sq (π : ℍ[ℚ_[p], α, β]) (hπ : N π = (p : ℝ) ^ (-1 : ℤ)) :
    N ((p : ℚ_[p])⁻¹ • (π * π)) = 1 := by
  have hP : (p : ℝ) ≠ 0 := p_pos.ne'
  rw [N_smul, N_mul, hπ, norm_inv, Padic.norm_p, inv_inv, ← zpow_add₀ hP,
    show (-1 : ℤ) + -1 = -2 by norm_num, zpow_neg, zpow_two]
  field_simp

theorem N_eq_of_mul_self_eq_neg_p (x : ℍ[ℚ_[p], α, β]) (hx : x * x = -((p : ℚ_[p]) : ℍ[ℚ_[p], α, β])) :
    N x = (p : ℝ) ^ (-1 : ℤ) := by
  have h := congrArg N hx
  rw [N_mul] at h
  have hN : N (-((p : ℚ_[p]) : ℍ[ℚ_[p], α, β])) = ((p : ℝ) ^ (-1 : ℤ)) ^ 2 := by
    unfold N
    rw [nrd_neg, nrd_coe, norm_pow, Padic.norm_p, zpow_neg, zpow_one]
  have h' : N x ^ 2 = ((p : ℝ) ^ (-1 : ℤ)) ^ 2 := by
    rw [sq, h, hN]
  exact (pow_left_inj₀ (N_nonneg x) (by positivity) two_ne_zero).mp h'

end LocalB

end RamifiedHecke

namespace RamifiedHecke

section Places

theorem isMaximal_span_natCast_of_prime {p : ℕ} (hp : p.Prime) :
    (Ideal.span {(p : 𝓞 ℚ)} : Ideal (𝓞 ℚ)).IsMaximal := by
  have e : 𝓞 ℚ ≃+* ℤ := Rat.ringOfIntegersEquiv
  have hpZ : _root_.Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpO : _root_.Prime (p : 𝓞 ℚ) := by
    have : (p : 𝓞 ℚ) = e.symm (p : ℤ) := by rw [map_natCast]
    rw [this]
    exact (MulEquiv.prime_iff (e.symm : ℤ ≃* 𝓞 ℚ)).mpr hpZ
  have hne : (Ideal.span {(p : 𝓞 ℚ)} : Ideal (𝓞 ℚ)) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hp.ne_zero
  have hprime : (Ideal.span {(p : 𝓞 ℚ)} : Ideal (𝓞 ℚ)).IsPrime := (Ideal.span_singleton_prime hpO.ne_zero).mpr hpO
  exact hprime.isMaximal hne

theorem exists_place {p : ℕ} (hp : p.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 ℚ), ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
  refine ⟨⟨Ideal.span {(p : 𝓞 ℚ)}, (isMaximal_span_natCast_of_prime hp).isPrime, ?_⟩, Ideal.mem_span_singleton_self _⟩
  rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hp.ne_zero

theorem place_eq_of_mem {p : ℕ} (hp : p.Prime) {v v' : HeightOneSpectrum (𝓞 ℚ)}
    (hv : (p : 𝓞 ℚ) ∈ v.asIdeal) (hv' : (p : 𝓞 ℚ) ∈ v'.asIdeal) : v = v' := by
  have hmax := isMaximal_span_natCast_of_prime hp
  have h1 : v.asIdeal = Ideal.span {(p : 𝓞 ℚ)} :=
    (hmax.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).mpr hv)).symm
  have h2 : v'.asIdeal = Ideal.span {(p : 𝓞 ℚ)} :=
    (hmax.eq_of_le v'.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).mpr hv')).symm
  exact HeightOneSpectrum.ext (h1.trans h2.symm)

theorem primesEquiv_eq {p : ℕ} (hp : p.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) = p := by
  show Rat.HeightOneSpectrum.natGenerator v = p
  have hdvd : Rat.HeightOneSpectrum.natGenerator v ∣ p := by
    rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff]
    have := Ideal.mem_map_of_mem (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) hv
    rwa [map_natCast] at this
  exact (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator v) hp).mp hdvd

theorem inv_natCast_mem_adicCompletionIntegers {ℓ : ℕ} (hℓ : ℓ ≠ 0)
    {v : HeightOneSpectrum (𝓞 ℚ)} (hv : ((ℓ : ℕ) : 𝓞 ℚ) ∉ v.asIdeal) :
    algebraMap ℚ (v.adicCompletion ℚ) ((ℓ : ℚ)⁻¹) ∈ v.adicCompletionIntegers ℚ := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers,
    show Valued.v (algebraMap ℚ (v.adicCompletion ℚ) ((ℓ : ℚ)⁻¹)) = v.valuation ℚ ((ℓ : ℚ)⁻¹) from
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _, map_inv₀]
  have h1 : v.valuation ℚ (ℓ : ℚ) = 1 := by
    have : (ℓ : ℚ) = algebraMap (𝓞 ℚ) ℚ (ℓ : 𝓞 ℚ) := by simp
    rw [this, HeightOneSpectrum.valuation_of_algebraMap]
    have hle := v.intValuation_le_one (ℓ : 𝓞 ℚ)
    have hnlt : ¬ v.intValuation (ℓ : 𝓞 ℚ) < 1 := by
      rw [HeightOneSpectrum.intValuation_lt_one_iff_mem]
      exact hv
    exact le_antisymm hle (not_lt.mp hnlt)
  rw [h1, inv_one]

theorem natCast_mem_adicCompletionIntegers (ℓ : ℕ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    algebraMap ℚ (v.adicCompletion ℚ) (ℓ : ℚ) ∈ v.adicCompletionIntegers ℚ := by
  rw [map_natCast]
  exact natCast_mem _ ℓ

end Places

section Components

variable {a b : ℚ}

local notation "ℍ𝔸" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "ev" v => Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v

noncomputable abbrev evU (v : HeightOneSpectrum (𝓞 ℚ)) : (ℍ𝔸)ˣ →* (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ :=
  Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom

theorem ev_smul (v : HeightOneSpectrum (𝓞 ℚ)) (c : ℚ) (x : ℍ𝔸) : (ev v) (c • x) = c • (ev v) x := map_smul _ _ _

theorem coe_evU (v : HeightOneSpectrum (𝓞 ℚ)) (x : (ℍ𝔸)ˣ) : ((evU (a := a) (b := b) v x : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : _) = (ev v) (x : ℍ𝔸) := rfl

theorem coe_inv_evU (v : HeightOneSpectrum (𝓞 ℚ)) (x : (ℍ𝔸)ˣ) :
    (((evU (a := a) (b := b) v x)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : _) = (ev v) ((x⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) := by
  rw [← map_inv]; rfl

theorem smul_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (v : HeightOneSpectrum (𝓞 ℚ)) {c : ℚ}
    (hc : algebraMap ℚ (v.adicCompletion ℚ) c ∈ v.adicCompletionIntegers ℚ)
    {x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ} (hx : x ∈ Submodule.localBox Λ v) : c • x ∈ Submodule.localBox Λ v := by
  unfold Submodule.localBox at hx ⊢
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨z, hz, d, hd, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨z, hz, algebraMap ℚ (v.adicCompletion ℚ) c * d, mul_mem hc hd, ?_⟩
    rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul, Algebra.smul_def]
  | zero => rw [smul_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
  | neg y _ hy => rw [smul_neg]; exact neg_mem hy

theorem tmul_one_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} {z : ℍ[ℚ, a, b]} (hz : z ∈ Λ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    z ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ) ∈ Submodule.localBox Λ v :=
  AddSubgroup.subset_closure ⟨z, hz, 1, one_mem _, rfl⟩

theorem one_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (1 : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox Λ v := by
  rw [Algebra.TensorProduct.one_def]; exact tmul_one_mem_localBox hΛ.one_mem v

end Components

end RamifiedHecke

namespace RamifiedHecke

section Transport

variable {a b : ℚ}

scoped instance instFactPrimesRH (P : Nat.Primes) : Fact P.1.Prime := ⟨P.2⟩

theorem theta_natCast_smul {v : HeightOneSpectrum (𝓞 ℚ)} {D : Type*} [Ring D] [Algebra ℚ_[Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v] D]
    (Θ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* D) (n : ℕ) (x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :
    Θ ((n : ℚ) • x) = ((n : ℚ_[Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v])) • Θ x := by
  rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul, map_mul, map_natCast, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]

theorem theta_inv_natCast_smul {v : HeightOneSpectrum (𝓞 ℚ)} {D : Type*} [Ring D] [Algebra ℚ_[Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v] D]
    (Θ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* D) {n : ℕ} (hn : n ≠ 0) (x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :
    Θ ((n : ℚ)⁻¹ • x) = ((n : ℚ_[Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v]))⁻¹ • Θ x := by
  have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  have hnP : (n : ℚ_[Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v]) ≠ 0 := by exact_mod_cast hn
  rw [eq_inv_smul_iff₀ hnP, ← theta_natCast_smul, smul_smul, mul_inv_cancel₀ hnQ, one_smul]

end Transport

end RamifiedHecke
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_eq_natCast_smul_of_two_le_padicValRat_nrd.RamifiedHecke"

namespace RamifiedHecke

section Dictionary

variable {a b : ℚ}

local notation "ℍ𝔸" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "ev" v => Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v

structure RamData (O : Submodule ℤ ℍ[ℚ, a, b]) (v₀ : HeightOneSpectrum (𝓞 ℚ)) where
  hO : IsOrder O
  hv₀ : ((((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v₀ : Nat.Primes) : ℕ) : ℕ) : 𝓞 ℚ) ∈ v₀.asIdeal
  hdiv : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v₀.adicCompletion ℚ, x ≠ 0 → IsUnit x
  Θ : ℍ[ℚ, a, b] ⊗[ℚ] v₀.adicCompletion ℚ ≃+*
      ℍ[ℚ_[Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v₀], (a : ℚ_[Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v₀]),
        (b : ℚ_[Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v₀])]
  hΘc : ∀ c : v₀.adicCompletion ℚ, Θ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) =
      (Rat.HeightOneSpectrum.adicCompletion.padicEquiv (R := 𝓞 ℚ) v₀ c) •
        (1 : ℍ[ℚ_[Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v₀],
          (a : ℚ_[Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v₀]), (b : ℚ_[Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v₀])])
  hbox : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v₀.adicCompletion ℚ, x ∈ Submodule.localBox O v₀ ↔ N (Θ x) ≤ 1

variable {O : Submodule ℤ ℍ[ℚ, a, b]} {v₀ : HeightOneSpectrum (𝓞 ℚ)}

namespace RamData

noncomputable abbrev p (_D : RamData O v₀) : ℕ := ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v₀ : Nat.Primes) : ℕ)

theorem p_prime (D : RamData O v₀) : D.p.Prime := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v₀).2

theorem p_ne_zero (D : RamData O v₀) : D.p ≠ 0 := D.p_prime.ne_zero

theorem hdivP (D : RamData O v₀) :
    ∀ x : ℍ[ℚ_[Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v₀], (a : ℚ_[Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v₀]),
        (b : ℚ_[Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v₀])], x ≠ 0 → IsUnit x := by
  intro x hx
  have h0 : D.Θ.symm x ≠ 0 := fun h => hx (by simpa using congrArg D.Θ h)
  simpa using (D.hdiv _ h0).map D.Θ

theorem not_mem_of_ne (D : RamData O v₀) {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v₀) :
    ((D.p : ℕ) : 𝓞 ℚ) ∉ w.asIdeal :=
  fun h => hw (place_eq_of_mem D.p_prime h D.hv₀)

theorem ne_of_not_mem (D : RamData O v₀) {w : HeightOneSpectrum (𝓞 ℚ)} (hw : ((D.p : ℕ) : 𝓞 ℚ) ∉ w.asIdeal) :
    w ≠ v₀ := fun h => hw (h ▸ D.hv₀)

theorem inv_mem_localBox_of_ne (D : RamData O v₀) {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v₀)
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ)
    (h2 : (D.p : ℚ) • ((x⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) ∈ Submodule.localBox O w) :
    ((x⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) ∈ Submodule.localBox O w := by
  have := smul_mem_localBox w (inv_natCast_mem_adicCompletionIntegers D.p_ne_zero (D.not_mem_of_ne hw)) h2
  rwa [smul_smul, inv_mul_cancel₀ (by exact_mod_cast D.p_ne_zero : (D.p : ℚ) ≠ 0), one_smul] at this

theorem mem_localBoxUnits_iff_N (D : RamData O v₀) (y : (ℍ[ℚ, a, b] ⊗[ℚ] v₀.adicCompletion ℚ)ˣ) :
    y ∈ Submodule.localBoxUnits O v₀ ↔ N (D.Θ y) = 1 := by
  rw [Submodule.mem_localBoxUnits_iff, SetLike.mem_coe, SetLike.mem_coe, D.hbox, D.hbox]
  have := N_unit_eq_one_iff D.hdivP (Units.map D.Θ.toMonoidHom y)
  simpa using this

theorem hecke_iff_N (D : RamData O v₀) (y : (ℍ[ℚ, a, b] ⊗[ℚ] v₀.adicCompletion ℚ)ˣ) :
    ((y : ℍ[ℚ, a, b] ⊗[ℚ] v₀.adicCompletion ℚ) ∈ Submodule.localBox O v₀ ∧
      (D.p : ℚ) • ((y⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v₀.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v₀.adicCompletion ℚ) ∈ Submodule.localBox O v₀ ∧
      ((y⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v₀.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v₀.adicCompletion ℚ) ∉ Submodule.localBox O v₀ ∧
      (D.p : ℚ)⁻¹ • (y : ℍ[ℚ, a, b] ⊗[ℚ] v₀.adicCompletion ℚ) ∉ Submodule.localBox O v₀) ↔
    N (D.Θ y) = (D.p : ℝ) ^ (-1 : ℤ) := by
  rw [D.hbox, D.hbox, D.hbox, D.hbox, theta_natCast_smul, theta_inv_natCast_smul _ D.p_ne_zero]
  have := hecke_conditions_iff D.hdivP (Units.map D.Θ.toMonoidHom y)
  simpa using this

end RamData
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_eq_natCast_smul_of_two_le_padicValRat_nrd.RamifiedHecke"

end Dictionary
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_eq_natCast_smul_of_two_le_padicValRat_nrd.RamifiedHecke"

end RamifiedHecke
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_eq_natCast_smul_of_two_le_padicValRat_nrd.RamifiedHecke"

namespace RamifiedHecke

section NrdTransport

variable {a b : ℚ}

theorem quat_mul_self {R : Type*} [CommRing R] {c₁ c₃ : R} (x : ℍ[R, c₁, c₃]) :
    x * x = ((trd x : R) : ℍ[R, c₁, c₃]) * x - ((nrd x : R) : ℍ[R, c₁, c₃]) := by
  have h1 := mul_star_eq_coe_nrd x
  have h2 : star x = ((trd x : R) : ℍ[R, c₁, c₃]) - x := eq_sub_of_add_eq' (add_star_eq_coe_trd x)
  rw [h2, mul_sub] at h1
  have h3 : x * ((trd x : R) : ℍ[R, c₁, c₃]) = ((trd x : R) : ℍ[R, c₁, c₃]) * x := by
    rw [QuaternionAlgebra.mul_coe_eq_smul, QuaternionAlgebra.coe_mul_eq_smul]
  calc x * x = x * ((trd x : R) : ℍ[R, c₁, c₃]) - ((nrd x : R) : ℍ[R, c₁, c₃]) := by rw [← h1]; abel
    _ = _ := by rw [h3]

theorem theta_intCast_smul {v : HeightOneSpectrum (𝓞 ℚ)} {D : Type*} [Ring D] [Algebra ℚ_[Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v] D]
    (Θ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* D) (n : ℤ) (x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :
    Θ ((n : ℚ) • x) = ((n : ℚ_[Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v])) • Θ x := by
  rw [Int.cast_smul_eq_zsmul, zsmul_eq_mul, map_mul, map_intCast, Int.cast_smul_eq_zsmul, zsmul_eq_mul]

theorem theta_ratCast_smul {v : HeightOneSpectrum (𝓞 ℚ)} {D : Type*} [Ring D] [Algebra ℚ_[Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v] D]
    (Θ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* D) (r : ℚ) (x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :
    Θ (r • x) = ((r : ℚ_[Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v])) • Θ x := by
  have hd : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have hdP : (r.den : ℚ_[Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v]) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have h1 : (r.den : ℚ) • (r • x) = (r.num : ℚ) • x := by
    rw [smul_smul, Rat.den_mul_eq_num]
  have h2 := congrArg Θ h1
  rw [theta_natCast_smul, theta_intCast_smul] at h2

  have h3 : Θ (r • x) = ((r.den : ℚ_[Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v]))⁻¹ •
      (((r.num : ℚ_[Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v])) • Θ x) := by
    rw [eq_inv_smul_iff₀ hdP, h2]
  rw [h3, smul_smul]
  congr 1
  rw [Rat.cast_def, div_eq_inv_mul]

variable (v : HeightOneSpectrum (𝓞 ℚ))
  (Θ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+*
    ℍ[ℚ_[Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v], (a : ℚ_[Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v]),
      (b : ℚ_[Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v])])
  (hΘc : ∀ c : v.adicCompletion ℚ, Θ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) =
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv (R := 𝓞 ℚ) v c) •
      (1 : ℍ[ℚ_[Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v],
        (a : ℚ_[Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v]), (b : ℚ_[Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v])]))

local notation "Kv" => HeightOneSpectrum.adicCompletion ℚ v
local notation "ℚP" => ℚ_[Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v]
local notation "ℍP" => ℍ[ℚ_[Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v], (a : ℚ_[Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v]),
      (b : ℚ_[Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v])]

end NrdTransport
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_eq_natCast_smul_of_two_le_padicValRat_nrd.RamifiedHecke"

end RamifiedHecke
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_eq_natCast_smul_of_two_le_padicValRat_nrd.RamifiedHecke"

namespace RamifiedHecke

section NrdTransport2

variable {a b : ℚ} (v : HeightOneSpectrum (𝓞 ℚ))
  (Θ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+*
    ℍ[ℚ_[Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v], (a : ℚ_[Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v]),
      (b : ℚ_[Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v])])
  (hΘc : ∀ c : v.adicCompletion ℚ, Θ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) =
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv (R := 𝓞 ℚ) v c) •
      (1 : ℍ[ℚ_[Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v],
        (a : ℚ_[Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v]), (b : ℚ_[Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v])]))

local notation "Kv" => HeightOneSpectrum.adicCompletion ℚ v
local notation "ℚP" => ℚ_[Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v]
local notation "ℍP" => ℍ[ℚ_[Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v], (a : ℚ_[Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v]),
      (b : ℚ_[Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v])]

omit Θ hΘc in
theorem tmul_one_mul_tmul_one (z w : ℍ[ℚ, a, b]) :
    (z * w) ⊗ₜ[ℚ] (1 : Kv) = (z ⊗ₜ[ℚ] (1 : Kv)) * (w ⊗ₜ[ℚ] (1 : Kv)) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]

omit Θ hΘc in
theorem coe_tmul_one (r : ℚ) : ((r : ℚ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : Kv) = r • (1 : ℍ[ℚ, a, b] ⊗[ℚ] Kv) := by
  rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', show r • (1 : ℍ[ℚ, a, b]) = (r : ℍ[ℚ, a, b]) by
    rw [← QuaternionAlgebra.coe_mul_eq_smul, mul_one]]

omit hΘc in

theorem theta_coe_tmul_one (r : ℚ) : Θ (((r : ℚ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : Kv)) = ((r : ℚP) : ℍP) := by
  rw [coe_tmul_one, theta_ratCast_smul, map_one, ← QuaternionAlgebra.coe_mul_eq_smul, mul_one]

omit hΘc in

theorem theta_tmul_mul_self (z : ℍ[ℚ, a, b]) :
    Θ (z ⊗ₜ[ℚ] (1 : Kv)) * Θ (z ⊗ₜ[ℚ] (1 : Kv)) =
      (((trd z : ℚ) : ℚP) : ℍP) * Θ (z ⊗ₜ[ℚ] (1 : Kv)) - (((nrd z : ℚ) : ℚP) : ℍP) := by
  rw [← map_mul, ← tmul_one_mul_tmul_one, quat_mul_self, TensorProduct.sub_tmul, map_sub, tmul_one_mul_tmul_one, map_mul,
    theta_coe_tmul_one, theta_coe_tmul_one]

omit Θ hΘc in

theorem eq_coe_re_of_tmul_one_eq (z : ℍ[ℚ, a, b]) (e : Kv)
    (h : z ⊗ₜ[ℚ] (1 : Kv) = (1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] e) : z = ((z.re : ℚ) : ℍ[ℚ, a, b]) := by
  have h' : (1 : Kv) ⊗ₜ[ℚ] z = e ⊗ₜ[ℚ] (1 : ℍ[ℚ, a, b]) := by
    have := congrArg (TensorProduct.comm ℚ ℍ[ℚ, a, b] Kv) h
    simpa using this
  set B := QuaternionAlgebra.basisOneIJK (R := ℚ) a 0 b with hB
  have hrep := congrArg (fun t => (Algebra.TensorProduct.basis Kv B).repr t) h'
  simp only [Algebra.TensorProduct.basis_repr_tmul, one_smul] at hrep
  have hcoord : ∀ i : Fin 4, algebraMap ℚ Kv (B.repr z i) = e * algebraMap ℚ Kv (B.repr 1 i) := by
    intro i
    have := DFunLike.congr_fun hrep i
    simpa [Finsupp.mapRange_apply] using this
  have hinj : Function.Injective (algebraMap ℚ Kv) := (algebraMap ℚ Kv).injective
  have h1 := hcoord 1
  have h2 := hcoord 2
  have h3 := hcoord 3
  rw [hB, QuaternionAlgebra.coe_basisOneIJK_repr, QuaternionAlgebra.coe_basisOneIJK_repr] at h1 h2 h3
  simp only [Matrix.cons_val_one, Matrix.cons_val, QuaternionAlgebra.imI_one,
    QuaternionAlgebra.imJ_one, QuaternionAlgebra.imK_one, map_zero, mul_zero] at h1 h2 h3
  have e1 : z.imI = 0 := hinj (by rw [map_zero]; exact h1)
  have e2 : z.imJ = 0 := hinj (by rw [map_zero]; exact h2)
  have e3 : z.imK = 0 := hinj (by rw [map_zero]; exact h3)
  ext <;> simp [e1, e2, e3]

include hΘc in

theorem nrd_theta_tmul_one (z : ℍ[ℚ, a, b]) : nrd (Θ (z ⊗ₜ[ℚ] (1 : Kv))) = ((nrd z : ℚ) : ℚP) := by
  set y := Θ (z ⊗ₜ[ℚ] (1 : Kv)) with hy
  have h1 := theta_tmul_mul_self v Θ z
  have h2 := quat_mul_self y
  rw [← hy] at h1

  have h3 : ((((trd z : ℚ) : ℚP) - trd y : ℚP) : ℍP) * y = ((((nrd z : ℚ) : ℚP) - nrd y : ℚP) : ℍP) := by
    rw [QuaternionAlgebra.coe_sub, QuaternionAlgebra.coe_sub, sub_mul]
    have := h1.symm.trans h2

    exact sub_eq_sub_iff_sub_eq_sub.mp this
  by_cases ht : (((trd z : ℚ) : ℚP) - trd y : ℚP) = 0
  · rw [ht, QuaternionAlgebra.coe_zero, zero_mul] at h3
    have h4 := QuaternionAlgebra.coe_injective (R := ℚP) (c₁ := (a : ℚP)) (c₂ := (0 : ℚP)) (c₃ := (b : ℚP))
      (h3.symm.trans QuaternionAlgebra.coe_zero.symm)
    exact (sub_eq_zero.mp h4).symm
  ·
    set c : ℚP := ((((trd z : ℚ) : ℚP) - trd y : ℚP))⁻¹ * ((((nrd z : ℚ) : ℚP) - nrd y : ℚP)) with hc
    have hyc : y = ((c : ℚP) : ℍP) := by
      have := congrArg (HMul.hMul ((((((trd z : ℚ) : ℚP) - trd y : ℚP))⁻¹ : ℚP) : ℍP)) h3
      rwa [← mul_assoc, ← QuaternionAlgebra.coe_mul, inv_mul_cancel₀ ht, QuaternionAlgebra.coe_one, one_mul,
        ← QuaternionAlgebra.coe_mul] at this

    set e : Kv := (Rat.HeightOneSpectrum.adicCompletion.padicEquiv (R := 𝓞 ℚ) v).symm c with he
    have hze : z ⊗ₜ[ℚ] (1 : Kv) = (1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] e := by
      apply Θ.injective
      rw [← hy, hyc, hΘc, he, show (Rat.HeightOneSpectrum.adicCompletion.padicEquiv (R := 𝓞 ℚ) v)
          ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv (R := 𝓞 ℚ) v).symm c) = c from
          (Rat.HeightOneSpectrum.adicCompletion.padicEquiv (R := 𝓞 ℚ) v).apply_symm_apply c,
        ← QuaternionAlgebra.coe_mul_eq_smul, mul_one]
    obtain ⟨r, hr⟩ : ∃ r : ℚ, z = ((r : ℚ) : ℍ[ℚ, a, b]) := ⟨z.re, eq_coe_re_of_tmul_one_eq v z e hze⟩
    rw [hy, hr, theta_coe_tmul_one, nrd_coe, nrd_coe]
    push_cast
    ring

end NrdTransport2
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_eq_natCast_smul_of_two_le_padicValRat_nrd.RamifiedHecke"

end RamifiedHecke
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_eq_natCast_smul_of_two_le_padicValRat_nrd.RamifiedHecke"

namespace RamifiedHecke

section LatticeCut

variable {a b : ℚ}

local notation "ℍ𝔸" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "ev" v => Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v

theorem nrd_pos_of_ne_zero (ha : a < 0) (hb : b < 0) {z : ℍ[ℚ, a, b]} (hz : z ≠ 0) : 0 < nrd z := by
  obtain ⟨z₀, z₁, z₂, z₃⟩ := z
  simp only [nrd_mk]
  have h0 : 0 ≤ z₀ ^ 2 := sq_nonneg _
  have h1 : 0 ≤ -a * z₁ ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h2 : 0 ≤ -b * z₂ ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h3 : 0 ≤ a * b * z₃ ^ 2 := mul_nonneg (le_of_lt (mul_pos_of_neg_of_neg ha hb)) (sq_nonneg _)
  by_contra hle
  push Not at hle
  have e0 : z₀ ^ 2 = 0 := by linarith
  have e1 : -a * z₁ ^ 2 = 0 := by linarith
  have e2 : -b * z₂ ^ 2 = 0 := by linarith
  have e3 : a * b * z₃ ^ 2 = 0 := by linarith
  have hab : a * b ≠ 0 := (mul_pos_of_neg_of_neg ha hb).ne'
  simp only [mul_eq_zero, neg_eq_zero, ha.ne, hb.ne, false_or, pow_eq_zero_iff, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, hab] at e0 e1 e2 e3
  exact hz (by ext <;> simp [e0, e1, e2, e3])

variable {O : Submodule ℤ ℍ[ℚ, a, b]} {v₀ : HeightOneSpectrum (𝓞 ℚ)}

namespace RamData

theorem mem_box_iff (D : RamData O v₀) (x : ℍ𝔸) :
    x ∈ Submodule.finiteAdeleBox O ↔ ∀ w, (ev w) x ∈ Submodule.localBox O w :=
  Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox O D.hO.fg D.hO.spanTop x

theorem mem_ofFiniteIdele_iff_local (D : RamData O v₀) (g : (ℍ𝔸)ˣ) (z : ℍ[ℚ, a, b]) :
    z ∈ Submodule.ofFiniteIdele O g ↔
      ∀ w : HeightOneSpectrum (𝓞 ℚ),
        (((evU w g)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) *
            (z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) ∈ Submodule.localBox O w := by
  rw [Submodule.mem_ofFiniteIdele_iff, AddSubgroup.mem_map]
  have key : ∀ w : HeightOneSpectrum (𝓞 ℚ), (ev w) (((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * (z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ))) =
      (((evU w g)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) *
        (z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) := by
    intro w
    rw [map_mul, ← coe_inv_evU, Submodule.finiteAdeleEvalAt_tmul]
    rfl
  constructor
  · rintro ⟨y, hy, hgy⟩
    have hy' : ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * (z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) = y := by
      rw [← hgy, AddMonoidHom.coe_mulLeft, ← mul_assoc, Units.inv_mul, one_mul]
    intro w
    rw [← key, hy']
    exact (D.mem_box_iff y).mp hy w
  · intro h
    refine ⟨((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * (z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)), (D.mem_box_iff _).mpr fun w => ?_, ?_⟩
    · rw [key]; exact h w
    · rw [AddMonoidHom.coe_mulLeft, ← mul_assoc, Units.mul_inv, one_mul]

theorem N_evU_of_mem_primeHeckeSet (D : RamData O v₀) (h : (ℍ𝔸)ˣ) (hh : h ∈ primeHeckeSet O D.p) :
    N (D.Θ (evU v₀ h)) = (D.p : ℝ) ^ (-1 : ℤ) := by
  obtain ⟨c1, c2, c3, c4⟩ := hh
  rw [D.mem_box_iff] at c1 c2 c3 c4
  push Not at c3 c4
  have hinv_away : ∀ w, w ≠ v₀ →
      (((evU w h)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) ∈ Submodule.localBox O w := by
    intro w hw
    refine D.inv_mem_localBox_of_ne hw _ ?_
    have := c2 w
    rwa [ev_smul, ← coe_inv_evU] at this
  obtain ⟨w₃, hw₃⟩ := c3
  have hw₃v : w₃ = v₀ := by
    by_contra hne
    exact hw₃ (by rw [← coe_inv_evU]; exact hinv_away w₃ hne)
  subst hw₃v
  obtain ⟨w₄, hw₄⟩ := c4
  have hw₄v : w₄ = w₃ := by
    by_contra hne
    apply hw₄
    rw [ev_smul]
    exact smul_mem_localBox w₄ (inv_natCast_mem_adicCompletionIntegers D.p_ne_zero (D.not_mem_of_ne hne)) (c1 w₄)
  subst hw₄v
  rw [← D.hecke_iff_N]
  refine ⟨c1 w₄, ?_, ?_, ?_⟩
  · have := c2 w₄; rwa [ev_smul, ← coe_inv_evU] at this
  · rwa [← coe_inv_evU] at hw₃
  · rwa [ev_smul] at hw₄

theorem N_theta_tmul_one_eq (D : RamData O v₀) (ha : a < 0) (hb : b < 0) {z : ℍ[ℚ, a, b]} (hz : z ≠ 0) :
    N (D.Θ (z ⊗ₜ[ℚ] (1 : v₀.adicCompletion ℚ))) = (D.p : ℝ) ^ (-padicValRat D.p (nrd z)) := by
  have hn : nrd z ≠ 0 := (nrd_pos_of_ne_zero ha hb hz).ne'
  unfold N
  rw [nrd_theta_tmul_one v₀ D.Θ D.hΘc, Padic.eq_padicNorm, padicNorm.eq_zpow_of_nonzero hn]
  push_cast
  rfl

theorem N_theta_zero (D : RamData O v₀) : N (D.Θ 0) = 0 := by
  unfold N; rw [map_zero, nrd_zero, norm_zero]

theorem one_lt_p' (D : RamData O v₀) : (1 : ℝ) < D.p := by exact_mod_cast D.p_prime.one_lt
theorem p_pos' (D : RamData O v₀) : (0 : ℝ) < D.p := lt_trans zero_lt_one D.one_lt_p'

end RamData
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_eq_natCast_smul_of_two_le_padicValRat_nrd.RamifiedHecke"

end LatticeCut
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_eq_natCast_smul_of_two_le_padicValRat_nrd.RamifiedHecke"

end RamifiedHecke
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_eq_natCast_smul_of_two_le_padicValRat_nrd.RamifiedHecke"

namespace RamifiedHecke

section PSquared

variable {a b : ℚ}

theorem mainQ2 {q' : ℕ} (hq' : q'.Prime) (hdef : IsDefiniteRamifiedExactlyAt a b q')
    {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsMaximalOrder Λ)
    {h : ℍ[ℚ, a, b]} (hh : h ∈ Λ) (hv : h = 0 ∨ 2 ≤ padicValRat q' (QuaternionAlgebra.nrd h)) :
    ∃ h' ∈ Λ, h = (q' : ℤ) • h' := by
  rcases hv with h0 | hv
  · exact ⟨0, Λ.zero_mem, by rw [h0, smul_zero]⟩
  have hn0 : nrd h ≠ 0 := by
    intro hn; rw [hn, padicValRat.zero] at hv; omega
  have hne : h ≠ 0 := fun h0 => hn0 (by rw [h0, nrd_zero])
  obtain ⟨v₀, hv₀⟩ := exists_place hq'
  have hq := primesEquiv_eq hq' v₀ hv₀
  subst hq
  have hO : IsOrder Λ := hΛ.isOrder
  have hdiv₀ : ∀ y : ℍ[ℚ, a, b] ⊗[ℚ] v₀.adicCompletion ℚ, y ≠ 0 → IsUnit y := (hdef.2.2 v₀).mpr hv₀
  obtain ⟨Θ, hΘc, hΘbox⟩ :=
    QuaternionAlgebra.IsMaximalOrder.exists_ringEquiv_coe_localBox_eq_setOf_norm_nrd_le_one_of_forall_isUnit hΛ v₀ hdiv₀
  have hbox : ∀ y : ℍ[ℚ, a, b] ⊗[ℚ] v₀.adicCompletion ℚ, y ∈ Submodule.localBox Λ v₀ ↔ N (Θ y) ≤ 1 := by
    intro y
    have := Set.ext_iff.mp hΘbox y
    simpa [N] using this
  let D : RamData Λ v₀ := { hO := hO, hv₀ := hv₀, hdiv := hdiv₀, Θ := Θ, hΘc := hΘc, hbox := hbox }
  have hq0 : ((D.p : ℕ) : ℚ) ≠ 0 := by exact_mod_cast D.p_ne_zero
  have hv' : (2 : ℤ) ≤ padicValRat D.p (nrd h) := hv
  refine ⟨((D.p : ℕ) : ℚ)⁻¹ • h, ?_, ?_⟩
  swap
  · rw [← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast, smul_smul, mul_inv_cancel₀ hq0, one_smul]

  have key : ((D.p : ℕ) : ℚ)⁻¹ • h ∈ Submodule.ofFiniteIdele Λ 1 := by
    rw [D.mem_ofFiniteIdele_iff_local]
    intro w
    rw [map_one, inv_one, Units.val_one, one_mul, ← TensorProduct.smul_tmul']
    by_cases hw : w = v₀
    · subst hw
      rw [hbox, theta_inv_natCast_smul Θ D.p_ne_zero, N_smul, norm_inv, Padic.norm_p, inv_inv,
        D.N_theta_tmul_one_eq hdef.1 hdef.2.1 hne, ← zpow_natCast, ← zpow_add₀ D.p_pos'.ne']
      calc (D.p : ℝ) ^ (((2 : ℕ) : ℤ) + -padicValRat D.p (nrd h)) ≤ (D.p : ℝ) ^ (0 : ℤ) :=
            zpow_le_zpow_right₀ D.one_lt_p'.le (by push_cast; omega)
        _ = 1 := zpow_zero _
    · exact smul_mem_localBox w (inv_natCast_mem_adicCompletionIntegers D.p_ne_zero (D.not_mem_of_ne hw))
        (tmul_one_mem_localBox hh w)
  rwa [Submodule.ofFiniteIdele_one Λ hO.fg hO.spanTop] at key

end PSquared
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_eq_natCast_smul_of_two_le_padicValRat_nrd.RamifiedHecke"

end RamifiedHecke
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_eq_natCast_smul_of_two_le_padicValRat_nrd.RamifiedHecke"

open RamifiedHecke in
theorem solution
    {a b : ℚ} {q' : ℕ} (hq' : q'.Prime) (hdef : IsDefiniteRamifiedExactlyAt a b q')
    {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsMaximalOrder Λ)
    {h : ℍ[ℚ, a, b]} (hh : h ∈ Λ) (hv : h = 0 ∨ 2 ≤ padicValRat q' (QuaternionAlgebra.nrd h)) :
    ∃ h' ∈ Λ, h = (q' : ℤ) • h' :=
  mainQ2 hq' hdef hΛ hh hv

end S_QuaternionAlgebra_IsMaximalOrder_exists_eq_natCast_smul_of_two_le_padicValRat_nrd
end P2MW
export P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_eq_natCast_smul_of_two_le_padicValRat_nrd (solution)
