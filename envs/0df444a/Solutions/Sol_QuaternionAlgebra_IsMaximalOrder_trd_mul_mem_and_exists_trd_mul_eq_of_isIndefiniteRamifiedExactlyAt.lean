-- Prove2me | solution 1 for QuaternionAlgebra.IsMaximalOrder.trd_mul_mem_and_exists_trd_mul_eq_of_isIndefiniteRamifiedExactlyAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/381cb42e-6484-505b-adc5-7e86b49e5de5

import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_dvd_trd_of_dvd_nrd_of_isIndefiniteRamifiedExactlyAt
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_forall_exists_intCast_eq_trd_mul_iff_mul_mem_of_isIndefiniteRamifiedExactlyAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_trd_mul_mem_and_exists_trd_mul_eq_of_isIndefiniteRamifiedExactlyAt
p2m_attr_erase "instance" "CerednikDrinfeld.CosetGraph.projGraphAction CerednikDrinfeld.CosetGraph.projVertMulAction CerednikDrinfeld.CosetGraph.awayVertMulAction CerednikDrinfeld.CosetGraph.actionKer_normal CerednikDrinfeld.CosetGraph.vertMulAction CerednikDrinfeld.Mumford.dartAction"
p2m_attr_erase "simp" "QuaternionAlgebra.ClassSet.map_mk QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open scoped Quaternion
open QuaternionAlgebra

namespace TraceImage29

variable {a b : ℚ}

theorem trd_smul' (c : ℚ) (x : ℍ[ℚ, a, b]) : trd (c • x) = c * trd x := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x; simp [trd]; ring

theorem trd_neg' (x : ℍ[ℚ, a, b]) : trd (-x) = -trd x := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x; simp [trd]

theorem trd_add' (x y : ℍ[ℚ, a, b]) : trd (x + y) = trd x + trd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x; obtain ⟨y₀, y₁, y₂, y₃⟩ := y; simp [trd]; ring

theorem nrd_mul' (x y : ℍ[ℚ, a, b]) : nrd (x * y) = nrd x * nrd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x; obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_mul_mk, nrd_mk]; ring

theorem nrd_eq_of_re (x : ℍ[ℚ, a, b]) : nrd x = 2 * x.re ^ 2 - (x * x).re := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x; simp [nrd]; ring

theorem re_eq_zero_of_mul_self {μ : ℍ[ℚ, a, b]} {s : ℚ} (hs : s < 0) (hμ : μ * μ = s • (1 : ℍ[ℚ, a, b])) :
    μ.re = 0 := by
  obtain ⟨m₀, m₁, m₂, m₃⟩ := μ
  by_contra h
  have hI := congrArg QuaternionAlgebra.imI hμ
  have hJ := congrArg QuaternionAlgebra.imJ hμ
  have hK := congrArg QuaternionAlgebra.imK hμ
  have hR := congrArg QuaternionAlgebra.re hμ
  simp only [QuaternionAlgebra.mk_mul_mk] at hI hJ hK hR
  simp at hI hJ hK hR h
  have h1 : m₁ = 0 := by
    have : m₀ * m₁ * 2 = 0 := by linarith
    simpa [h] using this
  have h2 : m₂ = 0 := by
    have : m₀ * m₂ * 2 = 0 := by linarith
    simpa [h] using this
  have h3 : m₃ = 0 := by
    have : m₀ * m₃ * 2 = 0 := by nlinarith
    simpa [h] using this
  subst h1 h2 h3
  have : m₀ * m₀ = s := by simpa using hR
  nlinarith

theorem exists_int_of_smul_one_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (r : ℚ)
    (hr : r • (1 : ℍ[ℚ, a, b]) ∈ Λ) : ∃ k : ℤ, (k : ℚ) = r := by
  obtain ⟨⟨n, hn⟩, ⟨t, ht⟩⟩ := QuaternionAlgebra.IsOrder.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hΛ hr
  have hn' : (n : ℚ) = r ^ 2 := by rw [hn]; simp [nrd]
  have ht' : (t : ℚ) = 2 * r := by rw [ht]; simp [trd]

  have h4 : t ^ 2 = 4 * n := by
    have : ((t : ℚ)) ^ 2 = 4 * (n : ℚ) := by rw [ht', hn']; ring
    exact_mod_cast this
  have hte : Even t := by
    have : Even (t ^ 2) := ⟨2 * n, by rw [h4]; ring⟩
    exact (Int.even_pow.mp this).1
  obtain ⟨s, hs⟩ := hte
  refine ⟨s, ?_⟩
  have : (t : ℚ) = 2 * s := by rw [hs]; push_cast; ring
  linarith

end TraceImage29

open TraceImage29

theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b]))) :
    (∀ z ∈ Λ, ∃ t : ℤ, trd ((μ : ℍ[ℚ, a, b]) * z) = ((q * q' : ℕ) : ℚ) * t) ∧
    (∃ z ∈ Λ, trd ((μ : ℍ[ℚ, a, b]) * z) = ((q * q' : ℕ) : ℚ)) := by
  have hΛo : IsOrder Λ := hΛ.isOrder
  set QQ : ℚ := ((q * q' : ℕ) : ℚ) with hQQ
  have hQQpos : 0 < QQ := by
    rw [hQQ]; exact_mod_cast Nat.mul_pos (Fact.out : q.Prime).pos (Fact.out : q'.Prime).pos
  have hQQne : QQ ≠ 0 := hQQpos.ne'
  set m : ℍ[ℚ, a, b] := (μ : ℍ[ℚ, a, b]) with hm
  have hmm : m * m = (-QQ) • (1 : ℍ[ℚ, a, b]) := by rw [hμ, neg_smul]
  have hre : m.re = 0 := re_eq_zero_of_mul_self (by linarith) hmm
  have hnrdμ : nrd m = QQ := by
    rw [nrd_eq_of_re, hre, hmm]; simp

  have h1 : ∀ z ∈ Λ, ∃ t : ℤ, trd (m * z) = QQ * t := by
    intro z hz
    have hmz : m * z ∈ Λ := hΛo.mul_mem μ.2 hz
    obtain ⟨⟨nz, hnz⟩, -⟩ := QuaternionAlgebra.IsOrder.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hΛo hz
    have hn : nrd (m * z) = QQ * nz := by rw [nrd_mul', hnrdμ, hnz]
    obtain ⟨t₁, ht₁⟩ := QuaternionAlgebra.IsMaximalOrder.dvd_trd_of_dvd_nrd_of_isIndefiniteRamifiedExactlyAt hB Λ hΛ q
      (Or.inl rfl) _ hmz ⟨(q' : ℤ) * nz, by rw [hn, hQQ]; push_cast; ring⟩
    obtain ⟨t₂, ht₂⟩ := QuaternionAlgebra.IsMaximalOrder.dvd_trd_of_dvd_nrd_of_isIndefiniteRamifiedExactlyAt hB Λ hΛ q'
      (Or.inr rfl) _ hmz ⟨(q : ℤ) * nz, by rw [hn, hQQ]; push_cast; ring⟩
    obtain ⟨-, ⟨t₀, ht₀⟩⟩ := QuaternionAlgebra.IsOrder.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hΛo hmz
    have dq : (q : ℤ) ∣ t₀ := ⟨t₁, by exact_mod_cast ht₀.trans ht₁⟩
    have dq' : (q' : ℤ) ∣ t₀ := ⟨t₂, by exact_mod_cast ht₀.trans ht₂⟩
    have hcop : IsCoprime (q : ℤ) (q' : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes Fact.out Fact.out).mpr (Ne.symm hqq'))
    obtain ⟨t, ht⟩ := IsCoprime.mul_dvd hcop dq dq'
    exact ⟨t, by rw [← ht₀, ht, hQQ]; push_cast; ring⟩
  refine ⟨h1, ?_⟩

  let S : AddSubgroup ℤ :=
    { carrier := {t : ℤ | ∃ z ∈ Λ, trd (m * z) = (t : ℚ)}
      zero_mem' := ⟨0, zero_mem _, by simp [trd]⟩
      add_mem' := by
        rintro s t ⟨z, hz, hzs⟩ ⟨w, hw, hws⟩
        exact ⟨z + w, add_mem hz hw, by rw [mul_add, trd_add', hzs, hws]; push_cast; ring⟩
      neg_mem' := by
        rintro s ⟨z, hz, hzs⟩
        exact ⟨-z, neg_mem hz, by rw [mul_neg, trd_neg', hzs]; push_cast; ring⟩ }
  obtain ⟨d, hd⟩ := Int.subgroup_cyclic S
  have hdS : d ∈ S := by rw [hd]; exact AddSubgroup.subset_closure rfl
  obtain ⟨z₀, hz₀, hz₀d⟩ := hdS
  have hdiv : ∀ z ∈ Λ, ∃ k : ℤ, trd (m * z) = (d : ℚ) * k := by
    intro z hz
    obtain ⟨-, ⟨t₀, ht₀⟩⟩ := QuaternionAlgebra.IsOrder.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hΛo
      (hΛo.mul_mem μ.2 hz)
    have ht₀S : t₀ ∈ S := ⟨z, hz, ht₀.symm⟩
    rw [hd, AddSubgroup.mem_closure_singleton] at ht₀S
    obtain ⟨k, hk⟩ := ht₀S
    have hk' : t₀ = d * k := by rw [← hk, smul_eq_mul, mul_comm]
    exact ⟨k, by rw [← ht₀, hk', Int.cast_mul]⟩

  have hcod : ∀ s : ℚ, (∀ x ∈ Λ, ∃ n : ℤ, (n : ℚ) = s * trd (m * x)) → ∃ k : ℤ, (k : ℚ) = -(s * QQ) := by
    intro s hs
    have hmem := (QuaternionAlgebra.IsMaximalOrder.forall_exists_intCast_eq_trd_mul_iff_mul_mem_of_isIndefiniteRamifiedExactlyAt
      hqq' hB Λ hΛ μ hμ (s • m)).mp (fun x hx => by
        obtain ⟨n, hn⟩ := hs x hx
        exact ⟨n, by rw [hn, smul_mul_assoc, trd_smul']⟩)
    have : (μ : ℍ[ℚ, a, b]) * (s • m) = (-(s * QQ)) • (1 : ℍ[ℚ, a, b]) := by
      rw [mul_smul_comm, ← hm, hmm, smul_smul, mul_neg]
    rw [this] at hmem
    exact exists_int_of_smul_one_mem hΛo _ hmem
  by_cases hd0 : d = 0
  ·
    exfalso
    obtain ⟨k, hk⟩ := hcod (1 / (2 * QQ)) (fun x hx => ⟨0, by
      obtain ⟨k, hk⟩ := hdiv x hx
      rw [hk, hd0]; simp⟩)
    have : (k : ℚ) = -(1 / 2) := by rw [hk]; field_simp
    have : (2 * k : ℚ) = -1 := by rw [this]; ring
    have : 2 * k = -1 := by exact_mod_cast this
    omega
  · obtain ⟨k, hk⟩ := hcod (1 / (d : ℚ)) (fun x hx => by
      obtain ⟨k, hk⟩ := hdiv x hx
      exact ⟨k, by rw [hk]; field_simp⟩)

    obtain ⟨t, ht⟩ := h1 z₀ hz₀
    have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd0
    have e1 : (k : ℚ) * d = -QQ := by rw [hk]; field_simp
    have e2 : (d : ℚ) = QQ * t := by rw [← hz₀d, ht]
    have e3 : QQ * (t * k + 1) = 0 := by
      rw [e2] at e1
      linear_combination e1
    have e4 : (t : ℚ) * k = -1 := by
      have := (mul_eq_zero.mp e3).resolve_left hQQne
      linarith
    have e5 : t * k = -1 := by exact_mod_cast e4
    rcases Int.eq_one_or_neg_one_of_mul_eq_neg_one e5 with rfl | rfl
    · exact ⟨z₀, hz₀, by rw [ht]; push_cast; ring⟩
    · exact ⟨-z₀, neg_mem hz₀, by rw [mul_neg, trd_neg', ht]; push_cast; ring⟩

end S_QuaternionAlgebra_IsMaximalOrder_trd_mul_mem_and_exists_trd_mul_eq_of_isIndefiniteRamifiedExactlyAt
end P2MW
export P2MW.S_QuaternionAlgebra_IsMaximalOrder_trd_mul_mem_and_exists_trd_mul_eq_of_isIndefiniteRamifiedExactlyAt (solution)
