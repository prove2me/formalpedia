-- Prove2me | solution 1 for PadicAlgCl.exists_norm_le_one_and_trace_eq_of_forall_traceDual_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/f0dc078c-e1cc-57d0-8a8c-4602d7652927

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicAlgCl_exists_norm_le_one_and_trace_eq_of_forall_traceDual_norm_le

set_option autoImplicit false

noncomputable section

namespace TP9C1

open Polynomial

variable (p : ℕ) [Fact p.Prime]

local notation "Ω" => PadicAlgCl p

lemma p_pos : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
lemma one_lt_p : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt

lemma norm_natCast_p : ‖(p : Ω)‖ = (p : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[p] Ω) p, norm_algebraMap', Padic.norm_p]

lemma exists_norm_eq_rpow_of_natDegree_le {x : Ω} (hx : x ≠ 0) {d : ℕ}
    (hd : (minpoly ℚ_[p] x).natDegree ≤ d) :
    ∃ k : ℤ, ‖x‖ = (p : ℝ) ^ ((k : ℝ) / (d.factorial : ℝ)) := by
  have hint : IsIntegral ℚ_[p] x := Algebra.IsIntegral.isIntegral x
  set m := (minpoly ℚ_[p] x).natDegree with hm
  have hmpos : 0 < m := minpoly.natDegree_pos hint
  have hc0 : (minpoly ℚ_[p] x).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint hx
  have hnorm : ‖x‖ = ‖(minpoly ℚ_[p] x).coeff 0‖ ^ (1 / (m : ℝ)) := by
    rw [← PadicAlgCl.spectralNorm_eq]
    exact spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow (K := ℚ_[p]) (L := Ω) x
  rw [Padic.norm_eq_zpow_neg_valuation hc0] at hnorm
  set v : ℤ := ((minpoly ℚ_[p] x).coeff 0).valuation with hv
  have hmd : m ∣ d.factorial := Nat.dvd_factorial hmpos hd
  obtain ⟨q, hq⟩ := hmd
  refine ⟨-v * q, ?_⟩
  rw [hnorm, ← Real.rpow_intCast, ← Real.rpow_mul (p_pos p).le]
  congr 1
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hmpos.ne'
  have hq0 : (q : ℝ) ≠ 0 := by
    rintro hq0
    have : (q : ℕ) = 0 := by exact_mod_cast hq0
    rw [this, mul_zero] at hq
    exact (Nat.factorial_pos d).ne' hq
  have hdf : (d.factorial : ℝ) = (m : ℝ) * (q : ℝ) := by exact_mod_cast hq
  rw [hdf]
  field_simp
  push_cast
  ring

lemma exists_norm_coe_eq_rpow (F : IntermediateField ℚ_[p] Ω) [FiniteDimensional ℚ_[p] F]
    {x : F} (hx : x ≠ 0) :
    ∃ k : ℤ, ‖(x : Ω)‖ =
      (p : ℝ) ^ ((k : ℝ) / ((Module.finrank ℚ_[p] F).factorial : ℝ)) := by
  have hx' : (x : Ω) ≠ 0 := by
    simpa using hx
  refine exists_norm_eq_rpow_of_natDegree_le p hx' ?_
  have h1 : minpoly ℚ_[p] (x : Ω) = minpoly ℚ_[p] x :=
    minpoly.algebraMap_eq (algebraMap F Ω).injective x
  rw [h1]
  exact minpoly.natDegree_le x

section trace

variable (F : IntermediateField ℚ_[p] (PadicAlgCl p)) (E : IntermediateField F (PadicAlgCl p))

lemma norm_algHom_apply (σ : E →ₐ[F] Ω) (y : E) : ‖σ y‖ = ‖(y : Ω)‖ := by
  have h1 : minpoly ℚ_[p] (σ y) = minpoly ℚ_[p] y :=
    minpoly.algHom_eq (σ.restrictScalars ℚ_[p]) σ.injective y
  have h2 : minpoly ℚ_[p] (E.val y) = minpoly ℚ_[p] y :=
    minpoly.algHom_eq (E.val.restrictScalars ℚ_[p]) (algebraMap E Ω).injective y
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm, h1]
  change spectralValue (minpoly ℚ_[p] y) = spectralValue (minpoly ℚ_[p] (E.val y))
  rw [h2]

variable [FiniteDimensional F E]

scoped instance : Algebra.IsSeparable F E := Algebra.IsSeparable.of_integral F E

lemma norm_trace_le (y : E) : ‖((Algebra.trace F E y : F) : Ω)‖ ≤ ‖(y : Ω)‖ := by
  have h := trace_eq_sum_embeddings Ω (K := F) (L := E) (x := y)
  have h' : ((Algebra.trace F E y : F) : Ω) = ∑ σ : E →ₐ[F] Ω, σ y := h
  rw [h']
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) ?_
  intro σ _
  exact (norm_algHom_apply p F E σ y).le

lemma norm_trace_le_one {y : E} (hy : ‖(y : Ω)‖ ≤ 1) :
    ‖((Algebra.trace F E y : F) : Ω)‖ ≤ 1 :=
  (norm_trace_le p F E y).trans hy

variable [FiniteDimensional ℚ_[p] F]

lemma exists_trace_ne_zero : ∃ y : E, ‖(y : Ω)‖ ≤ 1 ∧ Algebra.trace F E y ≠ 0 := by
  obtain ⟨y, hy⟩ : ∃ y : E, Algebra.trace F E y ≠ 0 := by
    by_contra h
    push Not at h
    exact Algebra.trace_ne_zero F E (LinearMap.ext h)

  obtain ⟨N, hN⟩ : ∃ N : ℕ, ‖(y : Ω)‖ ≤ (p : ℝ) ^ N := by
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt ‖(y : Ω)‖ (one_lt_p p)
    exact ⟨N, hN.le⟩
  refine ⟨algebraMap ℚ_[p] E ((p : ℚ_[p]) ^ N) * y, ?_, ?_⟩
  · have hcoe : ((algebraMap ℚ_[p] E ((p : ℚ_[p]) ^ N) * y : E) : Ω) =
        (p : Ω) ^ N * (y : Ω) := by
      push_cast
      congr 1
    rw [hcoe, norm_mul, norm_pow, norm_natCast_p, inv_pow]
    have hpN : (0 : ℝ) < (p : ℝ) ^ N := pow_pos (p_pos p) N
    calc ((p : ℝ) ^ N)⁻¹ * ‖(y : Ω)‖ ≤ ((p : ℝ) ^ N)⁻¹ * (p : ℝ) ^ N := by gcongr
      _ = 1 := inv_mul_cancel₀ hpN.ne'
  · rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, LinearMap.map_smul_of_tower]
    refine smul_ne_zero ?_ hy
    exact pow_ne_zero N (by exact_mod_cast (Fact.out : p.Prime).ne_zero)

def expo (k : ℤ) : Prop :=
  ∃ y : E, ‖(y : Ω)‖ ≤ 1 ∧ Algebra.trace F E y ≠ 0 ∧
    ‖((Algebra.trace F E y : F) : Ω)‖ =
      (p : ℝ) ^ ((k : ℝ) / ((Module.finrank ℚ_[p] F).factorial : ℝ))

omit [FiniteDimensional ℚ_[p] F] in
lemma expo_le_zero {k : ℤ} (hk : expo p F E k) : k ≤ 0 := by
  obtain ⟨y, hy, -, hk⟩ := hk
  have h1 : ‖((Algebra.trace F E y : F) : Ω)‖ ≤ 1 := norm_trace_le_one p F E hy
  rw [hk] at h1
  have hD : (0 : ℝ) < ((Module.finrank ℚ_[p] F).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  have h2 : (k : ℝ) / ((Module.finrank ℚ_[p] F).factorial : ℝ) ≤ 0 := by
    by_contra h3
    push Not at h3
    have := Real.one_lt_rpow (one_lt_p p) h3
    linarith
  have h3 : (k : ℝ) ≤ 0 := by
    by_contra h4
    push Not at h4
    exact absurd (div_pos h4 hD) (not_lt.mpr h2)
  exact_mod_cast h3

lemma exists_max_trace : ∃ y₀ : E, ‖(y₀ : Ω)‖ ≤ 1 ∧ Algebra.trace F E y₀ ≠ 0 ∧
    ∀ y : E, ‖(y : Ω)‖ ≤ 1 →
      ‖((Algebra.trace F E y : F) : Ω)‖ ≤ ‖((Algebra.trace F E y₀ : F) : Ω)‖ := by
  have hinh : ∃ k : ℤ, expo p F E k := by
    obtain ⟨y, hy, hty⟩ := exists_trace_ne_zero p F E
    obtain ⟨k, hk⟩ := exists_norm_coe_eq_rpow p F hty
    exact ⟨k, y, hy, hty, hk⟩
  obtain ⟨k₀, ⟨y₀, hy₀, hty₀, hk₀⟩, hmax⟩ :=
    Int.exists_greatest_of_bdd ⟨0, fun k hk => expo_le_zero p F E hk⟩ hinh
  refine ⟨y₀, hy₀, hty₀, fun y hy => ?_⟩
  by_cases hty : Algebra.trace F E y = 0
  · rw [hty]
    simp
  obtain ⟨k, hk⟩ := exists_norm_coe_eq_rpow p F hty
  have hkk : k ≤ k₀ := hmax k ⟨y, hy, hty, hk⟩
  rw [hk, hk₀]
  refine Real.rpow_le_rpow_of_exponent_le (one_lt_p p).le ?_
  have hD : (0 : ℝ) < ((Module.finrank ℚ_[p] F).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  exact div_le_div_of_nonneg_right (by exact_mod_cast hkk) hD.le

end trace

theorem main (F : IntermediateField ℚ_[p] Ω) [FiniteDimensional ℚ_[p] F]
    (E : IntermediateField F Ω) [FiniteDimensional F E] (r : ℝ)
    (hE : ∀ z : E, (∀ w : E, ‖(w : Ω)‖ ≤ 1 →
        ‖((Algebra.trace F E (z * w) : F) : Ω)‖ ≤ 1) → ‖(z : Ω)‖ ≤ r)
    (x : F) (hx : ‖(x : Ω)‖ ≤ r⁻¹) :
    ∃ y : E, ‖(y : Ω)‖ ≤ 1 ∧ Algebra.trace F E y = x := by
  obtain ⟨y₀, hy₀, hty₀, hmax⟩ := exists_max_trace p F E
  set t₀ : F := Algebra.trace F E y₀ with ht₀
  have ht₀' : (t₀ : Ω) ≠ 0 := by simpa using hty₀
  have hnt₀ : 0 < ‖(t₀ : Ω)‖ := norm_pos_iff.mpr ht₀'

  have hz : ‖((algebraMap F E t₀⁻¹ : E) : Ω)‖ ≤ r := by
    refine hE _ fun w hw => ?_
    have h1 : Algebra.trace F E (algebraMap F E t₀⁻¹ * w) = t₀⁻¹ * Algebra.trace F E w := by
      rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, map_smul, smul_eq_mul]
    rw [h1]
    push_cast
    rw [norm_mul, norm_inv, inv_mul_le_iff₀ hnt₀, mul_one]
    exact hmax w hw
  have hzr : ‖(t₀ : Ω)‖⁻¹ ≤ r := by
    have : ((algebraMap F E t₀⁻¹ : E) : Ω) = (t₀ : Ω)⁻¹ := by
      rw [IntermediateField.coe_algebraMap_apply]
      push_cast
      rfl
    rw [this, norm_inv] at hz
    exact hz
  have hr : 0 < r := lt_of_lt_of_le (inv_pos.mpr hnt₀) hzr
  have hxt : ‖(x : Ω)‖ ≤ ‖(t₀ : Ω)‖ := by
    refine hx.trans ?_
    rw [inv_le_comm₀ hr hnt₀]
    exact hzr
  refine ⟨algebraMap F E (x * t₀⁻¹) * y₀, ?_, ?_⟩
  · have hcoe : ((algebraMap F E (x * t₀⁻¹) * y₀ : E) : Ω) = (x : Ω) * (t₀ : Ω)⁻¹ * (y₀ : Ω) := by
      push_cast
      rfl
    rw [hcoe, norm_mul, norm_mul, norm_inv]
    have h1 : ‖(x : Ω)‖ * ‖(t₀ : Ω)‖⁻¹ ≤ 1 := by
      rw [mul_inv_le_iff₀ hnt₀, one_mul]
      exact hxt
    calc ‖(x : Ω)‖ * ‖(t₀ : Ω)‖⁻¹ * ‖(y₀ : Ω)‖ ≤ 1 * 1 := by
          gcongr
      _ = 1 := one_mul 1
  · rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, map_smul, smul_eq_mul, ← ht₀,
      mul_assoc, inv_mul_cancel₀ hty₀, mul_one]

end TP9C1
p2m_reactivate "P2MW.S_PadicAlgCl_exists_norm_le_one_and_trace_eq_of_forall_traceDual_norm_le.TP9C1"

end
p2m_reactivate "P2MW.S_PadicAlgCl_exists_norm_le_one_and_trace_eq_of_forall_traceDual_norm_le.TP9C1"

theorem solution
    (p : ℕ) [Fact p.Prime] (F : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] F]
    (E : IntermediateField F (PadicAlgCl p)) [FiniteDimensional F E] (r : ℝ)
    (hE : ∀ z : E, (∀ w : E, ‖(w : PadicAlgCl p)‖ ≤ 1 →
        ‖((Algebra.trace F E (z * w) : F) : PadicAlgCl p)‖ ≤ 1) → ‖(z : PadicAlgCl p)‖ ≤ r)
    (x : F) (hx : ‖(x : PadicAlgCl p)‖ ≤ r⁻¹) :
    ∃ y : E, ‖(y : PadicAlgCl p)‖ ≤ 1 ∧ Algebra.trace F E y = x :=
  TP9C1.main p F E r hE x hx

end S_PadicAlgCl_exists_norm_le_one_and_trace_eq_of_forall_traceDual_norm_le
end P2MW
export P2MW.S_PadicAlgCl_exists_norm_le_one_and_trace_eq_of_forall_traceDual_norm_le (solution)
