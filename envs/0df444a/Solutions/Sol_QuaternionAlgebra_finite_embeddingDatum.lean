-- Prove2me | solution 1 for QuaternionAlgebra.finite_embeddingDatum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/9f3d6878-3ebb-5618-a5b7-d4c9c1136d22

import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_finite_embeddingDatum

open scoped Quaternion

noncomputable section

section SqEq
open QuaternionAlgebra
variable {a b : ℚ}

theorem q15_sq_eq (α : ℍ[ℚ, a, b]) :
    α * α = (2 * α.re) • α - (α.re ^ 2 - a * α.imI ^ 2 - b * α.imJ ^ 2 + a * b * α.imK ^ 2) • (1 : ℍ[ℚ, a, b]) := by
  ext <;> simp [sq] <;> ring
end SqEq

section FiniteData

open QuaternionAlgebra

variable {a b : ℚ}

theorem q15_exists_den (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hfg : Λ.FG) :
    ∃ M : ℕ, M ≠ 0 ∧ ∀ x ∈ Λ, (∃ z : ℤ, (M : ℚ) * x.re = z) ∧ (∃ z : ℤ, (M : ℚ) * x.imI = z) ∧
      (∃ z : ℤ, (M : ℚ) * x.imJ = z) ∧ (∃ z : ℤ, (M : ℚ) * x.imK = z) := by
  classical
  obtain ⟨s, hs⟩ := hfg

  refine ⟨∏ g ∈ s, (g.re.den * g.imI.den * g.imJ.den * g.imK.den), ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr fun g _ =>
      mul_ne_zero (mul_ne_zero (mul_ne_zero g.re.den_nz g.imI.den_nz) g.imJ.den_nz) g.imK.den_nz
  set M : ℕ := ∏ g ∈ s, (g.re.den * g.imI.den * g.imJ.den * g.imK.den) with hM

  have hint : ∀ q : ℚ, (q.den : ℕ) ∣ M → ∃ z : ℤ, (M : ℚ) * q = z := by
    intro q hq
    obtain ⟨k, hk⟩ := hq
    refine ⟨k * q.num, ?_⟩
    have h1 : (M : ℚ) = (q.den : ℚ) * k := by exact_mod_cast hk
    rw [h1, mul_comm (q.den : ℚ), mul_assoc, Rat.den_mul_eq_num, Int.cast_mul, Int.cast_natCast]
  have hgen : ∀ g ∈ s, (g.re.den ∣ M) ∧ (g.imI.den ∣ M) ∧ (g.imJ.den ∣ M) ∧ (g.imK.den ∣ M) := by
    intro g hg
    have hd : g.re.den * g.imI.den * g.imJ.den * g.imK.den ∣ M := Finset.dvd_prod_of_mem _ hg
    exact ⟨dvd_trans ⟨g.imI.den * g.imJ.den * g.imK.den, by ring⟩ hd,
      dvd_trans ⟨g.re.den * g.imJ.den * g.imK.den, by ring⟩ hd,
      dvd_trans ⟨g.re.den * g.imI.den * g.imK.den, by ring⟩ hd,
      dvd_trans ⟨g.re.den * g.imI.den * g.imJ.den, by ring⟩ hd⟩
  intro x hx
  rw [← hs] at hx
  refine Submodule.span_induction (p := fun x _ => (∃ z : ℤ, (M : ℚ) * x.re = z) ∧ (∃ z : ℤ, (M : ℚ) * x.imI = z) ∧
      (∃ z : ℤ, (M : ℚ) * x.imJ = z) ∧ (∃ z : ℤ, (M : ℚ) * x.imK = z)) ?_ ?_ ?_ ?_ hx
  · intro g hg
    obtain ⟨h0, h1, h2, h3⟩ := hgen g hg
    exact ⟨hint _ h0, hint _ h1, hint _ h2, hint _ h3⟩
  · exact ⟨⟨0, by simp⟩, ⟨0, by simp⟩, ⟨0, by simp⟩, ⟨0, by simp⟩⟩
  · rintro x y - - ⟨⟨z0, h0⟩, ⟨z1, h1⟩, ⟨z2, h2⟩, ⟨z3, h3⟩⟩ ⟨⟨w0, e0⟩, ⟨w1, e1⟩, ⟨w2, e2⟩, ⟨w3, e3⟩⟩
    refine ⟨⟨z0 + w0, ?_⟩, ⟨z1 + w1, ?_⟩, ⟨z2 + w2, ?_⟩, ⟨z3 + w3, ?_⟩⟩
    · show (M : ℚ) * (x.re + y.re) = _; rw [mul_add, h0, e0, Int.cast_add]
    · show (M : ℚ) * (x.imI + y.imI) = _; rw [mul_add, h1, e1, Int.cast_add]
    · show (M : ℚ) * (x.imJ + y.imJ) = _; rw [mul_add, h2, e2, Int.cast_add]
    · show (M : ℚ) * (x.imK + y.imK) = _; rw [mul_add, h3, e3, Int.cast_add]
  · rintro k x - ⟨⟨z0, h0⟩, ⟨z1, h1⟩, ⟨z2, h2⟩, ⟨z3, h3⟩⟩
    refine ⟨⟨k * z0, ?_⟩, ⟨k * z1, ?_⟩, ⟨k * z2, ?_⟩, ⟨k * z3, ?_⟩⟩
    · show (M : ℚ) * ((k • x).re) = _
      rw [show (k • x).re = (k : ℚ) * x.re by rw [← Int.cast_smul_eq_zsmul ℚ k x]; rfl, mul_left_comm, h0, Int.cast_mul]
    · show (M : ℚ) * ((k • x).imI) = _
      rw [show (k • x).imI = (k : ℚ) * x.imI by rw [← Int.cast_smul_eq_zsmul ℚ k x]; rfl, mul_left_comm, h1, Int.cast_mul]
    · show (M : ℚ) * ((k • x).imJ) = _
      rw [show (k • x).imJ = (k : ℚ) * x.imJ by rw [← Int.cast_smul_eq_zsmul ℚ k x]; rfl, mul_left_comm, h2, Int.cast_mul]
    · show (M : ℚ) * ((k • x).imK) = _
      rw [show (k • x).imK = (k : ℚ) * x.imK by rw [← Int.cast_smul_eq_zsmul ℚ k x]; rfl, mul_left_comm, h3, Int.cast_mul]

theorem q15_datum_bounds (ha : a < 0) (hb : b < 0) {t n : ℤ} {x : ℍ[ℚ, a, b]} (hq : IsQuadraticDatum t n x) :
    x.re ^ 2 ≤ (t : ℚ) ^ 2 + 2 * |(n : ℚ)| ∧ (-a) * x.imI ^ 2 ≤ |(n : ℚ)| ∧ (-b) * x.imJ ^ 2 ≤ |(n : ℚ)| ∧
      (a * b) * x.imK ^ 2 ≤ |(n : ℚ)| := by
  have e1 := q15_sq_eq x
  have e2 : x * x = (t : ℚ) • x - (n : ℚ) • (1 : ℍ[ℚ, a, b]) := by
    have h : x * x - (t : ℚ) • x + (n : ℚ) • (1 : ℍ[ℚ, a, b]) = 0 := hq
    rw [← sub_eq_zero]; rw [← h]; abel
  have e3 : (2 * x.re) • x - (x.re ^ 2 - a * x.imI ^ 2 - b * x.imJ ^ 2 + a * b * x.imK ^ 2) • (1 : ℍ[ℚ, a, b])
      = (t : ℚ) • x - (n : ℚ) • (1 : ℍ[ℚ, a, b]) := by rw [← e1, e2]
  have hre := congrArg QuaternionAlgebra.re e3
  have hI := congrArg QuaternionAlgebra.imI e3
  have hJ := congrArg QuaternionAlgebra.imJ e3
  have hK := congrArg QuaternionAlgebra.imK e3
  simp at hre hI hJ hK

  have hS : (-a) * x.imI ^ 2 + (-b) * x.imJ ^ 2 + (a * b) * x.imK ^ 2 = x.re ^ 2 - t * x.re + n := by nlinarith
  have hIpos : 0 ≤ (-a) * x.imI ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have hJpos : 0 ≤ (-b) * x.imJ ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have hKpos : 0 ≤ (a * b) * x.imK ^ 2 := mul_nonneg (by nlinarith) (sq_nonneg _)
  have hn : (n : ℚ) ≤ |(n : ℚ)| := le_abs_self _
  have hn' : -(n : ℚ) ≤ |(n : ℚ)| := neg_le_abs _

  by_cases hc : x.imI = 0 ∧ x.imJ = 0 ∧ x.imK = 0
  · obtain ⟨h1, h2, h3⟩ := hc
    rw [h1, h2, h3] at hS ⊢
    refine ⟨?_, by simpa using abs_nonneg (n : ℚ), by simpa using abs_nonneg (n : ℚ), by simpa using abs_nonneg (n : ℚ)⟩

    nlinarith [sq_nonneg (x.re - t), sq_nonneg (x.re + t), sq_abs (n : ℚ), abs_nonneg (n : ℚ)]
  · have h2re : 2 * x.re = t := by
      rw [not_and_or, not_and_or] at hc
      rcases hc with h | h | h
      · exact hI.resolve_right h
      · exact hJ.resolve_right h
      · exact hK.resolve_right h
    have hre2 : x.re = (t : ℚ) / 2 := by linarith
    have hsq : x.re ^ 2 = (t : ℚ) ^ 2 / 4 := by rw [hre2]; ring
    have hS' : (-a) * x.imI ^ 2 + (-b) * x.imJ ^ 2 + (a * b) * x.imK ^ 2 ≤ |(n : ℚ)| := by
      have e : x.re ^ 2 - (t : ℚ) * x.re + n = n - (t : ℚ) ^ 2 / 4 := by rw [hre2]; ring
      rw [hS, e]
      nlinarith [sq_nonneg (t : ℚ)]
    refine ⟨?_, by linarith, by linarith, by linarith⟩
    rw [hsq]; nlinarith [abs_nonneg (n : ℚ), sq_nonneg (t : ℚ)]

theorem q15_natAbs_le_of_sq_le {z : ℤ} {R : ℚ} (h : ((z : ℚ)) ^ 2 ≤ R) : z.natAbs ≤ ⌈R⌉₊ := by
  have h1 : ((z.natAbs : ℤ) : ℚ) ≤ ((z : ℚ)) ^ 2 := by
    have : (z.natAbs : ℤ) ≤ z ^ 2 := Int.natAbs_le_self_sq z
    exact_mod_cast this
  have h2 : (z.natAbs : ℚ) ≤ R := by
    have : ((z.natAbs : ℤ) : ℚ) = (z.natAbs : ℚ) := Int.cast_natCast _
    linarith
  exact_mod_cast h2.trans (Nat.le_ceil R)

theorem q15_finite_embeddingDatum (ha : a < 0) (hb : b < 0) (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hfg : Λ.FG) (t n : ℤ) :
    Finite (EmbeddingDatum Λ t n) := by
  classical
  obtain ⟨M, hM0, hM⟩ := q15_exists_den Λ hfg
  have hMq : (M : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hM0

  have hapos : 0 < -a := by linarith
  have hbpos : 0 < -b := by linarith
  have habpos : 0 < a * b := by nlinarith
  set R : ℚ := (M : ℚ) ^ 2 * ((t : ℚ) ^ 2 + 2 * |(n : ℚ)|) * (1 + 1 / (-a) + 1 / (-b) + 1 / (a * b)) with hR
  set N : ℕ := ⌈R⌉₊ with hN
  let S : Finset ℤ := Finset.Icc (-(N : ℤ)) N
  let g : ℤ × ℤ × ℤ × ℤ → ℍ[ℚ, a, b] := fun z => ⟨(z.1 : ℚ) / M, (z.2.1 : ℚ) / M, (z.2.2.1 : ℚ) / M, (z.2.2.2 : ℚ) / M⟩
  have hfin : Set.Finite (g '' ((S ×ˢ S ×ˢ S ×ˢ S : Finset (ℤ × ℤ × ℤ × ℤ)) : Set (ℤ × ℤ × ℤ × ℤ))) :=
    (Finset.finite_toSet _).image g
  have hsub : {x : ℍ[ℚ, a, b] | x ∈ Λ ∧ IsQuadraticDatum t n x} ⊆ g '' ((S ×ˢ S ×ˢ S ×ˢ S : Finset (ℤ × ℤ × ℤ × ℤ)) : Set _) := by
    rintro x ⟨hxΛ, hq⟩
    obtain ⟨⟨z0, h0⟩, ⟨z1, h1⟩, ⟨z2, h2⟩, ⟨z3, h3⟩⟩ := hM x hxΛ
    obtain ⟨bre, bI, bJ, bK⟩ := q15_datum_bounds ha hb hq
    have hT : 0 ≤ (t : ℚ) ^ 2 + 2 * |(n : ℚ)| := by positivity
    have hF : 1 ≤ (1 + 1 / (-a) + 1 / (-b) + 1 / (a * b)) := by
      have : 0 ≤ 1 / (-a) + 1 / (-b) + 1 / (a * b) := by positivity
      linarith

    have hz0 : ((z0 : ℚ)) ^ 2 ≤ R := by
      rw [← h0, mul_pow, hR]
      have : x.re ^ 2 ≤ ((t : ℚ) ^ 2 + 2 * |(n : ℚ)|) * (1 + 1 / (-a) + 1 / (-b) + 1 / (a * b)) := by nlinarith
      calc (M : ℚ) ^ 2 * x.re ^ 2 ≤ (M : ℚ) ^ 2 * (((t : ℚ) ^ 2 + 2 * |(n : ℚ)|) * (1 + 1 / (-a) + 1 / (-b) + 1 / (a * b))) :=
            mul_le_mul_of_nonneg_left this (sq_nonneg _)
        _ = _ := by ring
    have key : ∀ (c : ℚ) (y : ℚ), 0 < c → c * y ^ 2 ≤ |(n : ℚ)| → 1 / c ≤ (1 + 1 / (-a) + 1 / (-b) + 1 / (a * b)) →
        ∀ z : ℤ, (M : ℚ) * y = z → ((z : ℚ)) ^ 2 ≤ R := by
      intro c y hc hcy hcF z hz
      rw [← hz, mul_pow, hR]
      have hy : y ^ 2 ≤ |(n : ℚ)| * (1 / c) := by
        rw [mul_one_div, le_div_iff₀ hc]; linarith
      have : y ^ 2 ≤ ((t : ℚ) ^ 2 + 2 * |(n : ℚ)|) * (1 + 1 / (-a) + 1 / (-b) + 1 / (a * b)) := by
        calc y ^ 2 ≤ |(n : ℚ)| * (1 / c) := hy
          _ ≤ ((t : ℚ) ^ 2 + 2 * |(n : ℚ)|) * (1 + 1 / (-a) + 1 / (-b) + 1 / (a * b)) := by
              apply mul_le_mul _ hcF (by positivity) hT
              nlinarith [abs_nonneg (n : ℚ), sq_nonneg (t : ℚ)]
      calc (M : ℚ) ^ 2 * y ^ 2 ≤ (M : ℚ) ^ 2 * (((t : ℚ) ^ 2 + 2 * |(n : ℚ)|) * (1 + 1 / (-a) + 1 / (-b) + 1 / (a * b))) :=
            mul_le_mul_of_nonneg_left this (sq_nonneg _)
        _ = _ := by ring
    have hFa : 1 / (-a) ≤ 1 + 1 / (-a) + 1 / (-b) + 1 / (a * b) := by
      have : 0 ≤ 1 / (-b) + 1 / (a * b) := by positivity
      linarith
    have hFb : 1 / (-b) ≤ 1 + 1 / (-a) + 1 / (-b) + 1 / (a * b) := by
      have : 0 ≤ 1 / (-a) + 1 / (a * b) := by positivity
      linarith
    have hFab : 1 / (a * b) ≤ 1 + 1 / (-a) + 1 / (-b) + 1 / (a * b) := by
      have : 0 ≤ 1 / (-a) + 1 / (-b) := by positivity
      linarith
    have hz1 := key (-a) x.imI hapos bI hFa z1 h1
    have hz2 := key (-b) x.imJ hbpos bJ hFb z2 h2
    have hz3 := key (a * b) x.imK habpos bK hFab z3 h3
    have memS : ∀ z : ℤ, ((z : ℚ)) ^ 2 ≤ R → z ∈ S := by
      intro z hz
      have h := q15_natAbs_le_of_sq_le hz
      rw [Finset.mem_Icc]
      constructor <;> omega
    refine ⟨(z0, z1, z2, z3), ?_, ?_⟩
    · simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe]
      exact ⟨memS z0 hz0, memS z1 hz1, memS z2 hz2, memS z3 hz3⟩
    · ext
      · show (z0 : ℚ) / M = x.re
        rw [← h0, mul_div_cancel_left₀ _ hMq]
      · show (z1 : ℚ) / M = x.imI
        rw [← h1, mul_div_cancel_left₀ _ hMq]
      · show (z2 : ℚ) / M = x.imJ
        rw [← h2, mul_div_cancel_left₀ _ hMq]
      · show (z3 : ℚ) / M = x.imK
        rw [← h3, mul_div_cancel_left₀ _ hMq]
  have hsetfin : Set.Finite {x : ℍ[ℚ, a, b] | x ∈ Λ ∧ IsQuadraticDatum t n x} := hfin.subset hsub
  exact hsetfin.to_subtype

end FiniteData

open scoped Quaternion in
theorem solution
    {a b : ℚ} (ha : a < 0) (hb : b < 0) (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hfg : Λ.FG) (t n : ℤ) :
    Finite (QuaternionAlgebra.EmbeddingDatum Λ t n) :=
  q15_finite_embeddingDatum ha hb Λ hfg t n

end

end S_QuaternionAlgebra_finite_embeddingDatum
end P2MW
export P2MW.S_QuaternionAlgebra_finite_embeddingDatum (solution)
