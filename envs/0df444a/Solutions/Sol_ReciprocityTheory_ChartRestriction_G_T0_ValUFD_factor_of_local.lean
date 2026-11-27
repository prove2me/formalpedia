-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.ValUFD.factor_of_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:28:27.546117+00:00
-- url     : https://prove2.me/submissions/51ce0944-758d-4248-b7a6-3820a11de7b4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValUFD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValUFD_gen_prime
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValUFD_factor_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open ReciprocityTheory.ChartRestriction.G.T0.ValUFD
variable {R F : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] [Field F]
  [Algebra R F] [IsFractionRing R F]
variable {gen : Ideal R → R}
namespace ReciprocityTheory.ChartRestriction.G.T0.ValUFD
theorem _root_.solution (gen : Ideal R → R)
    (hgen : ∀ p : Ideal R, p.IsPrime → p.height = 1 → p = Ideal.span {gen p})
    (z : F) (hz : z ≠ 0) (n : Ideal R → ℤ)
    (hn : ∀ p : Ideal R, p.IsPrime → p.height = 1 → ∃ a s : R, a ∉ p ∧ s ∉ p ∧
      z * algebraMap R F s = algebraMap R F (gen p) ^ n p * algebraMap R F a) :
    {p : Ideal R | p.IsPrime ∧ p.height = 1 ∧ n p ≠ 0}.Finite ∧
      ∃ κ : R, IsUnit κ ∧
        z = algebraMap R F κ *
          ∏ᶠ (p : Ideal R) (_ : p ∈ {p : Ideal R | p.IsPrime ∧ p.height = 1}),
            algebraMap R F (gen p) ^ n p := by
  classical
  set H := {p : Ideal R | p.IsPrime ∧ p.height = 1} with hH
  have hinj := IsFractionRing.injective R F
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := R) z
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hyF : algebraMap R F y ≠ 0 := by rw [Ne, map_eq_zero_iff _ hinj]; exact hy0
  have hx0 : x ≠ 0 := by rintro rfl; rw [map_zero, zero_div] at hxy; exact hz hxy.symm
  have hzx : z * algebraMap R F y = algebraMap R F x := by rw [← hxy, div_mul_cancel₀ _ hyF]
  have hloc : ∀ p ∈ H, n p = (multiplicity (gen p) x : ℤ) - multiplicity (gen p) y := by
    intro p hp
    obtain ⟨a, s, ha, hs, he⟩ := hn p hp.1 hp.2
    have hg := gen_prime hgen hp
    have hgp := hgen p hp.1 hp.2
    have hna : ¬ gen p ∣ a := fun h => ha (by rw [hgp]; exact Ideal.mem_span_singleton.mpr h)
    have hns : ¬ gen p ∣ s := fun h => hs (by rw [hgp]; exact Ideal.mem_span_singleton.mpr h)
    have ha0 : a ≠ 0 := by rintro rfl; exact hna (dvd_zero _)
    have hs0 : s ≠ 0 := by rintro rfl; exact hns (dvd_zero _)
    have hGne : algebraMap R F (gen p) ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ hinj]; exact hg.ne_zero
    have h1 : algebraMap R F (gen p) ^ (n p).toNat =
        algebraMap R F (gen p) ^ n p * algebraMap R F (gen p) ^ (-n p).toNat := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hGne]; congr 1; omega
    have hR : x * s * gen p ^ (-n p).toNat = y * a * gen p ^ (n p).toNat := by
      apply hinj
      simp only [map_mul, map_pow]
      rw [h1, ← hzx]
      linear_combination (algebraMap R F y * algebraMap R F (gen p) ^ (-n p).toNat) * he
    have hm := congrArg (multiplicity (gen p)) hR
    have hf : ∀ b : R, b ≠ 0 → FiniteMultiplicity (gen p) b := fun b hb =>
      FiniteMultiplicity.of_prime_left hg hb
    have hpw : ∀ k : ℕ, gen p ^ k ≠ 0 := fun k => pow_ne_zero k hg.ne_zero
    rw [multiplicity_mul hg (hf _ (mul_ne_zero (mul_ne_zero hx0 hs0) (hpw _))),
      multiplicity_mul hg (hf _ (mul_ne_zero hx0 hs0)),
      multiplicity_mul hg (hf _ (mul_ne_zero (mul_ne_zero hy0 ha0) (hpw _))),
      multiplicity_mul hg (hf _ (mul_ne_zero hy0 ha0)),
      multiplicity_pow_self_of_prime hg, multiplicity_pow_self_of_prime hg,
      multiplicity_eq_zero.mpr hns, multiplicity_eq_zero.mpr hna] at hm
    omega
  obtain ⟨hfx, κx, hκx, hx⟩ := factor_int (F := F) hgen x hx0
  obtain ⟨hfy, κy, hκy, hyq⟩ := factor_int (F := F) hgen y hy0
  have hfinn : {p : Ideal R | p.IsPrime ∧ p.height = 1 ∧ n p ≠ 0}.Finite := by
    refine (hfx.union hfy).subset ?_
    rintro p ⟨h1, h2, h3⟩
    rw [hloc p ⟨h1, h2⟩] at h3
    by_cases hx' : multiplicity (gen p) x = 0
    · refine Or.inr ⟨⟨h1, h2⟩, fun h => h3 ?_⟩
      rw [hx', h]; simp
    · exact Or.inl ⟨⟨h1, h2⟩, hx'⟩
  refine ⟨hfinn, ?_⟩
  set fn : Ideal R → F := fun p => algebraMap R F (gen p) ^ n p with hfn
  set fy : Ideal R → F := fun p => algebraMap R F (gen p) ^ (multiplicity (gen p) y : ℤ) with hfy'
  have hsp : ∀ p ∈ H, algebraMap R F (gen p) ^ (multiplicity (gen p) x : ℤ) = fn p * fy p := by
    intro p hp
    have hGne : algebraMap R F (gen p) ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ hinj]; exact (gen_prime hgen hp).ne_zero
    simp only [hfn, hfy']
    rw [← zpow_add₀ hGne, hloc p hp]; congr 1; ring
  have hfin1 : (H ∩ Function.mulSupport fn).Finite :=
    hfinn.subset fun p ⟨hp, hs⟩ => ⟨hp.1, hp.2, fun h0 => hs (by simp [hfn, h0])⟩
  have hfin2 : (H ∩ Function.mulSupport fy).Finite :=
    hfy.subset fun p ⟨hp, hs⟩ => ⟨hp, fun h0 => hs (by simp [hfy', h0])⟩
  have hPx : ∏ᶠ (p : Ideal R) (_ : p ∈ H),
      algebraMap R F (gen p) ^ (multiplicity (gen p) x : ℤ) =
      (∏ᶠ (p : Ideal R) (_ : p ∈ H), fn p) * ∏ᶠ (p : Ideal R) (_ : p ∈ H), fy p := by
    rw [finprod_mem_congr rfl hsp, finprod_mem_mul_distrib' hfin1 hfin2]
  rw [hPx] at hx
  have hyq' : algebraMap R F y = algebraMap R F κy * ∏ᶠ (p : Ideal R) (_ : p ∈ H), fy p := hyq
  have hPy : (∏ᶠ (p : Ideal R) (_ : p ∈ H), fy p) ≠ 0 := by
    intro h; rw [h, mul_zero] at hyq'; exact hyF hyq'
  have hκy0 : algebraMap R F κy ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ hinj]; exact hκy.ne_zero
  refine ⟨κx * ↑hκy.unit⁻¹, hκx.mul (Units.isUnit _), ?_⟩
  have hu1 : algebraMap R F κy * algebraMap R F ↑hκy.unit⁻¹ = 1 := by
    have h2 : κy * ↑hκy.unit⁻¹ = 1 := by simp
    rw [← map_mul, h2, map_one]
  apply mul_right_cancel₀ (mul_ne_zero hκy0 hPy)
  have e1 : z * (algebraMap R F κy * ∏ᶠ (p : Ideal R) (_ : p ∈ H), fy p) = algebraMap R F x := by
    rw [← hyq', hzx]
  rw [e1, hx, map_mul]
  linear_combination (-(algebraMap R F κx * (∏ᶠ (p : Ideal R) (_ : p ∈ H), fn p) *
    ∏ᶠ (p : Ideal R) (_ : p ∈ H), fy p)) * hu1
end ReciprocityTheory.ChartRestriction.G.T0.ValUFD
