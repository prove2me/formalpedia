-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.v_zeta_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:27:15.697627+00:00
-- url     : https://prove2.me/submissions/e11ede48-51a1-4f21-9286-c41373220d0b

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PowerSeriesCoeffGaps_exists_real
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PowerSeriesCoeffGaps_v_one_sub_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps
open ReciprocityTheory.PGsh PowerSeries
noncomputable section
variable {K : Type*} [Field K] (v : AddValuation K (WithTop ℝ))
namespace ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps
theorem _root_.solution {p : ℕ} (hp : p.Prime) (hp1 : v (p : K) = 1) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) : v (ζ - 1) = ((1 / ((p : ℝ) - 1) : ℝ) : WithTop ℝ) := by
  classical
  have := Fact.mk hp
  have : NeZero p := ⟨hp.ne_zero⟩
  have hall : ∀ μ ∈ primitiveRoots p K, v (1 - μ) = v (1 - ζ) := by
    intro μ hμ
    have hμ' : IsPrimitiveRoot μ p := (mem_primitiveRoots hp.pos).mp hμ
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hμ'.pow_eq_one
    obtain ⟨j, -, hj⟩ := hμ'.eq_pow_of_pow_eq_one hζ.pow_eq_one
    exact le_antisymm (v_one_sub_le v hp.ne_zero hμ'.pow_eq_one j hj.symm)
      (v_one_sub_le v hp.ne_zero hζ.pow_eq_one i hi.symm)
  have hprod : (p : K) = ∏ μ ∈ primitiveRoots p K, (1 - μ) := by
    have := congrArg (Polynomial.eval (1 : K))
      (Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ)
    rw [Polynomial.eval_one_cyclotomic_prime, Polynomial.eval_prod] at this
    simpa using this
  have hsum : ∀ s : Finset K, (∀ μ ∈ s, v (1 - μ) = v (1 - ζ)) →
      v (∏ μ ∈ s, (1 - μ)) = s.card • v (1 - ζ) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simp
    | insert a s ha ih =>
      intro h
      rw [Finset.prod_insert ha, v.map_mul, h a (Finset.mem_insert_self a s),
        ih (fun μ hμ => h μ (Finset.mem_insert_of_mem hμ)), Finset.card_insert_of_notMem ha,
        succ_nsmul']
  have hcard : (primitiveRoots p K).card = p - 1 := by
    rw [hζ.card_primitiveRoots, Nat.totient_prime hp]
  have hmain : v (p : K) = (p - 1) • v (1 - ζ) := by rw [hprod, hsum _ hall, hcard]
  have hne : (1 : K) - ζ ≠ 0 := sub_ne_zero.mpr (hζ.ne_one hp.one_lt).symm
  obtain ⟨r, hr⟩ := exists_real v hne
  rw [hp1, hr, ← WithTop.coe_nsmul, ← WithTop.coe_one] at hmain
  have hr' : (1 : ℝ) = (p - 1 : ℕ) • r := WithTop.coe_injective hmain
  have e : ζ - 1 = -(1 - ζ) := by ring
  rw [e, v.map_neg, hr]
  congr 1
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  rw [nsmul_eq_mul, Nat.cast_sub hp.one_le, Nat.cast_one] at hr'
  rw [eq_div_iff (by linarith)]
  linarith
end ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps
