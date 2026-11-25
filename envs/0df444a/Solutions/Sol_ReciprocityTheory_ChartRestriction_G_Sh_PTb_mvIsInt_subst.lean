-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:29:14.694021+00:00
-- url     : https://prove2.me/submissions/ec3a9547-14ee-45d5-a4e4-f83005a61da6

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_TangentEqLcZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_mem_intRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.Sh.PTb
open MvPowerSeries ReciprocityTheory.PGsh
noncomputable section
variable {C : Type} [Field C]
private theorem hs_lemma_2 {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha0 : ∀ s, constantCoeff (a s) = 0) : HasSubst a := by
  first
  | exact hasSubst_of_constantCoeff_zero ha0
  | exact HasSubst.of_constantCoeff_zero' ha0
  | exact hasSubst_of_constantCoeff_nilpotent (fun s => by rw [ha0 s]; exact IsNilpotent.zero)
  | exact HasSubst.of_constantCoeff_nilpotent (fun s => by rw [ha0 s]; exact IsNilpotent.zero)
variable {v : AddValuation C (WithTop ℝ)} {d : ℕ}
end
end ReciprocityTheory.ChartRestriction.G.Sh.PTb
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh ReciprocityTheory.ChartRestriction.G.Sh.PTb
open MvPowerSeries ReciprocityTheory.PGsh
noncomputable section
variable {C : Type} [Field C]
namespace ReciprocityTheory.ChartRestriction.G.Sh.PTb
theorem _root_.solution {σ τ : Type} [Finite σ] (v : AddValuation C (WithTop ℝ))
    {f : MvPowerSeries σ C} (hf : MvIsInt v f) {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, MvIsInt v (a s)) (ha0 : ∀ s, constantCoeff (a s) = 0) :
    MvIsInt v (subst a f) := by
  classical
  have hS : HasSubst a := hs_lemma_2 ha0
  have hmul : ∀ p q : MvPowerSeries τ C, MvIsInt v p → MvIsInt v q → MvIsInt v (p * q) := by
    intro p q hp hq e
    rw [coeff_mul]
    exact mem_intRing.mp (Subring.sum_mem _ fun x _ =>
      Subring.mul_mem _ (mem_intRing.mpr (hp _)) (mem_intRing.mpr (hq _)))
  have hone : MvIsInt v (1 : MvPowerSeries τ C) := by
    intro e
    rw [coeff_one]
    split_ifs
    · exact mem_intRing.mp (Subring.one_mem _)
    · exact mem_intRing.mp (Subring.zero_mem _)
  have hpow : ∀ (p : MvPowerSeries τ C) (n : ℕ), MvIsInt v p → MvIsInt v (p ^ n) := by
    intro p n hp
    induction n with
    | zero => simpa using hone
    | succ n ih => rw [pow_succ]; exact hmul _ _ ih hp
  have hprod : ∀ d : σ →₀ ℕ, MvIsInt v (d.prod fun s e => a s ^ e) := by
    intro d
    show MvIsInt v (∏ s ∈ d.support, a s ^ d s)
    exact Finset.prod_induction _ (MvIsInt v) hmul hone (fun s _ => hpow _ _ (ha s))
  intro e
  rw [coeff_subst hS]
  apply mem_intRing.mp
  refine finsum_induction (fun x => x ∈ intRing v) (Subring.zero_mem _)
    (fun x y hx hy => Subring.add_mem _ hx hy) (fun d => ?_)
  rw [smul_eq_mul]
  exact Subring.mul_mem _ (mem_intRing.mpr (hf d)) (mem_intRing.mpr (hprod d e))
end ReciprocityTheory.ChartRestriction.G.Sh.PTb
