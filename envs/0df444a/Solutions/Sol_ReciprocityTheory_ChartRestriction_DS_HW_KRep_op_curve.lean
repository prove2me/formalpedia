-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.KRep.op_curve
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:10:19.571593+00:00
-- url     : https://prove2.me/submissions/cbb94b49-50e4-4439-a17d-add6568e567d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_DerivExistsAllPosStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_SingleMulJmComm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_Stable
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_onep_KG_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.HW
namespace KRep
theorem _root_.solution {ε : Fin n → Bool} (R : KRep ε)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (γ : ℝ → KG ε)
    (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) (t : ℝ) :
    R.op (γ t) = NormedSpace.exp ((t : ℂ) • R.dτ X) := by
  set A := R.dτ X with hA
  have hmulK : ∀ a b : KG ε, toMK (a * b) = toMK a * toMK b := fun a b => rfl
  have honeK : toMK (1 : KG ε) = 1 := rfl
  have hγadd : ∀ s u : ℝ, γ (s + u) = γ s * γ u := by
    intro s u
    apply onep_KG_ext
    rw [hmulK, hγ, hγ, hγ, Complex.ofReal_add, add_smul]
    exact Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left _).smul_right _)
  have hop : ∀ a b : KG ε, R.op (a * b) = R.op a * R.op b := by
    intro a b
    simp [KRep.op]
  have hγ0 : γ 0 = 1 := by
    apply onep_KG_ext
    rw [hγ, honeK]
    simp
  have hd0 : HasDerivAt (fun t => R.op (γ t)) A 0 := R.hasDeriv X hX γ hγ
  have hd : ∀ s : ℝ, HasDerivAt (fun t => R.op (γ t)) (R.op (γ s) * A) s := by
    intro s
    have h1 : HasDerivAt (fun t => R.op (γ (t - s))) A s :=
      HasDerivAt.comp_sub_const (f := fun t => R.op (γ t)) s s (by rwa [sub_self])
    refine (h1.const_mul (R.op (γ s))).congr_of_eventuallyEq ?_
    filter_upwards with u
    rw [← hop, ← hγadd, add_sub_cancel]
  have hE : ∀ s : ℝ, HasDerivAt (fun u : ℝ => NormedSpace.exp (u • -A))
      (NormedSpace.exp (s • -A) * -A) s := fun s => hasDerivAt_exp_smul_const (-A) s
  have hcomm : ∀ s : ℝ, Commute A (NormedSpace.exp (s • -A)) := fun s =>
    (((Commute.refl A).neg_right).smul_right s).exp_right
  have hh : ∀ s : ℝ, HasDerivAt (fun u => R.op (γ u) * NormedSpace.exp (u • -A)) 0 s := by
    intro s
    have := (hd s).mul (hE s)
    have key : R.op (γ s) * A * NormedSpace.exp (s • -A) +
        R.op (γ s) * (NormedSpace.exp (s • -A) * -A) = 0 := by
      rw [mul_assoc, (hcomm s).eq, mul_neg, mul_neg, add_neg_cancel]
    rw [key] at this
    exact this
  have hconst : ∀ u : ℝ, R.op (γ u) * NormedSpace.exp (u • -A) = 1 := by
    intro u
    have := is_const_of_deriv_eq_zero (f := fun u => R.op (γ u) * NormedSpace.exp (u • -A))
      (fun s => (hh s).differentiableAt) (fun s => (hh s).deriv) u 0
    rw [this]
    simp [hγ0, KRep.op]
  have hinv : NormedSpace.exp (t • -A) * NormedSpace.exp (t • A) = 1 := by
    have hk : ∀ s : ℝ, HasDerivAt (fun u : ℝ => NormedSpace.exp (u • -A) * NormedSpace.exp (u • A))
        0 s := by
      intro s
      have := (hE s).mul (hasDerivAt_exp_smul_const A s)
      have hcF : Commute (NormedSpace.exp (s • A)) A := ((Commute.refl A).smul_left s).exp_left
      have key : NormedSpace.exp (s • -A) * -A * NormedSpace.exp (s • A) +
          NormedSpace.exp (s • -A) * (NormedSpace.exp (s • A) * A) = 0 := by
        rw [mul_assoc, neg_mul, mul_neg, hcF.eq, neg_add_cancel]
      rw [key] at this
      exact this
    have := is_const_of_deriv_eq_zero
      (f := fun u : ℝ => NormedSpace.exp (u • -A) * NormedSpace.exp (u • A))
      (fun s => (hk s).differentiableAt) (fun s => (hk s).deriv) t 0
    rw [this]
    simp
  calc R.op (γ t) = R.op (γ t) * (NormedSpace.exp (t • -A) * NormedSpace.exp (t • A)) := by
        rw [hinv, mul_one]
    _ = NormedSpace.exp (t • A) := by rw [← mul_assoc, hconst, one_mul]
    _ = NormedSpace.exp ((t : ℂ) • A) := by rw [Complex.coe_smul]
end KRep
end ReciprocityTheory.ChartRestriction.DS.HW
