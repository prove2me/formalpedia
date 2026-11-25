-- Prove2me | solution 1 for ReciprocityTheory.PTheta.quad_diag_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:54:21.020828+00:00
-- url     : https://prove2.me/submissions/0052cd14-4d7a-444c-a499-c9497c29be60

import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix
open ReciprocityTheory ReciprocityTheory.PTheta
variable {ι : Type*} [Fintype ι]
namespace ReciprocityTheory.PTheta
theorem _root_.solution (B : Matrix ι ι ℤ) (hB : B.IsSymm) (l : ι → ℤ) :
    ∃ k : ℤ, l ⬝ᵥ (B *ᵥ l) = l ⬝ᵥ (fun i => B i i) + 2 * k := by
  classical
  have hsq : ∀ x : ZMod 2, x * x = x := by decide
  have htwo : ∀ x : ZMod 2, x + x = 0 := by decide
  have key : ∀ f : ι → ι → ZMod 2, (∀ i j, f i j = f j i) →
      ∑ i, ∑ j, f i j = ∑ i, f i i := by
    intro f hf
    have h : ∑ p : ι × ι, (f p.1 p.2 - if p.1 = p.2 then f p.1 p.2 else 0) = 0 := by
      refine Finset.sum_involution (fun p _ => p.swap) ?_ ?_ (fun p _ => Finset.mem_univ _)
        (fun p _ => Prod.swap_swap p)
      · intro p _
        simp only [Prod.fst_swap, Prod.snd_swap]
        rw [hf p.2 p.1]
        by_cases hp : p.1 = p.2
        · simp [hp]
        · simp only [if_neg hp, if_neg (Ne.symm hp), sub_zero]
          exact htwo _
      · intro p _ hne heq
        apply hne
        have h12 : p.1 = p.2 := by
          have := congrArg Prod.fst heq
          simpa using this.symm
        simp only [if_pos h12, sub_self]
    rw [Fintype.sum_prod_type] at h
    simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
    exact sub_eq_zero.mp h
  suffices h2 : ((l ⬝ᵥ (B *ᵥ l) - l ⬝ᵥ (fun i => B i i) : ℤ) : ZMod 2) = 0 by
    obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp h2
    exact ⟨k, by push_cast at hk; linarith⟩
  push_cast [dotProduct, Matrix.mulVec]
  simp_rw [Finset.mul_sum]
  rw [sub_eq_zero]
  refine (key (fun i j => (l i : ZMod 2) * ((B i j : ZMod 2) * (l j : ZMod 2))) ?_).trans ?_
  · intro i j
    show (l i : ZMod 2) * ((B i j : ZMod 2) * (l j : ZMod 2)) =
      (l j : ZMod 2) * ((B j i : ZMod 2) * (l i : ZMod 2))
    rw [hB.apply i j]
    ring
  · refine Finset.sum_congr rfl fun i _ => ?_
    show (l i : ZMod 2) * ((B i i : ZMod 2) * (l i : ZMod 2)) = _
    rw [mul_comm (B i i : ZMod 2), ← mul_assoc, hsq]
end ReciprocityTheory.PTheta
