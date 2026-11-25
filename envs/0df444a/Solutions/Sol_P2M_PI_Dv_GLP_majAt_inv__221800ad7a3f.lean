-- Prove2me | solution 1 for P2M_PI_Dv_GLP_majAt_inv__221800ad7a3f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:47:25.210087+00:00
-- url     : https://prove2.me/submissions/4d4898c4-8256-417b-8397-c9e818a93acb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionLattices_MajAtZeroRight
import Theorems.Thm_P2M_PI_Dv_GLP_majAt_self__8841b9ff969c
import Theorems.Thm_P2M_PI_Dv_GLP_majAt_expand__abf1581fe1b3
import Theorems.Thm_PI_Dv_GLP_exists_nonreal
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.GLP
open Formalism.HermitianLatticesTheory NumberField
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
  (v : InfinitePlace K)
namespace PI.Dv.GLP
theorem _root_.solution [NumberField.IsTotallyComplex K] (g : V →ₗ[K] V)
    (hg : ∀ x, normAt b X v (g x) = normAt b X v x) (x y : V) :
    majAt b X v (g x) (g y) = majAt b X v x y := by
  have hs : ∀ z, majAt b X v (g z) (g z) = majAt b X v z z := fun z => by
    rw [majAt_self', majAt_self', hg]
  have key : ∀ c : K, v.embedding c * majAt b X v (g x) (g y) +
      star (v.embedding c) * star (majAt b X v (g x) (g y)) =
      v.embedding c * majAt b X v x y + star (v.embedding c) * star (majAt b X v x y) := by
    intro c
    have h1 := majAt_expand' b X v c (g x) (g y)
    have h2 := majAt_expand' b X v c x y
    have e1 : g x + c • g y = g (x + c • y) := by simp
    rw [e1, hs (x + c • y), h2, hs x, hs y] at h1
    linear_combination -h1
  obtain ⟨c0, hc0⟩ := exists_nonreal (v := v)
  have k1 := key 1
  have k2 := key c0
  simp only [map_one, star_one, one_mul] at k1
  generalize majAt b X v (g x) (g y) = a at k1 k2 ⊢
  generalize majAt b X v x y = a0 at k1 k2 ⊢
  generalize v.embedding c0 = z at k2 hc0
  have r1 := congrArg Complex.re k1
  simp only [Complex.add_re, Complex.star_def, Complex.conj_re] at r1
  have h1 : a.re = a0.re := by linarith
  have r2 := congrArg Complex.re k2
  simp only [Complex.add_re, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im] at r2
  have e2 : z.re * a.re = z.re * a0.re := by rw [h1]
  have h3 : z.im * (a.im - a0.im) = 0 := by linarith
  refine Complex.ext h1 ?_
  rcases mul_eq_zero.mp h3 with h | h
  · exact absurd h hc0
  · linarith
end PI.Dv.GLP
