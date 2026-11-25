-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfB.Ms_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:48:42.798618+00:00
-- url     : https://prove2.me/submissions/3fd987b0-6502-4fcd-96a4-29cc41a9df45

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ModeHalfStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ModeHalfStatementPfB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero


section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up
namespace ModeHalfB
open Matrix NumberField Complex ReciprocityTheory.ChartRestriction.G.FD Topology Filter ModeHalfA ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.L2DbarEstimates
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
private theorem sum_castLE_lemma {p0 : ℕ} (hp : p0 ≤ r) (f : Fin r → ℝ) :
    ∑ a : Fin p0, f (Fin.castLE hp a) = ∑ k : Fin r, if (k : ℕ) < p0 then f k else 0 := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun a _ => Fin.castLE hp a) ?_ ?_ ?_ ?_
  · intro a _
    simp [a.2]
  · intro a _ b _ h
    exact Fin.castLE_injective hp h
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    exact ⟨⟨k, hk⟩, Finset.mem_univ _, Fin.ext rfl⟩
  · intro a _
    rfl
end ModeHalfB
end ReciprocityTheory.ChartRestriction.G.AR.Up
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfB
open Matrix NumberField Complex ReciprocityTheory.ChartRestriction.G.FD Topology Filter ModeHalfA ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.L2DbarEstimates
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfB
theorem _root_.solution (X : Data E r) (τ : X.Ψ) (v : Fin r → ℂ) :
    Ms X.p0 X.p0_le (Nid r) v = ∑ k, ‖v k‖ ^ 2 := by
  have hA : Ag X.p0 X.p0_le (Nid r) = 1 := by
    ext a b
    simp only [Ag, Matrix.of_apply, sf, cl, Nid, Matrix.one_apply]
    rw [Finset.sum_eq_single (Fin.castLE X.p0_le a)]
    · have hs : sgn X.p0 ((Fin.castLE X.p0_le a : Fin r) : ℕ) = 1 := by simp [sgn, a.2]
      by_cases hab : a = b
      · subst hab; simp [hs, sgn, a.2]
      · have : Fin.castLE X.p0_le a ≠ Fin.castLE X.p0_le b := fun h => hab (Fin.castLE_injective X.p0_le h)
        simp [hab, this]
    · intro k _ hk; simp [hk]
    · simp
  have hsf : ∀ c : Fin r, sf X.p0 v (cl (Nid r) c) = ((sgn X.p0 c : ℝ) : ℂ) * v c := by
    intro c
    simp only [sf, cl, Nid]
    rw [Finset.sum_eq_single c]
    · simp
    · intro k _ hk
      simp [hk]
    · simp
  have hin : (∑ a : Fin X.p0, ∑ b : Fin X.p0, sf X.p0 v (cl (Nid r) (Fin.castLE X.p0_le a)) *
      (1 : Matrix (Fin X.p0) (Fin X.p0) ℂ) a b * conj (sf X.p0 v (cl (Nid r) (Fin.castLE X.p0_le b)))) =
      ∑ a : Fin X.p0, ((Complex.normSq (v (Fin.castLE X.p0_le a)) : ℝ) : ℂ) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single a]
    · rw [Matrix.one_apply_eq, mul_one, hsf, map_mul, Complex.conj_ofReal]
      have : sgn X.p0 ((Fin.castLE X.p0_le a : Fin r) : ℕ) = 1 := by simp [sgn, a.2]
      rw [this]
      push_cast
      rw [one_mul, one_mul, Complex.mul_conj]
    · intro b _ hb
      rw [Matrix.one_apply_ne (Ne.symm hb), mul_zero, zero_mul]
    · simp
  have hvv : (sf X.p0 v v).re = ∑ k : Fin r, sgn X.p0 (k : ℕ) * Complex.normSq (v k) := by
    simp only [sf, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_assoc, Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_re]
  simp only [Ms, hA, inv_one]
  rw [hin, hvv, Complex.re_sum]
  simp only [Complex.ofReal_re]
  rw [sum_castLE_lemma X.p0_le (fun k => Complex.normSq (v k)), Finset.mul_sum, ← Finset.sum_sub_distrib]
  simp only [Complex.sq_norm]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [sgn]
  split_ifs <;> ring
end ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfB
