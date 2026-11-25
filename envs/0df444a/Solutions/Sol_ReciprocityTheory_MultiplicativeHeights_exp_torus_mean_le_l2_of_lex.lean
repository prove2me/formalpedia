-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.exp_torus_mean_le_l2_of_lex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:01:19.570895+00:00
-- url     : https://prove2.me/submissions/4ed28776-2de9-43db-85ae-dfca460c4101

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExpTorusMeanLeL2OfLex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Finset
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {ι : Type} [Fintype ι] [LinearOrder ι]
    (hBasic : TorusMeanBasicStatement) (hLex : TorusLexStatement)
    (hL2 : TorusL2Cauchy) (F : MvPolynomial ι ℂ) (hF : F ≠ 0) (s : ι →₀ ℕ)
    (Q : MvPolynomial ι ℂ) (hQ : ∀ t ∈ Q.support, toLex s < toLex t) :
    Real.exp (torusMean F) ≤ polyL2 (F * (MvPolynomial.monomial s 1 - Q)) := by
  classical
  set P := MvPolynomial.monomial s (1 : ℂ) - Q with hPdef
  have hsQ : s ∉ Q.support := fun h => lt_irrefl _ (hQ s h)
  have hQs : Q.coeff s = 0 := MvPolynomial.notMem_support_iff.mp hsQ
  have hPs : P.coeff s = 1 := by
    rw [hPdef, MvPolynomial.coeff_sub, MvPolynomial.coeff_monomial, if_pos rfl, hQs, sub_zero]
  have hP0 : P ≠ 0 := fun h => by rw [h, MvPolynomial.coeff_zero] at hPs; exact zero_ne_one hPs
  have hsupp : s ∈ P.support := by rw [MvPolynomial.mem_support_iff, hPs]; exact one_ne_zero
  have hlex : Real.log ‖P.coeff s‖ ≤ torusMean P := by
    apply hLex ι P s hsupp
    intro t ht hts
    have htQ : t ∈ Q.support := by
      by_contra h
      have h0 : P.coeff t = 0 := by
        rw [hPdef, MvPolynomial.coeff_sub, MvPolynomial.coeff_monomial, if_neg (Ne.symm hts),
          MvPolynomial.notMem_support_iff.mp h, sub_zero]
      exact (MvPolynomial.mem_support_iff.mp ht) h0
    obtain ⟨i, h1, h2⟩ := hQ t htQ
    exact ⟨i, h1, h2⟩
  rw [hPs, norm_one, Real.log_one] at hlex
  have hFP : F * P ≠ 0 := mul_ne_zero hF hP0
  have hmul := (hBasic ι).2.1 F P hF hP0
  have hL := (hL2 ι (F * P)).1 hFP
  have hpos : 0 < polyL2 (F * P) := by
    unfold polyL2
    apply Real.sqrt_pos.mpr
    obtain ⟨t, hne⟩ := MvPolynomial.ne_zero_iff.mp hFP
    have ht : t ∈ (F * P).support := MvPolynomial.mem_support_iff.mpr hne
    calc (0 : ℝ) < ‖(F * P).coeff t‖ ^ 2 := pow_pos (norm_pos_iff.mpr hne) 2
      _ ≤ _ := Finset.single_le_sum (f := fun s => ‖(F * P).coeff s‖ ^ 2)
          (fun _ _ => by positivity) ht
  calc Real.exp (torusMean F) ≤ Real.exp (torusMean (F * P)) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ polyL2 (F * P) := by
      rw [← Real.exp_log hpos]; exact Real.exp_le_exp.mpr hL
end ReciprocityTheory.MultiplicativeHeights
