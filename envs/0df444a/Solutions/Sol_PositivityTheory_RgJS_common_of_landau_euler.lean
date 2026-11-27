-- Prove2me | solution 1 for PositivityTheory.RgJS.common_of_landau_euler
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:21:27.931682+00:00
-- url     : https://prove2.me/submissions/81382e15-ae60-45e7-9722-a6d97a9a0e36

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_SubtypeIteSums_CommonOfLandauEuler
import Theorems.Thm_PositivityTheory_RgJS_Common0Aux_sum_lterm
import Theorems.Thm_PositivityTheory_RgJS_Common0Aux_cc_nonneg
import Theorems.Thm_PositivityTheory_RgJS_Common0Aux_ll_nonneg
import Theorems.Thm_PositivityTheory_RgJS_Common0Aux_term_real
import Theorems.Thm_PositivityTheory_RgJS_Common0Aux_exists_pos_le
import Theorems.Thm_PositivityTheory_RgJS_Common0Aux_dsum_subtype

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open Finset
open PositivityTheory.RgJS.Common0Aux
namespace PositivityTheory.RgJS
theorem _root_.solution : LandauL → EulerLog → Conv1 → Unb → Common0 := by
  classical
  intro hL hE hC hU W q X d A hS ι κ _ _ x y hR ht ht' h0
  by_contra hne
  push Not at hne
  have hq := hS.primes.two
  have hP : ∀ w k, Pw q A y w k = Pw q A x w k := fun w k => (hR w (k + 1)).symm
  have hxy : ∀ (σ : ℝ) (p : W × ℕ), ∑ i, ∑ j, lterm q (A (x i).1) (A (y j).1) (((σ + (x i).2 + (y j).2 : ℝ)) : ℂ) p =
      ((cc q A x p * Real.exp (-(ll q p * σ)) : ℝ) : ℂ) := fun σ p => by
    rw [sum_lterm q hq A x y σ p, hP, term_real q hq A x σ p]
  have hxx : ∀ (σ : ℝ) (p : W × ℕ), ∑ i, ∑ j, lterm q (A (x i).1) (A (x j).1) (((σ + (x i).2 + (x j).2 : ℝ)) : ℂ) p =
      ((cc q A x p * Real.exp (-(ll q p * σ)) : ℝ) : ℂ) := fun σ p => by
    rw [sum_lterm q hq A x x σ p, term_real q hq A x σ p]
  have hsum : ∀ (u v : X) (s : ℝ), 1 < s → Summable fun p => ‖lterm q (A u) (A v) (s : ℂ) p‖ :=
    fun u v s hs => (hC W q X d A hS u v).1 s hs
  have hcn : ∀ (σ : ℝ) (p : W × ℕ), 0 ≤ cc q A x p * Real.exp (-(ll q p * σ)) := fun σ p =>
    mul_nonneg (cc_nonneg q A x p) (Real.exp_pos _).le

  have hD1 : ∀ σ : ℝ, 1 < σ → Summable fun p => cc q A x p * Real.exp (-(ll q p * σ)) := by
    intro σ hσ
    refine Summable.of_nonneg_of_le (hcn σ) (fun p => ?_)
      (summable_sum (s := Finset.univ) fun i _ => summable_sum (s := Finset.univ) fun j _ =>
        hsum (x i).1 (y j).1 (σ + (x i).2 + (y j).2) (by linarith [ht i, ht' j]))
    calc cc q A x p * Real.exp (-(ll q p * σ)) = ‖((cc q A x p * Real.exp (-(ll q p * σ)) : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_of_nonneg (hcn σ p)]
      _ = ‖∑ i, ∑ j, lterm q (A (x i).1) (A (y j).1) (((σ + (x i).2 + (y j).2 : ℝ)) : ℂ) p‖ := by rw [hxy]
      _ ≤ ∑ i, ∑ j, ‖lterm q (A (x i).1) (A (y j).1) (((σ + (x i).2 + (y j).2 : ℝ)) : ℂ) p‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)

  obtain ⟨δ, hδ, hδ1, hδle⟩ := exists_pos_le (fun p : ι × κ => (x p.1).2 + (y p.2).2)
    (fun p => (x p.1).1 = (y p.2).1) (by
      rintro ⟨i, j⟩ hij
      have h1 := ht i
      have h2 := ht' j
      rcases (add_nonneg h1 h2).lt_or_eq with h | h
      · exact h
      · exfalso
        have a1 : (x i).2 = 0 := by linarith
        have a2 : (y j).2 = 0 := by linarith
        exact hne i j (Prod.ext hij (by rw [a1, a2])))
  choose F σ0 hFa hFe using fun p : ι × κ => hS.rs (x p.1).1 (y p.2).1
  have hGa' : ∀ σ : ℝ, 1 - δ < σ → ∀ p : ι × κ, AnalyticAt ℂ (gf F x y p) σ := by
    intro σ hσ p
    have hpos : 0 < σ + ((x p.1).2 + (y p.2).2) := by linarith [ht p.1, ht' p.2]
    have hF' : AnalyticAt ℂ (fun s : ℂ => F p (s + (((x p.1).2 + (y p.2).2 : ℝ) : ℂ))) (σ : ℂ) := by
      have := hFa p (σ + ((x p.1).2 + (y p.2).2)) hpos
      have hlin : AnalyticAt ℂ (fun s : ℂ => s + (((x p.1).2 + (y p.2).2 : ℝ) : ℂ)) (σ : ℂ) :=
        analyticAt_id.add analyticAt_const
      exact AnalyticAt.comp_of_eq this hlin (by push_cast; ring)
    by_cases hc : (x p.1).1 = (y p.2).1
    · have hne1 : (σ : ℂ) + (((x p.1).2 + (y p.2).2 : ℝ) : ℂ) - 1 ≠ 0 := by
        have h3 : 1 < σ + ((x p.1).2 + (y p.2).2) := by have := hδle p hc; linarith
        intro h
        have := congrArg Complex.re h
        simp at this
        linarith
      have : AnalyticAt ℂ (fun s : ℂ => F p (s + (((x p.1).2 + (y p.2).2 : ℝ) : ℂ)) /
          (s + (((x p.1).2 + (y p.2).2 : ℝ) : ℂ) - 1)) (σ : ℂ) :=
        hF'.div ((analyticAt_id.add analyticAt_const).sub analyticAt_const) hne1
      have hgf : gf F x y p = fun s : ℂ => F p (s + (((x p.1).2 + (y p.2).2 : ℝ) : ℂ)) /
          (s + (((x p.1).2 + (y p.2).2 : ℝ) : ℂ) - 1) := by
        funext s
        unfold gf
        rw [if_pos hc]
      rw [hgf]
      exact this
    · have hgf : gf F x y p = fun s : ℂ => F p (s + (((x p.1).2 + (y p.2).2 : ℝ) : ℂ)) := by
        funext s
        unfold gf
        rw [if_neg hc]
      rw [hgf]
      exact hF'
  have hGa : ∀ σ : ℝ, 1 - δ < σ → AnalyticAt ℂ (fun s => ∏ p, gf F x y p s) σ := by
    intro σ hσ
    have := Finset.analyticAt_prod (f := fun p => gf F x y p) Finset.univ (fun p _ => hGa' σ hσ p)
    rw [Finset.prod_fn] at this
    exact this
  set σ₁ : ℝ := 2 + ∑ p, |σ0 p| with hσ₁
  have hσ0le : ∀ p, σ0 p ≤ σ₁ - 2 := fun p => by
    have := Finset.single_le_sum (f := fun p => |σ0 p|) (fun p _ => abs_nonneg _) (Finset.mem_univ p)
    have := le_abs_self (σ0 p)
    simp only [hσ₁]
    linarith
  have hσ₁2 : 2 ≤ σ₁ := by
    have : 0 ≤ ∑ p, |σ0 p| := Finset.sum_nonneg fun p _ => abs_nonneg _
    simp only [hσ₁]
    linarith
  have hGe : ∀ σ : ℝ, σ₁ < σ → (fun s => ∏ p, gf F x y p s) σ =
      ((Real.exp (∑' p, cc q A x p * Real.exp (-(ll q p * σ))) : ℝ) : ℂ) := by
    intro σ hσ
    have hs' : ∀ p : ι × κ, Summable fun r => lterm q (A (x p.1).1) (A (y p.2).1) (((σ + (x p.1).2 + (y p.2).2 : ℝ)) : ℂ) r :=
      fun p => (hsum _ _ _ (by linarith [ht p.1, ht' p.2])).of_norm
    have hg : ∀ p : ι × κ, gf F x y p σ =
        Complex.exp (∑' r, lterm q (A (x p.1).1) (A (y p.2).1) (((σ + (x p.1).2 + (y p.2).2 : ℝ)) : ℂ) r) := by
      intro p
      have hs : σ0 p < σ + (x p.1).2 + (y p.2).2 := by linarith [hσ0le p, ht p.1, ht' p.2]
      have hs2 : 2 < ((((σ + (x p.1).2 + (y p.2).2 : ℝ)) : ℂ)).re := by
        rw [Complex.ofReal_re]
        linarith [ht p.1, ht' p.2]
      have hEL := (hE W q (Fin (d (x p.1).1)) (Fin (d (y p.2).1)) (A (x p.1).1) (A (y p.2).1) _ hS.primes
        (hS.bd _) (hS.bd _) hs2).2.1
      have hFE := hFe p _ hs
      have ecast : (σ : ℂ) + (((x p.1).2 + (y p.2).2 : ℝ) : ℂ) = (((σ + (x p.1).2 + (y p.2).2 : ℝ)) : ℂ) := by
        push_cast
        ring
      unfold gf
      rw [ecast]
      split_ifs with hc
      · have hne1 : ((((σ + (x p.1).2 + (y p.2).2 : ℝ)) : ℂ)) - 1 ≠ 0 := by
          intro h
          have := congrArg Complex.re h
          simp at this
          linarith [ht p.1, ht' p.2]
        rw [hFE, if_pos hc, mul_div_cancel_left₀ _ hne1, hEL]
      · rw [hFE, if_neg hc, one_mul, hEL]
    show ∏ p, gf F x y p σ = _
    simp only [hg]
    rw [← Complex.exp_sum, ← Summable.tsum_finsetSum (fun p _ => hs' p)]
    simp only [Fintype.sum_prod_type]
    rw [show (fun r => ∑ i, ∑ j, lterm q (A (x i).1) (A (y j).1) (((σ + (x i).2 + (y j).2 : ℝ)) : ℂ) r) =
      fun r => ((cc q A x r * Real.exp (-(ll q r * σ)) : ℝ) : ℂ) from funext (hxy σ)]
    rw [← Complex.ofReal_tsum, ← Complex.ofReal_exp]
  have hL1 := hL (W × ℕ) (cc q A x) (ll q) (1 - δ) σ₁ (fun s => ∏ p, gf F x y p s) (cc_nonneg q A x) (ll_nonneg q hq)
    hGa (fun σ hσ => hD1 σ (by linarith)) hGe 1 (by linarith)

  obtain ⟨τ, hτ, -, hτle⟩ := exists_pos_le (fun i => (x i).2) (fun i => (x i).2 ≠ 0)
    (fun i hi => lt_of_le_of_ne (ht i) (Ne.symm hi))
  choose M hM using fun i i' : ι => (hC W q X d A hS (x i).1 (x i').1).2 (1 + τ) (by linarith)
  obtain ⟨i₀, hi₀⟩ := h0
  have : Nonempty {i // (x i).2 = 0} := ⟨⟨i₀, hi₀⟩⟩
  refine hU W q X d A hS {i // (x i).2 = 0} (fun i => (x i.1).1)
    ⟨(∑' p, cc q A x p * Real.exp (-(ll q p * 1))) + ∑ i, ∑ i', |M i i'|, fun σ hσ1 hσ2 => ?_⟩
  have hs : ∀ i j, Summable fun p => lterm q (A (x i).1) (A (x j).1) (((σ + (x i).2 + (x j).2 : ℝ)) : ℂ) p :=
    fun i j => (hsum _ _ _ (by linarith [ht i, ht j])).of_norm
  have hform : ∑ i : {i // (x i).2 = 0}, ∑ j : {i // (x i).2 = 0}, ∑' p, lterm q (A (x i.1).1) (A (x j.1).1) (σ : ℂ) p =
      ∑ i : {i // (x i).2 = 0}, ∑ j : {i // (x i).2 = 0},
        ∑' p, lterm q (A (x i.1).1) (A (x j.1).1) (((σ + (x i.1).2 + (x j.1).2 : ℝ)) : ℂ) p := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [i.2, j.2, add_zero, add_zero]
  have htot : ∑ i, ∑ j, ∑' p, lterm q (A (x i).1) (A (x j).1) (((σ + (x i).2 + (x j).2 : ℝ)) : ℂ) p =
      ((∑' p, cc q A x p * Real.exp (-(ll q p * σ)) : ℝ) : ℂ) := by
    calc ∑ i, ∑ j, ∑' p, lterm q (A (x i).1) (A (x j).1) (((σ + (x i).2 + (x j).2 : ℝ)) : ℂ) p
        = ∑ i, ∑' p, ∑ j, lterm q (A (x i).1) (A (x j).1) (((σ + (x i).2 + (x j).2 : ℝ)) : ℂ) p :=
          Finset.sum_congr rfl fun i _ => (Summable.tsum_finsetSum fun j _ => hs i j).symm
      _ = ∑' p, ∑ i, ∑ j, lterm q (A (x i).1) (A (x j).1) (((σ + (x i).2 + (x j).2 : ℝ)) : ℂ) p :=
          (Summable.tsum_finsetSum fun i _ => summable_sum (s := Finset.univ) fun j _ => hs i j).symm
      _ = ∑' p, ((cc q A x p * Real.exp (-(ll q p * σ)) : ℝ) : ℂ) := tsum_congr fun p => hxx σ p
      _ = _ := (Complex.ofReal_tsum _).symm
  rw [hform, dsum_subtype (fun i => (x i).2 = 0)
    (fun i j => ∑' p, lterm q (A (x i).1) (A (x j).1) (((σ + (x i).2 + (x j).2 : ℝ)) : ℂ) p)]
  set f : ι → ι → ℂ := fun i j => ∑' p, lterm q (A (x i).1) (A (x j).1) (((σ + (x i).2 + (x j).2 : ℝ)) : ℂ) p with hf
  have hsplit : ∑ i, ∑ j, f i j = (∑ i, ∑ j, if (x i).2 = 0 ∧ (x j).2 = 0 then f i j else 0) +
      ∑ i, ∑ j, if (x i).2 = 0 ∧ (x j).2 = 0 then 0 else f i j := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  have hrest : ‖∑ i, ∑ j, if (x i).2 = 0 ∧ (x j).2 = 0 then (0 : ℂ) else f i j‖ ≤ ∑ i, ∑ i', |M i i'| := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun j _ => ?_))
    split_ifs with hij
    · simp
    · have hge : 1 + τ ≤ σ + (x i).2 + (x j).2 := by
        rcases not_and_or.1 hij with h | h
        · linarith [hτle i h, ht j]
        · linarith [hτle j h, ht i]
      exact (hM i j _ hge).trans (le_abs_self _)
  have hDle : (∑' p, cc q A x p * Real.exp (-(ll q p * σ))) ≤ ∑' p, cc q A x p * Real.exp (-(ll q p * 1)) := by
    refine Summable.tsum_le_tsum (fun p => ?_) (hD1 σ hσ1) hL1
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (cc_nonneg q A x p)
    have := ll_nonneg q hq p
    nlinarith
  have hD0 : 0 ≤ ∑' p, cc q A x p * Real.exp (-(ll q p * σ)) := tsum_nonneg (hcn σ)
  have heq : (∑ i, ∑ j, if (x i).2 = 0 ∧ (x j).2 = 0 then f i j else 0) =
      ((∑' p, cc q A x p * Real.exp (-(ll q p * σ)) : ℝ) : ℂ) -
        ∑ i, ∑ j, if (x i).2 = 0 ∧ (x j).2 = 0 then 0 else f i j := by
    rw [← htot, hsplit]
    ring
  rw [heq]
  calc ‖((∑' p, cc q A x p * Real.exp (-(ll q p * σ)) : ℝ) : ℂ) -
        ∑ i, ∑ j, if (x i).2 = 0 ∧ (x j).2 = 0 then 0 else f i j‖
      ≤ ‖((∑' p, cc q A x p * Real.exp (-(ll q p * σ)) : ℝ) : ℂ)‖ +
        ‖∑ i, ∑ j, if (x i).2 = 0 ∧ (x j).2 = 0 then (0 : ℂ) else f i j‖ := norm_sub_le _ _
    _ ≤ _ := by
        rw [Complex.norm_real, Real.norm_of_nonneg hD0]
        linarith
end PositivityTheory.RgJS
