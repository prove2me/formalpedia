-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.card_lpsTraceQuadraticShell_firstCoordinate_le_ninetySix_mul_seventh
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:05:35.06351+00:00
-- url     : https://prove2.me/submissions/73173224-4497-4b91-b360-5ee7bcfff2ac

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIntegerThreeSquare_card_le_ninetySix_mul_seventh
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (q n K : ℕ) (hq : 0 < q) (hK : 0 < K) (hn : n ≤ 4*q^2*K^8) (x : ℤ) :
    ((lpsTraceQuadraticShell q n).filter fun t => t.a=x).card ≤ 96*K^7 := by
  classical
  let s := (lpsTraceQuadraticShell q n).filter fun t => t.a=x
  by_cases hne : s.Nonempty
  · obtain ⟨t0,ht0⟩ := hne
    let f : LPSQuaternion → (ℤ × ℤ) × ℤ := fun t => ((t.b,t.c),t.d)
    let scale : ℤ := 4*(q : ℤ)^2
    have hqZ : 0 < (q : ℤ) := by exact_mod_cast hq
    have hscale : 0 < scale := by dsimp [scale]; positivity
    have hform : ∀ t ∈ s, t.a^2+scale*(t.b^2+t.c^2+t.d^2)=(n : ℤ) := by
      intro t ht
      have hnT := (mem_lpsTraceQuadraticShell_iff hq t).mp (Finset.mem_filter.mp ht).1
      calc
        _ = lpsTraceQuadraticForm q t := by unfold lpsTraceQuadraticForm; dsimp [scale]; ring
        _ = (n : ℤ) := hnT
    have hzero : 0 ≤ t0.b^2+t0.c^2+t0.d^2 := by positivity
    let m := (t0.b^2+t0.c^2+t0.d^2).toNat
    have hm : (m : ℤ)=t0.b^2+t0.c^2+t0.d^2 := Int.toNat_of_nonneg hzero
    have hnZ : (n : ℤ) ≤ scale*(K : ℤ)^8 := by dsimp [scale]; exact_mod_cast hn
    have hprod : scale*(t0.b^2+t0.c^2+t0.d^2) ≤ scale*(K : ℤ)^8 := by
      linarith [hform t0 ht0, sq_nonneg t0.a]
    have hmK : m ≤ K^8 := by
      have hh := le_of_mul_le_mul_left hprod hscale
      rw [← hm] at hh
      exact_mod_cast hh
    have hi : (s : Set LPSQuaternion).InjOn f := by
      intro a ha b hb h
      apply LPSQuaternion.ext
      · exact (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm
      · exact congrArg (fun v : (ℤ × ℤ) × ℤ => v.1.1) h
      · exact congrArg (fun v : (ℤ × ℤ) × ℤ => v.1.2) h
      · exact congrArg Prod.snd h
    have hsI : ∀ a ∈ s.image f, a.1.1^2+a.1.2^2+a.2^2=(m : ℤ) := by
      intro a ha
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp ha
      have h0 := hform t0 ht0
      have hT := hform t ht
      have h0a := (Finset.mem_filter.mp ht0).2
      have hTa := (Finset.mem_filter.mp ht).2
      rw [h0a] at h0
      rw [hTa] at hT
      have he : scale*(t.b^2+t.c^2+t.d^2)=scale*(t0.b^2+t0.c^2+t0.d^2) := by linarith
      change t.b^2+t.c^2+t.d^2=(m : ℤ)
      rw [hm]
      exact mul_left_cancel₀ (ne_of_gt hscale) he
    change s.card ≤ 96*K^7
    rw [← Finset.card_image_of_injOn hi]
    exact lpsIntegerThreeSquare_card_le_ninetySix_mul_seventh (s.image f) m K hK hmK hsI
  · have he : s=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    change s.card ≤ 96*K^7
    rw [he]
    simp
end QEC.Coding.TannerLiftedProduct
