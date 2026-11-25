-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.neg_log_norm_coeff_le_finitePlaces
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:33:08.697309+00:00
-- url     : https://prove2.me/submissions/12e36458-27e7-478a-b9ab-da37b52cdff2

import Definitions.Def_ReciprocityTheory_SemistableReduction_RestBlockSubstIsMultiHomogeneous
import Definitions.Def_ReciprocityTheory_SemistableReduction_LogNormCoeffSubLeBlockSphereLogMean

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory MvPolynomial NumberField
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {K : Type*} [Field K] [NumberField K] {ι : Type*} (f : MvPolynomial ι K)
    (s : ι →₀ ℕ) (hs : s ∈ f.support) :
    -Real.log |((Algebra.norm ℚ (f.coeff s) : ℚ) : ℝ)| ≤
      ∑ᶠ w : FinitePlace K, Real.log (gaussAbs w f) := by
  classical
  have hc : f.coeff s ≠ 0 := MvPolynomial.mem_support_iff.mp hs
  have hA : ∀ w : FinitePlace K, w (f.coeff s) ≤ gaussAbs w f := by
    intro w
    unfold gaussAbs
    have h1 := Finset.le_sup (f := fun t => (w (f.coeff t)).toNNReal) hs
    calc w (f.coeff s) ≤ ((w (f.coeff s)).toNNReal : ℝ) := Real.le_coe_toNNReal _
      _ ≤ _ := by exact_mod_cast h1
  have hpos : ∀ w : FinitePlace K, 0 < w (f.coeff s) := fun w => NumberField.FinitePlace.pos_iff.mpr hc
  have hU : (⋃ t ∈ f.support, Function.mulSupport (fun w : FinitePlace K => w (f.coeff t))).Finite :=
    Set.Finite.biUnion f.support.finite_toSet
      (fun t ht => NumberField.FinitePlace.mulSupport_finite (MvPolynomial.mem_support_iff.mp ht))
  set T := hU.toFinset with hT
  have hsubG : Function.support (fun w : FinitePlace K => Real.log (gaussAbs w f)) ⊆ (T : Set _) := by
    intro w hw
    rw [hT, Set.Finite.coe_toFinset]
    by_contra hnot
    apply hw
    simp only [Set.mem_iUnion, Function.mem_mulSupport, not_exists, not_not] at hnot
    have h1 : gaussAbs w f = 1 := by
      unfold gaussAbs
      have hne : f.support.Nonempty := ⟨s, hs⟩
      rw [Finset.sup_congr rfl (g := fun _ => (1 : NNReal)) (fun t ht => by simp [hnot t ht]),
        Finset.sup_const hne]
      simp
    simp [h1]
  have hsubW : Function.mulSupport (fun w : FinitePlace K => w (f.coeff s)) ⊆ (T : Set _) := by
    intro w hw
    rw [hT, Set.Finite.coe_toFinset]
    exact Set.mem_biUnion hs hw
  have hprod := NumberField.FinitePlace.prod_eq_inv_abs_norm hc
  rw [finprod_eq_prod_of_mulSupport_subset _ hsubW] at hprod
  rw [finsum_eq_sum_of_support_subset _ hsubG]
  have hlog : Real.log (∏ w ∈ T, w (f.coeff s)) = ∑ w ∈ T, Real.log (w (f.coeff s)) :=
    Real.log_prod (fun w _ => (hpos w).ne')
  rw [hprod] at hlog
  have hle : ∑ w ∈ T, Real.log (w (f.coeff s)) ≤ ∑ w ∈ T, Real.log (gaussAbs w f) :=
    Finset.sum_le_sum (fun w _ => Real.log_le_log (hpos w) (hA w))
  push_cast at hlog
  rw [Real.log_inv] at hlog
  linarith
end ReciprocityTheory.MultiplicativeHeights
