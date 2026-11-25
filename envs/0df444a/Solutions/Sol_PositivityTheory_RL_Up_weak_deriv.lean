-- Prove2me | solution 1 for PositivityTheory.RL.Up.weak_deriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:51:08.743873+00:00
-- url     : https://prove2.me/submissions/bf0fd979-e8d7-488e-9b5c-3bfefbdc64fa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_RLLieA
import Theorems.Thm_PositivityTheory_RL_Up_good_mul
import Theorems.Thm_PositivityTheory_RL_Up_seminorm_succ_n
import Theorems.Thm_PositivityTheory_RL_Up_seminorm_succ_k

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix Filter Topology Asymptotics
open scoped Real RealInnerProductSpace ContDiff
open PositivityTheory PositivityTheory.RL PositivityTheory.RL.Up
open GlobalTheory.RealWeil
variable {l : Type} [Fintype l] [DecidableEq l]
namespace PositivityTheory.RL.Up
theorem _root_.solution (U : ℝ → (Sch l →L[ℂ] Sch l)) (Q : Sch l →L[ℂ] Sch l) (h0 : U 0 = 1)
    (hj : Good U Q (toBoundedContinuousFunctionCLM ℂ _ ℂ))
    (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) (c : ℝ → (l ⊕ l → ℝ) → (l ⊕ l → ℝ))
    (hc0 : ∀ w, c 0 w = w) (hc : ∀ w a, HasDerivAt (fun t => c t w a) (-(X *ᵥ w) a) 0)
    (hD : ∀ t w, dRho w * U t = U t * dRho (c t w))
    (hQ : ∀ w, Q * dRho w - dRho w * Q = dRho (X *ᵥ w)) (T : Sch l →L[ℂ] ℂ) : Good U Q T := by
  intro f
  let W := Submonoid.closure (Set.range (dRho (l := l)))
  let R : ℝ → Sch l := fun t => U t f - f - (t : ℂ) • Q f
  have hW : ∀ L ∈ W, Good U Q (toBoundedContinuousFunctionCLM ℂ _ ℂ ∘L L) := fun L hL => by
    induction hL using Submonoid.closure_induction_right with
    | one => exact hj
    | mul_right x _ y hy ih =>
      obtain ⟨w, rfl⟩ := hy
      exact good_mul U Q h0 X c hc0 hc hD hQ ih w
  have hDW : ∀ w, ∀ L ∈ W, dRho w * L ∈ W := fun w L hL => mul_mem (Submonoid.subset_closure ⟨w, rfl⟩) hL
  have hk : ∀ k, ∀ L ∈ W, (fun t => SchwartzMap.seminorm ℂ k 0 (L (R t))) =o[𝓝 0] fun t => t := fun k => by
    induction k with
    | zero =>
      intro L hL
      have := hasDerivAt_iff_isLittleO_nhds_zero.1 (hW L hL f)
      refine IsBigO.trans_isLittleO (IsBigO.of_bound 1 (.of_forall fun t => ?_)) this
      rw [one_mul, Real.norm_of_nonneg (apply_nonneg _ _)]
      refine SchwartzMap.seminorm_le_bound ℂ 0 0 _ (norm_nonneg _) fun x => ?_
      rw [pow_zero, one_mul, norm_iteratedFDeriv_zero]
      refine le_trans (BoundedContinuousFunction.norm_coe_le_norm (toBoundedContinuousFunctionCLM ℂ _ ℂ (L (R t))) x)
        (le_of_eq ?_)
      simp [R, h0, ← Complex.coe_smul]
    | succ k ih =>
      intro L hL
      refine IsBigO.trans_isLittleO (IsBigO.of_bound 1 (.of_forall fun t => ?_))
        (IsLittleO.fun_sum (s := Finset.univ) fun i _ => ih _ (hDW (Pi.single (Sum.inr i) 1) L hL))
      rw [one_mul, Real.norm_of_nonneg (apply_nonneg _ _)]
      exact (seminorm_succ_k k _).trans (le_abs_self _)
  have hn : ∀ n k, ∀ L ∈ W, (fun t => SchwartzMap.seminorm ℂ k n (L (R t))) =o[𝓝 0] fun t => t := fun n => by
    induction n with
    | zero => exact hk
    | succ n ih =>
      intro k L hL
      refine IsBigO.trans_isLittleO (IsBigO.of_bound 1 (.of_forall fun t => ?_))
        (IsLittleO.fun_sum (s := Finset.univ) fun i _ => ih k _ (hDW (Pi.single (Sum.inl i) 1) L hL))
      rw [one_mul, Real.norm_of_nonneg (apply_nonneg _ _)]
      exact (seminorm_succ_n k n _).trans (le_abs_self _)
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ (EuclideanSpace ℝ l) ℂ)
    ((normSeminorm ℂ ℂ).comp T.toLinearMap) T.continuous.norm
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  refine IsBigO.trans_isLittleO (IsBigO.of_bound C (.of_forall fun t => ?_))
    (IsLittleO.fun_sum (s := s) fun i _ => hn i.2 i.1 1 (one_mem _))
  have h1 := hC (R t)
  have h2 : (s.sup (schwartzSeminormFamily ℂ (EuclideanSpace ℝ l) ℂ)) (R t) ≤
      ∑ i ∈ s, SchwartzMap.seminorm ℂ i.1 i.2 (R t) :=
    Seminorm.finset_sup_apply_le (Finset.sum_nonneg fun _ _ => apply_nonneg _ _) fun i hi =>
      Finset.single_le_sum (f := fun i : ℕ × ℕ => SchwartzMap.seminorm ℂ i.1 i.2 (R t)) (fun _ _ => apply_nonneg _ _) hi
  have h3 : ‖T (R t)‖ ≤ C * ∑ i ∈ s, SchwartzMap.seminorm ℂ i.1 i.2 (R t) :=
    h1.trans (mul_le_mul_of_nonneg_left h2 C.2)
  refine le_trans (le_of_eq ?_) (h3.trans (mul_le_mul_of_nonneg_left (le_abs_self _) C.2))
  simp [R, h0]
end PositivityTheory.RL.Up
