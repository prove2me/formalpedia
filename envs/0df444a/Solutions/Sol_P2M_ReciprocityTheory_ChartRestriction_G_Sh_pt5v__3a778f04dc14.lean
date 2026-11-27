-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_Sh_pt5v__3a778f04dc14
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:20:42.291187+00:00
-- url     : https://prove2.me/submissions/615372db-1ab8-4db7-a5d9-40103732f679

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_TypicalCurveStructureConstants
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_CoeffLgPcurveTop
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_GeomSumRoot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_WtSubOneLe
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Sh_pt5__381c8ae8e2ba
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_wt_sub_one_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTAgree_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTAgree_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_tangent_eq_lc_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.Sh
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh.PTb
noncomputable section
private theorem le_valuation_finset_sum {C : Type} [Field C] (v : AddValuation C (WithTop ℝ))
    {ι : Type} (s : Finset ι) (f : ι → C) (g : WithTop ℝ) (h : ∀ i ∈ s, g ≤ v (f i)) :
    g ≤ v (∑ i ∈ s, f i) := by
  classical
  revert h
  refine Finset.induction_on s (fun _ => by simp) ?_
  intro i s hi ih h
  rw [Finset.sum_insert hi]
  exact le_trans (le_min (h i (Finset.mem_insert_self i s))
    (ih fun j hj => h j (Finset.mem_insert_of_mem hj))) (AddValuation.map_add v _ _)
end
end ReciprocityTheory.ChartRestriction.G.Sh
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh.PTb
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Sh
theorem _root_.solution : TypicalCurveValuationBounds := by
  unfold TypicalCurveValuationBounds
  intro C _ _ _ v p hp hv d h ty G γ hB a
  obtain ⟨sc, hsc, -, hrec⟩ := pt5' C v p hp hv d h ty G γ hB
  obtain ⟨hcur, -, hdet⟩ := hB
  have H1 : ∀ (n : ℕ) (b c : Fin d), (((-(n : ℝ)) : ℝ) : WithTop ℝ) ≤ v (G.lc p (γ b) n c) := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih b c
    rcases n with _ | n
    · rw [← tangent_eq_lc_zero G p (fun e => (hcur b e).1)]
      have h0 : (0 : WithTop ℝ) ≤ v (tangent (γ b) c) := (hcur b c).2 1
      have e0 : (((-((0 : ℕ) : ℝ)) : ℝ) : WithTop ℝ) = 0 := by simp
      rw [e0]
      exact h0
    · have hr := congrFun (hrec b n) c
      simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at hr
      have hge : (((-(n : ℝ)) : ℝ) : WithTop ℝ) ≤ v ((p : C) * G.lc p (γ b) (n + 1) c) := by
        rw [hr]
        apply le_valuation_finset_sum
        intro m hm
        apply le_valuation_finset_sum
        intro e _
        rw [AddValuation.map_mul, AddValuation.map_pow]
        have hm' : m < n + 1 := Finset.mem_range.mp hm
        have h1 : (0 : WithTop ℝ) ≤ (p ^ m) • v (sc (n - m) e b) := nsmul_nonneg (hsc _ _ _) _
        have h2 := ih m hm' e c
        have h3 : (((-(n : ℝ)) : ℝ) : WithTop ℝ) ≤ (((-(m : ℝ)) : ℝ) : WithTop ℝ) := by
          apply WithTop.coe_le_coe.mpr
          have : (m : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp hm'
          linarith
        calc (((-(n : ℝ)) : ℝ) : WithTop ℝ) = 0 + (((-(n : ℝ)) : ℝ) : WithTop ℝ) := (zero_add _).symm
          _ ≤ (p ^ m) • v (sc (n - m) e b) + v (G.lc p (γ e) m c) := add_le_add h1 (h3.trans h2)
      rw [AddValuation.map_mul, hv] at hge
      have := wt_sub_one_le hge
      convert this using 2
      push_cast
      ring
  refine ⟨fun n c => H1 n a c, ?_⟩
  intro h1 n c hn
  have hne : Matrix.det (Matrix.of fun a b => tangent (γ a) b) ≠ 0 := by
    intro h0
    rw [h0, AddValuation.map_zero] at hdet
    simp at hdet
  have hs0 : ∀ e, sc 0 e a = 0 := by
    have hr := hrec a 0
    simp only [zero_add] at hr
    rw [h1, smul_zero, Finset.sum_range_one] at hr
    simp only [tsub_zero, pow_zero, pow_one] at hr
    have hM : Matrix.vecMul (fun e => sc 0 e a) (Matrix.of fun e b => tangent (γ e) b) = 0 := by
      funext b
      have hb := congrFun hr b
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hb
      simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.zero_apply]
      refine Eq.trans ?_ hb.symm
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [tangent_eq_lc_zero G p (fun f => (hcur e f).1)]
    intro e
    exact congrFun (Matrix.eq_zero_of_vecMul_eq_zero hne hM) e
  obtain _ | _ | k := n
  · omega
  · have h10 : G.lc p (γ a) (0 + 1) c = 0 := by simp [h1]
    rw [h10, AddValuation.map_zero]
    exact le_top
  · have hr := congrFun (hrec a (k + 1)) c
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at hr
    have hge : (((-(k : ℝ)) : ℝ) : WithTop ℝ) ≤ v ((p : C) * G.lc p (γ a) (k + 1 + 1) c) := by
      rw [hr]
      apply le_valuation_finset_sum
      intro m hm
      apply le_valuation_finset_sum
      intro e _
      have hm' : m < k + 1 + 1 := Finset.mem_range.mp hm
      rcases Nat.lt_succ_iff_lt_or_eq.mp hm' with hlt | heq
      · rw [AddValuation.map_mul, AddValuation.map_pow]
        have h1' : (0 : WithTop ℝ) ≤ (p ^ m) • v (sc (k + 1 - m) e a) := nsmul_nonneg (hsc _ _ _) _
        have h2 := H1 m e c
        have h3 : (((-(k : ℝ)) : ℝ) : WithTop ℝ) ≤ (((-(m : ℝ)) : ℝ) : WithTop ℝ) := by
          apply WithTop.coe_le_coe.mpr
          have : (m : ℝ) ≤ k := by exact_mod_cast Nat.lt_succ_iff.mp hlt
          linarith
        calc (((-(k : ℝ)) : ℝ) : WithTop ℝ) = 0 + (((-(k : ℝ)) : ℝ) : WithTop ℝ) := (zero_add _).symm
          _ ≤ (p ^ m) • v (sc (k + 1 - m) e a) + v (G.lc p (γ e) m c) := add_le_add h1' (h3.trans h2)
      · subst heq
        rw [Nat.sub_self, hs0 e, zero_pow (pow_ne_zero _ hp.ne_zero), zero_mul, AddValuation.map_zero]
        exact le_top
    rw [AddValuation.map_mul, hv] at hge
    have := wt_sub_one_le hge
    convert this using 2
    push_cast
    ring
end ReciprocityTheory.ChartRestriction.G.Sh
