-- Prove2me | solution 1 for SpatialDemandEq.Optimal.Supplement.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:11:15.942293+00:00
-- url     : https://prove2.me/submissions/6335463e-cec7-4898-85fa-e27f7cbdf64a

import Mathlib
import Definitions.Def_SpatialDemandEq_Optimal_Model
import Definitions.Def_SpatialDemandEq_Optimal_Supplement_Model

open MeasureTheory SpatialDemandEq.Optimal

open SpatialDemandEq
open SpatialDemandEq.Optimal
open SpatialDemandEq.Optimal.Supplement

theorem solution {n K : ℕ} (S : Set (E n)) (ν : Measure (E n)) (dst : E n → E n → ℝ)
    (xs : Fin K → E n) (c lam : ℝ) (hS : Standing S ν dst xs c lam) (μ : Fin K → ℝ)
    (hμ : ∀ k, 0 < μ k) (hcap : lam < ∑ k, μ k) (w : Fin K → ℝ)
    (hW : w ∈ boxW S (distFn dst xs) c lam μ)
    (hfix : ∀ k, phi ν S (distFn dst xs) c lam μ w k = w k) :
    IsEqWeight ν S (distFn dst xs) c lam μ w := by
      classical
      have hKne : Nonempty (Fin K) := ⟨⟨0, hS.K_pos⟩⟩
      have hc : 0 < c := hS.c_pos
      have hlam : 0 < lam := hS.lam_pos
      have : IsProbabilityMeasure ν := hS.prob
      have hreg := hS.regular
      set d := distFn dst xs with hd
      have hdcont : ∀ k, Continuous (d k) := fun k =>
        hS.metric.1.comp (continuous_id.prodMk continuous_const)
      have hdst_nonneg : ∀ a b, 0 ≤ dst a b := by
        intro a b
        have h1 := hS.metric.2.2.2 a b a
        have h2 := (hS.metric.2.1 a a).2 rfl
        have h3 := hS.metric.2.2.1 a b
        linarith
      have hwc_ne_bot : ∀ k a, waitCost c lam μ k a ≠ ⊥ := by
        intro k a; unfold waitCost; split_ifs <;> simp
      have hmono : ∀ k (a b : ℝ), a ≤ b → waitCost c lam μ k a ≤ waitCost c lam μ k b := by
        intro k a b hab
        unfold waitCost
        split_ifs with h1 h2 h2
        · exact EReal.coe_le_coe_iff.2
            (div_le_div_of_nonneg_left hc.le (by linarith) (by nlinarith))
        · exact le_top
        · exfalso; nlinarith
        · exact le_rfl
      have hwc0 : ∀ k, waitCost c lam μ k 0 = ((c / μ k : ℝ) : EReal) := by
        intro k; unfold waitCost; simp [hμ k]
      -- bounds
      set Ms := ∑ k, μ k with hMs
      have hMs_pos : 0 < Ms := by linarith
      have hden : ∀ i, 0 < μ i - lam * (μ i / Ms) := by
        intro i
        have : lam * (μ i / Ms) < μ i := by
          rw [mul_div_assoc', div_lt_iff₀ hMs_pos]
          have := hμ i
          nlinarith
        linarith
      set B := ∑ i, c / (μ i - lam * (μ i / Ms)) with hB
      have hwbar_le : wbar c lam μ ≤ (B : EReal) := by
        unfold wbar
        refine iSup₂_le fun a ha => ?_
        obtain ⟨k, hk⟩ : ∃ k, a k ≤ μ k / Ms := by
          by_contra hcon
          push Not at hcon
          have h1 : ∑ k, μ k / Ms < ∑ k, a k :=
            Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun k _ => hcon k)
          rw [← Finset.sum_div, ← hMs, div_self hMs_pos.ne', ha.2] at h1
          exact lt_irrefl _ h1
        refine (iInf_le _ k).trans ?_
        have hlt : lam * a k < μ k := by
          have := hden k
          have : lam * a k ≤ lam * (μ k / Ms) := mul_le_mul_of_nonneg_left hk hlam.le
          linarith
        unfold waitCost
        rw [if_pos hlt]
        refine EReal.coe_le_coe_iff.2 ?_
        calc c / (μ k - lam * a k) ≤ c / (μ k - lam * (μ k / Ms)) :=
              div_le_div_of_nonneg_left hc.le (hden k) (by nlinarith)
          _ ≤ B := by
              rw [hB]
              exact Finset.single_le_sum (f := fun i => c / (μ i - lam * (μ i / Ms)))
                (fun i _ => (div_pos hc (hden i)).le) (Finset.mem_univ k)
      set D := ∑ i, ∑ j, dst (xs i) (xs j) with hD
      have hspread_le : distSpread S d ≤ (D : EReal) := by
        unfold distSpread
        refine iSup₂_le fun x hx => iSup_le fun i => iSup_le fun j => ?_
        refine EReal.coe_le_coe_iff.2 ?_
        have htri : |d i x - d j x| ≤ dst (xs i) (xs j) := by
          simp only [hd, distFn]
          rw [abs_sub_le_iff]
          have t1 := hS.metric.2.2.2 x (xs j) (xs i)
          have t2 := hS.metric.2.2.2 x (xs i) (xs j)
          have s1 := hS.metric.2.2.1 (xs j) (xs i)
          constructor <;> linarith
        refine htri.trans ?_
        calc dst (xs i) (xs j) ≤ ∑ j', dst (xs i) (xs j') :=
              Finset.single_le_sum (f := fun j' => dst (xs i) (xs j'))
                (fun _ _ => hdst_nonneg _ _) (Finset.mem_univ j)
          _ ≤ D := Finset.single_le_sum (f := fun i' => ∑ j', dst (xs i') (xs j'))
                (fun _ _ => Finset.sum_nonneg fun _ _ => hdst_nonneg _ _) (Finset.mem_univ i)
      set C0 := ∑ i, c / μ i with hC0
      have hsup0_le : (⨆ k, waitCost c lam μ k 0) ≤ (C0 : EReal) := by
        refine iSup_le fun k => ?_
        rw [hwc0]
        exact EReal.coe_le_coe_iff.2 (Finset.single_le_sum (f := fun i => c / μ i)
          (fun i _ => (div_pos hc (hμ i)).le) (Finset.mem_univ k))
      have i0 : Fin K := ⟨0, hS.K_pos⟩
      set M : EReal := max (1 + wbar c lam μ + distSpread S d) (⨆ k, waitCost c lam μ k 0)
        with hMdef
      have hM_top : M ≠ ⊤ := by
        refine ne_top_of_le_ne_top (b := ((max (1 + B + D) C0 : ℝ) : EReal)) (EReal.coe_ne_top _) ?_
        have h1 : 1 + wbar c lam μ + distSpread S d ≤ ((1 + B + D : ℝ) : EReal) := by
          calc 1 + wbar c lam μ + distSpread S d ≤ 1 + (B : EReal) + (D : EReal) :=
                add_le_add (add_le_add le_rfl hwbar_le) hspread_le
            _ = ((1 + B + D : ℝ) : EReal) := by norm_cast
        calc M ≤ max ((1 + B + D : ℝ) : EReal) (C0 : EReal) := max_le_max h1 hsup0_le
          _ = ((max (1 + B + D) C0 : ℝ) : EReal) := by
              exact (EReal.coe_strictMono.monotone.map_max).symm
      have hM_bot : M ≠ ⊥ :=
        ne_bot_of_le_ne_bot (hwc_ne_bot i0 0) ((le_iSup (fun k => waitCost c lam μ k 0) i0).trans
          (le_max_right _ _))
      set W := wbarStar S d c lam μ with hWdef
      have hWM : (W : EReal) = M := EReal.coe_toReal hM_top hM_bot
      have hF1 : ∀ k, waitCost c lam μ k 0 ≤ (W : EReal) := fun k => by
        rw [hWM]; exact (le_iSup (fun k => waitCost c lam μ k 0) k).trans (le_max_right _ _)
      have hF2 : 1 + wbar c lam μ + distSpread S d ≤ (W : EReal) := by
        rw [hWM]; exact le_max_left _ _
      have hphi : ∀ k, w k = (min (waitCost c lam μ k (area ν (cell S d w k))) (W : EReal)).toReal :=
        fun k => (hfix k).symm
      -- areas sum to at most one
      have hmeas : ∀ k, MeasurableSet (cell S d w k) := by
        intro k
        have : cell S d w k = S ∩ ⋂ j, ⋂ (_ : j ≠ k), {x | d k x + w k ≤ d j x + w j} := by
          ext x; simp [cell]
        rw [this]
        refine hS.closed.measurableSet.inter
          (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => ?_)
        exact measurableSet_le ((hdcont k).measurable.add_const _)
          ((hdcont j).measurable.add_const _)
      have hdisj : ∀ i j, i ≠ j → ν (cell S d w i ∩ cell S d w j) = 0 := by
        intro i j hij
        have hsub : cell S d w i ∩ cell S d w j ⊆ (fun x => d i x - d j x) ⁻¹' {w j - w i} := by
          rintro x ⟨hxi, hxj⟩
          have h1 := hxi.2 j (Ne.symm hij)
          have h2 := hxj.2 i hij
          simp only [Set.mem_preimage, Set.mem_singleton_iff]
          linarith
        refine measure_mono_null hsub ?_
        have hg : Measurable (fun x => d i x - d j x) := ((hdcont i).sub (hdcont j)).measurable
        rw [← Measure.map_apply hg (measurableSet_singleton _)]
        exact hreg i j hij (Real.volume_singleton)
      have hsum : ∑ k, area ν (cell S d w k) ≤ 1 := by
        have hU : ν (⋃ k, cell S d w k) = ∑ k, ν (cell S d w k) := by
          rw [measure_iUnion₀ (fun i j hij => hdisj i j hij)
            (fun k => (hmeas k).nullMeasurableSet), tsum_fintype]
        have h1 : ∑ k, ν (cell S d w k) ≤ 1 := by
          rw [← hU]; exact prob_le_one
        unfold area
        rw [← ENNReal.toReal_sum (fun k _ => measure_ne_top ν _)]
        exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using h1)
      have hA_nonneg : ∀ k, 0 ≤ area ν (cell S d w k) := fun k => ENNReal.toReal_nonneg
      have hinf_le : (⨅ k, waitCost c lam μ k (area ν (cell S d w k))) ≤ wbar c lam μ := by
        let a' : Fin K → ℝ := fun i =>
          area ν (cell S d w i) + if i = i0 then 1 - ∑ k, area ν (cell S d w k) else 0
        have ha' : a' ∈ simplex K := by
          refine ⟨fun i => ?_, ?_⟩
          · simp only [a']; split_ifs <;> linarith [hA_nonneg i]
          · simp only [a', Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
            ring
        calc (⨅ k, waitCost c lam μ k (area ν (cell S d w k)))
              ≤ ⨅ k, waitCost c lam μ k (a' k) :=
              iInf_mono fun k => hmono k _ _ (by simp only [a']; split_ifs <;> linarith)
          _ ≤ wbar c lam μ :=
              le_iSup₂ (f := fun a (_ : a ∈ simplex K) => ⨅ k, waitCost c lam μ k (a k)) a' ha'
      obtain ⟨j, hjmin⟩ := Finite.exists_min (fun k => waitCost c lam μ k (area ν (cell S d w k)))
      have hj : waitCost c lam μ j (area ν (cell S d w j)) ≤ wbar c lam μ :=
        (le_iInf hjmin).trans hinf_le
      have hgood : ∀ k, waitCost c lam μ k (area ν (cell S d w k)) ≤ (W : EReal) := by
        intro k
        by_contra hbad
        push Not at hbad
        have hwk : w k = W := by
          rw [hphi k, min_eq_right hbad.le, EReal.toReal_coe]
        obtain ⟨x, hx⟩ : (cell S d w k).Nonempty := by
          rw [Set.nonempty_iff_ne_empty]
          intro hempty
          rw [hempty] at hbad
          have h0 : area ν (∅ : Set (E n)) = 0 := by simp [area]
          rw [h0] at hbad
          exact absurd (hF1 k) (not_le.2 hbad)
        have hwj : ((w j : ℝ) : EReal) ≤ wbar c lam μ := by
          have hmin_ne_top : min (waitCost c lam μ j (area ν (cell S d w j))) (W : EReal) ≠ ⊤ :=
            ne_top_of_le_ne_top (EReal.coe_ne_top W) (min_le_right _ _)
          have hmin_ne_bot : min (waitCost c lam μ j (area ν (cell S d w j))) (W : EReal) ≠ ⊥ := by
            rw [ne_eq, min_eq_bot]; push Not; exact ⟨hwc_ne_bot _ _, EReal.coe_ne_bot W⟩
          rw [hphi j, EReal.coe_toReal hmin_ne_top hmin_ne_bot]
          exact (min_le_left _ _).trans hj
        have hspx : ((|d j x - d k x| : ℝ) : EReal) ≤ distSpread S d := by
          unfold distSpread
          exact le_iSup₂_of_le x hx.1 (le_iSup_of_le j (le_iSup_of_le k le_rfl))
        have hreal : 1 + w j + |d j x - d k x| ≤ W := by
          have : ((1 + w j + |d j x - d k x| : ℝ) : EReal) ≤ (W : EReal) := by
            calc ((1 + w j + |d j x - d k x| : ℝ) : EReal)
                  = 1 + ((w j : ℝ) : EReal) + ((|d j x - d k x| : ℝ) : EReal) := by norm_cast
              _ ≤ 1 + wbar c lam μ + distSpread S d := add_le_add (add_le_add le_rfl hwj) hspx
              _ ≤ W := hF2
          exact EReal.coe_le_coe_iff.1 this
        by_cases hjk : j = k
        · subst hjk; simp at hreal; linarith
        · have h1 := hx.2 j hjk
          have h2 := le_abs_self (d j x - d k x)
          linarith
      intro k
      have hg := hgood k
      have hlt : lam * area ν (cell S d w k) < μ k := by
        by_contra h
        have hg' := hg
        unfold waitCost at hg'
        rw [if_neg h] at hg'
        exact EReal.coe_ne_top W (top_le_iff.1 hg')
      refine ⟨hlt, ?_⟩
      rw [hphi k, min_eq_left hg]
      unfold waitCost; rw [if_pos hlt, EReal.toReal_coe]
