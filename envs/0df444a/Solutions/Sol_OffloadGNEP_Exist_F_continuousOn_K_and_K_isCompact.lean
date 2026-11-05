-- Prove2me | solution 1 for OffloadGNEP.Exist.F_continuousOn_K_and_K_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T21:46:28.335673+00:00
-- url     : https://prove2.me/submissions/d7d9f120-6493-487a-bfe3-9e0de5b910bb

import Mathlib
import Definitions.Def_OffloadGNEP_Exist_Setting

open OffloadGNEP.Exist

theorem solution {N : ℕ} (P : Params N) (hA : P.AssumptionA)
    (hS : P.Standing) :
    ContinuousOn (F P) (K P) ∧ IsCompact (K P) ∧ Convex ℝ (K P) := by
  obtain ⟨hU0, hU1, hA'⟩ := hA
  obtain ⟨hn, hchi0, hchi1⟩ := hS
  have hnR : (0 : ℝ) < P.n := by exact_mod_cast hn
  have hload_cont : Continuous (fun x : Fin N → Tier → ℝ => load P x) := by
    unfold load; fun_prop
  -- facts on K
  have hKbd : ∀ x ∈ K P, ∀ u i, 0 ≤ x u i ∧ x u i ≤ 1 := by
    intro x hx u i
    have h := hx.1 u
    obtain ⟨h0, h1, -, -⟩ := h
    have := h0 Tier.m; have := h0 Tier.clet; have := h0 Tier.cloud
    refine ⟨h0 i, ?_⟩
    cases i <;> linarith
  have hDpos : ∀ x ∈ K P, 0 < 1 - load P x := by
    intro x hx
    have := hx.2
    simp only [Omega, Set.mem_ofPred_eq] at this
    linarith
  have hmpos : ∀ x ∈ K P, ∀ u, 0 < 1 - P.alpha u * x u .m := by
    intro x hx u
    have h1 := (hKbd x hx u .m).2
    have h0 := (hKbd x hx u .m).1
    have := hA' u
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · -- continuity
    apply continuousOn_pi.mpr
    intro u
    apply continuousOn_pi.mpr
    intro i
    cases i
    · simp only [F]
      apply ContinuousOn.div continuousOn_const
      · fun_prop
      · intro x hx; exact pow_ne_zero _ (hmpos x hx u).ne'
    · simp only [F]
      apply ContinuousOn.add continuousOn_const
      apply ContinuousOn.div
      · fun_prop
      · exact (Continuous.pow (continuous_const.sub hload_cont) 2).continuousOn
      · intro x hx; exact pow_ne_zero _ (hDpos x hx).ne'
    · simp only [F]; exact continuousOn_const
  · -- compactness
    have hbox : IsCompact (Set.univ.pi fun _ : Fin N => Set.univ.pi fun _ : Tier => Set.Icc (0:ℝ) 1) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
    apply hbox.of_isClosed_subset
    · have hKt : ∀ u, IsClosed (Ktil P u) := by
        intro u
        have : Ktil P u = (⋂ i, {y : Tier → ℝ | 0 ≤ y i}) ∩ {y | y .m + y .clet + y .cloud = 1} ∩
            {y | y .clet + y .cloud ≤ P.chi} ∩
            {y | P.alpha u * P.Pm u * y .m + P.beta u * P.Pt u * (y .clet + y .cloud) ≤ P.Pmax u} := by
          ext y; simp [Ktil, and_assoc]
        rw [this]
        refine IsClosed.inter (IsClosed.inter (IsClosed.inter ?_ ?_) ?_) ?_
        · exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
        · exact isClosed_eq (by fun_prop) continuous_const
        · exact isClosed_le (by fun_prop) continuous_const
        · exact isClosed_le (by fun_prop) continuous_const
      have : K P = (⋂ u, (fun x : Fin N → Tier → ℝ => x u) ⁻¹' Ktil P u) ∩
          {x | load P x ≤ P.Umax} := by
        ext x; simp [K, Kprod, Omega]
      rw [this]
      exact IsClosed.inter (isClosed_iInter fun u => (hKt u).preimage (continuous_apply u))
        (isClosed_le hload_cont continuous_const)
    · intro x hx
      simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
      exact fun u i => hKbd x hx u i
  · -- convexity
    have hKt : ∀ u, Convex ℝ (Ktil P u) := by
      intro u y hy z hz a b ha hb hab
      obtain ⟨hy0, hy1, hy2, hy3⟩ := hy
      obtain ⟨hz0, hz1, hz2, hz3⟩ := hz
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have := hy0 i; have := hz0 i; positivity
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        linear_combination a * hy1 + b * hz1 + hab
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        nlinarith [mul_le_mul_of_nonneg_left hy2 ha, mul_le_mul_of_nonneg_left hz2 hb]
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        linear_combination (mul_le_mul_of_nonneg_left hy3 ha) + (mul_le_mul_of_nonneg_left hz3 hb) +
          P.Pmax u * hab
    intro x hx y hy a b ha hb hab
    refine ⟨fun u => ?_, ?_⟩
    · have := hKt u (hx.1 u) (hy.1 u) ha hb hab
      simpa using this
    · have hx2 := hx.2; have hy2 := hy.2
      simp only [Omega, Set.mem_ofPred_eq] at hx2 hy2 ⊢
      have : load P (a • x + b • y) = a * load P x + b * load P y := by
        simp only [load, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro v _; ring
      rw [this]
      nlinarith [mul_le_mul_of_nonneg_left hx2 ha, mul_le_mul_of_nonneg_left hy2 hb]
