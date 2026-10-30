-- Prove2me | solution 1 for SideConstrainedDTA.Existence.claim_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T23:34:21.508906+00:00
-- url     : https://prove2.me/submissions/b5fd18ed-5970-4394-b2ce-a19e8ee2b9ec

import Mathlib
import Definitions.Def_SideConstrainedDTA_Existence_Setting
import Theorems.Thm_SideConstrainedDTA_Existence_lam_weak_seq_compact

open MeasureTheory Set Filter Topology

open SideConstrainedDTA.Existence

lemma SideConstrainedDTA.Existence.Sol5.psi_bdd {I W E : Type*} [Fintype W] [DecidableEq I]
    (N : Model I W E) (h18 : A18 N) (p : W) :
    ∃ M : ℝ, ∀ h, Lam N h → ∀ t ∈ Icc N.t0 N.tf, N.Psi h p t ≤ M := by
  by_contra hcon
  simp only [not_exists, not_forall, not_le] at hcon
  have hex : ∀ n : ℕ, ∃ h, Lam N h ∧ ∃ t ∈ Icc N.t0 N.tf, (n : ℝ) < N.Psi h p t :=
    fun n => by
      obtain ⟨h, hh, t, ht, hlt⟩ := hcon n
      exact ⟨h, hh, t, ht, hlt⟩
  choose hs hhs ts hts hgt using hex
  obtain ⟨φ, hφ, hstar, hLam, hweak⟩ := lam_weak_seq_compact N hs hhs
  have hU := h18.2 (fun n => hs (φ n)) hstar ⟨fun n => hhs (φ n), hLam, hweak⟩ p
  obtain ⟨C, hC⟩ := (isCompact_Icc.exists_bound_of_continuousOn (h18.1 hstar hLam p))
  rw [Metric.tendstoUniformlyOn_iff] at hU
  obtain ⟨n0, hn0⟩ := (hU 1 one_pos).exists_forall_of_atTop
  obtain ⟨n, hn⟩ := exists_nat_gt (C + 1)
  have hle : n ≤ φ (max n n0) := (le_max_left n n0).trans (hφ.id_le _)
  have h1 := hn0 (max n n0) (le_max_right _ _) (ts (φ (max n n0))) (hts _)
  have h2 := hC _ (hts (φ (max n n0)))
  have h3 := hgt (φ (max n n0))
  have h4 : (n : ℝ) ≤ (φ (max n n0) : ℝ) := by exact_mod_cast hle
  rw [Real.dist_eq] at h1
  rw [Real.norm_eq_abs] at h2
  have := abs_lt.1 h1
  have := abs_le.1 h2
  linarith

theorem solution {I W E : Type*} [Fintype I] [Fintype W] [DecidableEq I] [DecidableEq W]
    (N : Model I W E) (hN : N.Standing) (h2 : A2 N) (h10 : A10 N) (h18 : A18 N)
    (h19 : A19 N) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ lam : ℝ, 0 ≤ lam → ∀ i h, Lam N h → ∃ p, N.com p = i ∧
      ∃ J ⊆ Icc N.t0 N.tf, MeasurableSet J ∧ 0 < volume J ∧
        ∀ t ∈ J, h p t < N.B p ∧ PsiPen N lam h p t ≤ M := by
  have hb := fun p => SideConstrainedDTA.Existence.Sol5.psi_bdd N h18 p
  choose Mp hMp using hb
  refine ⟨max 0 (∑ p, |Mp p|), le_max_left _ _, fun lam _ i h hh => ?_⟩
  obtain ⟨p, hpi, J, hJI, hJm, hJpos, hJ⟩ := h10 h hh i
  refine ⟨p, hpi, J, hJI, hJm, hJpos, fun t ht => ⟨(hJ t ht).1, ?_⟩⟩
  have hxi : xiWalk N h p t = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    unfold xi
    have := (hJ t ht).2 j j.isLt
    exact max_eq_left (sub_nonpos.2 this)
  unfold PsiPen
  rw [hxi, mul_zero, add_zero]
  calc N.Psi h p t ≤ Mp p := hMp p h hh t (hJI ht)
    _ ≤ |Mp p| := le_abs_self _
    _ ≤ ∑ q, |Mp q| :=
        Finset.single_le_sum (f := fun q => |Mp q|) (fun q _ => abs_nonneg _) (Finset.mem_univ p)
    _ ≤ _ := le_max_right _ _
