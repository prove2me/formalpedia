-- Prove2me | solution 1 for RetirePartialInfo.Duality.eq_11
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T05:45:00.236339+00:00
-- url     : https://prove2.me/submissions/d953d582-03e5-45ab-a633-f3a606805bb3

import Mathlib
import Definitions.Def_RetirePartialInfo_Duality_Market
import Definitions.Def_RetirePartialInfo_Duality_Utility

open Filter Set
open scoped Topology
open RetirePartialInfo.Duality

theorem solution (p : Params) (U : ℝ → ℝ → ℝ) (hU : Assumption22 p U) (t : ℝ)
    (ht : t ∈ Icc 0 p.T) (y : ℝ) (hy : 0 < y) :
    0 < Iinv U t y ∧
    IsGreatest ((fun c => U t c - y * c) '' Ioi 0) (U t (Iinv U t y) - y * Iinv U t y) ∧
    Utilde U t y = U t (Iinv U t y) - y * Iinv U t y := by
  obtain ⟨hcd, hconc, hlim0, hliminf, -⟩ := hU
  set f : ℝ → ℝ := U t with hf
  set D : ℝ → ℝ := deriv f with hD
  -- differentiability of `f` on `(0, ∞)`
  have hfcd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Ioi 0) := by
    have hpair : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun c : ℝ => (t, c)) (Ioi 0) :=
      (contDiff_const.prodMk contDiff_id).contDiffOn
    exact hcd.comp hpair (fun c hc => ⟨ht, hc⟩)
  have hfdiff : ∀ c ∈ Ioi (0 : ℝ), DifferentiableAt ℝ f c := by
    intro c hc
    have := (hfcd.differentiableOn (by simp)) c hc
    exact this.differentiableAt (Ioi_mem_nhds hc)
  have hanti : StrictAntiOn D (Ioi 0) := (hconc t ht).strictAntiOn_deriv hfdiff
  set S : Set ℝ := {c | 0 < c ∧ deriv (U t) c ≤ y} with hS
  have hIinv : Iinv U t y = sInf S := rfl
  -- `S` is nonempty
  have hSne : S.Nonempty := by
    have h1 : ∀ᶠ c in atTop, D c < y := (hliminf t ht).eventually (gt_mem_nhds hy)
    obtain ⟨c, hc1, hc2⟩ := (h1.and (eventually_gt_atTop 0)).exists
    exact ⟨c, hc2, hc1.le⟩
  have hSbdd : BddBelow S := ⟨0, fun c hc => hc.1.le⟩
  -- a positive lower bound for `S`
  obtain ⟨ε, hε, hεS⟩ : ∃ ε > 0, ∀ c ∈ S, ε ≤ c := by
    have h1 : ∀ᶠ c in 𝓝[>] (0 : ℝ), y < D c := (hlim0 t ht).eventually (eventually_gt_atTop y)
    obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h1
    refine ⟨u, hu, fun c hc => ?_⟩
    by_contra hlt
    rw [not_le] at hlt
    have := hsub ⟨hc.1, hlt⟩
    exact absurd hc.2 (not_le.2 this)
  set c0 := sInf S with hc0
  have hc0pos : 0 < c0 := lt_of_lt_of_le hε (le_csInf hSne hεS)
  -- sign of `D - y`
  have hbelow : ∀ c, 0 < c → c < c0 → y < D c := by
    intro c hc hcc
    have : c ∉ S := notMem_of_lt_csInf hcc hSbdd
    by_contra h
    exact this ⟨hc, not_lt.1 h⟩
  have habove : ∀ c, c0 < c → D c < y := by
    intro c hcc
    obtain ⟨s, hsS, hsc⟩ := exists_lt_of_csInf_lt hSne hcc
    exact lt_of_lt_of_le (hanti hsS.1 (lt_trans hsS.1 hsc) hsc) hsS.2
  set g : ℝ → ℝ := fun c => U t c - y * c with hg
  have hgdiff : ∀ c ∈ Ioi (0 : ℝ), DifferentiableAt ℝ g c := fun c hc =>
    (hfdiff c hc).sub ((differentiableAt_id).const_mul y)
  have hgderiv : ∀ c ∈ Ioi (0 : ℝ), deriv g c = D c - y := by
    intro c hc
    have h : HasDerivAt g (D c - y * 1) c :=
      (hfdiff c hc).hasDerivAt.sub ((hasDerivAt_id c).const_mul y)
    rw [h.deriv, mul_one]
  have hgcont : ContinuousOn g (Ioi 0) := fun c hc => (hgdiff c hc).continuousAt.continuousWithinAt
  have hmono : StrictMonoOn g (Ioc 0 c0) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioc 0 c0) (hgcont.mono Ioc_subset_Ioi_self) ?_
    intro c hc
    rw [interior_Ioc] at hc
    rw [hgderiv c hc.1]
    linarith [hbelow c hc.1 hc.2]
  have hantig : StrictAntiOn g (Ici c0) := by
    refine strictAntiOn_of_deriv_neg (convex_Ici c0)
      (hgcont.mono fun c hc => lt_of_lt_of_le hc0pos hc) ?_
    intro c hc
    rw [interior_Ici] at hc
    rw [hgderiv c (lt_trans hc0pos hc)]
    linarith [habove c hc]
  have hgreat : IsGreatest ((fun c => U t c - y * c) '' Ioi 0) (U t c0 - y * c0) := by
    refine ⟨⟨c0, hc0pos, rfl⟩, ?_⟩
    rintro v ⟨c, hc, rfl⟩
    show g c ≤ g c0
    rcases le_total c c0 with h | h
    · exact hmono.monotoneOn ⟨hc, h⟩ ⟨hc0pos, le_rfl⟩ h
    · exact hantig.antitoneOn (le_refl c0) (show c0 ≤ c from h) h
  refine ⟨hc0pos, hgreat, ?_⟩
  unfold Utilde
  exact hgreat.csSup_eq
