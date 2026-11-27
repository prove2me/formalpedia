-- Prove2me | solution 1 for ProjSelfConcordant.ConicExt.Supplement.lemma_5_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:26:22.146402+00:00
-- url     : https://prove2.me/submissions/e79d0a08-ea96-4842-9f54-0e950f7ab84c

import Mathlib
import Definitions.Def_ProjSelfConcordant_ConicExt_Setting
import Definitions.Def_ProjSelfConcordant_ConicExt_Supplement_Barrier

open ProjSelfConcordant
open ProjSelfConcordant.ConicExt
open ProjSelfConcordant.ConicExt.Supplement

/-- Lemma 5.1, p. 13: let `D ⊂ ℝⁿ` be open and convex and `q` of class `C²` on `D`. If there is a
co-vector field `w` on `D` (with no regularity) such that
`q″(x) − q′(x) w(x)ᵀ − w(x) q′(x)ᵀ ≻ 0` for all `x ∈ D`, then `q` is quasi-convex on `D`. -/
theorem solution {n : ℕ} (D : Set (EuclideanSpace ℝ (Fin n)))
    (hDo : IsOpen D) (hDc : Convex ℝ D)
    (q : EuclideanSpace ℝ (Fin n) → ℝ) (hq : ContDiffOn ℝ 2 q D)
    (w : EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))
    (hw : ∀ x ∈ D, ∀ h : EuclideanSpace ℝ (Fin n), h ≠ 0 →
      0 < d2 q x h h - fderiv ℝ q x h * w x h - w x h * fderiv ℝ q x h) :
    QuasiconvexOn ℝ D q := by
      rw [quasiconvexOn_iff_le_max]
      refine ⟨hDc, ?_⟩
      intro x hx y hy a b ha hb hab
      by_cases hxy : x = y
      · subst hxy
        rw [← add_smul, hab, one_smul, max_self]
      set h : EuclideanSpace ℝ (Fin n) := y - x with hh
      have hh0 : h ≠ 0 := by
        intro h0; apply hxy; rw [hh, sub_eq_zero] at h0; exact h0.symm
      set p : ℝ → EuclideanSpace ℝ (Fin n) := fun t => x + t • h with hp
      set g : ℝ → ℝ := fun t => q (p t) with hg
      have hpc : Continuous p := by
        rw [hp]; fun_prop
      have hpD : ∀ t ∈ Set.Icc (0:ℝ) 1, p t ∈ D := fun t ht => hDc.add_smul_sub_mem hx hy ht
      have hpt : ∀ t, HasDerivAt p h t := by
        intro t
        have := ((hasDerivAt_id t).smul_const h).const_add x
        simpa [hp] using this
      have hab' : a • x + b • y = p b := by
        have : a = 1 - b := by linarith
        rw [this, hp, hh]; simp only [sub_smul, one_smul, smul_sub]; abel
      rw [hab']
      have hp0 : p 0 = x := by simp [hp]
      have hp1 : p 1 = y := by simp [hp, hh]
      by_contra hcon
      push Not at hcon
      have hb1 : b ≤ 1 := by linarith
      -- maximum on [0,1]
      have hgc : ContinuousOn g (Set.Icc 0 1) :=
        hq.continuousOn.comp hpc.continuousOn (fun t ht => hpD t ht)
      obtain ⟨t1, ht1, hmax⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_isMaxOn
        ⟨0, by norm_num⟩ hgc
      have hgb : g b ≤ g t1 := hmax ⟨hb, hb1⟩
      have hg0 : g 0 < g t1 := by
        have : g 0 = q x := by simp [hg, hp0]
        rw [this]; exact lt_of_lt_of_le (lt_of_le_of_lt (le_max_left _ _) hcon) hgb
      have hg1 : g 1 < g t1 := by
        have : g 1 = q y := by simp [hg, hp1]
        rw [this]; exact lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hcon) hgb
      have ht1' : t1 ∈ Set.Ioo (0:ℝ) 1 := by
        refine ⟨lt_of_le_of_ne ht1.1 ?_, lt_of_le_of_ne ht1.2 ?_⟩
        · rintro rfl; exact lt_irrefl _ hg0
        · rintro rfl; exact lt_irrefl _ hg1
      have hloc : IsLocalMax g t1 :=
        hmax.localize.isLocalMax (Icc_mem_nhds ht1'.1 ht1'.2)
      -- derivatives
      have hU : IsOpen (p ⁻¹' D) := hDo.preimage hpc
      have hz1 : p t1 ∈ D := hpD t1 ht1
      have hev : ∀ᶠ t in nhds t1, p t ∈ D := hU.mem_nhds hz1
      have hcd : ∀ z ∈ D, ContDiffAt ℝ 2 q z := fun z hz => hq.contDiffAt (hDo.mem_nhds hz)
      have hg' : ∀ t, p t ∈ D → HasDerivAt g (fderiv ℝ q (p t) h) t := by
        intro t ht
        have hd : DifferentiableAt ℝ q (p t) := (hcd _ ht).differentiableAt (by norm_num)
        exact hd.hasFDerivAt.comp_hasDerivAt t (hpt t)
      have hderiv_ev : deriv g =ᶠ[nhds t1] fun t => fderiv ℝ q (p t) h :=
        hev.mono fun t ht => (hg' t ht).deriv
      have hdq : DifferentiableAt ℝ (fderiv ℝ q) (p t1) :=
        ((hcd _ hz1).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
      have hg'' : HasDerivAt (fun t => fderiv ℝ q (p t) h) (fderiv ℝ (fderiv ℝ q) (p t1) h h) t1 := by
        have h1 := hdq.hasFDerivAt.comp_hasDerivAt t1 (hpt t1)
        have h2 := (ContinuousLinearMap.apply ℝ ℝ h).hasFDerivAt.comp_hasDerivAt t1 h1
        exact h2
      have hdd : deriv (deriv g) t1 = fderiv ℝ (fderiv ℝ q) (p t1) h h := by
        rw [hderiv_ev.deriv_eq]; exact hg''.deriv
      have hd1 : deriv g t1 = 0 := hloc.hasDerivAt_eq_zero (hg' t1 hz1) ▸ (hg' t1 hz1).deriv
      have hfd0 : fderiv ℝ q (p t1) h = 0 := by rw [← (hg' t1 hz1).deriv]; exact hd1
      have hpos : 0 < fderiv ℝ (fderiv ℝ q) (p t1) h h := by
        have := hw (p t1) hz1 h hh0
        rw [hfd0] at this
        have e : d2 q (p t1) h h = fderiv ℝ (fderiv ℝ q) (p t1) h h := by
          simp [d2, iteratedFDeriv_two_apply]
        linarith
      have hmin : IsLocalMin g t1 :=
        isLocalMin_of_deriv_deriv_pos (by rw [hdd]; exact hpos) hd1 (hg' t1 hz1).continuousAt
      have hconst : g =ᶠ[nhds t1] fun _ => g t1 := by
        filter_upwards [hloc, hmin] with t h1 h2
        exact le_antisymm h1 h2
      have hdconst : deriv g =ᶠ[nhds t1] fun _ => 0 := by
        filter_upwards [hconst.eventuallyEq_nhds] with t ht
        rw [ht.deriv_eq]; simp
      have : deriv (deriv g) t1 = 0 := by
        rw [hdconst.deriv_eq]; simp
      rw [hdd] at this
      linarith
