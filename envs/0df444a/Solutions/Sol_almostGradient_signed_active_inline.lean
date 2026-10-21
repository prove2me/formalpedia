-- Prove2me | solution 1 for almostGradient_signed_active_inline
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T15:07:30.345978+00:00
-- url     : https://prove2.me/submissions/b49c8072-e184-4e6e-b59c-aff44df217b9

import Mathlib
import Definitions.Def_ShorNonsmooth_NonlinEq_maxResidual
import Definitions.Def_ShorNonsmooth_NonlinEq_jacobianMatrix
import Definitions.Def_ShorNonsmooth_AlmostDiff_almostGradients
import Theorems.Thm_ShorNonsmooth_NonlinEq_maxResidual_local_inverse_bound
import Theorems.Thm_ShorNonsmooth_NonlinEq_maxResidual_active_signed_inner_approx
import Theorems.Thm_ShorNonsmooth_NonlinEq_maxResidual_differentiable_gradient_signed_active
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ShorNonsmooth.NonlinEq
theorem solution {n : ℕ}
    (ψ : Fin n → EuclideanSpace ℝ (Fin n) → ℝ) (xstar : EuclideanSpace ℝ (Fin n))
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : U ∈ nhds xstar)
    (hψ : ∀ i, ContDiffOn ℝ 1 (ψ i) U) :
    ∃ V ∈ nhds xstar, ∀ x ∈ V, maxResidual ψ x ≠ 0 →
      ∀ g ∈ ShorNonsmooth.AlmostDiff.almostGradients (maxResidual ψ) x,
        ∃ i : Fin n, ∃ σ : ℝ, σ ^ 2 = 1 ∧ g = σ • gradient (ψ i) x ∧
          σ * ψ i x = maxResidual ψ x ∧ |ψ i x| = maxResidual ψ x := by
  classical
    obtain ⟨Vdiff, hVdiff, hdiff⟩ :=
      maxResidual_differentiable_gradient_signed_active ψ xstar U hU hψ
    rcases mem_nhds_iff.mp (Filter.inter_mem hVdiff hU) with
      ⟨O, hOsub, hOopen, hxO⟩
    refine ⟨O, hOopen.mem_nhds hxO, ?_⟩
    intro x hxO hF0 g hg
    have hxUnhds : U ∈ nhds x :=
      Filter.mem_of_superset (hOopen.mem_nhds hxO) (fun y hy => (hOsub hy).2)
    haveI : Nonempty (Fin n) := by
      by_contra hne; haveI : IsEmpty (Fin n) := not_nonempty_iff.mp hne
      apply hF0; simp [maxResidual]
    obtain ⟨i0, hi0⟩ := exists_eq_ciSup_of_finite (f := fun i => |ψ i x|)
    have hFpos : 0 < maxResidual ψ x := by
      have hnonneg : 0 ≤ maxResidual ψ x := by
        unfold maxResidual
        exact Real.iSup_nonneg (fun i => abs_nonneg _)
      exact lt_of_le_of_ne hnonneg (Ne.symm hF0)
    have hi0pos : 0 < |ψ i0 x| := by
      rw [show |ψ i0 x| = maxResidual ψ x from hi0]
      exact hFpos
    have hi0ne : ψ i0 x ≠ 0 := abs_pos.mp hi0pos
    have hψi0cont : ContinuousAt (fun y => ψ i0 y) x :=
      ((hψ i0).contDiffAt hxUnhds).continuousAt
    have hFcont : ContinuousAt (maxResidual ψ) x := by
      have hneFinset : (Finset.univ : Finset (Fin n)).Nonempty :=
        Finset.univ_nonempty
      have hsup : ContinuousAt
          (fun y => Finset.univ.sup' hneFinset (fun i => |ψ i y|)) x := by
        refine ContinuousAt.finset_sup'_apply hneFinset ?_
        intro i _
        exact ((hψ i).contDiffAt hxUnhds).continuousAt.abs
      convert hsup using 1
      funext y
      unfold maxResidual
      exact (Finset.sup'_univ_eq_ciSup (fun i => |ψ i y|)).symm
    rcases hg with ⟨xs, hxs, hxsdiff, hcluster⟩
    have hxsi : ∀ᶠ k in Filter.atTop, xs k ∈ O :=
      hxs.eventually (hOopen.mem_nhds hxO)
    have hi0ev : ∀ᶠ k in Filter.atTop, ψ i0 (xs k) ≠ 0 :=
      hxs.eventually (hψi0cont.eventually_ne hi0ne)
    have hbranch_ev : ∀ᶠ k in Filter.atTop,
        ∃ i : Fin n, ∃ σ : ℝ, σ ^ 2 = 1 ∧
          gradient (maxResidual ψ) (xs k) = σ • gradient (ψ i) (xs k) ∧
          σ * ψ i (xs k) = maxResidual ψ (xs k) ∧
          |ψ i (xs k)| = maxResidual ψ (xs k) := by
      filter_upwards [hxsi, hi0ev] with k hkO hkne
      have hFne : maxResidual ψ (xs k) ≠ 0 := by
        intro hzero
        have hle := Finite.le_ciSup (fun j => |ψ j (xs k)|) i0
        have hpos : 0 < |ψ i0 (xs k)| := abs_pos.mpr hkne
        have hle0 : |ψ i0 (xs k)| ≤ 0 := hzero ▸ hle
        linarith
      exact hdiff (xs k) (hOsub hkO).1 hFne (hxsdiff k)
    obtain ⟨φ, hclusterφ, hφtop⟩ := hcluster.exists_seq_tendsto
    have hbranchφ : ∀ᶠ k in Filter.atTop,
        ∃ i : Fin n, ∃ σ : ℝ, σ ^ 2 = 1 ∧
          gradient (maxResidual ψ) (xs (φ k)) =
            σ • gradient (ψ i) (xs (φ k)) ∧
          σ * ψ i (xs (φ k)) = maxResidual ψ (xs (φ k)) ∧
          |ψ i (xs (φ k))| = maxResidual ψ (xs (φ k)) :=
      hφtop.eventually hbranch_ev
    let sign : Bool → ℝ := fun b => if b then -1 else 1
    have hlabel_ev : ∀ᶠ k in Filter.atTop,
        ∃ p : Fin n × Bool,
          gradient (maxResidual ψ) (xs (φ k)) =
            sign p.2 • gradient (ψ p.1) (xs (φ k)) ∧
          sign p.2 * ψ p.1 (xs (φ k)) = maxResidual ψ (xs (φ k)) ∧
          |ψ p.1 (xs (φ k))| = maxResidual ψ (xs (φ k)) := by
      filter_upwards [hbranchφ] with k hk
      rcases hk with ⟨i, σ, hσ2, hgσ, hσF, habs⟩
      rcases sq_eq_one_iff.mp hσ2 with hσ | hσ
      · refine ⟨(i, false), ?_⟩
        simpa [sign, hσ] using And.intro hgσ (And.intro hσF habs)
      · refine ⟨(i, true), ?_⟩
        simpa [sign, hσ] using And.intro hgσ (And.intro hσF habs)
    have hfreq : ∃ᶠ k in Filter.atTop, ∃ p ∈ (Set.univ : Set (Fin n × Bool)),
        gradient (maxResidual ψ) (xs (φ k)) =
          sign p.2 • gradient (ψ p.1) (xs (φ k)) ∧
        sign p.2 * ψ p.1 (xs (φ k)) = maxResidual ψ (xs (φ k)) ∧
        |ψ p.1 (xs (φ k))| = maxResidual ψ (xs (φ k)) :=
      hlabel_ev.frequently.mono (fun k hk => ⟨Classical.choose hk,
        Set.mem_univ _, Classical.choose_spec hk⟩)
    obtain ⟨⟨i, b⟩, _, hfreq⟩ :=
      (Filter.frequently_exists_finite (I := Set.univ) Set.finite_univ).mp hfreq
    let σ : ℝ := sign b
    let P : ℕ → Prop := fun k =>
      gradient (maxResidual ψ) (xs (φ k)) = sign b • gradient (ψ i) (xs (φ k)) ∧
      sign b * ψ i (xs (φ k)) = maxResidual ψ (xs (φ k)) ∧
      |ψ i (xs (φ k))| = maxResidual ψ (xs (φ k))
    have hfreqP : ∃ᶠ k in Filter.atTop, P k := by simpa [P] using hfreq
    have hPgt : ∀ N, ∃ k > N, P k := by
      intro N
      rcases (Filter.frequently_atTop.mp hfreqP) (N + 1) with ⟨k, hk, hP⟩
      exact ⟨k, Nat.lt_of_succ_le hk, hP⟩
    obtain ⟨ρ, hρmono, hρbranch⟩ := Nat.exists_strictMono_subsequence hPgt
    let zs : ℕ → EuclideanSpace ℝ (Fin n) := fun k => xs (φ (ρ k))
    have hzs : Filter.Tendsto zs Filter.atTop (nhds x) :=
      hxs.comp (hφtop.comp hρmono.tendsto_atTop)
    have hgradF : Filter.Tendsto (fun k => gradient (maxResidual ψ) (zs k))
        Filter.atTop (nhds g) := hclusterφ.comp hρmono.tendsto_atTop
    have hgradi : ContinuousAt (fun y => gradient (ψ i) y) x := by
      have hf := ((hψ i).contDiffAt hxUnhds).continuousAt_fderiv one_ne_zero
      change ContinuousAt (fun y =>
        (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
          (fderiv ℝ (ψ i) y)) x
      exact (InnerProductSpace.toDual ℝ
        (EuclideanSpace ℝ (Fin n))).symm.continuous.continuousAt.comp hf
    have hgradσ : Filter.Tendsto (fun k => σ • gradient (ψ i) (zs k))
        Filter.atTop (nhds (σ • gradient (ψ i) x)) :=
      hgradi.tendsto.const_smul σ |>.comp hzs
    have hgσ : g = σ • gradient (ψ i) x := by
      apply tendsto_nhds_unique hgradF
      convert hgradσ using 1
      funext k
      simpa [σ] using (hρbranch k).1
    have hψi : Filter.Tendsto (fun k => ψ i (zs k)) Filter.atTop (nhds (ψ i x)) :=
      ((hψ i).contDiffAt hxUnhds).continuousAt.tendsto.comp hzs
    have hσF : σ * ψ i x = maxResidual ψ x := by
      apply tendsto_nhds_unique (hψi.const_mul σ)
      rw [show (fun k => σ * ψ i (zs k)) = fun k => maxResidual ψ (zs k) from
        funext (fun k => by simpa [σ] using (hρbranch k).2.1)]
      exact hFcont.tendsto.comp hzs
    have habs : |ψ i x| = maxResidual ψ x := by
      apply tendsto_nhds_unique (hψi.abs)
      rw [show (fun k => |ψ i (zs k)|) = fun k => maxResidual ψ (zs k) from
        funext (fun k => by simpa [σ] using (hρbranch k).2.2)]
      exact hFcont.tendsto.comp hzs
    have hσ2 : σ ^ 2 = 1 := by dsimp [σ, sign]; cases b <;> norm_num
    exact ⟨i, σ, hσ2, hgσ, hσF, habs⟩
