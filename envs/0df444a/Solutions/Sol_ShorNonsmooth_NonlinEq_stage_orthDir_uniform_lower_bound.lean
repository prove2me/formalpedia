-- Prove2me | solution 1 for ShorNonsmooth.NonlinEq.stage_orthDir_uniform_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T15:20:08.651953+00:00
-- url     : https://prove2.me/submissions/190bde6e-2e89-476e-a0b3-74338c283da4

import Mathlib
import Definitions.Def_ShorNonsmooth_NonlinEq_orthStage
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ShorNonsmooth.NonlinEq
theorem solution {n : ℕ}
    (ψ : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (hψ : ∀ i, ContDiff ℝ 1 (ψ i))
    (hind : LinearIndependent ℝ fun i => gradient (ψ i) (0 : EuclideanSpace ℝ (Fin n))) :
    ∃ η > 0, ∃ b > 0, ∀ (x : ℕ → EuclideanSpace ℝ (Fin n)) (k : Fin n),
      (∀ j : Fin (k.val + 1), ‖x j.val‖ < η) → b ≤ ‖orthDir ψ x k‖ := by
  classical
  by_cases hn : n = 0
  · subst n
    refine ⟨1, by norm_num, 1, by norm_num, ?_⟩
    intro x k; exact k.elim0
  · let z0 : Fin n → EuclideanSpace ℝ (Fin n) := fun i => gradient (ψ i) 0
    let pref (k : Fin n) (z : Fin n → EuclideanSpace ℝ (Fin n)) :
        Fin (k.val + 1) → EuclideanSpace ℝ (Fin n) :=
      fun j => z ⟨j.val, by omega⟩
    let bad (k : Fin n) : Set (Fin n → EuclideanSpace ℝ (Fin n)) :=
      {z | ¬ LinearIndependent ℝ (pref k z)}
    have hbase (k : Fin n) : z0 ∉ bad k := by
      intro hlin
      apply hlin
      let prefk : Fin (k.val + 1) → Fin n := fun j => ⟨j.val, by omega⟩
      have himp : Function.Injective prefk := by
        intro a b hab
        apply Fin.ext
        simpa using congrArg Fin.val hab
      convert (hind.comp prefk himp) using 1
      ext j
      simp [pref, z0, prefk]
    have hbadClosed (k : Fin n) : IsClosed (bad k) := by
      have hprefcont : Continuous (pref k) := by
        apply continuous_pi
        intro j
        simpa [pref] using
          (continuous_apply (A := fun _ : Fin n => EuclideanSpace ℝ (Fin n))
            (i := ⟨j.val, by omega⟩))
      have hopen : IsOpen
          {z : Fin n → EuclideanSpace ℝ (Fin n) | LinearIndependent ℝ (pref k z)} :=
        (isOpen_setOf_linearIndependent (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin n))
          (ι := Fin (k.val + 1))).preimage hprefcont
      change IsClosed {z : Fin n → EuclideanSpace ℝ (Fin n) |
        ¬ LinearIndependent ℝ (pref k z)}
      exact hopen.isClosed_compl
    have hbadne (k : Fin n) : (bad k).Nonempty :=
      ⟨fun _ : Fin n => (0 : EuclideanSpace ℝ (Fin n)), by
        intro hli
        simpa [pref] using hli.ne_zero ⟨0, Nat.succ_pos k.val⟩⟩
    let d : Fin n → ℝ := fun k => Metric.infDist z0 (bad k)
    have hdpos : ∀ k, 0 < d k := fun k =>
      Iff.mp ((IsClosed.notMem_iff_infDist_pos (hbadClosed k)) (hbadne k)) (hbase k)
    let k0 : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
    let D := Finset.univ.inf' ⟨k0, Finset.mem_univ k0⟩ d
    have hDpos : 0 < D := by
      exact Iff.mpr ((Finset.lt_inf'_iff (s := Finset.univ) (f := d))
        ⟨k0, Finset.mem_univ k0⟩)
        (by intro k hk; exact hdpos k)
    have hDle : ∀ k, D ≤ d k := fun k => Finset.inf'_le d (Finset.mem_univ k)
    let G : EuclideanSpace ℝ (Fin n) → Fin n → EuclideanSpace ℝ (Fin n) :=
      fun y i => gradient (ψ i) y
    have hGcont : ContinuousAt G 0 := by
      apply continuousAt_pi.mpr; intro i
      have hcont : Continuous (fun y => gradient (ψ i) y) := by
        have hf := (hψ i).continuous_fderiv one_ne_zero
        change Continuous fun y =>
          (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
            (fderiv ℝ (ψ i) y)
        exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous.comp hf
      exact hcont.continuousAt
    have hnbhd :
        {y : EuclideanSpace ℝ (Fin n) | dist (G y) z0 < D / 2} ∈ nhds 0 :=
      hGcont.preimage_mem_nhds
        (Metric.ball_mem_nhds z0 (half_pos hDpos))
    rcases Metric.mem_nhds_iff.mp hnbhd with ⟨ε, hεpos, hε⟩
    refine ⟨ε, hεpos, D / 2, half_pos hDpos, ?_⟩
    intro x k hxsmall
    let y : ℕ → EuclideanSpace ℝ (Fin n) := fun j => if h : j ≤ k.val then x j else 0
    let z : Fin n → EuclideanSpace ℝ (Fin n) := fun i => gradient (ψ i) (y i)
    have hzclose : dist z z0 < D / 2 := by
      rw [dist_pi_lt_iff (half_pos hDpos)]
      intro i
      have hyball : y i ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε := by
        by_cases hi : i.val ≤ k.val
        · have hxi : ‖x i‖ < ε := hxsmall ⟨i.val, Nat.lt_succ_of_le hi⟩
          simpa [Metric.mem_ball, dist_eq_norm, y, hi] using hxi
        · simpa [Metric.mem_ball, y, hi] using hεpos
      have hcoord : dist (G (y i)) z0 < D / 2 := by simpa [G] using hε hyball
      exact lt_of_le_of_lt (by simpa [G, z, z0] using
        (dist_le_pi_dist (G (y i)) z0 i)) hcoord
    let K : Submodule ℝ (EuclideanSpace ℝ (Fin n)) := Submodule.span ℝ
      (Set.range fun j : Fin k.val =>
        gradient (ψ ⟨j.val, j.isLt.trans k.isLt⟩) (y j.val))
    let φ := Kᗮ.starProjection (z k)
    have hφ : φ = orthDir ψ y k := rfl
    let z' : Fin n → EuclideanSpace ℝ (Fin n) := Function.update z k (z k - φ)
    have hz' : z' ∈ bad k := by
      intro hli
      have hmemK : z k - φ ∈ K := by
        have hsum := Submodule.starProjection_add_starProjection_orthogonal
          (K := K) (z k)
        have : z k - φ = K.starProjection (z k) := by
          rw [show Kᗮ.starProjection (z k) = φ from rfl] at hsum
          simpa using congrArg (fun t => t - φ) hsum.symm
        rw [this]
        exact Submodule.starProjection_apply_mem K (z k)
      have hnot := hli.notMem_span (Fin.last k.val)
      apply hnot
      let earlier : Fin k.val → EuclideanSpace ℝ (Fin n) :=
        fun j => z' ⟨j.val, by omega⟩
      have hfun : earlier = (fun j : Fin k.val =>
          gradient (ψ ⟨j.val, j.isLt.trans k.isLt⟩) (y j.val)) := by
        funext j
        have hne : (⟨j.val, by omega⟩ : Fin n) ≠ k :=
          fun h => (Nat.ne_of_lt j.isLt) (congrArg Fin.val h)
        simp [earlier, z', z, hne]
      have hsubset : Set.range earlier ⊆ pref k z' '' ({Fin.last k.val}ᶜ) := by
        rintro _ ⟨j, rfl⟩
        refine ⟨⟨j.val, Nat.lt_succ_of_lt j.isLt⟩, ?_, ?_⟩
        · rw [Set.mem_compl_iff, Set.mem_singleton_iff]
          intro h
          exact (Nat.ne_of_lt j.isLt) (congrArg Fin.val h)
        · simp [pref, earlier]
      have hmemSpan : z k - φ ∈ Submodule.span ℝ (Set.range earlier) := by
        simpa [hfun, K] using hmemK
      simpa [pref, z', Function.update_self] using
        (Submodule.span_mono hsubset) hmemSpan
    have hdistle : dist z z' ≤ ‖φ‖ := by
      rw [dist_pi_le_iff (norm_nonneg φ)]
      intro i
      by_cases hik : i = k
      · subst i
        simp [z', Function.update_self, dist_eq_norm, φ, sub_sub_cancel]
      · simp only [z', Function.update_of_ne hik, dist_self]
        exact norm_nonneg φ
    have htriangle : d k ≤ dist z0 z + dist z z' := by
      calc
        d k ≤ dist z0 z' := Metric.infDist_le_dist_of_mem hz'
        _ ≤ dist z0 z + dist z z' := dist_triangle _ _ _
    have hhalf : D / 2 < ‖φ‖ := by
      have hzclose' : dist z0 z < D / 2 := by simpa [dist_comm] using hzclose
      have hdz : d k < D / 2 + ‖φ‖ := by linarith
      linarith [hDle k, hdz]
    have hφx : orthDir ψ y k = orthDir ψ x k := by simp [orthDir, y]
    rw [hφx] at hφ
    simpa [hφ] using le_of_lt hhalf
