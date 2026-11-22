-- Prove2me | solution 1 for PHarmGradientCompactness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:25:22.238044+00:00
-- url     : https://prove2.me/submissions/f4c42359-a759-4272-ad76-57e9a7d04497

import Definitions.Def_PHigherOrder_PHarmJetEquicontinuity
import Definitions.Def_PHigherOrder_PHarmRestrict
import Definitions.Def_PHigherOrder_PHarmJetTailEstimate
import Definitions.Def_PHigherOrder_JetLocalCompactness
import Definitions.Def_PHigherOrder_PHarmGradientCompactness
import Theorems.Thm_JetLocalCompactness
import Theorems.Thm_PHarmJetEquicontinuity
import Theorems.Thm_PHarmJetTailEstimate
import Theorems.Thm_PHarmRestrict


set_option autoImplicit false

theorem _root_.solution (p : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (F : FirstOrderEstimateInput p)
    (Ω : ℕ → Set Plane) (hmono : Monotone Ω)
    (v : ℕ → Plane → ℝ) (g : ℕ → Plane → Plane)
    (hph : ∀ n : ℕ, IsPHarm p (Ω n) (v n) (g n))
    (hbd : ∀ K : Set Plane, K ⊆ (⋃ n, Ω n) → IsCompact K →
        ∃ M : ℝ, 0 < M ∧ ∃ N : ℕ, ∀ n, N ≤ n → ∀ z ∈ K, |v n z| ≤ M) :
    (∀ n : ℕ, ContDiffOn ℝ 1 (v n) (Ω n)) ∧
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (V : Plane → ℝ) (G : Plane → Plane),
      (∀ K : Set Plane, K ⊆ (⋃ n, Ω n) → IsCompact K →
          TendstoUniformlyOn (fun i => v (φ i)) V Filter.atTop K) ∧
      (∀ K : Set Plane, K ⊆ (⋃ n, Ω n) → IsCompact K →
          TendstoUniformlyOn (fun i => gradient (v (φ i))) G Filter.atTop K) := by
  have hWopen : IsOpen (⋃ n, Ω n) := isOpen_iUnion fun n => (hph n).openOmega
  refine ⟨?_, ?_⟩
  · -- Part (a):  `C^1` is local, and near each point the one-ball estimate applies with a
    -- bound obtained from continuity on a compact closed ball.  `hbd` is not needed.
    intro n
    refine contDiffOn_of_locally_contDiffOn ?_
    intro z₀ hz₀
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hph n).openOmega z₀ hz₀
    have hR : (0 : ℝ) < ε / 8 := by positivity
    have hcbsub : Metric.closedBall z₀ (2 * (ε / 8)) ⊆ Ω n := by
      intro y hy
      refine hball ?_
      simp only [Metric.mem_closedBall] at hy
      simp only [Metric.mem_ball]
      linarith
    have hbsub : Metric.ball z₀ (2 * (ε / 8)) ⊆ Ω n :=
      Metric.ball_subset_closedBall.trans hcbsub
    obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall z₀ (2 * (ε / 8))).exists_bound_of_continuousOn
      ((hph n).contU.mono hcbsub)
    have hM : (0 : ℝ) < |M₀| + 1 := by positivity
    have hbnd : ∀ z ∈ Metric.ball z₀ (2 * (ε / 8)), |v n z| ≤ |M₀| + 1 := by
      intro z hz
      have h1 := hM₀ z (Metric.ball_subset_closedBall hz)
      rw [Real.norm_eq_abs] at h1
      have h2 : M₀ ≤ |M₀| := le_abs_self M₀
      linarith
    have hpharm : IsPHarm p (Metric.ball z₀ (2 * (ε / 8))) (v n) (g n) :=
      (PHarmRestrict p hp hp2 (Ω n) (v n) (g n) (hph n)).1 _ Metric.isOpen_ball hbsub
    have hjet := PHarmJetEquicontinuity p hp hp2 F z₀ (ε / 8) (|M₀| + 1) hR hM
      (v n) (g n) hpharm hbnd
    exact ⟨Metric.ball z₀ (3 * (ε / 8) / 2), Metric.isOpen_ball,
      Metric.mem_ball_self (by positivity), hjet.1.mono Set.inter_subset_right⟩
  · -- Part (b):  feed the tail estimate into the jet Arzela-Ascoli lemma, then read off
    -- the two components of the one resulting subsequence.
    have hunif : ∀ K : Set Plane, K ⊆ (⋃ n, Ω n) → IsCompact K →
        ∃ (N : ℕ) (A : ℝ),
          (∀ n, N ≤ n → ContinuousOn (fun z => (v n z, gradient (v n) z)) K) ∧
          (∀ n, N ≤ n → ∀ z ∈ K, ‖(v n z, gradient (v n) z)‖ ≤ A) ∧
          (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ n, N ≤ n → ∀ z ∈ K, ∀ z' ∈ K,
            dist z z' < δ →
              dist ((v n z, gradient (v n) z)) ((v n z', gradient (v n) z')) ≤ ε) := by
      intro K hK hKc
      obtain ⟨N, A, L, R, hA, hL, hR, hest⟩ :=
        PHarmJetTailEstimate p hp hp2 F Ω hmono v g hph hbd K hK hKc
      refine ⟨N, max A L, ?_, ?_, ?_⟩
      · exact fun n hn => ((hest n hn).1).prodMk (hest n hn).2.1
      · intro n hn z hz
        rw [Prod.norm_def]
        refine max_le ?_ ?_
        · rw [Real.norm_eq_abs]
          exact le_trans ((hest n hn).2.2.1 z hz) (le_max_left _ _)
        · exact le_trans ((hest n hn).2.2.2.1 z hz) (le_max_right _ _)
      · intro ε hε
        have hs0 : (0 : ℝ) < (ε / L) ^ (1 / F.kappa) :=
          Real.rpow_pos_of_pos (by positivity) _
        refine ⟨min (3 * R / 4) (min (2 * R * ((ε / L) ^ (1 / F.kappa))) (ε / L)),
          lt_min (by positivity) (lt_min (by positivity) (by positivity)), ?_⟩
        intro n hn z hz z' hz' hd
        rw [dist_eq_norm] at hd
        have hd1 : ‖z - z'‖ < 3 * R / 4 := lt_of_lt_of_le hd (min_le_left _ _)
        have hd2 : ‖z - z'‖ < 2 * R * ((ε / L) ^ (1 / F.kappa)) :=
          lt_of_lt_of_le hd ((min_le_right _ _).trans (min_le_left _ _))
        have hd3 : ‖z - z'‖ < ε / L :=
          lt_of_lt_of_le hd ((min_le_right _ _).trans (min_le_right _ _))
        rw [Prod.dist_eq]
        refine max_le ?_ ?_
        · rw [Real.dist_eq]
          calc |v n z - v n z'| ≤ L * ‖z - z'‖ := (hest n hn).2.2.2.2.2 z hz z' hz' hd1
            _ ≤ L * (ε / L) := mul_le_mul_of_nonneg_left hd3.le hL.le
            _ = ε := by field_simp
        · rw [dist_eq_norm]
          have hs : ‖z - z'‖ / (2 * R) ≤ (ε / L) ^ (1 / F.kappa) := by
            rw [div_le_iff₀ (by positivity)]
            nlinarith [hd2]
          calc ‖gradient (v n) z - gradient (v n) z'‖
              ≤ L * (‖z - z'‖ / (2 * R)) ^ F.kappa :=
                (hest n hn).2.2.2.2.1 z hz z' hz' hd1
            _ ≤ L * (((ε / L) ^ (1 / F.kappa)) ^ F.kappa) :=
                mul_le_mul_of_nonneg_left
                  (Real.rpow_le_rpow (by positivity) hs F.kappa_pos.le) hL.le
            _ = ε := by
                rw [← Real.rpow_mul (by positivity), one_div,
                  inv_mul_cancel₀ (ne_of_gt F.kappa_pos), Real.rpow_one]
                field_simp
    obtain ⟨φ, hφ, Jlim, hJ⟩ :=
      JetLocalCompactness (⋃ n, Ω n) hWopen (fun n z => (v n z, gradient (v n) z)) hunif
    refine ⟨φ, hφ, fun z => (Jlim z).1, fun z => (Jlim z).2, ?_, ?_⟩
    · intro K hK hKc
      have h := hJ K hK hKc
      rw [Metric.tendstoUniformlyOn_iff] at h ⊢
      intro ε hε
      filter_upwards [h ε hε] with i hi z hz
      refine lt_of_le_of_lt ?_ (hi z hz)
      rw [Prod.dist_eq]
      exact le_max_left _ _
    · intro K hK hKc
      have h := hJ K hK hKc
      rw [Metric.tendstoUniformlyOn_iff] at h ⊢
      intro ε hε
      filter_upwards [h ε hε] with i hi z hz
      refine lt_of_le_of_lt ?_ (hi z hz)
      rw [Prod.dist_eq]
      exact le_max_right _ _
