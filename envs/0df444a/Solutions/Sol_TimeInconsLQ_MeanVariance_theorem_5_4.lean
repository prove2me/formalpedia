-- Prove2me | solution 1 for TimeInconsLQ.MeanVariance.theorem_5_4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T12:55:48.489767+00:00
-- url     : https://prove2.me/submissions/6b73a4bf-3b95-434c-9a01-15815d24e1b2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_TimeInconsLQ_MeanVariance_Model
import Definitions.Def_TimeInconsLQ_MeanVariance_Market
import Definitions.Def_TimeInconsLQ_MeanVariance_Adjoint
import Theorems.Thm_TimeInconsLQ_MeanVariance_theorem_3_2
import Theorems.Thm_TimeInconsLQ_MeanVariance_lambda_identity
import Theorems.Thm_TimeInconsLQ_MeanVariance_proposition_5_3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Matrix

theorem prog_joint {Ω : Type*} [mΩ : MeasurableSpace Ω] {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E]
    (𝓕 : Filtration ℝ≥0 mΩ) (φ : ℝ≥0 → Ω → E) (hφ : IsStronglyProgressive 𝓕 φ) (T : ℝ≥0) :
    Measurable (fun q : ℝ × Ω => φ (min q.1.toNNReal T) q.2) := by
  have h := (hφ T).measurable
  have hm : @Measurable (ℝ × Ω) (Set.Iic T × Ω) _ (Subtype.instMeasurableSpace.prod (𝓕 T))
      (fun q : ℝ × Ω => ((⟨min q.1.toNNReal T, Set.mem_Iic.mpr (min_le_right _ _)⟩ : Set.Iic T), q.2)) := by
    let _ : MeasurableSpace Ω := 𝓕 T
    refine Measurable.prodMk ?_ ?_
    · refine Measurable.subtype_mk ?_
      exact (measurable_real_toNNReal.comp measurable_fst).min measurable_const
    · exact (measurable_id'' (𝓕.le T)).comp (@measurable_snd ℝ Ω _ mΩ)
  exact h.comp hm

theorem enorm_sq_le_sum {d : ℕ} (x : Fin d → ℝ) : ‖x‖ₑ ^ 2 ≤ ∑ j, ‖x j‖ₑ ^ 2 := by
  have h1 : ‖x‖₊ ≤ NNReal.sqrt (∑ j, ‖x j‖₊ ^ 2) := by
    rw [pi_nnnorm_le_iff]
    intro j
    rw [NNReal.le_sqrt_iff_sq_le]
    exact Finset.single_le_sum (f := fun j => ‖x j‖₊ ^ 2) (fun _ _ => bot_le) (Finset.mem_univ j)
  have h2 : ‖x‖₊ ^ 2 ≤ ∑ j, ‖x j‖₊ ^ 2 := by
    calc ‖x‖₊ ^ 2 ≤ (NNReal.sqrt (∑ j, ‖x j‖₊ ^ 2)) ^ 2 := pow_le_pow_left₀ bot_le h1 2
      _ = _ := NNReal.sq_sqrt _
  simp only [enorm_eq_nnnorm]
  exact_mod_cast h2

theorem L2F_of_coord {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}
    (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0) (φ : ℝ≥0 → Ω → Fin d → ℝ)
    (h : ∀ j, Peng1990.SMP.L2F 𝓕 P T (fun s ω => φ s ω j)) :
    Peng1990.SMP.L2F 𝓕 P T φ := by
  refine ⟨?_, ?_⟩
  · intro i
    let _ : MeasurableSpace (Set.Iic i × Ω) := Subtype.instMeasurableSpace.prod (𝓕 i)
    have := fun j => ((h j).1 i).measurable
    exact (measurable_pi_iff.mpr this).stronglyMeasurable
  · have hg : ∀ j, Measurable (fun q : ℝ × Ω => ‖φ (min q.1.toNNReal T) q.2 j‖ₑ ^ 2) :=
      fun j => (prog_joint 𝓕 _ (h j).1 T).enorm.pow_const 2
    have heq : ∀ ω (f : ℝ≥0 → Ω → ℝ≥0∞), ∫⁻ s in Set.Icc (0 : ℝ) T, f s.toNNReal ω =
        ∫⁻ s in Set.Icc (0 : ℝ) T, f (min s.toNNReal T) ω := by
      intro ω f
      refine setLIntegral_congr_fun measurableSet_Icc ?_
      intro s hs
      have : s.toNNReal ≤ T := by
        rw [Real.toNNReal_le_iff_le_coe]; exact hs.2
      simp [min_eq_left this]
    calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ‖φ s.toNNReal ω‖ₑ ^ 2 ∂volume ∂P
        ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∑ j, ‖φ s.toNNReal ω j‖ₑ ^ 2 ∂volume ∂P := by
          gcongr with ω s
          exact enorm_sq_le_sum _
      _ = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∑ j, ‖φ (min s.toNNReal T) ω j‖ₑ ^ 2 ∂volume ∂P := by
          congr 1; funext ω
          exact heq ω (fun s ω => ∑ j, ‖φ s ω j‖ₑ ^ 2)
      _ = ∑ j, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ‖φ (min s.toNNReal T) ω j‖ₑ ^ 2 ∂volume ∂P := by
          rw [← lintegral_finsetSum']
          · congr 1; funext ω
            rw [lintegral_finsetSum']
            intro j _
            exact ((hg j).comp (measurable_id.prodMk measurable_const)).aemeasurable
          · intro j _
            exact ((hg j).lintegral_prod_left').aemeasurable
      _ < ⊤ := by
          refine ENNReal.sum_lt_top.mpr ?_
          intro j _
          have := (h j).2
          simp only [heq _ (fun s ω => ‖φ s ω j‖ₑ ^ 2)] at this
          exact this

open TimeInconsLQ.MeanVariance in
theorem mvData_standing {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (mk : Market Ω d)
    (hmk : mk.Standing) : mk.mvData.Standing := by
  have hbdd0 : ∀ (c : ℝ), |c| ≤ 1 → EssBddOn mk.P mk.T (fun _ _ => c) := by
    intro c hc
    exact ⟨1, Filter.Eventually.of_forall (fun _ => hc)⟩
  have hL20 : ∀ {E : Type} [NormedAddCommGroup E],
      Peng1990.SMP.L2F mk.filt mk.P mk.T (fun (_ : ℝ≥0) (_ : Ω) => (0 : E)) := by
    intro E _
    refine ⟨isStronglyProgressive_const _ _, ?_⟩
    simp
  refine
    { prob := hmk.prob
      A_meas := fun _ _ => hmk.r_meas
      A_bdd := ?_
      B_prog := ?_
      C_prog := fun _ => isStronglyProgressive_const _ _
      D_prog := fun _ => isStronglyProgressive_const _ _
      Q_prog := isStronglyProgressive_const _ _
      R_prog := isStronglyProgressive_const _ _
      B_bdd := fun i _ => hmk.θ_bdd i
      C_bdd := fun _ _ _ => hbdd0 0 (by simp)
      D_bdd := ?_
      Q_bdd := fun _ _ => hbdd0 0 (by simp)
      R_bdd := fun _ _ => hbdd0 0 (by simp)
      b_L2 := hL20
      σ_L2 := fun _ => hL20
      Q_psd := Filter.Eventually.of_forall (fun _ => ⟨Matrix.isSymm_zero, Matrix.PosSemidef.zero⟩)
      R_psd := Filter.Eventually.of_forall (fun _ => ⟨Matrix.isSymm_zero, Matrix.PosSemidef.zero⟩)
      G_symm := Matrix.isSymm_one
      h_symm := Matrix.isSymm_one
      G_psd := Matrix.PosSemidef.one }
  · obtain ⟨K, hK⟩ := hmk.r_bdd
    exact ⟨K, fun s hs _ _ => hK s hs⟩
  · intro i
    have h := hmk.θ_prog i
    exact (Continuous.comp_stronglyMeasurable (g := fun (x : Fin d → ℝ) =>
      (Matrix.of fun (a : Fin d) (_ : Fin 1) => x a)) (by fun_prop) h)
  · intro k i j
    refine hbdd0 _ ?_
    show |(if j = k then (1:ℝ) else 0)| ≤ 1
    split_ifs <;> simp

open TimeInconsLQ.MeanVariance in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (mk : Market Ω d)
    (hmk : mk.Standing)
    (M : ℝ≥0 → Ω → ℝ) (U : ℝ≥0 → Ω → Fin d → ℝ) (hMU : mk.Class58 M U)
    (Γ2 : ℝ≥0 → Ω → ℝ) (γ2 : ℝ≥0 → Ω → Fin d → ℝ) (hΓ : mk.Class513 M U Γ2 γ2) :
    (∃ X, mk.mvData.IsClosedLoop (mk.alpha M U) (mk.beta M γ2) X) ∧
    ∀ X, mk.mvData.IsClosedLoop (mk.alpha M U) (mk.beta M γ2) X →
      mk.mvData.IsEquilibrium (mk.uStar M U γ2 X) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨X, hX, -⟩ := proposition_5_3 mk hmk M U hMU Γ2 γ2 hΓ
    exact ⟨X, hX⟩
  · intro X hX
    classical
    have hL := fun t (ht : t < mk.T) => lambda_identity mk hmk M U hMU Γ2 γ2 hΓ X hX t ht
    let p : ℝ≥0 → ℝ≥0 → Ω → Fin 1 → ℝ := fun t =>
      if ht : t < mk.T then Classical.choose (hL t ht) else 0
    have hp : ∀ t (ht : t < mk.T), p t = Classical.choose (hL t ht) := by
      intro t ht; simp [p, ht]
    refine theorem_3_2 mk.mvData (mvData_standing mk hmk) _ X p
      (fun _ => mk.kStar M U γ2 X) ?_ hX ?_ ?_
    · apply L2F_of_coord
      intro j
      obtain ⟨-, -, J, hJ, -⟩ := hX
      have h := (hJ 0 j).1
      convert h using 2
      simp [Market.mvData, Market.uStar, Matrix.mulVec, dotProduct]
    · intro t ht
      rw [hp t ht]
      exact (Classical.choose_spec (hL t ht)).1
    · intro t ht
      rw [hp t ht]
      exact (Classical.choose_spec (hL t ht)).2.2.2
