-- Prove2me | solution 1 for RiskFunctionals.Deviation.integral_conjugate_duality
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T17:54:58.813579+00:00
-- url     : https://prove2.me/submissions/8ff7ccfd-ecff-4490-b412-dfbd619bd6ff

import Mathlib
import Definitions.Def_RiskFunctionals_Deviation_MinimalLoss
-- ===== module A

noncomputable section
set_option linter.unusedSectionVars false
open MeasureTheory Set Filter Topology RiskFunctionals.Deviation

namespace X5ICD

/-- The right derivative, a measurable subgradient selection. -/
def dR (h : ℝ → ℝ) (v : ℝ) : ℝ := derivWithin h (Ioi v) v

variable {h : ℝ → ℝ} (hconv : ConvexOn ℝ univ h)
include hconv

lemma dR_sub (v u : ℝ) : h v + dR h v * (u - v) ≤ h u := by
  have hi : ∀ x : ℝ, x ∈ interior (univ : Set ℝ) := by simp
  rcases lt_trichotomy u v with huv | rfl | huv
  · have h1 := hconv.slope_le_leftDeriv_of_mem_interior (mem_univ u) (hi v) huv
    have h2 := hconv.leftDeriv_le_rightDeriv_of_mem_interior (hi v)
    have h3 : slope h u v ≤ dR h v := h1.trans h2
    rw [slope_def_field] at h3
    rw [div_le_iff₀ (by linarith)] at h3
    nlinarith
  · simp
  · have h1 := hconv.rightDeriv_le_slope_of_mem_interior (hi v) (mem_univ u) huv
    change dR h v ≤ slope h v u at h1
    rw [slope_def_field, le_div_iff₀ (by linarith)] at h1
    nlinarith

lemma dR_mono : Monotone (dR h) := by
  intro x y hxy
  exact hconv.monotoneOn_rightDeriv (by simp) (by simp) hxy

lemma conj_dR (v : ℝ) : fenchelConj h (dR h v) = ((v * dR h v - h v : ℝ) : EReal) := by
  apply le_antisymm
  · refine iSup_le fun u => EReal.coe_le_coe_iff.mpr ?_
    have := dR_sub hconv v u
    nlinarith
  · exact le_iSup (fun u : ℝ => ((u * dR h v - h u : ℝ) : EReal)) v

omit hconv in
lemma fy (u z : ℝ) : ((u * z - h u : ℝ) : EReal) ≤ fenchelConj h z :=
  le_iSup (fun u : ℝ => ((u * z - h u : ℝ) : EReal)) u

omit hconv in
lemma le_toReal' {x : EReal} {r : ℝ} (hx : x ≠ ⊤) (h : (r : EReal) ≤ x) : r ≤ x.toReal := by
  induction x using EReal.rec with
  | bot => exact absurd h (not_le.mpr (EReal.bot_lt_coe r))
  | top => exact absurd rfl hx
  | coe x => simpa using h

lemma h_cont : Continuous h :=
  continuousOn_univ.mp (hconv.continuousOn isOpen_univ)

end X5ICD

-- ===== module B

noncomputable section
set_option linter.unusedSectionVars false
open MeasureTheory Set Filter Topology RiskFunctionals.Deviation

namespace X5ICD

theorem main {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (p q : ENNReal) [hp1 : Fact (1 ≤ p)]
    [hpq : p.HolderConjugate q] (h : ℝ → ℝ) (hconv : ConvexOn ℝ Set.univ h)
    (V : Ω → ℝ) (hV : Measurable V) (hVp : MemLp V p P) :
    (Integrable (fun ω => h (V ω)) P →
      ((∫ ω, h (V ω) ∂P : ℝ) : EReal) =
        ⨆ Z ∈ {Z : Ω → ℝ | Measurable Z ∧ MemLp Z q P ∧ HasFiniteExpectedConj P h Z},
          ((∫ ω, V ω * Z ω ∂P - expectedConj P h Z : ℝ) : EReal)) ∧
    (¬ Integrable (fun ω => h (V ω)) P →
      ⨆ Z ∈ {Z : Ω → ℝ | Measurable Z ∧ MemLp Z q P ∧ HasFiniteExpectedConj P h Z},
          ((∫ ω, V ω * Z ω ∂P - expectedConj P h Z : ℝ) : EReal) = ⊤) := by
  set S := {Z : Ω → ℝ | Measurable Z ∧ MemLp Z q P ∧ HasFiniteExpectedConj P h Z} with hS
  set sup := ⨆ Z ∈ S, ((∫ ω, V ω * Z ω ∂P - expectedConj P h Z : ℝ) : EReal) with hsup
  have hc := h_cont hconv
  have hhV : Measurable (fun ω => h (V ω)) := hc.measurable.comp hV
  have hVi : Integrable V P := hVp.integrable hp1.out
  set z0 := dR h 0 with hz0
  set ℓ : Ω → ℝ := fun ω => V ω * z0 + h 0 with hℓ
  have hℓi : Integrable ℓ P := (hVi.mul_const z0).add (integrable_const _)
  have hℓm : Measurable ℓ := (hV.mul_const z0).add_const _
  have hℓle : ∀ ω, ℓ ω ≤ h (V ω) := by
    intro ω
    have := dR_sub hconv 0 (V ω)
    simp only [hℓ]; rw [← hz0] at this; linarith
  let E : ℕ → Set Ω := fun n => {ω | |V ω| ≤ n}
  have hEm : ∀ n, MeasurableSet (E n) := fun n =>
    measurableSet_le (continuous_abs.measurable.comp hV) measurable_const
  let F : Ω → ℝ := fun ω => h (V ω) - ℓ ω
  have hFm : Measurable F := hhV.sub hℓm
  have hF0 : ∀ ω, 0 ≤ F ω := fun ω => sub_nonneg.mpr (hℓle ω)
  let G : ℕ → Ω → ℝ := fun n => (E n).indicator F
  have hG0 : ∀ n ω, 0 ≤ G n ω := fun n ω => indicator_nonneg (fun ω _ => hF0 ω) ω
  -- bounds on [-n, n]
  have hbd : ∀ n : ℕ, ∃ C, ∀ x ∈ Icc (-(n : ℝ)) n, ‖h x‖ ≤ C := fun n =>
    isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
  have hGi : ∀ n, Integrable (G n) P := by
    intro n
    obtain ⟨C, hC⟩ := hbd n
    refine Integrable.of_bound (hFm.indicator (hEm n)).aestronglyMeasurable
      (C + n * |z0| + |h 0|) (ae_of_all _ fun ω => ?_)
    by_cases hω : ω ∈ E n
    · have hω' : |V ω| ≤ n := hω
      rw [show G n ω = F ω from indicator_of_mem hω _]
      have h1 := hC (V ω) (abs_le.mp hω')
      have h2 : |V ω * z0| ≤ n * |z0| := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_right hω' (abs_nonneg _)
      simp only [F, hℓ, Real.norm_eq_abs] at h1 ⊢
      have := abs_add_le (V ω * z0) (h 0)
      calc |h (V ω) - (V ω * z0 + h 0)| ≤ |h (V ω)| + |V ω * z0 + h 0| := abs_sub _ _
        _ ≤ C + n * |z0| + |h 0| := by linarith
    · rw [show G n ω = 0 from indicator_of_notMem hω _]
      simp only [norm_zero]
      have := (norm_nonneg (h 0)).trans (hC 0 (by constructor <;> simp))
      positivity
  -- the truncated subgradient
  let Zn : ℕ → Ω → ℝ := fun n ω => if |V ω| ≤ n then dR h (V ω) else z0
  let κ : ℕ → Ω → ℝ := fun n ω =>
    if |V ω| ≤ n then V ω * dR h (V ω) - h (V ω) else -h 0
  have hconjZ : ∀ n ω, fenchelConj h (Zn n ω) = ((κ n ω : ℝ) : EReal) := by
    intro n ω
    simp only [Zn, κ]
    split_ifs
    · exact conj_dR hconv _
    · rw [hz0, conj_dR hconv 0]; simp
  have hZm : ∀ n, Measurable (Zn n) := fun n =>
    Measurable.ite (hEm n) ((dR_mono hconv).measurable.comp hV) measurable_const
  have hZb : ∀ n : ℕ, ∀ ω, |Zn n ω| ≤ |dR h (-n)| + |dR h n| + |z0| := by
    intro n ω
    simp only [Zn]
    split_ifs with hω
    · have ⟨h1, h2⟩ := abs_le.mp hω
      have l1 := dR_mono hconv h1
      have l2 := dR_mono hconv h2
      have := abs_nonneg z0
      rw [abs_le]; constructor
      · have := neg_abs_le (dR h (-n)); have := abs_nonneg (dR h n); linarith
      · have := le_abs_self (dR h n); have := abs_nonneg (dR h (-n)); linarith
    · have := abs_nonneg (dR h (-n)); have := abs_nonneg (dR h n); linarith
  have hZq : ∀ n, MemLp (Zn n) q P := fun n =>
    MemLp.of_bound (hZm n).aestronglyMeasurable _ (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs]; exact hZb n ω)
  have hκ : ∀ n ω, V ω * Zn n ω - κ n ω = ℓ ω + G n ω := by
    intro n ω
    by_cases hω : |V ω| ≤ n
    · have hω' : ω ∈ E n := hω
      simp only [Zn, κ, G, F, if_pos hω, indicator_of_mem hω']
      ring
    · have hω' : ω ∉ E n := hω
      simp only [Zn, κ, G, if_neg hω, indicator_of_notMem hω']
      simp only [hℓ]; ring
  have hVZi : ∀ n, Integrable (fun ω => V ω * Zn n ω) P := fun n =>
    hVp.integrable_mul (hZq n)
  have hκi : ∀ n, Integrable (κ n) P := by
    intro n
    have : κ n = fun ω => V ω * Zn n ω - (ℓ ω + G n ω) := by
      funext ω; have := hκ n ω; linarith
    rw [this]
    exact (hVZi n).sub (hℓi.add (hGi n))
  have hZS : ∀ n, Zn n ∈ S := by
    intro n
    refine ⟨hZm n, hZq n, ae_of_all _ fun ω => by rw [hconjZ]; exact EReal.coe_ne_top _, ?_⟩
    have : (fun ω => (fenchelConj h (Zn n ω)).toReal) = κ n := by
      funext ω; rw [hconjZ]; rfl
    rw [this]; exact hκi n
  have hval : ∀ n, ∫ ω, V ω * Zn n ω ∂P - expectedConj P h (Zn n) =
      ∫ ω, ℓ ω ∂P + ∫ ω, G n ω ∂P := by
    intro n
    have : expectedConj P h (Zn n) = ∫ ω, κ n ω ∂P := by
      unfold expectedConj
      congr 1; funext ω; rw [hconjZ]; rfl
    rw [this, ← integral_sub (hVZi n) (hκi n), ← integral_add hℓi (hGi n)]
    congr 1; funext ω; exact hκ n ω
  have hge : ∀ n, ((∫ ω, ℓ ω ∂P + ∫ ω, G n ω ∂P : ℝ) : EReal) ≤ sup := by
    intro n
    rw [← hval n]
    exact le_iSup₂ (f := fun Z (_ : Z ∈ S) =>
      ((∫ ω, V ω * Z ω ∂P - expectedConj P h Z : ℝ) : EReal)) (Zn n) (hZS n)
  -- monotone convergence data
  have hmono : ∀ ω, Monotone fun n => G n ω := by
    intro ω n m hnm
    refine indicator_le_indicator_of_subset (fun x hx => ?_) (fun x => hF0 x) ω
    show |V x| ≤ (m : ℝ)
    exact le_trans (show |V x| ≤ (n : ℝ) from hx) (Nat.cast_le.mpr hnm)
  have htend : ∀ ω, Tendsto (fun n => G n ω) atTop (𝓝 (F ω)) := by
    intro ω
    refine tendsto_atTop_of_eventually_const (i₀ := ⌈|V ω|⌉₊) fun n hn => ?_
    have : ω ∈ E n := show |V ω| ≤ (n : ℝ) from
      le_trans (Nat.le_ceil (|V ω|)) (Nat.cast_le.mpr hn)
    exact indicator_of_mem this _
  refine ⟨fun hint => ?_, fun hni => ?_⟩
  · have hFi : Integrable F P := hint.sub hℓi
    apply le_antisymm
    · have ht := integral_tendsto_of_tendsto_of_monotone hGi hFi (ae_of_all _ hmono)
        (ae_of_all _ htend)
      have ht' : Tendsto (fun n => ∫ ω, ℓ ω ∂P + ∫ ω, G n ω ∂P) atTop
          (𝓝 (∫ ω, h (V ω) ∂P)) := by
        have : ∫ ω, h (V ω) ∂P = ∫ ω, ℓ ω ∂P + ∫ ω, F ω ∂P := by
          rw [← integral_add hℓi hFi]; congr 1; funext ω; simp [F]
        rw [this]; exact ht.const_add _
      exact le_of_tendsto' ((continuous_coe_real_ereal.tendsto _).comp ht') hge
    · refine iSup₂_le fun Z hZ => EReal.coe_le_coe_iff.mpr ?_
      obtain ⟨hZm', hZq', hfin, hint'⟩ := hZ
      have hVZ : Integrable (fun ω => V ω * Z ω) P := hVp.integrable_mul hZq'
      unfold expectedConj
      rw [← integral_sub hVZ hint']
      refine integral_mono_ae (hVZ.sub hint') hint ?_
      filter_upwards [hfin] with ω hω
      have := le_toReal' hω (fy (V ω) (Z ω))
      linarith
  · by_contra hne
    have hbot : sup ≠ ⊥ := ne_bot_of_gt (lt_of_lt_of_le (EReal.bot_lt_coe _) (hge 0))
    set M := sup.toReal
    have hM : ∀ n, ∫ ω, ℓ ω ∂P + ∫ ω, G n ω ∂P ≤ M := by
      intro n
      have := hge n
      rw [← EReal.coe_toReal hne hbot] at this
      exact EReal.coe_le_coe_iff.mp this
    have hFi : Integrable F P := by
      refine ⟨hFm.aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hF0)]
      have hl := lintegral_tendsto_of_tendsto_of_monotone (μ := P)
        (f := fun n ω => ENNReal.ofReal (G n ω)) (F := fun ω => ENNReal.ofReal (F ω))
        (fun n => ((hFm.indicator (hEm n)).ennreal_ofReal).aemeasurable)
        (ae_of_all _ fun ω n m hnm => ENNReal.ofReal_le_ofReal (hmono ω hnm))
        (ae_of_all _ fun ω => (ENNReal.continuous_ofReal.tendsto _).comp (htend ω))
      have hle : ∀ n, ∫⁻ ω, ENNReal.ofReal (G n ω) ∂P ≤
          ENNReal.ofReal (M - ∫ ω, ℓ ω ∂P) := by
        intro n
        rw [← ofReal_integral_eq_lintegral_ofReal (hGi n) (ae_of_all _ (hG0 n))]
        exact ENNReal.ofReal_le_ofReal (by linarith [hM n])
      exact lt_of_le_of_lt (le_of_tendsto' hl hle) ENNReal.ofReal_lt_top
    apply hni
    have : (fun ω => h (V ω)) = fun ω => F ω + ℓ ω := by funext ω; simp [F]
    rw [this]; exact hFi.add hℓi

end X5ICD

end

open MeasureTheory RiskFunctionals.Deviation

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (p q : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    [p.HolderConjugate q] (h : ℝ → ℝ) (hconv : ConvexOn ℝ Set.univ h)
    (hlsc : LowerSemicontinuous h) (hconj : ∀ v : ℝ, 0 ≤ fenchelConj h v)
    (V : Ω → ℝ) (hV : Measurable V) (hVp : MemLp V p P) :
    (Integrable (fun ω => h (V ω)) P →
      ((∫ ω, h (V ω) ∂P : ℝ) : EReal) =
        ⨆ Z ∈ {Z : Ω → ℝ | Measurable Z ∧ MemLp Z q P ∧ HasFiniteExpectedConj P h Z},
          ((∫ ω, V ω * Z ω ∂P - expectedConj P h Z : ℝ) : EReal)) ∧
    (¬ Integrable (fun ω => h (V ω)) P →
      ⨆ Z ∈ {Z : Ω → ℝ | Measurable Z ∧ MemLp Z q P ∧ HasFiniteExpectedConj P h Z},
          ((∫ ω, V ω * Z ω ∂P - expectedConj P h Z : ℝ) : EReal) = ⊤) :=
  X5ICD.main P p q h hconv V hV hVp

