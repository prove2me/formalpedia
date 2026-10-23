-- Prove2me | solution 1 for RiskFunctionals.Polyhedral.polyhedral_acceptability
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-22T08:50:46.551264+00:00
-- url     : https://prove2.me/submissions/708d7325-02e2-44f3-9048-9c96e0cbf353

import Mathlib
import Definitions.Def_RiskFunctionals_Polyhedral_Cones
import Definitions.Def_RiskFunctionals_Polyhedral_MultiPeriod

open MeasureTheory RiskFunctionals.Polyhedral

/-- counterexample data: T = 1, k = 1, V = univ, c 0 = 1, c 1 = 0, W t t = 1, W 1 0 = 0 -/
noncomputable def g79s_D : MultiPeriodData where
  k := fun _ => 1
  c := fun t _ => if t = 0 then 1 else 0
  V := fun _ => Set.univ
  W := fun t s _ => if s = t then 1 else 0

theorem g79s_k (t : ℕ) : g79s_D.k t = 1 := rfl

theorem g79s_sum (t : ℕ) (f : Fin (g79s_D.k t) → ℝ) : ∑ i, f i = f ⟨0, Nat.one_pos⟩ := by
  refine Fintype.sum_eq_single _ fun x hx => absurd (Fin.ext ?_) hx
  have : x.val < 1 := x.isLt
  show x.val = 0
  omega

@[simp] theorem g79s_card (t : ℕ) : (Finset.univ : Finset (Fin (g79s_D.k t))).card = 1 :=
  Finset.card_fin _

@[simp] theorem g79s_c (t : ℕ) : g79s_D.c t = fun _ => if t = 0 then 1 else 0 := rfl

@[simp] theorem g79s_W (t s : ℕ) :
    g79s_D.W t s = fun _ => if s = t then 1 else 0 := rfl

@[simp] theorem g79s_V (t : ℕ) : g79s_D.V t = Set.univ := rfl

theorem g79s_hD : g79s_D.IsPolyhedral 1 := fun t _ =>
  ⟨⟨0, Fin.elim0, Fin.elim0, by ext v; simp [g79s_D]⟩, Set.univ_nonempty⟩

theorem g79s_hi : g79s_D.CompleteRecourse 1 := by
  refine ⟨fun t _ => ⟨0, Fin.elim0, by ext v; simp [g79s_D]⟩, fun t ht => ?_⟩
  have ht1 : t = 1 := by simp at ht; omega
  subst ht1
  ext x
  simp only [Set.mem_image, Set.mem_univ, true_and, iff_true]
  refine ⟨fun _ => x, ?_⟩
  simp only [dotProduct, g79s_sum]
  simp

theorem solution : ¬ (∀ {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (p q : ENNReal) (hp : 1 ≤ p) (hp_top : p ≠ ⊤)
    (hpq : p⁻¹ + q⁻¹ = 1) (T : ℕ) (hT : 1 ≤ T) (𝓕 : ℕ → MeasurableSpace Ω)
    (h𝓕 : IsFiltrationUpTo mΩ T 𝓕) (D : MultiPeriodData) (hD : D.IsPolyhedral T)
    (hi : D.CompleteRecourse T),

    (D.dualSet P q T 𝓕 ⊆ {Z : ℕ → Ω → ℝ | ∀ t ∈ Finset.Icc 1 T,
        (∀ᵐ ω ∂P, 0 ≤ Z t ω) ∧ ∀ᵐ ω ∂P, P[Z t | 𝓕 (t - 1)] ω = 1} →
      (∀ Y : ℕ → Ω → ℝ, IsAdaptedLp P p T 𝓕 Y →
        D.functional P p T 𝓕 Y ≠ ⊥ ∧ D.functional P p T 𝓕 Y ≠ ⊤) ∧
      InformationMonotone P p T (fun 𝓖 Y => D.functional P p T 𝓖 Y) ∧
      PredictableTranslationEquivariant P p T 𝓕 (fun Y => (D.functional P p T 𝓕 Y).toReal) ∧
      ConcaveOnProcesses P p T 𝓕 (fun Y => (D.functional P p T 𝓕 Y).toReal) ∧
      MonotoneOnProcesses P p T 𝓕 (fun Y => (D.functional P p T 𝓕 Y).toReal) ∧
      StrictOnProcesses P p T 𝓕 (fun Y => (D.functional P p T 𝓕 Y).toReal) ∧
      ContinuousOnProcesses P p T 𝓕 (fun Y => (D.functional P p T 𝓕 Y).toReal) ∧
      PositivelyHomogeneousOnProcesses P p T 𝓕 (fun Y => (D.functional P p T 𝓕 Y).toReal)) ∧
    (D.dualSet P q T 𝓕 ⊆ {Z : ℕ → Ω → ℝ | ∀ t ∈ Finset.Icc 1 T,
        (∀ᵐ ω ∂P, 0 ≤ Z t ω) ∧ ∫ ω, Z t ω ∂P = 1} →
      (∀ Y : ℕ → Ω → ℝ, IsAdaptedLp P p T 𝓕 Y →
        D.functional P p T 𝓕 Y ≠ ⊥ ∧ D.functional P p T 𝓕 Y ≠ ⊤) ∧
      InformationMonotone P p T (fun 𝓖 Y => D.functional P p T 𝓖 Y) ∧
      WeakTranslationEquivariant P p T 𝓕 (fun Y => (D.functional P p T 𝓕 Y).toReal) ∧
      ConcaveOnProcesses P p T 𝓕 (fun Y => (D.functional P p T 𝓕 Y).toReal) ∧
      MonotoneOnProcesses P p T 𝓕 (fun Y => (D.functional P p T 𝓕 Y).toReal) ∧
      StrictOnProcesses P p T 𝓕 (fun Y => (D.functional P p T 𝓕 Y).toReal) ∧
      ContinuousOnProcesses P p T 𝓕 (fun Y => (D.functional P p T 𝓕 Y).toReal) ∧
      PositivelyHomogeneousOnProcesses P p T 𝓕 (fun Y => (D.functional P p T 𝓕 Y).toReal)) ∧
    (D.DualFeasible T →
      D.dualSet P q T 𝓕 ⊆ {Z : ℕ → Ω → ℝ |
        (∀ t ∈ Finset.Icc 1 T, ∀ᵐ ω ∂P, 0 ≤ Z t ω) ∧ ∫ ω, Z 1 ω ∂P = 1} →
      (∀ Y : ℕ → Ω → ℝ, IsAdaptedLp P p T 𝓕 Y →
        D.functional P p T 𝓕 Y ≠ ⊥ ∧ D.functional P p T 𝓕 Y ≠ ⊤) ∧
      InformationMonotone P p T (fun 𝓖 Y => D.functional P p T 𝓖 Y) ∧
      FirstPeriodTranslationEquivariant P p T 𝓕 (fun Y => (D.functional P p T 𝓕 Y).toReal) ∧
      ConcaveOnProcesses P p T 𝓕 (fun Y => (D.functional P p T 𝓕 Y).toReal) ∧
      MonotoneOnProcesses P p T 𝓕 (fun Y => (D.functional P p T 𝓕 Y).toReal) ∧
      ContinuousOnProcesses P p T 𝓕 (fun Y => (D.functional P p T 𝓕 Y).toReal) ∧
      PositivelyHomogeneousOnProcesses P p T 𝓕 (fun Y => (D.functional P p T 𝓕 Y).toReal))) := by
  intro h
  have hfil : IsFiltrationUpTo (inferInstance : MeasurableSpace Unit) 1
      (fun _ => (⊥ : MeasurableSpace Unit)) := ⟨rfl, fun _ _ _ _ => le_rfl, fun _ _ => bot_le⟩
  have hpq : (1 : ENNReal)⁻¹ + (⊤ : ENNReal)⁻¹ = 1 := by simp
  obtain ⟨ha, -, -⟩ := h (Measure.dirac ()) 1 ⊤ le_rfl ENNReal.one_ne_top hpq 1 le_rfl
    (fun _ => ⊥) hfil g79s_D g79s_hD g79s_hi
  have hsub : g79s_D.dualSet (Measure.dirac ()) ⊤ 1 (fun _ => ⊥) ⊆ {Z : ℕ → Unit → ℝ |
      ∀ t ∈ Finset.Icc 1 1, (∀ᵐ ω ∂(Measure.dirac ()), 0 ≤ Z t ω) ∧
        ∀ᵐ ω ∂(Measure.dirac ()), (Measure.dirac ())[Z t | (fun _ => ⊥) (t - 1)] ω = 1} := by
    intro Z hZ
    exfalso
    obtain ⟨-, h0, -⟩ := hZ
    have := h0 (fun _ => 1) (Set.mem_univ _)
    simp only [dotProduct, g79s_sum] at this
    simp at this
    linarith
  have hY : IsAdaptedLp (Measure.dirac ()) 1 1 (fun _ => ⊥) (fun _ _ => (0:ℝ)) :=
    fun t _ => ⟨measurable_const, memLp_const 0⟩
  obtain ⟨hbot, htop⟩ := (ha hsub).1 _ hY
  set F := g79s_D.functional (Measure.dirac ()) 1 1 (fun _ => ⊥) (fun _ _ => (0:ℝ)) with hF
  have hFr : F = ((F.toReal : ℝ) : EReal) := (EReal.coe_toReal htop hbot).symm
  let v : (t : ℕ) → Unit → Fin (g79s_D.k t) → ℝ :=
    fun t _ => if t = 0 then (fun _ => F.toReal + 1) else (fun _ => 0)
  have hfeas : g79s_D.Feasible (Measure.dirac ()) 1 1 (fun _ => ⊥) (fun _ _ => (0:ℝ)) v := by
    refine ⟨fun t _ => ⟨measurable_const, memLp_const _, Filter.Eventually.of_forall
      fun _ => Set.mem_univ _⟩, fun t ht => Filter.Eventually.of_forall fun ω => ?_⟩
    have ht1 : t = 1 := by simp at ht; omega
    subst ht1
    simp only [dotProduct, g79s_sum]
    simp [v, Finset.sum_range_succ]
  have hobj : g79s_D.objective (Measure.dirac ()) 1 v = F.toReal + 1 := by
    simp only [MultiPeriodData.objective, dotProduct, g79s_sum]
    simp [v, Finset.sum_range_succ]
  have hle : ((g79s_D.objective (Measure.dirac ()) 1 v : ℝ) : EReal) ≤ F :=
    le_sSup ⟨v, hfeas, rfl⟩
  rw [hobj] at hle
  have := EReal.coe_le_coe_iff.mp (hle.trans_eq hFr)
  linarith
