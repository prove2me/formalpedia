-- Prove2me | solution 1 for ReflectedBSDE.Existence.proposition_2_2
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-13T01:57:19.320168+00:00
-- url     : https://prove2.me/submissions/9d631b5d-8da9-4e54-aab6-4e1260a4e61c

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_ReflectedBSDE_Existence_Skorohod
import Definitions.Def_ReflectedBSDE_Existence_Setting
import Definitions.Def_ReflectedBSDE_Existence_Solution

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Peng1990.SMP

namespace ReflectedBSDE.Existence

namespace RCex

noncomputable def P0 : Measure Unit := Measure.dirac ()

instance : IsProbabilityMeasure P0 := by unfold P0; infer_instance

def B0 : ℝ≥0 → Unit → Fin 0 → ℝ := fun _ _ => 0

lemma hB0 : IsStdBrownian P0 B0 := ⟨fun _ => measurable_const, fun j => j.elim0,
  iIndepFun.of_subsingleton⟩

lemma prog_det (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Unit)) (g : ℝ≥0 → ℝ)
    (hg : Continuous g) : IsStronglyProgressive 𝓕 (fun t (_ : Unit) => g t) := fun i => by
  have h1 : Measurable[Subtype.instMeasurableSpace.prod (𝓕 i)]
      (fun p : Set.Iic i × Unit => (p.1 : ℝ≥0)) :=
    measurable_subtype_coe.comp (@measurable_fst _ _ _ (𝓕 i))
  exact (hg.measurable.comp h1).stronglyMeasurable

lemma ae_P0 {p : Unit → Prop} (h : ∀ᵐ ω ∂P0, p ω) : p () := by
  obtain ⟨ω, hω⟩ := h.exists
  exact hω

def f0 : ℝ≥0 → Unit → ℝ → (Fin 0 → ℝ) → ℝ := fun _ _ _ _ => 0

lemma zero_coeff (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Unit)) (T : ℝ≥0) :
    IsLipschitzCoeff 𝓕 P0 T 1 f0 :=
  ⟨fun _ _ => ⟨isStronglyProgressive_const _ _, by simp [f0]⟩, one_pos,
    ae_of_all _ fun _ _ _ y y' z z' => by
      simp only [f0, sub_self, abs_zero, one_mul]
      unfold euclNorm; positivity⟩

lemma zero_terminal (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Unit)) (T : ℝ≥0) :
    IsTerminalValue 𝓕 P0 T (fun _ => 0) := ⟨stronglyMeasurable_const, by simp⟩

lemma supSq_lt {T : ℝ≥0} {X : ℝ≥0 → Unit → ℝ} (h : ∀ t ≤ T, |X t ()| ≤ 1) :
    supSqMoment P0 T X < ⊤ := by
  unfold supSqMoment P0
  rw [lintegral_dirac]
  refine lt_of_le_of_lt (iSup₂_le fun t ht => ?_) (ENNReal.one_lt_top)
  rw [Real.enorm_eq_ofReal_abs]
  calc ENNReal.ofReal |X t ()| ^ 2 ≤ (ENNReal.ofReal 1) ^ 2 := by
        gcongr; exact h t ht
    _ = 1 := by simp

/-! ### Proposition 2.2 counterexample -/

noncomputable def S22 : ℝ≥0 → Unit → ℝ := fun t _ => (1 - (t : ℝ)) ^ 2
noncomputable def K22 : ℝ≥0 → Unit → ℝ := fun t _ => min (t : ℝ) 1

lemma hS22c : Continuous fun t : ℝ≥0 => (1 - (t : ℝ)) ^ 2 :=
  (continuous_const.sub NNReal.continuous_coe).pow 2

lemma hK22c : Continuous fun t : ℝ≥0 => min (t : ℝ) 1 :=
  NNReal.continuous_coe.min continuous_const

lemma data22 : IsStandardData (augmentedFiltration P0 hB0) P0 1 1 (fun _ => 0)
    f0 S22 := by
  refine ⟨zero_terminal _ _, zero_coeff _ _, ⟨prog_det _ (fun t => (1 - (t : ℝ)) ^ 2) hS22c,
    ae_of_all _ fun _ => hS22c.continuousOn,
    supSq_lt fun t ht => ?_⟩, ae_of_all _ fun _ => by simp [S22]⟩
  have h1 : (t : ℝ) ≤ 1 := by exact_mod_cast ht
  have h0 : (0 : ℝ) ≤ t := t.2
  simp only [S22]
  rw [abs_le]; constructor
  · have := le_max_right ((1 - (t : ℝ)) ^ 2) 0; linarith
  · exact max_le (by nlinarith) zero_le_one

lemma sol22 : SolvesRBSDEWith (augmentedFiltration P0 hB0) P0 1 B0 (fun _ => 0)
    f0 S22 S22 (fun _ _ => 0) K22 (fun j => j.elim0) := by
  refine ⟨prog_det _ (fun t => (1 - (t : ℝ)) ^ 2) hS22c, isStronglyProgressive_const _ _,
    prog_det _ (fun t => min (t : ℝ) 1) hK22c,
    fun j => j.elim0, ae_of_all _ fun ω => ⟨fun j => j.elim0, by simp [f0], fun t ht => ?_, fun t _ => le_rfl,
      ?_, ?_, by simp [K22], by simp⟩⟩
  · have h1 : (t : ℝ) ≤ 1 := by exact_mod_cast ht
    simp [S22, K22, f0, h1]
    ring
  · intro a b hab
    simp only [K22]
    exact min_le_min_right _ (by exact_mod_cast min_le_min_right _ hab)
  · exact hK22c.comp (continuous_id.min continuous_const)

theorem not_prop22 : ¬ (∀ {d : ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → Fin d → ℝ} (hB : IsStdBrownian P B)
    (T : ℝ≥0) (L : ℝ) (ξ : Ω → ℝ) (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ) (S : ℝ≥0 → Ω → ℝ)
    (hdata : IsStandardData (augmentedFiltration P hB) P T L ξ f S)
    (Y : ℝ≥0 → Ω → ℝ) (Z : ℝ≥0 → Ω → Fin d → ℝ) (K : ℝ≥0 → Ω → ℝ)
    (J : Fin d → ℝ≥0 → Ω → ℝ)
    (hsol : SolvesRBSDEWith (augmentedFiltration P hB) P T B ξ f S Y Z K J),
    ∀ᵐ ω ∂P, ∀ t ≤ T,
      K T ω - K t ω = ⨆ u : Icc t T,
        max (-(ξ ω
          + (∫ s in Icc ((u : ℝ≥0) : ℝ) T, f s.toNNReal ω (Y s.toNNReal ω) (Z s.toNNReal ω))
          - ∑ j, (J j T ω - J j u ω) - S u ω)) 0) := by
  intro h
  have H := ae_P0 (h hB0 1 1 _ _ _ data22 S22 _ K22 _ sol22) (1 / 2) (by norm_num)
  have hne : Nonempty (Icc (1 / 2 : ℝ≥0) 1) := ⟨⟨1, by norm_num, le_rfl⟩⟩
  have hle : (⨆ u : Icc (1 / 2 : ℝ≥0) 1, max (-((0 : ℝ)
          + (∫ s in Icc ((u : ℝ≥0) : ℝ) (1 : ℝ≥0), (0 : ℝ))
          - ∑ j : Fin 0, ((fun j => j.elim0 : Fin 0 → ℝ≥0 → Unit → ℝ) j 1 ()
            - (fun j => j.elim0 : Fin 0 → ℝ≥0 → Unit → ℝ) j u ()) - S22 u ())) 0) ≤ 1 / 4 := by
    apply ciSup_le
    rintro ⟨u, hu1, hu2⟩
    have h1 : (1 / 2 : ℝ) ≤ u := by exact_mod_cast hu1
    have h2 : (u : ℝ) ≤ 1 := by exact_mod_cast hu2
    simp only [S22, integral_zero, Finset.univ_eq_empty, Finset.sum_empty]
    apply max_le _ (by norm_num)
    nlinarith
  have hK : K22 1 () - K22 (1 / 2) () = 1 / 2 := by
    simp [K22]; norm_num
  rw [hK] at H
  linarith [H.trans_le hle]

end RCex

end ReflectedBSDE.Existence

open ReflectedBSDE.Existence ReflectedBSDE.Existence.RCex

theorem solution : ¬ (∀ {d : ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → Fin d → ℝ} (hB : IsStdBrownian P B)
    (T : ℝ≥0) (L : ℝ) (ξ : Ω → ℝ) (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ) (S : ℝ≥0 → Ω → ℝ)
    (hdata : IsStandardData (augmentedFiltration P hB) P T L ξ f S)
    (Y : ℝ≥0 → Ω → ℝ) (Z : ℝ≥0 → Ω → Fin d → ℝ) (K : ℝ≥0 → Ω → ℝ)
    (J : Fin d → ℝ≥0 → Ω → ℝ)
    (hsol : SolvesRBSDEWith (augmentedFiltration P hB) P T B ξ f S Y Z K J),
    ∀ᵐ ω ∂P, ∀ t ≤ T,
      K T ω - K t ω = ⨆ u : Icc t T,
        max (-(ξ ω
          + (∫ s in Icc ((u : ℝ≥0) : ℝ) T, f s.toNNReal ω (Y s.toNNReal ω) (Z s.toNNReal ω))
          - ∑ j, (J j T ω - J j u ω) - S u ω)) 0) :=
  not_prop22
