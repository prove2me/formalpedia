-- Prove2me | solution 1 for ReflectedBSDE.Existence.proposition_3_6
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-13T02:11:01.220056+00:00
-- url     : https://prove2.me/submissions/7bee61ed-9ab9-43a4-880a-80ac285d3954

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

universe u


noncomputable def P0 : Measure PUnit.{u+1} := Measure.dirac PUnit.unit

instance : IsProbabilityMeasure P0 := by unfold P0; infer_instance

def B0 : ℝ≥0 → PUnit.{u+1} → Fin 0 → ℝ := fun _ _ => 0

lemma hB0 : IsStdBrownian P0 B0 := ⟨fun _ => measurable_const, fun j => j.elim0,
  iIndepFun.of_subsingleton⟩

lemma prog_det (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace PUnit.{u+1})) (g : ℝ≥0 → ℝ)
    (hg : Continuous g) : IsStronglyProgressive 𝓕 (fun t (_ : PUnit.{u+1}) => g t) := fun i => by
  have h1 : Measurable[Subtype.instMeasurableSpace.prod (𝓕 i)]
      (fun p : Set.Iic i × PUnit.{u+1} => (p.1 : ℝ≥0)) :=
    measurable_subtype_coe.comp (@measurable_fst _ _ _ (𝓕 i))
  exact (hg.measurable.comp h1).stronglyMeasurable

lemma ae_P0 {p : PUnit.{u+1} → Prop} (h : ∀ᵐ ω ∂P0, p ω) : p PUnit.unit := by
  obtain ⟨ω, hω⟩ := h.exists
  exact hω

def f0 : ℝ≥0 → PUnit.{u+1} → ℝ → (Fin 0 → ℝ) → ℝ := fun _ _ _ _ => 0

lemma zero_coeff (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace PUnit.{u+1})) (T : ℝ≥0) :
    IsLipschitzCoeff 𝓕 P0 T 1 f0 :=
  ⟨fun _ _ => ⟨isStronglyProgressive_const _ _, by simp [f0]⟩, one_pos,
    ae_of_all _ fun _ _ _ y y' z z' => by
      simp only [f0, sub_self, abs_zero, one_mul]
      unfold euclNorm; positivity⟩

lemma zero_terminal (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace PUnit.{u+1})) (T : ℝ≥0) :
    IsTerminalValue 𝓕 P0 T (fun _ => 0) := ⟨stronglyMeasurable_const, by simp⟩

lemma supSq_lt {T : ℝ≥0} {X : ℝ≥0 → PUnit.{u+1} → ℝ} (h : ∀ t ≤ T, |X t PUnit.unit| ≤ 1) :
    supSqMoment P0 T X < ⊤ := by
  unfold supSqMoment P0
  rw [lintegral_dirac]
  refine lt_of_le_of_lt (iSup₂_le fun t ht => ?_) (ENNReal.one_lt_top)
  rw [Real.enorm_eq_ofReal_abs]
  calc ENNReal.ofReal |X t PUnit.unit| ^ 2 ≤ (ENNReal.ofReal 1) ^ 2 := by
        gcongr; exact h t ht
    _ = 1 := by simp

lemma pathMeasure_Ioc {k : ℝ≥0 → ℝ} (hm : Monotone k) (hc : Continuous k) (a b : ℝ) :
    pathMeasure k (Ioc a b) = ENNReal.ofReal (k b.toNNReal - k a.toNNReal) := by
  unfold pathMeasure; rw [dif_pos ⟨hm, hc⟩, StieltjesFunction.measure_Ioc]; rfl

/-! ### Ramp construction: large `K_T` with small obstacle -/

noncomputable def Kr (ε : ℝ) : ℝ≥0 → PUnit.{u+1} → ℝ :=
  fun t _ => max 0 (min (t : ℝ) 1 - (1 - ε)) / ε
noncomputable def Yr (ε : ℝ) : ℝ≥0 → PUnit.{u+1} → ℝ :=
  fun t _ => (1 - (t : ℝ)) * (1 - max 0 (min (t : ℝ) 1 - (1 - ε)) / ε)
noncomputable def Sr (ε : ℝ) : ℝ≥0 → PUnit.{u+1} → ℝ :=
  fun t _ => min ε ((1 - (t : ℝ)) ^ 2 / ε)

lemma Krc (ε : ℝ) : Continuous fun t : ℝ≥0 => max 0 (min (t : ℝ) 1 - (1 - ε)) / ε :=
  (continuous_const.max ((NNReal.continuous_coe.min continuous_const).sub continuous_const)).div_const _
lemma Yrc (ε : ℝ) : Continuous fun t : ℝ≥0 =>
    (1 - (t : ℝ)) * (1 - max 0 (min (t : ℝ) 1 - (1 - ε)) / ε) :=
  (continuous_const.sub NNReal.continuous_coe).mul (continuous_const.sub (Krc ε))
lemma Src (ε : ℝ) : Continuous fun t : ℝ≥0 => min ε ((1 - (t : ℝ)) ^ 2 / ε) :=
  continuous_const.min (((continuous_const.sub NNReal.continuous_coe).pow 2).div_const _)

section ramp
variable {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
include hε hε1

lemma Kr_one : Kr.{u} ε 1 PUnit.unit = 1 := by
  simp only [Kr, NNReal.coe_one, min_self]
  rw [show (1 : ℝ) - (1 - ε) = ε by ring, max_eq_right hε.le, div_self hε.ne']

lemma Kr_zero : Kr.{u} ε 0 PUnit.unit = 0 := by
  simp only [Kr, NNReal.coe_zero]
  rw [max_eq_left (by have := min_le_left (0 : ℝ) 1; linarith)]; simp

lemma Kr_mono : Monotone fun t => Kr.{u} ε (min t 1) PUnit.unit := by
  intro a b hab
  simp only [Kr]
  apply div_le_div_of_nonneg_right _ hε.le
  apply max_le_max le_rfl
  have : ((min a 1 : ℝ≥0) : ℝ) ≤ (min b 1 : ℝ≥0) := by exact_mod_cast min_le_min_right _ hab
  have := min_le_min_right (1 : ℝ) this
  linarith

lemma Kr_cont : Continuous fun t => Kr.{u} ε (min t 1) PUnit.unit :=
  (Krc ε).comp (continuous_id.min continuous_const)

lemma Kr_bounds (t : ℝ≥0) : 0 ≤ Kr.{u} ε t PUnit.unit ∧ Kr.{u} ε t PUnit.unit ≤ 1 := by
  simp only [Kr]
  have h1 := min_le_right (t : ℝ) 1
  constructor
  · exact div_nonneg (le_max_left _ _) hε.le
  · rw [div_le_one hε]; exact max_le hε.le (by linarith)

lemma Sr_bounds (t : ℝ≥0) : 0 ≤ Sr.{u} ε t PUnit.unit ∧ Sr.{u} ε t PUnit.unit ≤ ε := by
  simp only [Sr]
  exact ⟨le_min hε.le (by positivity), min_le_left _ _⟩

lemma Yr_bounds (t : ℝ≥0) (ht : t ≤ 1) : 0 ≤ Yr.{u} ε t PUnit.unit ∧ Yr.{u} ε t PUnit.unit ≤ 1 := by
  have hK := Kr_bounds.{u} hε hε1 t
  simp only [Kr] at hK
  simp only [Yr]
  have h1 : (t : ℝ) ≤ 1 := by exact_mod_cast ht
  have h0 : (0 : ℝ) ≤ t := t.2
  constructor
  · exact mul_nonneg (by linarith) (by linarith)
  · nlinarith

lemma Yr_eq (t : ℝ≥0) (ht : t ≤ 1) :
    Yr.{u} ε t PUnit.unit = (1 - (t : ℝ)) * (Kr.{u} ε 1 PUnit.unit - Kr.{u} ε t PUnit.unit) := by
  rw [Kr_one.{u} hε hε1]; rfl

lemma Sr_le_Yr (t : ℝ≥0) (ht : t ≤ 1) : Sr.{u} ε t PUnit.unit ≤ Yr.{u} ε t PUnit.unit := by
  have h1 : (t : ℝ) ≤ 1 := by exact_mod_cast ht
  simp only [Sr, Yr, min_eq_left h1]
  rcases le_or_gt (t : ℝ) (1 - ε) with h | h
  · rw [max_eq_left (by linarith)]
    simp only [zero_div, sub_zero, mul_one]
    exact (min_le_left _ _).trans (by linarith)
  · rw [max_eq_right (by linarith)]
    apply min_le_right _ _ |>.trans (le_of_eq _)
    field_simp
    ring

lemma Yr_sub_Sr (t : ℝ≥0) (ht : t ≤ 1) (h : 1 - ε < (t : ℝ)) :
    Yr.{u} ε t PUnit.unit - Sr.{u} ε t PUnit.unit = 0 := by
  have h1 : (t : ℝ) ≤ 1 := by exact_mod_cast ht
  simp only [Sr, Yr, min_eq_left h1]
  rw [max_eq_right (by linarith)]
  have h2 : (1 - (t : ℝ)) ^ 2 / ε ≤ ε := by
    rw [div_le_iff₀ hε]; nlinarith
  rw [min_eq_right h2]
  field_simp
  ring

lemma int_r : ∫⁻ t in Icc (0 : ℝ) (1 : ℝ≥0), ENNReal.ofReal (Yr.{u} ε t.toNNReal PUnit.unit
    - Sr.{u} ε t.toNNReal PUnit.unit) ∂(pathMeasure fun t => Kr.{u} ε (min t 1) PUnit.unit) = 0 := by
  set μ := pathMeasure fun t => Kr.{u} ε (min t 1) PUnit.unit
  have hnull : μ (Ioc (-1) (1 - ε)) = 0 := by
    rw [pathMeasure_Ioc (Kr_mono.{u} hε hε1) (Kr_cont.{u} hε hε1)]
    apply ENNReal.ofReal_eq_zero.2
    have hneg : (-1 : ℝ).toNNReal = 0 := by simp
    rw [hneg, min_eq_left (zero_le_one), Kr_zero.{u} hε hε1]
    have hle : (1 - ε).toNNReal ≤ 1 := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal']; simp; linarith
    rw [min_eq_left hle]
    simp only [Kr, Real.coe_toNNReal']
    have hm : min (max (1 - ε) 0) 1 = max (1 - ε) 0 := min_eq_left (max_le (by linarith) zero_le_one)
    rw [hm]
    rcases le_total (1 - ε) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; simp
    · rw [max_eq_left h, sub_self, max_self]; simp
  have hae : ∀ᵐ s ∂μ, s ∉ Ioc (-1) (1 - ε) := measure_eq_zero_iff_ae_notMem.1 hnull
  rw [show (0 : ℝ≥0∞) = ∫⁻ _ in Icc (0 : ℝ) (1 : ℝ≥0), 0 ∂μ by simp]
  apply lintegral_congr_ae
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Icc]
  filter_upwards [hae] with s hs hsI
  have hs0 : 0 ≤ s := hsI.1
  have hs1 : s ≤ 1 := by simpa using hsI.2
  have hgt : 1 - ε < s := by
    by_contra hc; push Not at hc; exact hs ⟨by linarith, hc⟩
  apply ENNReal.ofReal_eq_zero.2 (le_of_eq _)
  apply Yr_sub_Sr.{u} hε hε1
  · rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs0]; simpa using hs1
  · rw [Real.coe_toNNReal _ hs0]; exact hgt

lemma dataR : IsStandardData (augmentedFiltration P0.{u} hB0) P0 1 1 (fun _ => 0) f0 (Sr.{u} ε) := by
  refine ⟨zero_terminal _ _, zero_coeff _ _, ⟨prog_det _ (fun t => min ε ((1 - (t : ℝ)) ^ 2 / ε))
    (Src ε), ae_of_all _ fun _ => (Src ε).continuousOn, supSq_lt fun t _ => ?_⟩,
    ae_of_all _ fun _ => by simp [Sr]⟩
  have := Sr_bounds.{u} hε hε1 t
  rw [abs_le]; constructor
  · have := le_max_right (Sr.{u} ε t PUnit.unit) 0; linarith
  · exact max_le (by linarith) zero_le_one

lemma solR : SolvesRBSDEWith (augmentedFiltration P0.{u} hB0) P0 1 B0 (fun _ => 0)
    f0 (Sr.{u} ε) (Yr.{u} ε) (fun _ _ => 0) (Kr.{u} ε) (fun j => j.elim0) := by
  refine ⟨prog_det _ _ (Yrc ε), isStronglyProgressive_const _ _, prog_det _ _ (Krc ε),
    fun j => j.elim0, ae_of_all _ fun ω => ⟨fun j => j.elim0, by simp [f0], fun t ht => ?_,
      fun t ht => Sr_le_Yr.{u} hε hε1 t ht, Kr_mono.{u} hε hε1, Kr_cont.{u} hε hε1,
      Kr_zero.{u} hε hε1, int_r.{u} hε hε1⟩⟩
  have h1 : (t : ℝ) ≤ 1 := by exact_mod_cast ht
  rw [Yr_eq.{u} hε hε1 t ht]
  simp [f0, h1]

omit hε hε1 in
lemma vR : SatisfiesV (augmentedFiltration P0.{u} hB0) P0 1
    (fun _ _ => 0 : ℝ≥0 → PUnit.{u+1} → Fin 0 → ℝ) :=
  ⟨isStronglyProgressive_const _ _, by simp⟩

lemma vpR : SatisfiesVPrime (augmentedFiltration P0.{u} hB0) P0 1 (Yr.{u} ε) (Kr.{u} ε) := by
  refine ⟨⟨prog_det _ _ (Yrc ε), supSq_lt fun t ht => ?_⟩, ?_⟩
  · have := Yr_bounds.{u} hε hε1 t ht
    rw [abs_le]; constructor <;> linarith
  · unfold P0; rw [lintegral_dirac, Kr_one.{u} hε hε1]; simp

end ramp

/-! ### Proposition 2.2 counterexample -/

noncomputable def S22 : ℝ≥0 → PUnit.{u+1} → ℝ := fun t _ => (1 - (t : ℝ)) ^ 2
noncomputable def K22 : ℝ≥0 → PUnit.{u+1} → ℝ := fun t _ => min (t : ℝ) 1

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

/-! ### Existence fails -/

noncomputable def SE : ℝ≥0 → Unit → ℝ := fun t _ => Real.sqrt (1 - (t : ℝ))

lemma hSEc : Continuous fun t : ℝ≥0 => Real.sqrt (1 - (t : ℝ)) :=
  Real.continuous_sqrt.comp (continuous_const.sub NNReal.continuous_coe)

lemma obsE : IsObstacle (augmentedFiltration P0 hB0) P0 1 SE := by
  refine ⟨prog_det _ (fun t => Real.sqrt (1 - (t : ℝ))) hSEc,
    ae_of_all _ fun _ => hSEc.continuousOn, supSq_lt fun t _ => ?_⟩
  simp only [SE]
  have h0 : (0 : ℝ) ≤ t := t.2
  have h1 : Real.sqrt (1 - (t : ℝ)) ≤ 1 := by
    calc Real.sqrt (1 - (t : ℝ)) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith)
      _ = 1 := Real.sqrt_one
  have h2 := Real.sqrt_nonneg (1 - (t : ℝ))
  rw [abs_le]; constructor
  · have := le_max_right (Real.sqrt (1 - (t : ℝ))) 0; linarith
  · exact max_le h1 zero_le_one

lemma STE : ∀ᵐ ω ∂P0, SE 1 ω ≤ (fun _ => (0 : ℝ)) ω := ae_of_all _ fun _ => by simp [SE]

lemma dataE : IsStandardData (augmentedFiltration P0 hB0) P0 1 1 (fun _ => 0) f0 SE :=
  ⟨zero_terminal _ _, zero_coeff _ _, obsE, STE⟩

lemma no_solE (Y : ℝ≥0 → Unit → ℝ) (Z : ℝ≥0 → Unit → Fin 0 → ℝ) (K : ℝ≥0 → Unit → ℝ) :
    ¬ SolvesRBSDE (augmentedFiltration P0 hB0) P0 1 B0 (fun _ => 0) f0 SE Y Z K := by
  rintro ⟨J, -, -, -, -, hae⟩
  obtain ⟨-, -, hYeq, hSY, hKm, -, hK0, -⟩ := ae_P0 hae
  have hmono : ∀ a b : ℝ≥0, a ≤ b → b ≤ 1 → K a () ≤ K b () := fun a b hab hb => by
    have := hKm hab
    simp only [min_eq_left hb, min_eq_left (hab.trans hb)] at this
    exact this
  set c := K 1 () with hcdef
  have hc : 0 ≤ c := by
    have := hmono 0 1 (zero_le_one) le_rfl
    rw [hK0] at this; exact this
  set a : ℝ := 1 / (c + 1) with hadef
  have ha : 0 < a := by positivity
  have hac : a * (c + 1) = 1 := by rw [hadef]; field_simp
  have ha1 : a ≤ 1 := by nlinarith
  have ha2 : a ^ 2 ≤ 1 := by nlinarith
  set t0 : ℝ≥0 := ⟨1 - a ^ 2, by linarith⟩ with ht0def
  have ht0r : (t0 : ℝ) = 1 - a ^ 2 := rfl
  have ht0 : t0 ≤ 1 := by
    rw [← NNReal.coe_le_coe, ht0r]; simp; positivity
  have hKt0 : 0 ≤ K t0 () := by
    have := hmono 0 t0 bot_le ht0
    rw [hK0] at this; exact this
  have hKt1 : K t0 () ≤ c := hmono t0 1 ht0 le_rfl
  have H1 := hYeq t0 ht0
  have H2 := hSY t0 ht0
  have ht0' : (t0 : ℝ) ≤ 1 := by exact_mod_cast ht0
  simp [f0, ht0'] at H1
  simp only [SE, ht0r, sub_sub_cancel, Real.sqrt_sq ha.le] at H2
  rw [H1, ht0r] at H2
  have H3 : a ≤ a ^ 2 * c := by
    have : (1 - (1 - a ^ 2)) * (K 1 () - K t0 ()) ≤ a ^ 2 * c := by
      rw [sub_sub_cancel]; nlinarith
    linarith
  nlinarith

theorem not_exists_unique : ¬ (∀ {d : ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → Fin d → ℝ} (hB : IsStdBrownian P B)
    (T : ℝ≥0) (L : ℝ) (ξ : Ω → ℝ) (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ) (S : ℝ≥0 → Ω → ℝ)
    (hdata : IsStandardData (augmentedFiltration P hB) P T L ξ f S),
    (∃ (Y : ℝ≥0 → Ω → ℝ) (Z : ℝ≥0 → Ω → Fin d → ℝ) (K : ℝ≥0 → Ω → ℝ),
        SatisfiesV (augmentedFiltration P hB) P T Z ∧
        SolvesRBSDE (augmentedFiltration P hB) P T B ξ f S Y Z K ∧
        SatisfiesVPrime (augmentedFiltration P hB) P T Y K) ∧
    ∀ (Y : ℝ≥0 → Ω → ℝ) (Z : ℝ≥0 → Ω → Fin d → ℝ) (K : ℝ≥0 → Ω → ℝ)
      (Y' : ℝ≥0 → Ω → ℝ) (Z' : ℝ≥0 → Ω → Fin d → ℝ) (K' : ℝ≥0 → Ω → ℝ),
      SatisfiesV (augmentedFiltration P hB) P T Z →
      SolvesRBSDE (augmentedFiltration P hB) P T B ξ f S Y Z K →
      SatisfiesV (augmentedFiltration P hB) P T Z' →
      SolvesRBSDE (augmentedFiltration P hB) P T B ξ f S Y' Z' K' →
      SameSolution P T Y Z K Y' Z' K') := by
  intro h
  obtain ⟨Y, Z, K, -, hsol, -⟩ := (h hB0 1 1 _ _ _ dataE).1
  exact no_solE Y Z K hsol

theorem not_prop51 : ¬ (∀ {d : ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → Fin d → ℝ} (hB : IsStdBrownian P B)
    (T : ℝ≥0) (ξ : Ω → ℝ) (f : ℝ≥0 → Ω → ℝ) (S : ℝ≥0 → Ω → ℝ)
    (hξ : IsTerminalValue (augmentedFiltration P hB) P T ξ)
    (hf : L2F (augmentedFiltration P hB) P T f)
    (hS : IsObstacle (augmentedFiltration P hB) P T S)
    (hST : ∀ᵐ ω ∂P, S T ω ≤ ξ ω),
    (∃ (Y : ℝ≥0 → Ω → ℝ) (Z : ℝ≥0 → Ω → Fin d → ℝ) (K : ℝ≥0 → Ω → ℝ),
        SatisfiesV (augmentedFiltration P hB) P T Z ∧
        SolvesRBSDE (augmentedFiltration P hB) P T B ξ (fun t ω _ _ => f t ω) S Y Z K) ∧
    ∀ (Y : ℝ≥0 → Ω → ℝ) (Z : ℝ≥0 → Ω → Fin d → ℝ) (K : ℝ≥0 → Ω → ℝ)
      (Y' : ℝ≥0 → Ω → ℝ) (Z' : ℝ≥0 → Ω → Fin d → ℝ) (K' : ℝ≥0 → Ω → ℝ),
      SatisfiesV (augmentedFiltration P hB) P T Z →
      SolvesRBSDE (augmentedFiltration P hB) P T B ξ (fun t ω _ _ => f t ω) S Y Z K →
      SatisfiesV (augmentedFiltration P hB) P T Z' →
      SolvesRBSDE (augmentedFiltration P hB) P T B ξ (fun t ω _ _ => f t ω) S Y' Z' K' →
      SameSolution P T Y Z K Y' Z' K') := by
  intro h
  obtain ⟨Y, Z, K, -, hsol⟩ := (h hB0 1 (fun _ => 0) (fun _ _ => 0) SE (zero_terminal _ _)
    ⟨isStronglyProgressive_const _ _, by simp⟩ obsE STE).1
  exact no_solE Y Z K hsol

/-! ### Propositions 3.5 and 3.6 -/

lemma eps_facts (C : ℝ≥0) : 0 < 1 / ((C : ℝ) + 1) ∧ 1 / ((C : ℝ) + 1) ≤ 1 ∧
    (C : ℝ) * (1 / ((C : ℝ) + 1)) ^ 2 < 1 := by
  have hC : (0 : ℝ) ≤ C := C.2
  refine ⟨by positivity, by rw [div_le_one (by linarith)]; linarith, ?_⟩
  rw [div_pow, one_pow, mul_one_div, div_lt_one (by positivity)]
  nlinarith

lemma max_S_bound {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (t : ℝ≥0) (ω : PUnit.{u+1}) :
    ‖max (Sr.{u} ε t ω) 0‖ₑ ^ 2 ≤ ENNReal.ofReal (ε ^ 2) := by
  cases ω
  have := Sr_bounds.{u} hε hε1 t
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  rw [max_eq_left this.1, abs_of_nonneg this.1]
  exact pow_le_pow_left₀ this.1 this.2 2

lemma S_bound {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (t : ℝ≥0) (ω : PUnit.{u+1}) :
    ‖Sr.{u} ε t ω‖ₑ ^ 2 ≤ ENNReal.ofReal (ε ^ 2) := by
  cases ω
  have := Sr_bounds.{u} hε hε1 t
  have h2 := max_S_bound.{u} hε hε1 t PUnit.unit
  rwa [max_eq_left this.1] at h2

lemma rpow_half_le {x : ℝ≥0∞} {ε : ℝ} (hε : 0 ≤ ε) (h : x ≤ ENNReal.ofReal (ε ^ 2)) :
    x ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal ε := by
  calc x ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (ε ^ 2) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow h (by norm_num)
    _ = ENNReal.ofReal ε := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow,
          Real.sqrt_sq hε]

theorem not_prop35 : ¬ (∀ (T : ℝ≥0) (L : ℝ), ∃ C : ℝ≥0,
      ∀ (d : ℕ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : ℝ≥0 → Ω → Fin d → ℝ) (hB : IsStdBrownian P B)
        (ξ : Ω → ℝ) (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ) (S : ℝ≥0 → Ω → ℝ)
        (Y : ℝ≥0 → Ω → ℝ) (Z : ℝ≥0 → Ω → Fin d → ℝ) (K : ℝ≥0 → Ω → ℝ),
        IsStandardData (augmentedFiltration P hB) P T L ξ f S →
        SatisfiesV (augmentedFiltration P hB) P T Z →
        SolvesRBSDE (augmentedFiltration P hB) P T B ξ f S Y Z K →
        SatisfiesVPrime (augmentedFiltration P hB) P T Y K →
        ∫⁻ ω, ((⨆ t ∈ Iic T, ‖Y t ω‖ₑ ^ 2)
            + (∫⁻ s in Icc (0 : ℝ) T, ENNReal.ofReal (euclSq (Z s.toNNReal ω)))
            + ‖K T ω‖ₑ ^ 2) ∂P
          ≤ (C : ℝ≥0∞) * ∫⁻ ω, (‖ξ ω‖ₑ ^ 2
            + (∫⁻ s in Icc (0 : ℝ) T, ‖f s.toNNReal ω 0 0‖ₑ ^ 2)
            + ⨆ t ∈ Iic T, ‖max (S t ω) 0‖ₑ ^ 2) ∂P) := by
  intro h
  obtain ⟨C, hC⟩ := h 1 1
  obtain ⟨hε, hε1, hsmall⟩ := eps_facts C
  set ε := 1 / ((C : ℝ) + 1)
  have H := hC 0 PUnit.{u+1} P0 B0 hB0 (fun _ => 0) f0 (Sr.{u} ε) (Yr.{u} ε) (fun _ _ => 0)
    (Kr.{u} ε) (dataR.{u} hε hε1) vR ⟨_, solR.{u} hε hε1⟩ (vpR.{u} hε hε1)
  have hL : (1 : ℝ≥0∞) ≤ ∫⁻ ω, ((⨆ t ∈ Iic (1 : ℝ≥0), ‖Yr.{u} ε t ω‖ₑ ^ 2)
            + (∫⁻ s in Icc (0 : ℝ) (1 : ℝ≥0), ENNReal.ofReal
              (euclSq ((fun _ _ => 0 : ℝ≥0 → PUnit.{u+1} → Fin 0 → ℝ) s.toNNReal ω)))
            + ‖Kr.{u} ε 1 ω‖ₑ ^ 2) ∂P0 := by
    calc (1 : ℝ≥0∞) = ∫⁻ ω, ‖Kr.{u} ε 1 ω‖ₑ ^ 2 ∂P0 := by
          unfold P0; rw [lintegral_dirac, Kr_one.{u} hε hε1]; simp
      _ ≤ _ := lintegral_mono fun ω => le_add_self
  have hR : ∫⁻ ω, (‖(fun _ => (0 : ℝ)) ω‖ₑ ^ 2
            + (∫⁻ s in Icc (0 : ℝ) (1 : ℝ≥0), ‖f0 s.toNNReal ω 0 0‖ₑ ^ 2)
            + ⨆ t ∈ Iic (1 : ℝ≥0), ‖max (Sr.{u} ε t ω) 0‖ₑ ^ 2) ∂P0 ≤ ENNReal.ofReal (ε ^ 2) := by
    calc _ ≤ ∫⁻ _, ENNReal.ofReal (ε ^ 2) ∂P0 := lintegral_mono fun ω => by
          simp only [f0, enorm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
            lintegral_zero, zero_add]
          exact iSup₂_le fun t _ => max_S_bound.{u} hε hε1 t ω
      _ = ENNReal.ofReal (ε ^ 2) := by simp
  have h3 : (C : ℝ≥0∞) * ENNReal.ofReal (ε ^ 2) < 1 := by
    have : (C : ℝ≥0∞) * ENNReal.ofReal (ε ^ 2) = ENNReal.ofReal ((C : ℝ) * ε ^ 2) := by
      rw [ENNReal.ofReal_mul (NNReal.coe_nonneg C), ENNReal.ofReal_coe_nnreal]
    rw [this]
    exact ENNReal.ofReal_lt_one.2 hsmall
  have hR' := mul_le_mul_of_nonneg_left hR (by positivity : (0 : ℝ≥0∞) ≤ C)
  exact absurd (hL.trans (H.trans hR')) (not_le.2 h3)

lemma dataZ : IsStandardData (augmentedFiltration P0.{u} hB0) P0 1 1 (fun _ => 0) f0
    (fun _ _ => 0) :=
  ⟨zero_terminal _ _, zero_coeff _ _, ⟨isStronglyProgressive_const _ _,
    ae_of_all _ fun _ => continuousOn_const, supSq_lt fun _ _ => by simp⟩,
    ae_of_all _ fun _ => le_rfl⟩

lemma solZ : SolvesRBSDEWith (augmentedFiltration P0.{u} hB0) P0 1 B0 (fun _ => 0)
    f0 (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun j => j.elim0) :=
  ⟨isStronglyProgressive_const _ _, isStronglyProgressive_const _ _,
    isStronglyProgressive_const _ _, fun j => j.elim0, ae_of_all _ fun _ =>
      ⟨fun j => j.elim0, by simp [f0], fun t _ => by simp [f0], fun _ _ => le_rfl,
        monotone_const, continuous_const, rfl, by simp⟩⟩

lemma vpZ : SatisfiesVPrime (augmentedFiltration P0.{u} hB0) P0 1 (fun _ _ => 0)
    (fun _ _ => 0) :=
  ⟨⟨isStronglyProgressive_const _ _, supSq_lt fun _ _ => by simp⟩, by simp⟩

lemma final_ineq {L X A B : ℝ≥0∞} {c : ℝ≥0} {ε : ℝ} (hε : 0 < ε) (hsmall : (c : ℝ) * ε ^ 2 < 1)
    (H : L ≤ (c : ℝ≥0∞) * X + (c : ℝ≥0∞) * A ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ))
    (hL : 1 ≤ L) (hX : X = 0) (hA : A ≤ ENNReal.ofReal (ε ^ 2))
    (hB : B ≤ ENNReal.ofReal (ε ^ 2)) : False := by
  have h1 := rpow_half_le hε.le hA
  have h2 := rpow_half_le hε.le hB
  rw [hX, mul_zero, zero_add] at H
  have h3 : (c : ℝ≥0∞) * A ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ) ≤
      (c : ℝ≥0∞) * ENNReal.ofReal ε * ENNReal.ofReal ε := by gcongr
  have h4 : (c : ℝ≥0∞) * ENNReal.ofReal ε * ENNReal.ofReal ε = ENNReal.ofReal ((c : ℝ) * ε ^ 2) := by
    rw [mul_assoc, ← ENNReal.ofReal_mul hε.le, ENNReal.ofReal_mul (NNReal.coe_nonneg c),
      ENNReal.ofReal_coe_nnreal, sq]
  have h5 := hL.trans (H.trans (h3.trans h4.le))
  exact absurd h5 (not_le.2 (ENNReal.ofReal_lt_one.2 hsmall))

theorem not_prop36 : ¬ (∀ (T : ℝ≥0) (L : ℝ), ∃ c : ℝ≥0,
      ∀ (d : ℕ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : ℝ≥0 → Ω → Fin d → ℝ) (hB : IsStdBrownian P B)
        (ξ : Ω → ℝ) (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ) (S : ℝ≥0 → Ω → ℝ)
        (ξ' : Ω → ℝ) (f' : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ) (S' : ℝ≥0 → Ω → ℝ)
        (Y : ℝ≥0 → Ω → ℝ) (Z : ℝ≥0 → Ω → Fin d → ℝ) (K : ℝ≥0 → Ω → ℝ)
        (Y' : ℝ≥0 → Ω → ℝ) (Z' : ℝ≥0 → Ω → Fin d → ℝ) (K' : ℝ≥0 → Ω → ℝ),
        IsStandardData (augmentedFiltration P hB) P T L ξ f S →
        IsStandardData (augmentedFiltration P hB) P T L ξ' f' S' →
        SatisfiesV (augmentedFiltration P hB) P T Z →
        SolvesRBSDE (augmentedFiltration P hB) P T B ξ f S Y Z K →
        SatisfiesVPrime (augmentedFiltration P hB) P T Y K →
        SatisfiesV (augmentedFiltration P hB) P T Z' →
        SolvesRBSDE (augmentedFiltration P hB) P T B ξ' f' S' Y' Z' K' →
        SatisfiesVPrime (augmentedFiltration P hB) P T Y' K' →
        ∫⁻ ω, ((⨆ t ∈ Iic T, ‖Y t ω - Y' t ω‖ₑ ^ 2)
            + (∫⁻ s in Icc (0 : ℝ) T,
                ENNReal.ofReal (euclSq (Z s.toNNReal ω - Z' s.toNNReal ω)))
            + ‖K T ω - K' T ω‖ₑ ^ 2) ∂P
          ≤ (c : ℝ≥0∞) * ∫⁻ ω, (‖ξ ω - ξ' ω‖ₑ ^ 2
              + ∫⁻ s in Icc (0 : ℝ) T,
                ‖f s.toNNReal ω (Y s.toNNReal ω) (Z s.toNNReal ω)
                  - f' s.toNNReal ω (Y s.toNNReal ω) (Z s.toNNReal ω)‖ₑ ^ 2) ∂P
            + (c : ℝ≥0∞) * (supSqMoment P T (fun t ω => S t ω - S' t ω)) ^ (1 / 2 : ℝ)
              * (∫⁻ ω, (‖ξ ω‖ₑ ^ 2
                  + (∫⁻ s in Icc (0 : ℝ) T, ‖f s.toNNReal ω 0 0‖ₑ ^ 2)
                  + (⨆ t ∈ Iic T, ‖max (S t ω) 0‖ₑ ^ 2)
                  + ‖ξ' ω‖ₑ ^ 2
                  + (∫⁻ s in Icc (0 : ℝ) T, ‖f' s.toNNReal ω 0 0‖ₑ ^ 2)
                  + ⨆ t ∈ Iic T, ‖max (S' t ω) 0‖ₑ ^ 2) ∂P) ^ (1 / 2 : ℝ)) := by
  intro h
  obtain ⟨C, hC⟩ := h 1 1
  obtain ⟨hε, hε1, hsmall⟩ := eps_facts C
  set ε := 1 / ((C : ℝ) + 1)
  have H := hC 0 PUnit.{u+1} P0 B0 hB0 (fun _ => 0) f0 (Sr.{u} ε) (fun _ => 0) f0 (fun _ _ => 0)
    (Yr.{u} ε) (fun _ _ => 0) (Kr.{u} ε) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)
    (dataR.{u} hε hε1) dataZ vR ⟨_, solR.{u} hε hε1⟩ (vpR.{u} hε hε1) vR ⟨_, solZ⟩ vpZ
  refine final_ineq hε hsmall H ?_ ?_ ?_ ?_
  · calc (1 : ℝ≥0∞) = ∫⁻ ω, ‖Kr.{u} ε 1 ω - (fun _ _ => (0 : ℝ)) (1 : ℝ≥0) ω‖ₑ ^ 2 ∂P0 := by
          unfold P0; rw [lintegral_dirac, Kr_one.{u} hε hε1]; simp
      _ ≤ _ := lintegral_mono fun ω => le_add_self
  · simp [f0]
  · unfold supSqMoment P0
    rw [lintegral_dirac]
    refine iSup₂_le fun t _ => ?_
    simp only [sub_zero]
    exact S_bound.{u} hε hε1 t _
  · calc _ ≤ ∫⁻ _, ENNReal.ofReal (ε ^ 2) ∂P0 := lintegral_mono fun ω => by
          simp [f0]
          exact fun t _ => max_S_bound.{u} hε hε1 t ω
      _ = ENNReal.ofReal (ε ^ 2) := by simp

end RCex

end ReflectedBSDE.Existence

open ReflectedBSDE.Existence ReflectedBSDE.Existence.RCex

theorem solution : ¬ (∀ (T : ℝ≥0) (L : ℝ), ∃ c : ℝ≥0,
      ∀ (d : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : ℝ≥0 → Ω → Fin d → ℝ) (hB : IsStdBrownian P B)
        (ξ : Ω → ℝ) (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ) (S : ℝ≥0 → Ω → ℝ)
        (ξ' : Ω → ℝ) (f' : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ) (S' : ℝ≥0 → Ω → ℝ)
        (Y : ℝ≥0 → Ω → ℝ) (Z : ℝ≥0 → Ω → Fin d → ℝ) (K : ℝ≥0 → Ω → ℝ)
        (Y' : ℝ≥0 → Ω → ℝ) (Z' : ℝ≥0 → Ω → Fin d → ℝ) (K' : ℝ≥0 → Ω → ℝ),
        IsStandardData (augmentedFiltration P hB) P T L ξ f S →
        IsStandardData (augmentedFiltration P hB) P T L ξ' f' S' →
        SatisfiesV (augmentedFiltration P hB) P T Z →
        SolvesRBSDE (augmentedFiltration P hB) P T B ξ f S Y Z K →
        SatisfiesVPrime (augmentedFiltration P hB) P T Y K →
        SatisfiesV (augmentedFiltration P hB) P T Z' →
        SolvesRBSDE (augmentedFiltration P hB) P T B ξ' f' S' Y' Z' K' →
        SatisfiesVPrime (augmentedFiltration P hB) P T Y' K' →
        ∫⁻ ω, ((⨆ t ∈ Iic T, ‖Y t ω - Y' t ω‖ₑ ^ 2)
            + (∫⁻ s in Icc (0 : ℝ) T,
                ENNReal.ofReal (euclSq (Z s.toNNReal ω - Z' s.toNNReal ω)))
            + ‖K T ω - K' T ω‖ₑ ^ 2) ∂P
          ≤ (c : ℝ≥0∞) * ∫⁻ ω, (‖ξ ω - ξ' ω‖ₑ ^ 2
              + ∫⁻ s in Icc (0 : ℝ) T,
                ‖f s.toNNReal ω (Y s.toNNReal ω) (Z s.toNNReal ω)
                  - f' s.toNNReal ω (Y s.toNNReal ω) (Z s.toNNReal ω)‖ₑ ^ 2) ∂P
            + (c : ℝ≥0∞) * (supSqMoment P T (fun t ω => S t ω - S' t ω)) ^ (1 / 2 : ℝ)
              * (∫⁻ ω, (‖ξ ω‖ₑ ^ 2
                  + (∫⁻ s in Icc (0 : ℝ) T, ‖f s.toNNReal ω 0 0‖ₑ ^ 2)
                  + (⨆ t ∈ Iic T, ‖max (S t ω) 0‖ₑ ^ 2)
                  + ‖ξ' ω‖ₑ ^ 2
                  + (∫⁻ s in Icc (0 : ℝ) T, ‖f' s.toNNReal ω 0 0‖ₑ ^ 2)
                  + ⨆ t ∈ Iic T, ‖max (S' t ω) 0‖ₑ ^ 2) ∂P) ^ (1 / 2 : ℝ)) :=
  not_prop36.{0}
