-- Prove2me | solution 1 for StochKolmogorov.Classify.lemma_5_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-02T22:41:32.895449+00:00
-- url     : https://prove2.me/submissions/68effbe3-41ce-49ce-a5ee-cccd4c21f894

import Mathlib
import Definitions.Def_StochKolmogorov_Classify_Model
import Definitions.Def_StochKolmogorov_Classify_Faces
import Definitions.Def_StochKolmogorov_Classify_Classification
import Definitions.Def_StochKolmogorov_Persist_Model
import Definitions.Def_StochKolmogorov_Extinct_Extinction
import Theorems.Thm_StochKolmogorov_Persist_lemma_3_2
import Theorems.Thm_StochKolmogorov_Persist_lemma_3_3
import Theorems.Thm_StochKolmogorov_Extinct_lemma_5_1

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

set_option autoImplicit false

namespace ClassifyL51

/-- The same coefficients, read in the `Persist` copy of the model. -/
def toP {n : ℕ} (C : StochKolmogorov.Classify.Coeffs n) : StochKolmogorov.Persist.Coeffs n :=
  ⟨C.f, C.g, C.Γ⟩

/-- The same coefficients, read in the `Extinct` copy of the model. -/
def toE {n : ℕ} (C : StochKolmogorov.Classify.Coeffs n) : StochKolmogorov.Extinct.Coeffs n :=
  ⟨C.f, C.g, C.Γ⟩

open StochKolmogorov.Classify in
/-- `δ₀` of (3.2) exists: `δ₀ = γ_b / (3 S n + 3)` with `S = ∑ᵢⱼ |σᵢⱼ|`. -/
theorem exists_isDelta0 {n : ℕ} (C : Coeffs n) (γb : ℝ) (hγ : 0 < γb) :
    ∃ δ₀ : ℝ, IsDelta0 C γb δ₀ := by
  set S : ℝ := ∑ i, ∑ j, |C.sig i j| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hsij : ∀ i j, |C.sig i j| ≤ S := by
    intro i j
    calc |C.sig i j| ≤ ∑ j', |C.sig i j'| :=
          Finset.single_le_sum (f := fun j' => |C.sig i j'|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ j)
      _ ≤ S := Finset.single_le_sum (f := fun i' => ∑ j', |C.sig i' j'|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have hden : 0 < 3 * S * n + 3 := by positivity
  refine ⟨γb / (3 * S * n + 3), div_pos hγ hden, ?_, fun x _ => ?_⟩
  · rw [div_lt_div_iff₀ hden two_pos]
    nlinarith [mul_nonneg hS0 (Nat.cast_nonneg (α := ℝ) n)]
  · set δ := γb / (3 * S * n + 3) with hδ
    have hδ0 : 0 ≤ δ := (div_pos hγ hden).le
    set G : ℝ := ∑ i, C.g i x ^ 2 with hG
    have hG0 : 0 ≤ G := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hterm : ∀ i j, |C.g i x * C.g j x * C.sig i j|
        ≤ S * ((C.g i x ^ 2 + C.g j x ^ 2) / 2) := by
      intro i j
      rw [abs_mul, abs_mul]
      have h1 : |C.g i x| * |C.g j x| ≤ (C.g i x ^ 2 + C.g j x ^ 2) / 2 := by
        nlinarith [sq_nonneg (|C.g i x| - |C.g j x|), sq_abs (C.g i x), sq_abs (C.g j x)]
      calc |C.g i x| * |C.g j x| * |C.sig i j| ≤ ((C.g i x ^ 2 + C.g j x ^ 2) / 2) * S :=
            mul_le_mul h1 (hsij i j) (abs_nonneg _) (by positivity)
        _ = S * ((C.g i x ^ 2 + C.g j x ^ 2) / 2) := by ring
    have hsum : ∑ i, ∑ j, |C.g i x * C.g j x * C.sig i j| ≤ S * n * G := by
      calc ∑ i, ∑ j, |C.g i x * C.g j x * C.sig i j|
          ≤ ∑ i : Fin n, ∑ j : Fin n, S * ((C.g i x ^ 2 + C.g j x ^ 2) / 2) :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
        _ = S * n * G := by
            simp only [← Finset.mul_sum, add_div, Finset.sum_add_distrib, Finset.sum_const,
              Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hG, ← Finset.sum_div]
            ring
    have hkey : δ * (3 * S * n + 3) = γb := by rw [hδ, div_mul_cancel₀ _ hden.ne']
    calc 3 * δ * ∑ i, ∑ j, |C.g i x * C.g j x * C.sig i j| + δ * G
        ≤ 3 * δ * (S * n * G) + δ * G := by nlinarith
      _ ≤ δ * (3 * S * n + 3) * G := by nlinarith [mul_nonneg hδ0 hG0]
      _ = γb * G := by rw [hkey]

open EthierKurtz StochKolmogorov.Classify in
/-- The Lyapunov integrand `fᵢ − σᵢᵢgᵢ²/2` is integrable under every invariant law
(Lemma 3.2 (3.8) + Lemma 3.3 bound on the weight). -/
theorem lyap_integrable {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (μ : Measure (SDEState n)) (hμ : IsInvariant P X μ) (i : Fin n) :
    Integrable (fun y => C.f i y - C.sig i i * C.g i y ^ 2 / 2) μ := by
  obtain ⟨δ₀, hδ₀⟩ := exists_isDelta0 C γb hA.2.2.2.1
  obtain ⟨H₁, H₂, -, hH₂, -, h38, -⟩ :=
    StochKolmogorov.Persist.lemma_3_2 hn P (toP C) B X hX c γb hA δ₀ hδ₀
  have hW := (StochKolmogorov.Persist.lemma_3_3 hn P (toP C) B X hX c γb hA δ₀ hδ₀ H₂ hH₂ h38
    μ hμ).1
  have hc : c ∈ openOrthant n := hA.2.2.1
  have hae : ∀ᵐ x ∂μ, x ∈ orthant n := by rw [ae_iff]; exact hμ.2.1
  have hres : μ.restrict (orthant n) = μ := Measure.restrict_eq_self_of_ae_mem hae
  have hmeas : MeasurableSet (orthant n) := by
    have : orthant n = ⋂ j, {x : SDEState n | 0 ≤ x j} := by ext x; simp [orthant]
    rw [this]
    exact MeasurableSet.iInter fun j =>
      measurableSet_le measurable_const ((PiLp.continuous_apply 2 _ j).measurable)
  have hfc : ContinuousOn (C.f i) (orthant n) := (hA.2.1 i).1.continuousOn
  have hgc : ContinuousOn (C.g i) (orthant n) := (hA.2.1 i).2.continuousOn
  have hfall : ∀ j, ContinuousOn (C.f j) (orthant n) := fun j => (hA.2.1 j).1.continuousOn
  have hgall : ∀ j, ContinuousOn (C.g j) (orthant n) := fun j => (hA.2.1 j).2.continuousOn
  -- the weight
  set W : SDEState n → ℝ := fun x =>
    (1 + ∑ j, c j * x j) ^ δ₀ * (1 + ∑ j, (|C.f j x| + |C.g j x| ^ 2)) with hWdef
  have hlin : Continuous fun x : SDEState n => 1 + ∑ j, c j * x j :=
    continuous_const.add (continuous_finsetSum _ fun j _ =>
      continuous_const.mul (PiLp.continuous_apply 2 _ j))
  have hWc : ContinuousOn W (orthant n) := by
    refine ContinuousOn.mul ?_ ?_
    · refine (hlin.continuousOn).rpow_const ?_
      intro x _
      exact Or.inr hδ₀.1.le
    · exact continuousOn_const.add (continuousOn_finsetSum _ fun j _ =>
        ((hfall j).abs).add ((hgall j).abs.pow 2))
  have hWm : AEStronglyMeasurable W μ := by
    rw [← hres]; exact hWc.aestronglyMeasurable hmeas
  have hW0 : ∀ x ∈ orthant n, 0 ≤ W x := fun x hx => by
    have hp : 0 ≤ 1 + ∑ j, c j * x j := by
      have := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => mul_nonneg (hc j).le (hx j)
      linarith
    exact mul_nonneg (Real.rpow_nonneg hp _) (by positivity)
  have hWint : Integrable W μ := by
    refine (lintegral_ofReal_ne_top_iff_integrable hWm ?_).1 ?_
    · filter_upwards [hae] with x hx using hW0 x hx
    · exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hW
  have hhm : AEStronglyMeasurable (fun y => C.f i y - C.sig i i * C.g i y ^ 2 / 2) μ := by
    rw [← hres]
    exact (hfc.sub ((continuousOn_const.mul (hgc.pow 2)).div_const 2)).aestronglyMeasurable hmeas
  refine (hWint.const_mul (1 + |C.sig i i|)).mono' hhm ?_
  filter_upwards [hae] with x hx
  have hp : 1 ≤ 1 + ∑ j, c j * x j := by
    have := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => mul_nonneg (hc j).le (hx j)
    linarith
  have h1 : 1 ≤ (1 + ∑ j, c j * x j) ^ δ₀ := Real.one_le_rpow hp hδ₀.1.le
  have hfi : |C.f i x| ≤ ∑ j, (|C.f j x| + |C.g j x| ^ 2) := by
    have := Finset.single_le_sum (f := fun j => |C.f j x| + |C.g j x| ^ 2)
      (fun j _ => by positivity) (Finset.mem_univ i)
    have h2 : 0 ≤ |C.g i x| ^ 2 := by positivity
    linarith
  have hgi : C.g i x ^ 2 ≤ ∑ j, (|C.f j x| + |C.g j x| ^ 2) := by
    have := Finset.single_le_sum (f := fun j => |C.f j x| + |C.g j x| ^ 2)
      (fun j _ => by positivity) (Finset.mem_univ i)
    have h2 : 0 ≤ |C.f i x| := abs_nonneg _
    have h3 : |C.g i x| ^ 2 = C.g i x ^ 2 := sq_abs _
    linarith
  set Sx := ∑ j, (|C.f j x| + |C.g j x| ^ 2) with hSx
  have hS0 : 0 ≤ Sx := le_trans (abs_nonneg _) hfi
  have hsig : 0 ≤ |C.sig i i| := abs_nonneg _
  have hg2 : 0 ≤ C.g i x ^ 2 := sq_nonneg _
  have hb : ‖C.f i x - C.sig i i * C.g i x ^ 2 / 2‖ ≤ |C.f i x| + |C.sig i i| * C.g i x ^ 2 := by
    rw [Real.norm_eq_abs]
    calc |C.f i x - C.sig i i * C.g i x ^ 2 / 2|
        ≤ |C.f i x| + |C.sig i i * C.g i x ^ 2 / 2| := abs_sub _ _
      _ = |C.f i x| + |C.sig i i| * C.g i x ^ 2 / 2 := by
          rw [abs_div, abs_mul, abs_of_nonneg hg2, abs_two]
      _ ≤ |C.f i x| + |C.sig i i| * C.g i x ^ 2 := by
          have := mul_nonneg hsig hg2
          linarith
  have hb2 : |C.f i x| + |C.sig i i| * C.g i x ^ 2 ≤ (1 + |C.sig i i|) * (1 + Sx) := by
    have := mul_le_mul_of_nonneg_left hgi hsig
    nlinarith
  have hb3 : (1 + |C.sig i i|) * (1 + Sx) ≤ (1 + |C.sig i i|) * W x := by
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    show 1 + Sx ≤ (1 + ∑ j, c j * x j) ^ δ₀ * (1 + Sx)
    have := mul_le_mul_of_nonneg_right h1 (by linarith : (0:ℝ) ≤ 1 + Sx)
    linarith
  exact hb.trans (hb2.trans hb3)

open EthierKurtz StochKolmogorov.Classify in
theorem l51 {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb) :
    ∀ μ ∈ bdryErgodic P X, ∀ i ∈ supp μ,
      Integrable (fun y => C.f i y - C.sig i i * C.g i y ^ 2 / 2) μ ∧ lyap C i μ = 0 := by
  intro μ hμ i hi
  refine ⟨lyap_integrable hn P C B X hX c γb hA μ hμ.1.1 i, ?_⟩
  exact StochKolmogorov.Extinct.lemma_5_1 hn P (toE C) B X hX c γb hA μ hμ i hi

end ClassifyL51

open StochKolmogorov.Classify EthierKurtz in
theorem solution {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb) :
    ∀ μ ∈ bdryErgodic P X, ∀ i ∈ supp μ,
      Integrable (fun y => C.f i y - C.sig i i * C.g i y ^ 2 / 2) μ ∧ lyap C i μ = 0 := by
  exact ClassifyL51.l51 hn P C B X hX c γb hA
