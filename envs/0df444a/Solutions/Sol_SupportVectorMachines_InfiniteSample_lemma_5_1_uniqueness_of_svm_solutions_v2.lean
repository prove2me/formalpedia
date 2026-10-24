-- Prove2me | solution 1 for SupportVectorMachines.InfiniteSample.lemma_5_1_uniqueness_of_svm_solutions_v2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T08:59:28.137975+00:00
-- url     : https://prove2.me/submissions/f8711924-f69b-4ba0-9c1b-e11653f7147e

import Mathlib
import Definitions.Def_SupportVectorMachines_InfiniteSample_Loss_v2
import Definitions.Def_SupportVectorMachines_InfiniteSample_IsRKHSOfKernel
import Definitions.Def_SupportVectorMachines_InfiniteSample_populationRisk_v2

open MeasureTheory

namespace SV88

open SupportVectorMachines.InfiniteSample

theorem measurable_toFun {X : Type*} [MeasurableSpace X]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (toFun : H →ₗ[ℝ] (X → ℝ)) (k : X → X → ℝ) (hRKHS : IsRKHSOfKernel H toFun k)
    (hk : ∀ x, Measurable (fun x' => k x' x)) (f : H) : Measurable (toFun f) := by
  obtain ⟨hinj, kAt, hkAt, hrep⟩ := hRKHS
  -- elements of the span are measurable
  have hspan : ∀ g ∈ Submodule.span ℝ (Set.range kAt), Measurable (toFun g) := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, rfl⟩ := hx
      have : toFun (kAt y) = fun x' => k x' y := by
        funext x'
        rw [hkAt, ← hkAt, ← hkAt, hrep, hrep, real_inner_comm]
      rw [this]; exact hk y
    | zero => simp; exact measurable_const
    | add a b _ _ ha hb => rw [map_add]; exact ha.add hb
    | smul c a _ ha => rw [map_smul]; exact ha.const_smul c
  -- span is dense
  have hdense : (Submodule.span ℝ (Set.range kAt)).topologicalClosure = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    intro g hg
    apply hinj
    rw [map_zero]
    funext x
    rw [hrep]
    exact (Submodule.mem_orthogonal' _ _).1 hg _ (Submodule.subset_span ⟨x, rfl⟩)
  have hf : f ∈ closure (Submodule.span ℝ (Set.range kAt) : Set H) := by
    rw [← Submodule.topologicalClosure_coe, hdense]; trivial
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 hf
  apply measurable_of_tendsto_metrizable (f := fun n => toFun (u n))
  · intro n; exact hspan _ (hu n)
  · rw [tendsto_pi_nhds]
    intro x
    simp only [hrep]
    exact (hlim.inner tendsto_const_nhds)


theorem risk_mid {X : Type*} [MeasurableSpace X]
    (L : Loss X) (hL : ∀ x y, ConvexOn ℝ Set.univ (L x y)) (P : Measure (X × ℝ))
    (u v : X → ℝ) (hu : Measurable u) :
    populationRisk L P ((1/2 : ℝ) • u + (1/2 : ℝ) • v) ≤
      ENNReal.ofReal (1/2) * populationRisk L P u + ENNReal.ofReal (1/2) * populationRisk L P v := by
  unfold populationRisk
  have hmeas : Measurable (fun p : X × ℝ => ENNReal.ofReal (L p.1 p.2 (u p.1))) := by
    apply ENNReal.measurable_ofReal.comp
    have := L.measurable
    exact this.comp (measurable_fst.prodMk (measurable_snd.prodMk (hu.comp measurable_fst)))
  rw [← lintegral_const_mul _ hmeas, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_add_left (hmeas.const_mul _)]
  apply lintegral_mono
  intro p
  simp only []
  have h := (hL p.1 p.2).2 (Set.mem_univ (u p.1)) (Set.mem_univ (v p.1))
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  simp only [smul_eq_mul] at h
  have h1 := L.nonneg p.1 p.2 (u p.1)
  have h2 := L.nonneg p.1 p.2 (v p.1)
  rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h

theorem main {X : Type*} [MeasurableSpace X]
    (L : Loss X) (hL : ∀ x y, ConvexOn ℝ Set.univ (L x y))
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (toFun : H →ₗ[ℝ] (X → ℝ)) (k : X → X → ℝ) (hRKHS : IsRKHSOfKernel H toFun k)
    (hk : ∀ x, Measurable (fun x' => k x' x))
    (P : Measure (X × ℝ)) [IsProbabilityMeasure P]
    (hfin : ∃ f : H, populationRisk L P (toFun f) < ⊤)
    (lam : ℝ) (hlam : 0 < lam) (f1 f2 : H)
    (hf1 : ∀ g : H, ENNReal.ofReal (lam * ‖f1‖ ^ 2) + populationRisk L P (toFun f1) ≤
      ENNReal.ofReal (lam * ‖g‖ ^ 2) + populationRisk L P (toFun g))
    (hf2 : ∀ g : H, ENNReal.ofReal (lam * ‖f2‖ ^ 2) + populationRisk L P (toFun f2) ≤
      ENNReal.ofReal (lam * ‖g‖ ^ 2) + populationRisk L P (toFun g)) :
    f1 = f2 := by
  obtain ⟨f0, hf0⟩ := hfin
  have fin1 : populationRisk L P (toFun f1) ≠ ⊤ := by
    intro h; have := hf1 f0; rw [h, add_top] at this
    exact (ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, hf0⟩).ne (top_le_iff.1 this)
  have fin2 : populationRisk L P (toFun f2) ≠ ⊤ := by
    intro h; have := hf2 f0; rw [h, add_top] at this
    exact (ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, hf0⟩).ne (top_le_iff.1 this)
  set R1 := populationRisk L P (toFun f1) with hR1
  set R2 := populationRisk L P (toFun f2) with hR2
  set m : H := (1/2 : ℝ) • f1 + (1/2 : ℝ) • f2 with hm
  have hRm : populationRisk L P (toFun m) ≤ ENNReal.ofReal (1/2) * R1 + ENNReal.ofReal (1/2) * R2 := by
    have := risk_mid L hL P (toFun f1) (toFun f2) (measurable_toFun H toFun k hRKHS hk f1)
    simpa [hm, map_add, map_smul] using this
  have A : ENNReal.ofReal (lam * ‖f1‖ ^ 2) + R1 ≤ ENNReal.ofReal (lam * ‖f2‖ ^ 2) + R2 := hf1 f2
  have B : ENNReal.ofReal (lam * ‖f2‖ ^ 2) + R2 ≤ ENNReal.ofReal (lam * ‖f1‖ ^ 2) + R1 := hf2 f1
  have C := (hf1 m).trans (add_le_add_right hRm _)
  clear_value R1 R2 m
  lift R1 to NNReal using fin1
  lift R2 to NNReal using fin2
  simp only [← ENNReal.ofReal_coe_nnreal] at A B C
  have p1 : 0 ≤ (R1 : ℝ) := R1.2
  have p2 : 0 ≤ (R2 : ℝ) := R2.2
  have n1 : 0 ≤ lam * ‖f1‖ ^ 2 := by positivity
  have n2 : 0 ≤ lam * ‖f2‖ ^ 2 := by positivity
  have nm : 0 ≤ lam * ‖m‖ ^ 2 := by positivity
  rw [← ENNReal.ofReal_add n1 p1, ← ENNReal.ofReal_add n2 p2] at A B
  rw [← ENNReal.ofReal_add n1 p1, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add nm (by positivity)] at C
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at A B C
  -- parallelogram
  have par : ‖f1 + f2‖ ^ 2 + ‖f1 - f2‖ ^ 2 = 2 * (‖f1‖ ^ 2 + ‖f2‖ ^ 2) := by
    have := parallelogram_law_with_norm ℝ f1 f2
    simp only [sq]; linarith
  have hmn : ‖m‖ = (1/2) * ‖f1 + f2‖ := by
    rw [hm, ← smul_add, norm_smul]; norm_num
  have key : lam * ‖f1 - f2‖ ^ 2 ≤ 0 := by
    rw [hmn] at C
    have lp : lam * ‖f1 + f2‖ ^ 2 + lam * ‖f1 - f2‖ ^ 2 =
        2 * (lam * ‖f1‖ ^ 2) + 2 * (lam * ‖f2‖ ^ 2) := by
      rw [← mul_add, par]; ring
    have C' : lam * ‖f1‖ ^ 2 + (R1 : ℝ) ≤ (1/4) * (lam * ‖f1 + f2‖ ^ 2) +
        ((1/2) * (R1 : ℝ) + (1/2) * (R2 : ℝ)) := by
      have : lam * ((1/2) * ‖f1 + f2‖) ^ 2 = (1/4) * (lam * ‖f1 + f2‖ ^ 2) := by ring
      linarith
    linarith
  have hd : ‖f1 - f2‖ ^ 2 ≤ 0 := by
    by_contra h; rw [not_le] at h; have := mul_pos hlam h; linarith
  have : ‖f1 - f2‖ = 0 := by
    have := sq_nonneg ‖f1 - f2‖
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm hd this)
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

end SV88

open SupportVectorMachines.InfiniteSample in
theorem solution {X : Type*} [MeasurableSpace X]
    (L : Loss X) (hL : ∀ x y, ConvexOn ℝ Set.univ (L x y))
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (toFun : H →ₗ[ℝ] (X → ℝ)) (k : X → X → ℝ) (hRKHS : IsRKHSOfKernel H toFun k)
    (hk : ∀ x, Measurable (fun x' => k x' x))
    (P : Measure (X × ℝ)) [IsProbabilityMeasure P]
    (hfin : ∃ f : H, populationRisk L P (toFun f) < ⊤)
    (lam : ℝ) (hlam : 0 < lam) (f1 f2 : H)
    (hf1 : ∀ g : H, ENNReal.ofReal (lam * ‖f1‖ ^ 2) + populationRisk L P (toFun f1) ≤
      ENNReal.ofReal (lam * ‖g‖ ^ 2) + populationRisk L P (toFun g))
    (hf2 : ∀ g : H, ENNReal.ofReal (lam * ‖f2‖ ^ 2) + populationRisk L P (toFun f2) ≤
      ENNReal.ofReal (lam * ‖g‖ ^ 2) + populationRisk L P (toFun g)) :
    f1 = f2 :=
  SV88.main L hL H toFun k hRKHS hk P hfin lam hlam f1 f2 hf1 hf2
