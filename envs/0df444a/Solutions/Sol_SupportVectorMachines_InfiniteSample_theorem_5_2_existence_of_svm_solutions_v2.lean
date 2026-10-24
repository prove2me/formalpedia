-- Prove2me | solution 1 for SupportVectorMachines.InfiniteSample.theorem_5_2_existence_of_svm_solutions_v2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T15:02:41.511674+00:00
-- url     : https://prove2.me/submissions/56016609-77bb-41ec-80ae-0e4a115da1d4

import Mathlib
import Definitions.Def_SupportVectorMachines_InfiniteSample_Loss_v2
import Definitions.Def_SupportVectorMachines_InfiniteSample_NemitskiLoss_v2
import Definitions.Def_SupportVectorMachines_InfiniteSample_IsRKHSOfKernel
import Definitions.Def_SupportVectorMachines_InfiniteSample_populationRisk_v2

namespace SV90
open MeasureTheory Filter Topology SupportVectorMachines.InfiniteSample

theorem meas_toFun {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (toFun : H →ₗ[ℝ] (X → ℝ)) (inj : Function.Injective toFun) (kAt : X → H)
    (hrep : ∀ (f : H) (x : X), toFun f x = inner (𝕜 := ℝ) f (kAt x))
    (hkm : ∀ x, Measurable (toFun (kAt x))) (f : H) : Measurable (toFun f) := by
  let S : Submodule ℝ H :=
    { carrier := {f | Measurable (toFun f)}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq, map_add] at *
        exact ha.add hb
      zero_mem' := by
        simp only [Set.mem_ofPred_eq, map_zero]
        exact measurable_const
      smul_mem' := by
        intro c a ha
        simp only [Set.mem_ofPred_eq, map_smul] at *
        exact ha.const_smul c }
  have hS : IsClosed (S : Set H) := by
    apply IsSeqClosed.isClosed
    intro u p hu hup
    show Measurable (toFun p)
    apply measurable_of_tendsto_metrizable (f := fun n => toFun (u n)) hu
    rw [tendsto_pi_nhds]
    intro x
    simp only [hrep]
    exact hup.inner tendsto_const_nhds
  have hspan : Submodule.span ℝ (Set.range kAt) ≤ S := by
    rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact hkm x
  have htop : (Submodule.span ℝ (Set.range kAt)).topologicalClosure = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    intro g hg
    apply inj
    rw [map_zero]
    funext x
    rw [hrep]
    have := (Submodule.mem_orthogonal _ _).1 hg (kAt x) (Submodule.subset_span ⟨x, rfl⟩)
    rw [real_inner_comm]; simpa using this
  have h1 := Submodule.topologicalClosure_minimal _ hspan hS
  rw [htop] at h1
  exact h1 (Submodule.mem_top (x := f))

noncomputable def G {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (L : Loss X) (toFun : H →ₗ[ℝ] (X → ℝ)) (lam : ℝ) (f : H) (p : X × ℝ) : ENNReal :=
  ENNReal.ofReal (lam * ‖f‖ ^ 2 + L p.1 p.2 (toFun f p.1))

theorem main {X : Type*} [MeasurableSpace X]
    (L : Loss X) (hL : ∀ x y, ConvexOn ℝ Set.univ (L x y))
    (P : Measure (X × ℝ)) [IsProbabilityMeasure P]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (toFun : H →ₗ[ℝ] (X → ℝ)) (k : X → X → ℝ) (hRKHS : IsRKHSOfKernel H toFun k)
    (hk : ∀ x, Measurable (fun x' => k x' x))
    (lam : ℝ) (hlam : 0 < lam) :
    ∃ f : H, ∀ g : H, ENNReal.ofReal (lam * ‖f‖ ^ 2) + populationRisk L P (toFun f) ≤
      ENNReal.ofReal (lam * ‖g‖ ^ 2) + populationRisk L P (toFun g) := by
  obtain ⟨inj, kAt, hkAt, hrep⟩ := hRKHS
  have hsymm : ∀ x x', k x x' = k x' x := by
    intro x x'
    rw [← hkAt, ← hkAt, hrep, hrep]
    exact real_inner_comm _ _
  have hkm : ∀ x, Measurable (toFun (kAt x)) := by
    intro x
    have : toFun (kAt x) = fun x' => k x' x := funext fun x' => by rw [hkAt, hsymm]
    rw [this]; exact hk x
  have hmeasF : ∀ f, Measurable (toFun f) := meas_toFun toFun inj kAt hrep hkm
  have hLm : ∀ f : H, Measurable (fun p : X × ℝ => L p.1 p.2 (toFun f p.1)) := fun f =>
    L.measurable.comp (measurable_fst.prodMk (measurable_snd.prodMk ((hmeasF f).comp measurable_fst)))
  have hGmeas : ∀ f, Measurable (G L toFun lam f) := fun f =>
    ENNReal.measurable_ofReal.comp (measurable_const.add (hLm f))
  have hJ : ∀ f : H, ENNReal.ofReal (lam * ‖f‖ ^ 2) + populationRisk L P (toFun f)
      = ∫⁻ p, G L toFun lam f p ∂P := by
    intro f
    unfold populationRisk G
    rw [show (fun p : X × ℝ => ENNReal.ofReal (lam * ‖f‖ ^ 2 + L p.1 p.2 (toFun f p.1)))
        = fun p => ENNReal.ofReal (lam * ‖f‖ ^ 2) + ENNReal.ofReal (L p.1 p.2 (toFun f p.1)) from
        funext fun p => ENNReal.ofReal_add (by positivity) (L.nonneg _ _ _)]
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
  simp only [hJ]
  set J : H → ENNReal := fun f => ∫⁻ p, G L toFun lam f p ∂P with hJdef
  set m : ENNReal := ⨅ f, J f with hmdef
  by_cases hm : m = ⊤
  · refine ⟨0, fun g => ?_⟩
    have : J g = ⊤ := top_unique (hm ▸ iInf_le _ g)
    show J 0 ≤ J g
    rw [this]; exact le_top
  have hLc : ∀ x y, Continuous (L x y) := fun x y =>
    continuousOn_univ.1 ((hL x y).continuousOn isOpen_univ)
  -- strong convexity
  have sc : ∀ f g : H, J ((1/2 : ℝ) • (f + g)) + J ((1/2 : ℝ) • (f + g))
      + ENNReal.ofReal (lam / 2 * ‖f - g‖ ^ 2) ≤ J f + J g := by
    intro f g
    simp only [hJdef]
    rw [← lintegral_add_left (hGmeas f), ← lintegral_add_left (hGmeas _)]
    have : ENNReal.ofReal (lam / 2 * ‖f - g‖ ^ 2)
        = ∫⁻ _p, ENNReal.ofReal (lam / 2 * ‖f - g‖ ^ 2) ∂P := by
      rw [lintegral_const, measure_univ, mul_one]
    rw [this, ← lintegral_add_left (f := fun a => G L toFun lam ((1/2 : ℝ) • (f + g)) a
      + G L toFun lam ((1/2 : ℝ) • (f + g)) a) ((hGmeas _).add (hGmeas _))]
    apply lintegral_mono
    intro p
    simp only [G]
    have h1 : 0 ≤ lam * ‖(1/2 : ℝ) • (f + g)‖ ^ 2 + L p.1 p.2 (toFun ((1/2 : ℝ) • (f + g)) p.1) :=
      add_nonneg (by positivity) (L.nonneg _ _ _)
    have h2 : 0 ≤ lam * ‖f‖ ^ 2 + L p.1 p.2 (toFun f p.1) :=
      add_nonneg (by positivity) (L.nonneg _ _ _)
    have h3 : 0 ≤ lam * ‖g‖ ^ 2 + L p.1 p.2 (toFun g p.1) :=
      add_nonneg (by positivity) (L.nonneg _ _ _)
    rw [← ENNReal.ofReal_add h1 h1, ← ENNReal.ofReal_add (add_nonneg h1 h1) (by positivity),
      ← ENNReal.ofReal_add h2 h3]
    apply ENNReal.ofReal_le_ofReal
    have hconv := (hL p.1 p.2).2 (Set.mem_univ (toFun f p.1)) (Set.mem_univ (toFun g p.1))
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
    simp only [smul_eq_mul] at hconv
    have hfun : toFun ((1/2 : ℝ) • (f + g)) p.1 = 1/2 * toFun f p.1 + 1/2 * toFun g p.1 := by
      simp [map_smul, map_add]
    rw [hfun]
    have hpar := parallelogram_law_with_norm ℝ f g
    have hn : ‖(1/2 : ℝ) • (f + g)‖ = 1/2 * ‖f + g‖ := by
      rw [norm_smul]; norm_num
    rw [hn]
    nlinarith [hconv, hpar]
  have hmlt : m < ⊤ := lt_top_iff_ne_top.2 hm
  have hseq : ∀ n : ℕ, ∃ f, J f < m + ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
    intro n
    apply iInf_lt_iff.1
    apply ENNReal.lt_add_right hm
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  choose u hu using hseq
  have hbd : ∀ n k : ℕ, lam / 2 * ‖u n - u k‖ ^ 2 ≤ 1 / ((n : ℝ) + 1) + 1 / ((k : ℝ) + 1) := by
    intro n k
    have h := sc (u n) (u k)
    have hmid : m ≤ J ((1/2 : ℝ) • (u n + u k)) := iInf_le _ _
    have h2 : m + m + ENNReal.ofReal (lam / 2 * ‖u n - u k‖ ^ 2)
        ≤ m + m + (ENNReal.ofReal (1 / ((n : ℝ) + 1)) + ENNReal.ofReal (1 / ((k : ℝ) + 1))) := by
      calc m + m + ENNReal.ofReal (lam / 2 * ‖u n - u k‖ ^ 2)
          ≤ J ((1/2 : ℝ) • (u n + u k)) + J ((1/2 : ℝ) • (u n + u k))
            + ENNReal.ofReal (lam / 2 * ‖u n - u k‖ ^ 2) := by gcongr
        _ ≤ J (u n) + J (u k) := h
        _ ≤ (m + ENNReal.ofReal (1 / ((n : ℝ) + 1))) + (m + ENNReal.ofReal (1 / ((k : ℝ) + 1))) :=
            add_le_add (hu n).le (hu k).le
        _ = _ := by ring
    have h3 := (ENNReal.add_le_add_iff_left (ENNReal.add_ne_top.2 ⟨hm, hm⟩)).1 h2
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)] at h3
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h3
  have hcauchy : CauchySeq u := by
    apply cauchySeq_of_le_tendsto_0 (fun N : ℕ => Real.sqrt (4 / lam * (1 / ((N : ℝ) + 1))))
    · intro n k N hn hk
      rw [dist_eq_norm]
      apply Real.le_sqrt_of_sq_le
      have e1 : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        exact_mod_cast Nat.add_le_add_right hn 1
      have e2 : 1 / ((k : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        exact_mod_cast Nat.add_le_add_right hk 1
      have hb := hbd n k
      have : lam * ‖u n - u k‖ ^ 2 ≤ 4 * (1 / ((N : ℝ) + 1)) := by linarith
      calc ‖u n - u k‖ ^ 2 = (lam * ‖u n - u k‖ ^ 2) / lam := by field_simp
        _ ≤ (4 * (1 / ((N : ℝ) + 1))) / lam := div_le_div_of_nonneg_right this hlam.le
        _ = _ := by ring
    · have := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (4 / lam)).sqrt
      simpa using this
  obtain ⟨f, hf⟩ := cauchySeq_tendsto_of_complete hcauchy
  have htf : ∀ x, Tendsto (fun n => toFun (u n) x) atTop (𝓝 (toFun f x)) := by
    intro x
    simp only [hrep]
    exact hf.inner tendsto_const_nhds
  have hGt : ∀ p : X × ℝ, Tendsto (fun n => G L toFun lam (u n) p) atTop (𝓝 (G L toFun lam f p)) := by
    intro p
    simp only [G]
    apply ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    apply Tendsto.add
    · exact tendsto_const_nhds.mul (((continuous_norm.tendsto f).comp hf).pow 2)
    · exact (hLc _ _).continuousAt.tendsto.comp (htf p.1)
  have hfatou : J f ≤ liminf (fun n => J (u n)) atTop := by
    calc J f = ∫⁻ p, liminf (fun n => G L toFun lam (u n) p) atTop ∂P := by
          simp only [hJdef]
          apply lintegral_congr
          intro p
          exact ((hGt p).liminf_eq).symm
      _ ≤ _ := lintegral_liminf_le' (fun n => (hGmeas _).aemeasurable)
  have hlim : liminf (fun n => J (u n)) atTop ≤ m := by
    have ht : Tendsto (fun n : ℕ => m + ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 m) := by
      have := tendsto_const_nhds (x := m) |>.add
        (ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat)
      simpa using this
    calc liminf (fun n => J (u n)) atTop
        ≤ liminf (fun n : ℕ => m + ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop :=
          liminf_le_liminf (Eventually.of_forall fun n => (hu n).le)
      _ = m := ht.liminf_eq
  refine ⟨f, fun g => ?_⟩
  exact (hfatou.trans hlim).trans (iInf_le _ g)

end SV90

open MeasureTheory SupportVectorMachines.InfiniteSample in
theorem solution {X : Type*} [MeasurableSpace X]
    (L : Loss X) (hL : ∀ x y, ConvexOn ℝ Set.univ (L x y))
    (P : Measure (X × ℝ)) [IsProbabilityMeasure P] (hNem : PIntegrableNemitskiLoss L P)
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (toFun : H →ₗ[ℝ] (X → ℝ)) (k : X → X → ℝ) (hRKHS : IsRKHSOfKernel H toFun k)
    (hk : ∀ x, Measurable (fun x' => k x' x))
    (hkBdd : ∃ M : ℝ, ∀ x : X, k x x ≤ M)
    (lam : ℝ) (hlam : 0 < lam) :
    ∃ f : H, ∀ g : H, ENNReal.ofReal (lam * ‖f‖ ^ 2) + populationRisk L P (toFun f) ≤
      ENNReal.ofReal (lam * ‖g‖ ^ 2) + populationRisk L P (toFun g) :=
  SV90.main L hL P H toFun k hRKHS hk lam hlam
