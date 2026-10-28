-- Prove2me | solution 1 for SabanisEuler.UniformRate.maximal_inequality
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-10-28T08:57:48.566837+00:00
-- url     : https://prove2.me/submissions/42bb2acf-af26-4ce1-8834-a56a68ace80d

import Mathlib

namespace Prove2SwarmSubmission

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

/-! GSStop helpers for `SabanisEuler.UniformRate.maximal_inequality` (graph-scout %72).

Owner interface: analysis-prover's maximal-inequality INTERFACE.md v1 (sha256 256e2202). Helpers
only; this file does not prove the frozen target.

* Hitting times: for a path that is continuous on `[0, T]`, the hitting time of `Set.Ici c` is
  attained, its value is at most `c` when the path starts at or below `c`, and it is a stopping
  time for any filtration the process is adapted to on `[0, T]`. No `WellFoundedLT` is needed.
* Layer cake (exported last): the tail bound `P(F > c) ≤ P(A ≥ c) + E[min(A, c)]/c` for all
  `c > 0` gives `E F^γ ≤ ((2-γ)/(1-γ)) E A^γ` for `0 < γ < 1`. -/

namespace SabanisEuler.UniformRate.GSStop

/-- Attainment: if the path enters `Ici c` on `[0, T]`, it is in `Ici c` at the hitting time. -/
private theorem gs_mem_of_exists {Ω : Type*} (T : ℝ≥0) (u : ℝ≥0 → Ω → ℝ≥0) (c : ℝ≥0) (ω : Ω)
    (hu_cont : ContinuousOn (fun t => u t ω) (Set.Icc 0 T))
    (hex : ∃ j ∈ Set.Icc (0 : ℝ≥0) T, u j ω ∈ Set.Ici c) :
    c ≤ u (hittingBtwn u (Set.Ici c) 0 T ω) ω := by
  have hclosed : IsClosed (Set.Icc (0 : ℝ≥0) T ∩ {i : ℝ≥0 | u i ω ∈ Set.Ici c}) :=
    hu_cont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hne : (Set.Icc (0 : ℝ≥0) T ∩ {i : ℝ≥0 | u i ω ∈ Set.Ici c}).Nonempty := by
    obtain ⟨j, hj, hjs⟩ := hex
    exact ⟨j, hj, hjs⟩
  have hmem := hclosed.csInf_mem hne (BddBelow.inter_of_left bddBelow_Icc)
  have hdef : hittingBtwn u (Set.Ici c) 0 T ω =
      sInf (Set.Icc (0 : ℝ≥0) T ∩ {i : ℝ≥0 | u i ω ∈ Set.Ici c}) := by
    simp only [hittingBtwn, if_pos hex]
  rw [hdef]
  exact hmem.2

/-- The hitting time of `Set.Ici c` is an `ℱ`-stopping time, for a path continuous on `[0, T]`
and adapted up to `T`. -/
theorem isStoppingTime_hittingBtwn_Ici {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (ℱ : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (u : ℝ≥0 → Ω → ℝ≥0) (c : ℝ≥0)
    (hu_cont : ∀ ω, ContinuousOn (fun t => u t ω) (Set.Icc 0 T))
    (hu_adapt : ∀ t ≤ T, Measurable[ℱ t] (u t)) :
    IsStoppingTime ℱ (fun ω => ((hittingBtwn u (Set.Ici c) 0 T ω : ℝ≥0) : WithTop ℝ≥0)) := by
  intro i
  simp only [WithTop.coe_le_coe]
  rcases le_or_gt T i with hTi | hiT
  · have huniv : {ω | hittingBtwn u (Set.Ici c) 0 T ω ≤ i} = Set.univ :=
      Set.eq_univ_of_forall fun ω => (hittingBtwn_le ω).trans hTi
    rw [huniv]
    exact MeasurableSet.univ
  · let pt : ℚ → ℝ≥0 := fun q => min (Real.toNNReal (q : ℝ)) i
    have hpt_le : ∀ q, pt q ≤ i := fun q => min_le_right _ _
    have hD : DenseRange (fun q : ℚ => Real.toNNReal (q : ℝ)) :=
      (Function.Surjective.denseRange (fun r : ℝ≥0 => ⟨(r : ℝ), Real.toNNReal_coe⟩)).comp
        Rat.denseRange_cast continuous_real_toNNReal
    have hdense : ∀ j ∈ Set.Icc (0 : ℝ≥0) i, j ∈ closure (Set.range pt) := by
      intro j hj
      have hcont_min : Continuous fun x : ℝ≥0 => min x i := continuous_id.min continuous_const
      have h1 : (fun x : ℝ≥0 => min x i) '' closure (Set.range fun q : ℚ => Real.toNNReal (q : ℝ)) ⊆
          closure ((fun x : ℝ≥0 => min x i) '' Set.range fun q : ℚ => Real.toNNReal (q : ℝ)) :=
        image_closure_subset_closure_image hcont_min
      rw [hD.closure_range, Set.image_univ, ← Set.range_comp] at h1
      exact h1 ⟨j, min_eq_left hj.2⟩
    let v : Ω → ℝ≥0 := fun ω => ⨆ q, u (pt q) ω
    have hv : Measurable[ℱ i] v := Measurable.iSup fun q =>
      (hu_adapt (pt q) ((hpt_le q).trans hiT.le)).mono (ℱ.mono (hpt_le q)) le_rfl
    have hbdd : ∀ ω, BddAbove (Set.range fun q => u (pt q) ω) := by
      intro ω
      refine (isCompact_Icc.bddAbove_image (hu_cont ω)).mono ?_
      rintro _ ⟨q, rfl⟩
      exact ⟨pt q, ⟨zero_le, (hpt_le q).trans hiT.le⟩, rfl⟩
    have hle_v : ∀ ω, ∀ j ∈ Set.Icc (0 : ℝ≥0) i, u j ω ≤ v ω := by
      intro ω j hj
      have hclosed : IsClosed (Set.Icc (0 : ℝ≥0) T ∩ (fun t => u t ω) ⁻¹' Set.Iic (v ω)) :=
        (hu_cont ω).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
      have hsub : Set.range pt ⊆ Set.Icc (0 : ℝ≥0) T ∩ (fun t => u t ω) ⁻¹' Set.Iic (v ω) := by
        rintro _ ⟨q, rfl⟩
        exact ⟨⟨zero_le, (hpt_le q).trans hiT.le⟩, le_ciSup (hbdd ω) q⟩
      exact (hclosed.closure_subset_iff.mpr hsub (hdense j hj)).2
    have hset : {ω | hittingBtwn u (Set.Ici c) 0 T ω ≤ i} = v ⁻¹' Set.Ici c := by
      ext ω
      show hittingBtwn u (Set.Ici c) 0 T ω ≤ i ↔ c ≤ v ω
      constructor
      · intro h
        have hex : ∃ j ∈ Set.Icc (0 : ℝ≥0) T, u j ω ∈ Set.Ici c := by
          by_contra hne
          have hEq : hittingBtwn u (Set.Ici c) 0 T ω = T := by
            simp only [hittingBtwn, if_neg hne]
          rw [hEq] at h
          exact absurd (h.trans_lt hiT) (lt_irrefl T)
        exact (gs_mem_of_exists T u c ω (hu_cont ω) hex).trans (hle_v ω _ ⟨zero_le, h⟩)
      · intro h
        obtain ⟨j, hj, hjmax⟩ := isCompact_Icc.exists_isMaxOn
          (Set.nonempty_Icc.mpr (zero_le : (0 : ℝ≥0) ≤ i))
          ((hu_cont ω).mono (Set.Icc_subset_Icc_right hiT.le))
        have hv_le : v ω ≤ u j ω :=
          ciSup_le fun q => isMaxOn_iff.mp hjmax (pt q) ⟨zero_le, hpt_le q⟩
        exact (hittingBtwn_le_of_mem zero_le (hj.2.trans hiT.le) (h.trans hv_le)).trans hj.2
    rw [hset]
    exact hv measurableSet_Ici

/-- Attainment and minimality of the hitting time of `Set.Ici c`. -/
theorem hittingBtwn_Ici_spec {Ω : Type*} (T : ℝ≥0) (u : ℝ≥0 → Ω → ℝ≥0) (c : ℝ≥0) (ω : Ω)
    (hu_cont : ContinuousOn (fun t => u t ω) (Set.Icc 0 T)) {s : ℝ≥0} (hsT : s ≤ T)
    (hs : c ≤ u s ω) :
    hittingBtwn u (Set.Ici c) 0 T ω ≤ s ∧ c ≤ u (hittingBtwn u (Set.Ici c) 0 T ω) ω :=
  ⟨hittingBtwn_le_of_mem zero_le hsT hs,
    gs_mem_of_exists T u c ω hu_cont ⟨s, ⟨zero_le, hsT⟩, hs⟩⟩

/-- The value at the hitting time of `Set.Ici c` is at most `c` when the path starts at or
below `c`: by left continuity if the hit is positive, and otherwise because the path ends below `c`. -/
theorem hittingBtwn_Ici_value_le {Ω : Type*} (T : ℝ≥0) (u : ℝ≥0 → Ω → ℝ≥0) (c : ℝ≥0) (ω : Ω)
    (hu_cont : ContinuousOn (fun t => u t ω) (Set.Icc 0 T)) (h0 : u 0 ω ≤ c) :
    u (hittingBtwn u (Set.Ici c) 0 T ω) ω ≤ c := by
  by_cases hex : ∃ j ∈ Set.Icc (0 : ℝ≥0) T, u j ω ∈ Set.Ici c
  · rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ hittingBtwn u (Set.Ici c) 0 T ω) with h | h
    · rw [← h]
      exact h0
    · have hHT : hittingBtwn u (Set.Ici c) 0 T ω ≤ T := hittingBtwn_le ω
      have hclosed : IsClosed (Set.Icc (0 : ℝ≥0) T ∩ (fun t => u t ω) ⁻¹' Set.Iic c) :=
        hu_cont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
      have hsub : Set.Ico (0 : ℝ≥0) (hittingBtwn u (Set.Ici c) 0 T ω) ⊆
          Set.Icc (0 : ℝ≥0) T ∩ (fun t => u t ω) ⁻¹' Set.Iic c := by
        intro t ht
        refine ⟨⟨ht.1, ht.2.le.trans hHT⟩, ?_⟩
        have hnot : ¬ c ≤ u t ω := fun h' => notMem_of_lt_hittingBtwn ht.2 ht.1 (Set.mem_Ici.mpr h')
        exact (not_le.mp hnot).le
      have hcl := hclosed.closure_subset_iff.mpr hsub
      rw [closure_Ico h.ne] at hcl
      exact (hcl ⟨zero_le, le_rfl⟩).2
  · have hEq : hittingBtwn u (Set.Ici c) 0 T ω = T := by
      simp only [hittingBtwn, if_neg hex]
    have hT : ¬ c ≤ u T ω := fun h' => hex ⟨T, ⟨zero_le, le_rfl⟩, Set.mem_Ici.mpr h'⟩
    rw [hEq]
    exact (not_le.mp hT).le

private lemma gsLayer_coe_rpow (x : ℝ≥0) {γ : ℝ} (hγ : 0 ≤ γ) :
    (x : ℝ≥0∞) ^ γ = ENNReal.ofReal ((x : ℝ) ^ γ) := by
  rw [← ENNReal.ofReal_rpow_of_nonneg (NNReal.coe_nonneg x) hγ, ENNReal.ofReal_coe_nnreal]

private lemma gsLayer_mul_rpow {t : ℝ} (ht : 0 < t) (γ : ℝ) :
    t * t ^ (γ - 2) = t ^ (γ - 1) := by
  rw [show γ - 1 = 1 + (γ - 2) by ring, Real.rpow_add ht 1 (γ - 2), Real.rpow_one]

private lemma gsLayer_term (γ : ℝ) (x : ℝ≥0) {t : ℝ} (ht : 0 < t) :
    ((min x t.toNNReal : ℝ≥0) : ℝ≥0∞) * ((t.toNNReal : ℝ≥0∞)⁻¹ * ENNReal.ofReal (t ^ (γ - 1))) =
      ENNReal.ofReal (min (x : ℝ) t * t ^ (γ - 2)) := by
  have h1 : ((min x t.toNNReal : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (min (x : ℝ) t) := by
    rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_min, Real.coe_toNNReal t ht.le]
  have h2 : (t.toNNReal : ℝ≥0∞)⁻¹ * ENNReal.ofReal (t ^ (γ - 1)) =
      ENNReal.ofReal (t ^ (γ - 2)) := by
    rw [ENNReal.ofNNReal_toNNReal, ← ENNReal.ofReal_inv_of_pos ht,
      ← ENNReal.ofReal_mul (inv_nonneg.2 ht.le), inv_mul_eq_div,
      ← Real.rpow_sub_one ht.ne' (γ - 1), show γ - 1 - 1 = γ - 2 by ring]
  rw [h1, h2, ← ENNReal.ofReal_mul (le_min (NNReal.coe_nonneg x) ht.le)]

private lemma gsLayer_Ioc (γ : ℝ) (hγ0 : 0 < γ) {a : ℝ} (ha : 0 < a) :
    ∫⁻ t in Set.Ioc (0 : ℝ) a, ENNReal.ofReal (min a t * t ^ (γ - 2)) =
      ENNReal.ofReal (a ^ γ / γ) := by
  have e : ∫⁻ t in Set.Ioc (0 : ℝ) a, ENNReal.ofReal (min a t * t ^ (γ - 2)) =
      ∫⁻ t in Set.Ioc (0 : ℝ) a, ENNReal.ofReal (t ^ (γ - 1)) := by
    apply setLIntegral_congr_fun measurableSet_Ioc
    intro t ht
    show ENNReal.ofReal (min a t * t ^ (γ - 2)) = ENNReal.ofReal (t ^ (γ - 1))
    rw [min_eq_right ht.2, gsLayer_mul_rpow ht.1 γ]
  have hint : IntegrableOn (fun t : ℝ => t ^ (γ - 1)) (Set.Ioc (0 : ℝ) a) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ha.le).1
      (intervalIntegral.intervalIntegrable_rpow' (show (-1 : ℝ) < γ - 1 by linarith))
  have hnn : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) a)), 0 ≤ t ^ (γ - 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact Real.rpow_nonneg ht.1.le _
  rw [e, ← ofReal_integral_eq_lintegral_ofReal hint hnn,
    ← intervalIntegral.integral_of_le ha.le,
    integral_rpow (Or.inl (show (-1 : ℝ) < γ - 1 by linarith)), show γ - 1 + 1 = γ by ring,
    Real.zero_rpow hγ0.ne', sub_zero]

private lemma gsLayer_Ioi (γ : ℝ) (hγ1 : γ < 1) {a : ℝ} (ha : 0 < a) :
    ∫⁻ t in Set.Ioi a, ENNReal.ofReal (min a t * t ^ (γ - 2)) =
      ENNReal.ofReal a * ENNReal.ofReal (a ^ (γ - 1) / (1 - γ)) := by
  have e : ∫⁻ t in Set.Ioi a, ENNReal.ofReal (min a t * t ^ (γ - 2)) =
      ∫⁻ t in Set.Ioi a, ENNReal.ofReal a * ENNReal.ofReal (t ^ (γ - 2)) := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t ht
    show ENNReal.ofReal (min a t * t ^ (γ - 2)) = ENNReal.ofReal a * ENNReal.ofReal (t ^ (γ - 2))
    rw [min_eq_left (Set.mem_Ioi.mp ht).le, ENNReal.ofReal_mul ha.le]
  have hint : IntegrableOn (fun t : ℝ => t ^ (γ - 2)) (Set.Ioi a) :=
    integrableOn_Ioi_rpow_of_lt (show γ - 2 < -1 by linarith) ha
  have hnn : ∀ᵐ t ∂(volume.restrict (Set.Ioi a)), 0 ≤ t ^ (γ - 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg (ha.trans (Set.mem_Ioi.mp ht)).le _
  rw [e, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← ofReal_integral_eq_lintegral_ofReal hint hnn,
    integral_Ioi_rpow_of_lt (show γ - 2 < -1 by linarith) ha, show γ - 2 + 1 = γ - 1 by ring,
    neg_div, ← div_neg, neg_sub]

private lemma gsLayer_oneD (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) {a : ℝ} (ha : 0 ≤ a) :
    ENNReal.ofReal γ * ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (min a t * t ^ (γ - 2)) ≤
      ENNReal.ofReal (1 / (1 - γ)) * ENNReal.ofReal (a ^ γ) := by
  rcases ha.eq_or_lt with h0 | hpos
  · have hz : ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (min a t * t ^ (γ - 2)) =
        ∫⁻ _t in Set.Ioi (0 : ℝ), 0 := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro t ht
      show ENNReal.ofReal (min a t * t ^ (γ - 2)) = 0
      rw [← h0, min_eq_left (Set.mem_Ioi.mp ht).le, zero_mul, ENNReal.ofReal_zero]
    rw [hz, lintegral_zero, mul_zero]
    exact zero_le
  · have h1 : 0 < 1 - γ := sub_pos.2 hγ1
    have hX : a * a ^ (γ - 1) = a ^ γ := by
      have h := Real.rpow_add hpos 1 (γ - 1)
      rw [Real.rpow_one, show (1 : ℝ) + (γ - 1) = γ by ring] at h
      exact h.symm
    have hsplit : ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (min a t * t ^ (γ - 2)) =
        (∫⁻ t in Set.Ioc (0 : ℝ) a, ENNReal.ofReal (min a t * t ^ (γ - 2))) +
          ∫⁻ t in Set.Ioi a, ENNReal.ofReal (min a t * t ^ (γ - 2)) := by
      rw [← Set.Ioc_union_Ioi_eq_Ioi hpos.le,
        lintegral_union measurableSet_Ioi Set.Ioc_disjoint_Ioi_same]
    rw [hsplit, gsLayer_Ioc γ hγ0 hpos, gsLayer_Ioi γ hγ1 hpos, ← ENNReal.ofReal_mul ha,
      ← ENNReal.ofReal_add (div_nonneg (Real.rpow_nonneg ha γ) hγ0.le)
        (mul_nonneg ha (div_nonneg (Real.rpow_nonneg ha (γ - 1)) h1.le)),
      ← ENNReal.ofReal_mul hγ0.le, ← ENNReal.ofReal_mul (div_nonneg zero_le_one h1.le)]
    apply le_of_eq
    congr 1
    rw [← mul_div_assoc, hX]
    have i1 : γ * γ⁻¹ = 1 := mul_inv_cancel₀ hγ0.ne'
    have i2 : (1 - γ) * (1 - γ)⁻¹ = 1 := mul_inv_cancel₀ h1.ne'
    linear_combination a ^ γ * i1 - a ^ γ * i2

theorem lintegral_rpow_le_of_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (F A : Ω → ℝ≥0) (hF : Measurable F) (hA : Measurable A)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (htail : ∀ c : ℝ≥0, 0 < c →
      P {ω | c < F ω} ≤ P {ω | c ≤ A ω} + (∫⁻ ω, ((min (A ω) c : ℝ≥0) : ℝ≥0∞) ∂P) / (c : ℝ≥0∞)) :
    ∫⁻ ω, (F ω : ℝ≥0∞) ^ γ ∂P ≤ ENNReal.ofReal ((2 - γ) / (1 - γ)) * ∫⁻ ω, (A ω : ℝ≥0∞) ^ γ ∂P := by
  have hfst : Measurable (Prod.fst : ℝ × Ω → ℝ) := measurable_fst
  have hsnd : Measurable (fun p : ℝ × Ω => (A p.2 : ℝ)) := (hA.comp measurable_snd).coe_nnreal_real
  have hGm : Measurable (Function.uncurry fun (t : ℝ) (ω : Ω) =>
      ENNReal.ofReal (min (A ω : ℝ) t * t ^ (γ - 2))) :=
    ((hsnd.min hfst).mul (hfst.pow_const (γ - 2))).ennreal_ofReal
  have hYm : Measurable fun t : ℝ => ∫⁻ ω, ENNReal.ofReal (min (A ω : ℝ) t * t ^ (γ - 2)) ∂P :=
    hGm.lintegral_prod_right
  have hswap : ∫⁻ t in Set.Ioi (0 : ℝ), ∫⁻ ω, ENNReal.ofReal (min (A ω : ℝ) t * t ^ (γ - 2)) ∂P =
      ∫⁻ ω, (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (min (A ω : ℝ) t * t ^ (γ - 2))) ∂P :=
    lintegral_lintegral_swap hGm.aemeasurable
  have hlayerF : ∫⁻ ω, (F ω : ℝ≥0∞) ^ γ ∂P =
      ENNReal.ofReal γ *
        ∫⁻ t in Set.Ioi (0 : ℝ), P {a | t < (F a : ℝ)} * ENNReal.ofReal (t ^ (γ - 1)) :=
    (lintegral_congr fun ω => gsLayer_coe_rpow (F ω) hγ0.le).trans
      (lintegral_rpow_eq_lintegral_meas_lt_mul P (f := fun ω => (F ω : ℝ))
        (Eventually.of_forall fun ω => NNReal.coe_nonneg (F ω)) hF.coe_nnreal_real.aemeasurable hγ0)
  have hlayerA : ∫⁻ ω, (A ω : ℝ≥0∞) ^ γ ∂P =
      ENNReal.ofReal γ *
        ∫⁻ t in Set.Ioi (0 : ℝ), P {a | t ≤ (A a : ℝ)} * ENNReal.ofReal (t ^ (γ - 1)) :=
    (lintegral_congr fun ω => gsLayer_coe_rpow (A ω) hγ0.le).trans
      (lintegral_rpow_eq_lintegral_meas_le_mul P (f := fun ω => (A ω : ℝ))
        (Eventually.of_forall fun ω => NNReal.coe_nonneg (A ω)) hA.coe_nnreal_real.aemeasurable hγ0)
  have hT : ∀ t ∈ Set.Ioi (0 : ℝ),
      P {a | t < (F a : ℝ)} * ENNReal.ofReal (t ^ (γ - 1)) ≤
        P {a | t ≤ (A a : ℝ)} * ENNReal.ofReal (t ^ (γ - 1)) +
          ∫⁻ ω, ENNReal.ofReal (min (A ω : ℝ) t * t ^ (γ - 2)) ∂P := by
    intro t ht
    have ht' : 0 < t := ht
    have hc : 0 < t.toNNReal := Real.toNNReal_pos.2 ht'
    have e1 : {a | t < (F a : ℝ)} = {ω | t.toNNReal < F ω} :=
      Set.ext fun ω => (Real.toNNReal_lt_iff_lt_coe ht'.le).symm
    have e2 : {a | t ≤ (A a : ℝ)} = {ω | t.toNNReal ≤ A ω} :=
      Set.ext fun ω => Real.toNNReal_le_iff_le_coe.symm
    have hm : Measurable fun ω => ((min (A ω) t.toNNReal : ℝ≥0) : ℝ≥0∞) :=
      (hA.min measurable_const).coe_nnreal_ennreal
    have e3 : (∫⁻ ω, ((min (A ω) t.toNNReal : ℝ≥0) : ℝ≥0∞) ∂P) / (t.toNNReal : ℝ≥0∞) *
        ENNReal.ofReal (t ^ (γ - 1)) =
          ∫⁻ ω, ENNReal.ofReal (min (A ω : ℝ) t * t ^ (γ - 2)) ∂P := by
      rw [div_eq_mul_inv, mul_assoc, ← lintegral_mul_const _ hm]
      exact lintegral_congr fun ω => gsLayer_term γ (A ω) ht'
    rw [e1, e2, ← e3, ← add_mul]
    exact mul_le_mul_of_nonneg_right (htail _ hc) zero_le
  have hstep : ∫⁻ t in Set.Ioi (0 : ℝ), P {a | t < (F a : ℝ)} * ENNReal.ofReal (t ^ (γ - 1)) ≤
      (∫⁻ t in Set.Ioi (0 : ℝ), P {a | t ≤ (A a : ℝ)} * ENNReal.ofReal (t ^ (γ - 1))) +
        ∫⁻ t in Set.Ioi (0 : ℝ), ∫⁻ ω, ENNReal.ofReal (min (A ω : ℝ) t * t ^ (γ - 2)) ∂P :=
    (setLIntegral_mono' measurableSet_Ioi hT).trans_eq (lintegral_add_right _ hYm)
  have hone : ∀ ω, ENNReal.ofReal γ *
      ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (min (A ω : ℝ) t * t ^ (γ - 2)) ≤
        ENNReal.ofReal (1 / (1 - γ)) * (A ω : ℝ≥0∞) ^ γ := by
    intro ω
    rw [gsLayer_coe_rpow (A ω) hγ0.le]
    exact gsLayer_oneD γ hγ0 hγ1 (NNReal.coe_nonneg (A ω))
  have hconst : ENNReal.ofReal ((2 - γ) / (1 - γ)) = 1 + ENNReal.ofReal (1 / (1 - γ)) := by
    have h1 : 0 < 1 - γ := sub_pos.2 hγ1
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (div_nonneg zero_le_one h1.le)]
    congr 1
    linear_combination (mul_inv_cancel₀ h1.ne' : (1 - γ) * (1 - γ)⁻¹ = 1)
  calc ∫⁻ ω, (F ω : ℝ≥0∞) ^ γ ∂P
      = ENNReal.ofReal γ *
          ∫⁻ t in Set.Ioi (0 : ℝ), P {a | t < (F a : ℝ)} * ENNReal.ofReal (t ^ (γ - 1)) :=
        hlayerF
    _ ≤ ENNReal.ofReal γ *
          ((∫⁻ t in Set.Ioi (0 : ℝ), P {a | t ≤ (A a : ℝ)} * ENNReal.ofReal (t ^ (γ - 1))) +
            ∫⁻ t in Set.Ioi (0 : ℝ), ∫⁻ ω, ENNReal.ofReal (min (A ω : ℝ) t * t ^ (γ - 2)) ∂P) :=
        mul_le_mul_of_nonneg_left hstep zero_le
    _ = ∫⁻ ω, (A ω : ℝ≥0∞) ^ γ ∂P + ∫⁻ ω, ENNReal.ofReal γ *
          (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (min (A ω : ℝ) t * t ^ (γ - 2))) ∂P := by
        rw [mul_add, hlayerA, hswap, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ∫⁻ ω, (A ω : ℝ≥0∞) ^ γ ∂P +
          ∫⁻ ω, ENNReal.ofReal (1 / (1 - γ)) * (A ω : ℝ≥0∞) ^ γ ∂P :=
        add_le_add le_rfl (lintegral_mono hone)
    _ = ENNReal.ofReal ((2 - γ) / (1 - γ)) * ∫⁻ ω, (A ω : ℝ≥0∞) ^ γ ∂P := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hconst, add_mul, one_mul]

end SabanisEuler.UniformRate.GSStop

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace SabanisEuler.UniformRate.AAReadback

theorem iSup_rpow_eq {ι : Sort*} (h : ι → ℝ≥0∞) {γ : ℝ} (hγ : 0 < γ) :
    (⨆ i, h i ^ γ) = (⨆ i, h i) ^ γ := by
  exact ((ENNReal.orderIsoRpow γ hγ).map_iSup h).symm

end SabanisEuler.UniformRate.AAReadback

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace SabanisEuler.UniformRate.Owner

/-- One rational term of the countable supremum bounds the term itself. -/
theorem owner_term_le {Ω : Type*} (f : ℝ≥0 → Ω → ℝ≥0) (τ : Ω → WithTop ℝ≥0) (ω : Ω) (q : ℚ)
    (hq : (((q : ℝ).toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ ω) :
    (f (q : ℝ).toNNReal ω : ℝ≥0∞) ≤
      ⨆ r : ℚ, if (((r : ℝ).toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ ω then
        (f (r : ℝ).toNNReal ω : ℝ≥0∞) else 0 :=
  le_iSup_of_le q (le_of_eq (if_pos hq).symm)

/-- On `[0, τ ω] ⊆ [0, T]`, the supremum of a path that is continuous on `[0, T]` equals its
supremum over the rational points. -/
theorem owner_sup_eq_rat_sup {Ω : Type*} (T : ℝ≥0) (f : ℝ≥0 → Ω → ℝ≥0)
    (hf_cont : ∀ ω, ContinuousOn (fun t => f t ω) (Set.Icc 0 T))
    (τ : Ω → WithTop ℝ≥0) (hτT : ∀ ω, τ ω ≤ (T : WithTop ℝ≥0)) (ω : Ω) :
    (⨆ (t : ℝ≥0) (_ : (t : WithTop ℝ≥0) ≤ τ ω), (f t ω : ℝ≥0∞)) =
      ⨆ r : ℚ, if (((r : ℝ).toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ ω then
        (f (r : ℝ).toNNReal ω : ℝ≥0∞) else 0 := by
  apply le_antisymm
  · refine iSup₂_le fun t ht => ?_
    have htT : t ≤ T := by exact_mod_cast ht.trans (hτT ω)
    obtain ⟨u, -, hu_lt, hu_tend⟩ := Real.exists_seq_rat_strictMono_tendsto (t : ℝ)
    have hs_tend : Tendsto (fun n => ((u n : ℚ) : ℝ).toNNReal) atTop (𝓝 t) := by
      have h := (continuous_real_toNNReal.tendsto (t : ℝ)).comp hu_tend
      rw [Real.toNNReal_coe] at h
      exact h
    have hs_le : ∀ n, ((u n : ℚ) : ℝ).toNNReal ≤ t := fun n =>
      Real.toNNReal_le_iff_le_coe.mpr (hu_lt n).le
    have hs_mem : ∀ n, ((u n : ℚ) : ℝ).toNNReal ∈ Set.Icc (0 : ℝ≥0) T := fun n =>
      ⟨zero_le, (hs_le n).trans htT⟩
    have hcw : ContinuousWithinAt (fun s => f s ω) (Set.Icc 0 T) t :=
      hf_cont ω t ⟨zero_le, htT⟩
    have hf_tend : Tendsto (fun n => f ((u n : ℚ) : ℝ).toNNReal ω) atTop (𝓝 (f t ω)) :=
      hcw.tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hs_tend, Eventually.of_forall hs_mem⟩)
    have hE_tend : Tendsto (fun n => (f ((u n : ℚ) : ℝ).toNNReal ω : ℝ≥0∞)) atTop
        (𝓝 (f t ω : ℝ≥0∞)) :=
      (ENNReal.continuous_coe.tendsto _).comp hf_tend
    refine le_of_tendsto' hE_tend fun n => ?_
    have hq : ((((u n : ℚ) : ℝ).toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ ω :=
      (WithTop.coe_le_coe.mpr (hs_le n)).trans ht
    exact owner_term_le f τ ω (u n) hq
  · refine iSup_le fun r => ?_
    by_cases hr : (((r : ℝ).toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ ω
    · rw [if_pos hr]
      exact le_iSup₂ (f := fun (t : ℝ≥0) (_ : (t : WithTop ℝ≥0) ≤ τ ω) => (f t ω : ℝ≥0∞))
        (r : ℝ).toNNReal hr
    · rw [if_neg hr]
      exact zero_le

/-- The running supremum of an adapted path, continuous on `[0, T]`, up to a stopping time
`τ ≤ T` is measurable. -/
theorem owner_measurable_sup {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℝ≥0 mΩ)
    (T : ℝ≥0) (f : ℝ≥0 → Ω → ℝ≥0)
    (hf_cont : ∀ ω, ContinuousOn (fun t => f t ω) (Set.Icc 0 T))
    (hf_adapt : ∀ t ≤ T, Measurable[ℱ t] (f t))
    (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime ℱ τ) (hτT : ∀ ω, τ ω ≤ (T : WithTop ℝ≥0)) :
    Measurable (fun ω => ⨆ (t : ℝ≥0) (_ : (t : WithTop ℝ≥0) ≤ τ ω), (f t ω : ℝ≥0∞)) := by
  have heq : (fun ω => ⨆ (t : ℝ≥0) (_ : (t : WithTop ℝ≥0) ≤ τ ω), (f t ω : ℝ≥0∞)) =
      fun ω => ⨆ r : ℚ, if (((r : ℝ).toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ ω then
        (f (r : ℝ).toNNReal ω : ℝ≥0∞) else 0 :=
    funext (owner_sup_eq_rat_sup T f hf_cont τ hτT)
  rw [heq]
  refine Measurable.iSup fun r => ?_
  by_cases hrT : (r : ℝ).toNNReal ≤ T
  · have hset : MeasurableSet {ω | (((r : ℝ).toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ ω} :=
      hτ.measurableSpace_le _ (hτ.measurableSet_ge' _)
    have hfm : Measurable (fun ω => (f (r : ℝ).toNNReal ω : ℝ≥0∞)) :=
      ((hf_adapt _ hrT).mono (ℱ.le _) le_rfl).coe_nnreal_ennreal
    exact Measurable.ite hset hfm measurable_const
  · have hfalse : ∀ ω, ¬ ((((r : ℝ).toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ ω) := fun ω h =>
      hrT (by exact_mod_cast h.trans (hτT ω))
    have hconst : (fun ω => if (((r : ℝ).toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ ω then
        (f (r : ℝ).toNNReal ω : ℝ≥0∞) else 0) = fun _ => 0 :=
      funext fun ω => if_neg (hfalse ω)
    rw [hconst]
    exact measurable_const

/-- The running supremum up to `τ ≤ T` of a path continuous on `[0, T]` is finite. -/
theorem owner_sup_lt_top {Ω : Type*} (T : ℝ≥0) (f : ℝ≥0 → Ω → ℝ≥0)
    (hf_cont : ∀ ω, ContinuousOn (fun t => f t ω) (Set.Icc 0 T))
    (τ : Ω → WithTop ℝ≥0) (hτT : ∀ ω, τ ω ≤ (T : WithTop ℝ≥0)) (ω : Ω) :
    (⨆ (t : ℝ≥0) (_ : (t : WithTop ℝ≥0) ≤ τ ω), (f t ω : ℝ≥0∞)) < ⊤ := by
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image (hf_cont ω)
  refine lt_of_le_of_lt (iSup₂_le fun t ht => ?_) (ENNReal.coe_lt_top (r := C))
  have htT : t ≤ T := by exact_mod_cast ht.trans (hτT ω)
  exact ENNReal.coe_le_coe.mpr (hC ⟨t, ⟨zero_le, htT⟩, rfl⟩)

end SabanisEuler.UniformRate.Owner

namespace SabanisEuler.UniformRate.Owner

/-- If a path stays strictly below `c` on `[0, a]` with `a ≤ T`, its first entrance time into
`[c, ∞)` on `[0, T]` is at least `a`. -/
theorem owner_le_hittingBtwn {Ω : Type*} (T : ℝ≥0) (u : ℝ≥0 → Ω → ℝ≥0) (c : ℝ≥0) (ω : Ω)
    {a : ℝ≥0} (haT : a ≤ T) (h : ∀ j ≤ a, u j ω < c) :
    a ≤ hittingBtwn u (Set.Ici c) 0 T ω := by
  simp only [hittingBtwn]
  split_ifs with hex
  · obtain ⟨j₀, hj₀, hj₀s⟩ := hex
    refine le_csInf ⟨j₀, hj₀, hj₀s⟩ fun j hj => ?_
    have hj2 : u j ω ∈ Set.Ici c := hj.2
    by_contra hlt
    exact absurd (h j (le_of_lt (not_le.mp hlt))) (not_lt.mpr (Set.mem_Ici.mp hj2))
  · exact haT

/-- The tail estimate behind the Gyöngy–Krylov inequality: with `F` and `A` the running suprema
of `f` and `g` up to `τ`, `P(F > c) ≤ P(A ≥ c) + E[min(A, c)] / c` for every `c > 0`. It is
obtained from `hdom` at the stopping time `θ = σ_c ⊓ ρ_c ⊓ τ`, where `σ_c` and `ρ_c` are the first
entrance times of `f` and `g` into `[c, ∞)` on `[0, T]`. -/
theorem owner_tail {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    (ℱ : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (f g : ℝ≥0 → Ω → ℝ≥0)
    (hf_cont : ∀ ω, ContinuousOn (fun t => f t ω) (Set.Icc 0 T))
    (hg_cont : ∀ ω, ContinuousOn (fun t => g t ω) (Set.Icc 0 T))
    (hf_adapt : ∀ t ≤ T, Measurable[ℱ t] (f t))
    (hg_adapt : ∀ t ≤ T, Measurable[ℱ t] (g t))
    (hdom : ∀ c : ℝ≥0, 0 < c → ∀ τ : Ω → WithTop ℝ≥0, IsStoppingTime ℱ τ →
      (∀ ω, τ ω ≤ (T : WithTop ℝ≥0)) →
      ∫⁻ ω, {ω | g 0 ω ≤ c}.indicator (fun ω => ((stoppedValue f τ ω : ℝ≥0) : ℝ≥0∞)) ω ∂P
        ≤ ∫⁻ ω, {ω | g 0 ω ≤ c}.indicator (fun ω => ((stoppedValue g τ ω : ℝ≥0) : ℝ≥0∞)) ω ∂P)
    (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime ℱ τ) (hτT : ∀ ω, τ ω ≤ (T : WithTop ℝ≥0))
    (c : ℝ≥0) (hc : 0 < c) :
    P {ω | c < (⨆ (t : ℝ≥0) (_ : (t : WithTop ℝ≥0) ≤ τ ω), (f t ω : ℝ≥0∞)).toNNReal} ≤
      P {ω | c ≤ (⨆ (t : ℝ≥0) (_ : (t : WithTop ℝ≥0) ≤ τ ω), (g t ω : ℝ≥0∞)).toNNReal} +
        (∫⁻ ω, ((min (⨆ (t : ℝ≥0) (_ : (t : WithTop ℝ≥0) ≤ τ ω), (g t ω : ℝ≥0∞)).toNNReal c :
          ℝ≥0) : ℝ≥0∞) ∂P) / (c : ℝ≥0∞) := by
  obtain ⟨S, hSdef⟩ : ∃ S : Ω → ℝ≥0∞,
      S = fun ω => ⨆ (t : ℝ≥0) (_ : (t : WithTop ℝ≥0) ≤ τ ω), (f t ω : ℝ≥0∞) := ⟨_, rfl⟩
  obtain ⟨G, hGdef⟩ : ∃ G : Ω → ℝ≥0∞,
      G = fun ω => ⨆ (t : ℝ≥0) (_ : (t : WithTop ℝ≥0) ≤ τ ω), (g t ω : ℝ≥0∞) := ⟨_, rfl⟩
  have hS_eq : ∀ ω, (⨆ (t : ℝ≥0) (_ : (t : WithTop ℝ≥0) ≤ τ ω), (f t ω : ℝ≥0∞)) = S ω :=
    fun ω => by rw [hSdef]
  have hG_eq : ∀ ω, (⨆ (t : ℝ≥0) (_ : (t : WithTop ℝ≥0) ≤ τ ω), (g t ω : ℝ≥0∞)) = G ω :=
    fun ω => by rw [hGdef]
  simp only [hS_eq, hG_eq]
  have hSm : Measurable S := by
    rw [hSdef]
    exact owner_measurable_sup ℱ T f hf_cont hf_adapt τ hτ hτT
  have hGm : Measurable G := by
    rw [hGdef]
    exact owner_measurable_sup ℱ T g hg_cont hg_adapt τ hτ hτT
  have hGfin : ∀ ω, G ω ≠ ⊤ := fun ω => by
    rw [← hG_eq ω]
    exact (owner_sup_lt_top T g hg_cont τ hτT ω).ne
  have hSfin : ∀ ω, S ω ≠ ⊤ := fun ω => by
    rw [← hS_eq ω]
    exact (owner_sup_lt_top T f hf_cont τ hτT ω).ne
  -- the stopping time θ = σ_c ⊓ ρ_c ⊓ τ
  obtain ⟨θ, hθdef⟩ : ∃ θ : Ω → WithTop ℝ≥0, θ = fun ω =>
      min (min ((hittingBtwn f (Set.Ici c) 0 T ω : ℝ≥0) : WithTop ℝ≥0)
        ((hittingBtwn g (Set.Ici c) 0 T ω : ℝ≥0) : WithTop ℝ≥0)) (τ ω) := ⟨_, rfl⟩
  have hθ : IsStoppingTime ℱ θ := by
    rw [hθdef]
    exact ((GSStop.isStoppingTime_hittingBtwn_Ici ℱ T f c hf_cont hf_adapt).min
      (GSStop.isStoppingTime_hittingBtwn_Ici ℱ T g c hg_cont hg_adapt)).min hτ
  have hθτ : ∀ ω, θ ω ≤ τ ω := fun ω => by rw [hθdef]; exact min_le_right _ _
  have hθρ : ∀ ω, θ ω ≤ ((hittingBtwn g (Set.Ici c) 0 T ω : ℝ≥0) : WithTop ℝ≥0) := fun ω => by
    rw [hθdef]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hθT : ∀ ω, θ ω ≤ (T : WithTop ℝ≥0) := fun ω => (hθτ ω).trans (hτT ω)
  have hθv : ∀ ω, ∃ v : ℝ≥0, θ ω = (v : WithTop ℝ≥0) := fun ω => by
    obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_le_ne_top WithTop.coe_ne_top (hθT ω))
    exact ⟨v, hv.symm⟩
  -- values of g below A and below the hitting level
  have hg_le_G : ∀ ω (s : ℝ≥0), (s : WithTop ℝ≥0) ≤ τ ω → (g s ω : ℝ≥0∞) ≤ G ω := fun ω s hs => by
    rw [← hG_eq ω]
    exact le_iSup₂ (f := fun (t : ℝ≥0) (_ : (t : WithTop ℝ≥0) ≤ τ ω) => (g t ω : ℝ≥0∞)) s hs
  -- pointwise truncation of the stopped value of g
  have htrunc : ∀ ω, g 0 ω ≤ c → stoppedValue g θ ω ≤ min (G ω).toNNReal c := fun ω h0 => by
    obtain ⟨v, hv⟩ := hθv ω
    have hval : stoppedValue g θ ω = g v ω :=
      (congrArg (fun x : WithTop ℝ≥0 => g x.untopA ω) hv).trans rfl
    rw [hval]
    have hvτ : (v : WithTop ℝ≥0) ≤ τ ω := by
      rw [← hv]
      exact hθτ ω
    have hvρ : v ≤ hittingBtwn g (Set.Ici c) 0 T ω := by
      have h := hθρ ω
      rw [hv] at h
      exact WithTop.coe_le_coe.mp h
    refine le_min ?_ ?_
    · have h1 : (g v ω : ℝ≥0∞) ≤ G ω := hg_le_G ω v hvτ
      rw [← ENNReal.coe_toNNReal (hGfin ω)] at h1
      exact ENNReal.coe_le_coe.mp h1
    · rcases lt_or_eq_of_le hvρ with hlt | heq
      · have hnot := notMem_of_lt_hittingBtwn hlt (zero_le : (0 : ℝ≥0) ≤ v)
        exact le_of_lt (not_le.mp fun hge => hnot (Set.mem_Ici.mpr hge))
      · rw [heq]
        exact GSStop.hittingBtwn_Ici_value_le T g c ω (hg_cont ω) h0
  -- the bad event and its pointwise consequences
  have hevent : ∀ ω, c < (S ω).toNNReal → (G ω).toNNReal < c →
      g 0 ω ≤ c ∧ c ≤ stoppedValue f θ ω := fun ω hF hA => by
    have hcS : (c : ℝ≥0∞) < S ω := by
      rw [← ENNReal.coe_toNNReal (hSfin ω)]
      exact ENNReal.coe_lt_coe.mpr hF
    rw [← hS_eq ω] at hcS
    obtain ⟨t, ht⟩ := lt_iSup_iff.mp hcS
    obtain ⟨htτ, hct⟩ := lt_iSup_iff.mp ht
    have hct' : c < f t ω := ENNReal.coe_lt_coe.mp hct
    have htT : t ≤ T := by exact_mod_cast htτ.trans (hτT ω)
    obtain ⟨hσt, hfσ⟩ := GSStop.hittingBtwn_Ici_spec T f c ω (hf_cont ω) htT hct'.le
    have hg_lt : ∀ s : ℝ≥0, (s : WithTop ℝ≥0) ≤ τ ω → g s ω < c := fun s hs => by
      have h1 : (g s ω : ℝ≥0∞) ≤ G ω := hg_le_G ω s hs
      rw [← ENNReal.coe_toNNReal (hGfin ω)] at h1
      exact lt_of_le_of_lt (ENNReal.coe_le_coe.mp h1) hA
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_le_ne_top WithTop.coe_ne_top (hτT ω))
    have haT : a ≤ T := by
      have h := hτT ω
      rw [← ha] at h
      exact WithTop.coe_le_coe.mp h
    have hρa : a ≤ hittingBtwn g (Set.Ici c) 0 T ω :=
      owner_le_hittingBtwn T g c ω haT fun j hj =>
        hg_lt j (by rw [← ha]; exact WithTop.coe_le_coe.mpr hj)
    have hta : t ≤ a := by
      have h := htτ
      rw [← ha] at h
      exact WithTop.coe_le_coe.mp h
    have hθσ : θ ω = ((hittingBtwn f (Set.Ici c) 0 T ω : ℝ≥0) : WithTop ℝ≥0) := by
      rw [hθdef]
      show min (min ((hittingBtwn f (Set.Ici c) 0 T ω : ℝ≥0) : WithTop ℝ≥0)
        ((hittingBtwn g (Set.Ici c) 0 T ω : ℝ≥0) : WithTop ℝ≥0)) (τ ω) = _
      rw [min_eq_left (WithTop.coe_le_coe.mpr (hσt.trans (hta.trans hρa))), ← ha,
        min_eq_left (WithTop.coe_le_coe.mpr (hσt.trans hta))]
    refine ⟨(hg_lt 0 (by rw [← ha]; exact WithTop.coe_le_coe.mpr zero_le)).le, ?_⟩
    show c ≤ f (θ ω).untopA ω
    rw [hθσ]
    exact hfσ
  -- the bad event is measurable
  have hE : MeasurableSet ({ω | c < (S ω).toNNReal} ∩ {ω | (G ω).toNNReal < c}) :=
    (measurableSet_lt measurable_const hSm.ennreal_toNNReal).inter
      (measurableSet_lt hGm.ennreal_toNNReal measurable_const)
  -- Chebyshev with `hdom`
  have hcheb : (c : ℝ≥0∞) * P ({ω | c < (S ω).toNNReal} ∩ {ω | (G ω).toNNReal < c}) ≤
      ∫⁻ ω, ((min (G ω).toNNReal c : ℝ≥0) : ℝ≥0∞) ∂P := by
    rw [← lintegral_indicator_const hE]
    calc
      ∫⁻ ω, ({ω | c < (S ω).toNNReal} ∩ {ω | (G ω).toNNReal < c}).indicator
          (fun _ => (c : ℝ≥0∞)) ω ∂P
          ≤ ∫⁻ ω, {ω | g 0 ω ≤ c}.indicator
              (fun ω => ((stoppedValue f θ ω : ℝ≥0) : ℝ≥0∞)) ω ∂P := by
            refine lintegral_mono fun ω => ?_
            by_cases hω : ω ∈ {ω | c < (S ω).toNNReal} ∩ {ω | (G ω).toNNReal < c}
            · obtain ⟨h0, hcf⟩ := hevent ω hω.1 hω.2
              rw [Set.indicator_of_mem hω, Set.indicator_of_mem (show ω ∈ {ω | g 0 ω ≤ c} from h0)]
              exact ENNReal.coe_le_coe.mpr hcf
            · rw [Set.indicator_of_notMem hω]
              exact zero_le
      _ ≤ ∫⁻ ω, {ω | g 0 ω ≤ c}.indicator
              (fun ω => ((stoppedValue g θ ω : ℝ≥0) : ℝ≥0∞)) ω ∂P :=
            hdom c hc θ hθ hθT
      _ ≤ ∫⁻ ω, ((min (G ω).toNNReal c : ℝ≥0) : ℝ≥0∞) ∂P := by
            refine lintegral_mono fun ω => ?_
            by_cases h0 : g 0 ω ≤ c
            · rw [Set.indicator_of_mem (show ω ∈ {ω | g 0 ω ≤ c} from h0)]
              exact ENNReal.coe_le_coe.mpr (htrunc ω h0)
            · rw [Set.indicator_of_notMem (show ω ∉ {ω | g 0 ω ≤ c} from h0)]
              exact zero_le
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc.ne'
  have hbad : P ({ω | c < (S ω).toNNReal} ∩ {ω | (G ω).toNNReal < c}) ≤
      (∫⁻ ω, ((min (G ω).toNNReal c : ℝ≥0) : ℝ≥0∞) ∂P) / (c : ℝ≥0∞) := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl ENNReal.coe_ne_top), mul_comm]
    exact hcheb
  have hsplit : {ω | c < (S ω).toNNReal} ⊆
      {ω | c ≤ (G ω).toNNReal} ∪ ({ω | c < (S ω).toNNReal} ∩ {ω | (G ω).toNNReal < c}) :=
    fun ω hω => by
      by_cases hA : c ≤ (G ω).toNNReal
      · exact Or.inl hA
      · exact Or.inr ⟨hω, not_le.mp hA⟩
  calc
    P {ω | c < (S ω).toNNReal}
        ≤ P ({ω | c ≤ (G ω).toNNReal} ∪
            ({ω | c < (S ω).toNNReal} ∩ {ω | (G ω).toNNReal < c})) := measure_mono hsplit
    _ ≤ P {ω | c ≤ (G ω).toNNReal} +
          P ({ω | c < (S ω).toNNReal} ∩ {ω | (G ω).toNNReal < c}) := measure_union_le _ _
    _ ≤ P {ω | c ≤ (G ω).toNNReal} +
          (∫⁻ ω, ((min (G ω).toNNReal c : ℝ≥0) : ℝ≥0∞) ∂P) / (c : ℝ≥0∞) :=
        add_le_add le_rfl hbad

end SabanisEuler.UniformRate.Owner

namespace SabanisEuler.UniformRate

/-- Sabanis (2016), arXiv:1308.1796v4, p. 19, Lemma 5 (the Gyöngy–Krylov / Lenglart-type
maximal inequality). Let `T ∈ [0, ∞)` and let `f = (f_t)_{t ∈ [0, T]}`,
`g = (g_t)_{t ∈ [0, T]}` be nonnegative `ℱ`-adapted processes with continuous paths on
`[0, T]` such that, for every constant `c > 0` and every stopping time `τ ≤ T`,
`𝔼[f_τ 𝟙_{g₀ ≤ c}] ≤ 𝔼[g_τ 𝟙_{g₀ ≤ c}]`. Then for every stopping time `τ ≤ T` and every
`γ ∈ (0, 1)`,
`𝔼[sup_{t ≤ τ} f_t^γ] ≤ (2 - γ)/(1 - γ) · 𝔼[sup_{t ≤ τ} g_t^γ]`.
Nonnegativity is built into the value type `ℝ≥0`; expectations are lower Lebesgue integrals
in `[0, ∞]`. Nothing is required of `f`, `g` after `T`. `g` is not assumed nondecreasing,
and the right-hand side is `sup_{t ≤ τ} g_t^γ`, as printed. -/
theorem maximal_inequality
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 mΩ) [ℱ.IsRightContinuous]
    (T : ℝ≥0)
    (f g : ℝ≥0 → Ω → ℝ≥0)
    (hf_cont : ∀ ω, ContinuousOn (fun t => f t ω) (Set.Icc 0 T))
    (hg_cont : ∀ ω, ContinuousOn (fun t => g t ω) (Set.Icc 0 T))
    (hf_adapt : ∀ t ≤ T, Measurable[ℱ t] (f t))
    (hg_adapt : ∀ t ≤ T, Measurable[ℱ t] (g t))
    (hdom : ∀ c : ℝ≥0, 0 < c → ∀ τ : Ω → WithTop ℝ≥0, IsStoppingTime ℱ τ →
      (∀ ω, τ ω ≤ (T : WithTop ℝ≥0)) →
      ∫⁻ ω, {ω | g 0 ω ≤ c}.indicator (fun ω => ((stoppedValue f τ ω : ℝ≥0) : ℝ≥0∞)) ω ∂P
        ≤ ∫⁻ ω, {ω | g 0 ω ≤ c}.indicator (fun ω => ((stoppedValue g τ ω : ℝ≥0) : ℝ≥0∞)) ω ∂P) :
    ∀ τ : Ω → WithTop ℝ≥0, IsStoppingTime ℱ τ → (∀ ω, τ ω ≤ (T : WithTop ℝ≥0)) →
      ∀ γ : ℝ, 0 < γ → γ < 1 →
        ∫⁻ ω, (⨆ (t : ℝ≥0) (_ : (t : WithTop ℝ≥0) ≤ τ ω), (f t ω : ℝ≥0∞) ^ γ) ∂P
          ≤ ENNReal.ofReal ((2 - γ) / (1 - γ)) *
            ∫⁻ ω, (⨆ (t : ℝ≥0) (_ : (t : WithTop ℝ≥0) ≤ τ ω), (g t ω : ℝ≥0∞) ^ γ) ∂P := by
  intro τ hτ hτT γ hγ0 hγ1
  have hreadF : ∀ ω, (⨆ (t : ℝ≥0) (_ : (t : WithTop ℝ≥0) ≤ τ ω), (f t ω : ℝ≥0∞) ^ γ) =
      (((⨆ (t : ℝ≥0) (_ : (t : WithTop ℝ≥0) ≤ τ ω), (f t ω : ℝ≥0∞)).toNNReal : ℝ≥0) :
        ℝ≥0∞) ^ γ := fun ω => by
    rw [ENNReal.coe_toNNReal (Owner.owner_sup_lt_top T f hf_cont τ hτT ω).ne,
      ← AAReadback.iSup_rpow_eq _ hγ0]
    exact iSup_congr fun t =>
      AAReadback.iSup_rpow_eq (fun _ : (t : WithTop ℝ≥0) ≤ τ ω => (f t ω : ℝ≥0∞)) hγ0
  have hreadG : ∀ ω, (⨆ (t : ℝ≥0) (_ : (t : WithTop ℝ≥0) ≤ τ ω), (g t ω : ℝ≥0∞) ^ γ) =
      (((⨆ (t : ℝ≥0) (_ : (t : WithTop ℝ≥0) ≤ τ ω), (g t ω : ℝ≥0∞)).toNNReal : ℝ≥0) :
        ℝ≥0∞) ^ γ := fun ω => by
    rw [ENNReal.coe_toNNReal (Owner.owner_sup_lt_top T g hg_cont τ hτT ω).ne,
      ← AAReadback.iSup_rpow_eq _ hγ0]
    exact iSup_congr fun t =>
      AAReadback.iSup_rpow_eq (fun _ : (t : WithTop ℝ≥0) ≤ τ ω => (g t ω : ℝ≥0∞)) hγ0
  rw [lintegral_congr hreadF, lintegral_congr hreadG]
  exact GSStop.lintegral_rpow_le_of_tail P
    (fun ω => (⨆ (t : ℝ≥0) (_ : (t : WithTop ℝ≥0) ≤ τ ω), (f t ω : ℝ≥0∞)).toNNReal)
    (fun ω => (⨆ (t : ℝ≥0) (_ : (t : WithTop ℝ≥0) ≤ τ ω), (g t ω : ℝ≥0∞)).toNNReal)
    (Owner.owner_measurable_sup ℱ T f hf_cont hf_adapt τ hτ hτT).ennreal_toNNReal
    (Owner.owner_measurable_sup ℱ T g hg_cont hg_adapt τ hτ hτT).ennreal_toNNReal
    γ hγ0 hγ1
    (fun c hc => Owner.owner_tail P ℱ T f g hf_cont hg_cont hf_adapt hg_adapt hdom τ hτ hτT c hc)

end SabanisEuler.UniformRate

end Prove2SwarmSubmission

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 mΩ) [ℱ.IsRightContinuous]
    (T : ℝ≥0)
    (f g : ℝ≥0 → Ω → ℝ≥0)
    (hf_cont : ∀ ω, ContinuousOn (fun t => f t ω) (Set.Icc 0 T))
    (hg_cont : ∀ ω, ContinuousOn (fun t => g t ω) (Set.Icc 0 T))
    (hf_adapt : ∀ t ≤ T, Measurable[ℱ t] (f t))
    (hg_adapt : ∀ t ≤ T, Measurable[ℱ t] (g t))
    (hdom : ∀ c : ℝ≥0, 0 < c → ∀ τ : Ω → WithTop ℝ≥0, IsStoppingTime ℱ τ →
      (∀ ω, τ ω ≤ (T : WithTop ℝ≥0)) →
      ∫⁻ ω, {ω | g 0 ω ≤ c}.indicator (fun ω => ((stoppedValue f τ ω : ℝ≥0) : ℝ≥0∞)) ω ∂P
        ≤ ∫⁻ ω, {ω | g 0 ω ≤ c}.indicator (fun ω => ((stoppedValue g τ ω : ℝ≥0) : ℝ≥0∞)) ω ∂P) :
    ∀ τ : Ω → WithTop ℝ≥0, IsStoppingTime ℱ τ → (∀ ω, τ ω ≤ (T : WithTop ℝ≥0)) →
      ∀ γ : ℝ, 0 < γ → γ < 1 →
        ∫⁻ ω, (⨆ (t : ℝ≥0) (_ : (t : WithTop ℝ≥0) ≤ τ ω), (f t ω : ℝ≥0∞) ^ γ) ∂P
          ≤ ENNReal.ofReal ((2 - γ) / (1 - γ)) *
            ∫⁻ ω, (⨆ (t : ℝ≥0) (_ : (t : WithTop ℝ≥0) ≤ τ ω), (g t ω : ℝ≥0∞) ^ γ) ∂P := by
  exact Prove2SwarmSubmission.SabanisEuler.UniformRate.maximal_inequality P ℱ T f g hf_cont hg_cont hf_adapt hg_adapt hdom
