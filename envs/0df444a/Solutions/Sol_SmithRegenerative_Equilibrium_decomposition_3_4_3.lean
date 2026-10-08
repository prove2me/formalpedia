-- Prove2me | solution 1 for SmithRegenerative.Equilibrium.decomposition_3_4_3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T20:59:46.848088+00:00
-- url     : https://prove2.me/submissions/d5cd162e-4916-47bc-ba5c-808242fc4ebf

import Mathlib
import Definitions.Def_SmithRegenerative_Equilibrium_EquilibriumProcess



namespace SmithRegenerative.Equilibrium

open MeasureTheory ProbabilityTheory Filter Topology QueueingFundamentals.MG1

variable {Ω 𝔛 Z : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝔛]

/-! ### Epochs -/

lemma epoch_succ' (t : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) :
    epoch t (k + 1) ω = epoch t k ω + t (k + 1) ω := by
  simp [epoch, Finset.sum_range_succ]

lemma epoch_zero' (t : ℕ → Ω → ℝ) (ω : Ω) : epoch t 0 ω = t 0 ω := by
  simp [epoch]

lemma epoch_nonneg' (t : ℕ → Ω → ℝ) (hnn : ∀ i ω, 0 ≤ t i ω) (k : ℕ) (ω : Ω) :
    0 ≤ epoch t k ω :=
  Finset.sum_nonneg (fun i _ => hnn i ω)

lemma epoch_mono' (t : ℕ → Ω → ℝ) (hnn : ∀ i ω, 0 ≤ t i ω) (ω : Ω) :
    Monotone (fun k => epoch t k ω) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [epoch_succ']
  linarith [hnn (k + 1) ω]

lemma measurable_epoch' (t : ℕ → Ω → ℝ) (hm : ∀ i, Measurable (t i)) (k : ℕ) :
    Measurable (epoch t k) := by
  unfold epoch
  exact Finset.measurable_sum _ (fun i _ => hm i)

lemma renewalCount_pos_iff' (t : ℕ → Ω → ℝ) (hnn : ∀ i ω, 0 ≤ t i ω) (s : ℝ) (ω : Ω) :
    0 < renewalCount t s ω ↔ t 0 ω ≤ s := by
  unfold renewalCount
  rw [Set.encard_pos]
  constructor
  · rintro ⟨k, hk⟩
    have h0 : epoch t 0 ω ≤ epoch t k ω := epoch_mono' t hnn ω (Nat.zero_le k)
    rw [epoch_zero'] at h0
    exact le_trans h0 hk
  · intro h
    exact ⟨0, by simpa [epoch_zero'] using h⟩

lemma lastEpoch_eq' (t : ℕ → Ω → ℝ) (hnn : ∀ i ω, 0 ≤ t i ω) {s : ℝ} {k : ℕ} {ω : Ω}
    (h1 : epoch t k ω ≤ s) (h2 : s < epoch t (k + 1) ω) :
    lastEpoch t s ω = epoch t k ω := by
  unfold lastEpoch
  have hmono := epoch_mono' t hnn ω
  have hle : ∀ j, (if epoch t j ω ≤ s then epoch t j ω else 0) ≤ epoch t k ω := by
    intro j
    split_ifs with hj
    · by_contra hcon
      push_neg at hcon
      have hjk : k + 1 ≤ j := by
        by_contra hh
        push_neg at hh
        have := hmono (Nat.lt_succ_iff.mp hh)
        simp only at this
        linarith
      have := hmono hjk
      simp only at this
      linarith
    · exact epoch_nonneg' t hnn k ω
  apply le_antisymm
  · exact ciSup_le hle
  · have hb : BddAbove (Set.range fun j => if epoch t j ω ≤ s then epoch t j ω else 0) :=
      ⟨epoch t k ω, by rintro _ ⟨j, rfl⟩; exact hle j⟩
    have := le_ciSup hb k
    simp only [if_pos h1] at this
    exact this

/-! ### Laws of the epochs -/

lemma indep_epoch_next (E : EquilibriumProcess Ω 𝔛 Z) (z : Z) (k : ℕ) :
    IndepFun (epoch E.t k) (E.t (k + 1)) (E.P z) := by
  have h := (E.indep z).indepFun_finsetSum_of_notMem E.measurable_t
    (s := Finset.range (k + 1)) (i := k + 1) (by simp)
  have : (∑ j ∈ Finset.range (k + 1), E.t j) = epoch E.t k := by
    funext ω; simp [epoch, Finset.sum_apply]
  rwa [this] at h

lemma map_epoch_succ (E : EquilibriumProcess Ω 𝔛 Z) (z : Z) (k : ℕ) :
    (E.P z).map (epoch E.t (k + 1)) = ((E.P z).map (epoch E.t k)).conv E.F := by
  haveI := E.isProb z
  have hind := indep_epoch_next E z k
  have hm1 := measurable_epoch' E.t E.measurable_t k
  have hm2 := E.measurable_t (k + 1)
  have hprod := (indepFun_iff_map_prod_eq_prod_map_map hm1.aemeasurable hm2.aemeasurable).mp hind
  rw [E.law_cycle z (k + 1) (by omega)] at hprod
  have : epoch E.t (k + 1) =
      (fun p : ℝ × ℝ => p.1 + p.2) ∘ (fun ω => (epoch E.t k ω, E.t (k + 1) ω)) := by
    funext ω; simp [epoch_succ']
  rw [this, ← Measure.map_map (by fun_prop) (hm1.prodMk hm2), hprod]
  rfl

instance convPow_isProb (F : Measure ℝ) [IsProbabilityMeasure F] (k : ℕ) :
    IsProbabilityMeasure (convPow F k) := by
  induction k with
  | zero => simp only [convPow]; infer_instance
  | succ k ih => simp only [convPow]; infer_instance

lemma K_isProb (E : EquilibriumProcess Ω 𝔛 Z) (z : Z) : IsProbabilityMeasure (E.K z) := by
  haveI := E.isProb z
  rw [← E.law_delay z]
  exact Measure.isProbabilityMeasure_map (E.measurable_t 0).aemeasurable

lemma map_epoch_eq (E : EquilibriumProcess Ω 𝔛 Z) (z : Z) (k : ℕ) :
    (E.P z).map (epoch E.t k) = (E.K z).conv (convPow E.F k) := by
  haveI := E.isProb z
  haveI : IsProbabilityMeasure E.F := E.cycleLaw.1
  haveI := K_isProb E z
  induction k with
  | zero =>
    have : epoch E.t 0 = E.t 0 := funext (epoch_zero' E.t)
    rw [this, E.law_delay z]
    simp [convPow, Measure.conv_dirac_zero]
  | succ k ih =>
    rw [map_epoch_succ, ih]
    simp only [convPow]
    exact Measure.conv_assoc (E.K z) (convPow E.F k) E.F

/-! ### The null event of infinitely many regenerations in `[0, s]` -/

lemma rho_lt_one (F : Measure ℝ) (hF : IsCycleLaw F) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (-x)) ∂F < 1 := by
  obtain ⟨hprob, h0, hne⟩ := hF
  haveI := hprob
  have hae : ∀ᵐ x ∂F, 0 ≤ x := by
    rw [ae_iff]
    simpa [Set.Iio] using h0
  have hpos : F (Set.Ioi 0) ≠ 0 := by
    intro hz
    apply hne
    have hcompl : F ({0}ᶜ) = 0 := by
      have : ({0}ᶜ : Set ℝ) = Set.Iio 0 ∪ Set.Ioi 0 := by
        ext x
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_union, Set.mem_Iio,
          Set.mem_Ioi]
        exact ⟨lt_or_gt_of_ne, fun h => h.elim ne_of_lt ne_of_gt⟩
      rw [this]
      exact measure_union_null h0 hz
    have h1 : F {0} = 1 := by
      have hc := measure_compl (MeasurableSet.singleton (0:ℝ)) (measure_ne_top F _)
      rw [hcompl, measure_univ] at hc
      have hle : F {0} ≤ 1 := prob_le_one
      have := (tsub_eq_zero_iff_le).mp hc.symm
      exact le_antisymm hle this
    ext s hs
    rw [Measure.dirac_apply' _ hs]
    by_cases h0s : (0:ℝ) ∈ s
    · simp only [Set.indicator_of_mem h0s, Pi.one_apply]
      exact le_antisymm prob_le_one (h1 ▸ measure_mono (Set.singleton_subset_iff.mpr h0s))
    · simp only [Set.indicator_of_notMem h0s]
      exact measure_mono_null (Set.subset_compl_singleton_iff.mpr h0s) hcompl
  have hle : (fun x => ENNReal.ofReal (Real.exp (-x))) ≤ᵐ[F] fun _ => (1 : ENNReal) := by
    filter_upwards [hae] with x hx
    rw [ENNReal.ofReal_le_one]
    exact Real.exp_le_one_iff.mpr (by linarith)
  calc ∫⁻ x, ENNReal.ofReal (Real.exp (-x)) ∂F
      < ∫⁻ _, (1 : ENNReal) ∂F := by
        apply lintegral_strict_mono_of_ae_le_of_ae_lt_on measurable_const.aemeasurable
        · exact ne_of_lt (lt_of_le_of_lt (lintegral_mono_ae hle) (by simp))
        · exact hle
        · exact hpos
        · filter_upwards with x hx
          rw [ENNReal.ofReal_lt_one]
          exact Real.exp_lt_one_iff.mpr (by simpa using hx)
    _ = 1 := by simp

lemma lintegral_exp_epoch (E : EquilibriumProcess Ω 𝔛 Z) (z : Z) (k : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (-(epoch E.t k ω))) ∂(E.P z)
      = (∫⁻ ω, ENNReal.ofReal (Real.exp (-(E.t 0 ω))) ∂(E.P z)) *
        (∫⁻ x, ENNReal.ofReal (Real.exp (-x)) ∂E.F) ^ k := by
  haveI := E.isProb z
  induction k with
  | zero => simp [epoch_zero']
  | succ k ih =>
    have hm1 := measurable_epoch' E.t E.measurable_t k
    have hm2 := E.measurable_t (k + 1)
    have hφ : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (-x))) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp measurable_neg)
    have hfun : (fun ω => ENNReal.ofReal (Real.exp (-(epoch E.t (k + 1) ω)))) =
        ((fun x : ℝ => ENNReal.ofReal (Real.exp (-x))) ∘ epoch E.t k) *
          ((fun x : ℝ => ENNReal.ofReal (Real.exp (-x))) ∘ E.t (k + 1)) := by
      funext ω
      simp only [Pi.mul_apply, Function.comp_apply, epoch_succ']
      rw [← ENNReal.ofReal_mul (by positivity), ← Real.exp_add]
      ring_nf
    have hF : ∫⁻ ω, ENNReal.ofReal (Real.exp (-(E.t (k + 1) ω))) ∂(E.P z)
        = ∫⁻ x, ENNReal.ofReal (Real.exp (-x)) ∂E.F := by
      rw [← E.law_cycle z (k + 1) (by omega), lintegral_map hφ hm2]
    rw [hfun, lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun (hφ.comp hm1) (hφ.comp hm2)
      ((indep_epoch_next E z k).comp hφ hφ)]
    simp only [Function.comp_apply]
    rw [ih, hF]
    ring

lemma measure_epoch_le_bound (E : EquilibriumProcess Ω 𝔛 Z) (z : Z) (s : ℝ) (k : ℕ) :
    E.P z {ω | epoch E.t k ω ≤ s} ≤
      ENNReal.ofReal (Real.exp s) * ((∫⁻ ω, ENNReal.ofReal (Real.exp (-(E.t 0 ω))) ∂(E.P z)) *
        (∫⁻ x, ENNReal.ofReal (Real.exp (-x)) ∂E.F) ^ k) := by
  have hm := measurable_epoch' E.t E.measurable_t k
  have hs : MeasurableSet {ω | epoch E.t k ω ≤ s} := measurableSet_le hm measurable_const
  have hφ : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (-x))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp measurable_neg)
  rw [← lintegral_exp_epoch, ← lintegral_indicator_one hs]
  calc ∫⁻ a, {ω | epoch E.t k ω ≤ s}.indicator 1 a ∂(E.P z)
      ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp s) * ENNReal.ofReal (Real.exp (-(epoch E.t k ω))) ∂(E.P z) := ?_
    _ = _ := lintegral_const_mul _ (hφ.comp hm)
  apply lintegral_mono
  intro ω
  by_cases hω : epoch E.t k ω ≤ s
  · simp only [Set.indicator_of_mem (show ω ∈ {ω | epoch E.t k ω ≤ s} from hω), Pi.one_apply]
    rw [← ENNReal.ofReal_mul (by positivity), ← Real.exp_add]
    rw [ENNReal.one_le_ofReal]
    exact Real.one_le_exp (by linarith)
  · simp [Set.indicator_of_notMem (show ω ∉ {ω | epoch E.t k ω ≤ s} from hω)]

lemma measure_all_epoch_le (E : EquilibriumProcess Ω 𝔛 Z) (z : Z) (s : ℝ) :
    E.P z {ω | ∀ k, epoch E.t k ω ≤ s} = 0 := by
  haveI := E.isProb z
  set ρ := ∫⁻ x, ENNReal.ofReal (Real.exp (-x)) ∂E.F with hρdef
  have hρ : ρ < 1 := rho_lt_one E.F E.cycleLaw
  set c := ∫⁻ ω, ENNReal.ofReal (Real.exp (-(E.t 0 ω))) ∂(E.P z) with hcdef
  have hc : c ≤ 1 := by
    calc c ≤ ∫⁻ _, (1 : ENNReal) ∂(E.P z) := by
          apply lintegral_mono
          intro ω
          rw [ENNReal.ofReal_le_one]
          exact Real.exp_le_one_iff.mpr (by linarith [E.t_nonneg 0 ω])
      _ = 1 := by simp
  have hbound : ∀ k, E.P z {ω | ∀ k, epoch E.t k ω ≤ s} ≤
      (ENNReal.ofReal (Real.exp s) * c) * ρ ^ k := by
    intro k
    calc E.P z {ω | ∀ k, epoch E.t k ω ≤ s} ≤ E.P z {ω | epoch E.t k ω ≤ s} :=
          measure_mono (fun ω hω => hω k)
      _ ≤ _ := measure_epoch_le_bound E z s k
      _ = _ := by ring
  have hlim : Tendsto (fun k => (ENNReal.ofReal (Real.exp s) * c) * ρ ^ k) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => ρ ^ k) atTop (𝓝 0) :=
      ENNReal.tendsto_pow_atTop_nhds_zero_iff.mpr hρ
    have h2 := ENNReal.Tendsto.const_mul h1 (a := ENNReal.ofReal (Real.exp s) * c)
      (Or.inr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top hc)))
    simpa using h2
  exact le_antisymm (ge_of_tendsto' hlim hbound) zero_le

/-! ### The window events `T_k ≤ s < T_{k+1}` -/

def S (E : EquilibriumProcess Ω 𝔛 Z) (s : ℝ) (k : ℕ) : Set Ω :=
  {ω | epoch E.t k ω ≤ s ∧ s < epoch E.t (k + 1) ω}

lemma measurableSet_S (E : EquilibriumProcess Ω 𝔛 Z) (s : ℝ) (k : ℕ) :
    MeasurableSet (S E s k) :=
  (measurableSet_le (measurable_epoch' E.t E.measurable_t k) measurable_const).inter
    (measurableSet_lt measurable_const (measurable_epoch' E.t E.measurable_t (k + 1)))

lemma S_disjoint (E : EquilibriumProcess Ω 𝔛 Z) (s : ℝ) : Pairwise (fun i j => Disjoint (S E s i) (S E s j)) := by
  have key : ∀ i j : ℕ, i < j → Disjoint (S E s i) (S E s j) := by
    intro i j h
    rw [Set.disjoint_left]
    rintro ω ⟨hi1, hi2⟩ ⟨hj1, hj2⟩
    have : epoch E.t (i + 1) ω ≤ epoch E.t j ω :=
      epoch_mono' E.t E.t_nonneg ω (show i + 1 ≤ j from h)
    linarith
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h
  · exact (key j i h).symm

lemma S_subset_U (E : EquilibriumProcess Ω 𝔛 Z) (s : ℝ) (k : ℕ) :
    S E s k ⊆ {ω | 0 < renewalCount E.t s ω} := by
  intro ω hω
  rw [Set.mem_setOf_eq, renewalCount_pos_iff' E.t E.t_nonneg]
  have h0 : epoch E.t 0 ω ≤ epoch E.t k ω := epoch_mono' E.t E.t_nonneg ω (Nat.zero_le k)
  rw [epoch_zero'] at h0
  exact le_trans h0 hω.1

lemma U_subset (E : EquilibriumProcess Ω 𝔛 Z) (s : ℝ) :
    {ω | 0 < renewalCount E.t s ω} ⊆ (⋃ k, S E s k) ∪ {ω | ∀ k, epoch E.t k ω ≤ s} := by
  intro ω hω
  rw [Set.mem_setOf_eq, renewalCount_pos_iff' E.t E.t_nonneg] at hω
  by_cases hall : ∀ k, epoch E.t k ω ≤ s
  · exact Or.inr hall
  · left
    push_neg at hall
    classical
    have hm0 : s < epoch E.t (Nat.find hall) ω := Nat.find_spec hall
    have hm0pos : Nat.find hall ≠ 0 := by
      intro h; rw [h, epoch_zero'] at hm0; linarith
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hm0pos
    refine Set.mem_iUnion.mpr ⟨k, ?_⟩
    show epoch E.t k ω ≤ s ∧ s < epoch E.t (k + 1) ω
    refine ⟨?_, ?_⟩
    · have := Nat.find_min hall (show k < Nat.find hall by omega)
      push_neg at this; exact this
    · rw [hk] at hm0; exact hm0

lemma restrict_Iic_eq_Icc (E : EquilibriumProcess Ω 𝔛 Z) (z : Z) (s : ℝ) (k : ℕ) :
    ((E.P z).map (epoch E.t k)).restrict (Set.Iic s) =
      ((E.P z).map (epoch E.t k)).restrict (Set.Icc 0 s) := by
  apply Measure.restrict_congr_set
  rw [ae_eq_set]
  constructor
  · apply measure_mono_null (t := Set.Iio 0)
    · intro x hx
      simp only [Set.mem_diff, Set.mem_Iic, Set.mem_Icc, not_and] at hx
      simp only [Set.mem_Iio]
      by_contra h
      push_neg at h
      exact hx.2 h hx.1
    · rw [Measure.map_apply (measurable_epoch' E.t E.measurable_t k) measurableSet_Iio]
      have : (epoch E.t k) ⁻¹' Set.Iio 0 = ∅ := by
        ext ω; simp [not_lt.mpr (epoch_nonneg' E.t E.t_nonneg k ω)]
      rw [this, measure_empty]
  · have : Set.Icc 0 s \ Set.Iic s = ∅ := by
      ext x; simp only [Set.mem_diff, Set.mem_Icc, Set.mem_Iic, Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨_, h1⟩, h2⟩; exact h2 h1
    rw [this, measure_empty]

/-! ### The window integral (Fubini) -/

lemma integral_window (E : EquilibriumProcess Ω 𝔛 Z) (z : Z) (s : ℝ) (k : ℕ) (ψ : ℝ → ℝ)
    (hψ : Measurable ψ)
    (hint : IntegrableOn (fun ω => ψ (s - epoch E.t k ω)) (S E s k) (E.P z)) :
    IntegrableOn (fun τ => ψ (s - τ) * (E.F (Set.Ioi (s - τ))).toReal) (Set.Iic s)
        ((E.P z).map (epoch E.t k)) ∧
    ∫ ω in S E s k, ψ (s - epoch E.t k ω) ∂(E.P z)
      = ∫ τ in Set.Iic s, ψ (s - τ) * (E.F (Set.Ioi (s - τ))).toReal
          ∂((E.P z).map (epoch E.t k)) := by
  haveI := E.isProb z
  haveI : IsProbabilityMeasure E.F := E.cycleLaw.1
  have hm1 := measurable_epoch' E.t E.measurable_t k
  have hm2 := E.measurable_t (k + 1)
  set μ := (E.P z).map (epoch E.t k) with hμ
  have hprod : (E.P z).map (fun ω => (epoch E.t k ω, E.t (k + 1) ω)) = μ.prod E.F := by
    have := (indepFun_iff_map_prod_eq_prod_map_map hm1.aemeasurable hm2.aemeasurable).mp
      (indep_epoch_next E z k)
    rw [E.law_cycle z (k + 1) (by omega)] at this
    exact this
  let h : ℝ × ℝ → ℝ := fun p => if p.1 ≤ s ∧ s < p.1 + p.2 then ψ (s - p.1) else 0
  have hhm : Measurable h := by
    apply Measurable.ite
    · exact (measurableSet_le measurable_fst measurable_const).inter
        (measurableSet_lt measurable_const (measurable_fst.add measurable_snd))
    · exact hψ.comp (measurable_const.sub measurable_fst)
    · exact measurable_const
  have hpt : ∀ ω, (S E s k).indicator (fun ω => ψ (s - epoch E.t k ω)) ω
      = h (epoch E.t k ω, E.t (k + 1) ω) := by
    intro ω
    simp only [Set.indicator_apply, S, Set.mem_setOf_eq, h, epoch_succ']
  have hX : Measurable (fun ω => (epoch E.t k ω, E.t (k + 1) ω)) := hm1.prodMk hm2
  have hint' : Integrable h (μ.prod E.F) := by
    rw [← hprod, integrable_map_measure hhm.aestronglyMeasurable hX.aemeasurable]
    have : h ∘ (fun ω => (epoch E.t k ω, E.t (k + 1) ω))
        = (S E s k).indicator (fun ω => ψ (s - epoch E.t k ω)) := by
      funext ω; simp only [Function.comp_apply, hpt]
    rw [this]
    exact (integrable_indicator_iff (measurableSet_S E s k)).mpr hint
  have hinner : ∀ τ, ∫ y, h (τ, y) ∂E.F
      = (Set.Iic s).indicator (fun τ => ψ (s - τ) * (E.F (Set.Ioi (s - τ))).toReal) τ := by
    intro τ
    by_cases hτ : τ ≤ s
    · have : (fun y => h (τ, y)) = (Set.Ioi (s - τ)).indicator (fun _ => ψ (s - τ)) := by
        funext y
        simp only [h, Set.indicator_apply, Set.mem_Ioi, hτ, true_and, sub_lt_iff_lt_add']
      rw [this, integral_indicator_const _ measurableSet_Ioi,
        Set.indicator_of_mem (Set.mem_Iic.mpr hτ)]
      simp only [Measure.real, smul_eq_mul, mul_comm]
    · have h1 : (fun y => h (τ, y)) = fun _ => (0 : ℝ) := by
        funext y; simp only [h, hτ, false_and, if_false]
      rw [h1, Set.indicator_of_notMem (show τ ∉ Set.Iic s from hτ)]
      simp
  constructor
  · have := hint'.integral_prod_left
    simp_rw [hinner] at this
    exact (integrable_indicator_iff measurableSet_Iic).mp this
  · calc ∫ ω in S E s k, ψ (s - epoch E.t k ω) ∂(E.P z)
        = ∫ ω, (S E s k).indicator (fun ω => ψ (s - epoch E.t k ω)) ω ∂(E.P z) :=
          (integral_indicator (measurableSet_S E s k)).symm
      _ = ∫ ω, h (epoch E.t k ω, E.t (k + 1) ω) ∂(E.P z) := by simp_rw [hpt]
      _ = ∫ p, h p ∂((E.P z).map (fun ω => (epoch E.t k ω, E.t (k + 1) ω))) :=
          (integral_map hX.aemeasurable hhm.aestronglyMeasurable).symm
      _ = ∫ p, h p ∂(μ.prod E.F) := by rw [hprod]
      _ = ∫ τ, ∫ y, h (τ, y) ∂E.F ∂μ := integral_prod h hint'
      _ = ∫ τ, (Set.Iic s).indicator
            (fun τ => ψ (s - τ) * (E.F (Set.Ioi (s - τ))).toReal) τ ∂μ := by simp_rw [hinner]
      _ = _ := integral_indicator measurableSet_Iic

/-! ### The decomposition -/

theorem decomposition_core (E : EquilibriumProcess Ω 𝔛 Z) (z : Z) (A : Set 𝔛) (hA : A ∈ E.𝒜)
    (t : ℝ) (ht : 0 ≤ t) :
    (E.P z {ω | E.x t ω ∈ A}).toReal =
      (E.P z {ω | E.x t ω ∈ A ∧ t < E.t 0 ω}).toReal +
        ∫ τ in Set.Icc 0 t, E.φ A (t - τ) * (E.F (Set.Ioi (t - τ))).toReal
          ∂(renewalMeasure (E.K z) E.F) := by
  haveI := E.isProb z
  set f : Ω → ℝ := fun ω => E.φ A (t - lastEpoch E.t t ω) with hf
  set U := {ω | 0 < renewalCount E.t t ω} with hU
  set g : ℝ → ℝ := fun τ => E.φ A (t - τ) * (E.F (Set.Ioi (t - τ))).toReal with hg
  have hφm := E.measurable_φ A hA
  -- Step A: split according to whether `t₀ ≤ t`
  have hxA : MeasurableSet {ω | E.x t ω ∈ A} := E.measurable_x t (E.measurableSet_of_mem A hA)
  have hU_eq : U = {ω | E.t 0 ω ≤ t} := by
    ext ω; simp only [hU, Set.mem_setOf_eq, renewalCount_pos_iff' E.t E.t_nonneg]
  have hU_meas : MeasurableSet U := by
    rw [hU_eq]; exact measurableSet_le (E.measurable_t 0) measurable_const
  have hdisj : Disjoint {ω | E.x t ω ∈ A ∧ t < E.t 0 ω} ({ω | E.x t ω ∈ A} ∩ U) := by
    rw [Set.disjoint_left]
    rintro ω ⟨_, h1⟩ ⟨_, h2⟩
    rw [hU_eq] at h2
    simp only [Set.mem_setOf_eq] at h2
    linarith
  have hsplit : E.P z {ω | E.x t ω ∈ A} =
      E.P z {ω | E.x t ω ∈ A ∧ t < E.t 0 ω} + E.P z ({ω | E.x t ω ∈ A} ∩ U) := by
    rw [← measure_union hdisj (hxA.inter hU_meas)]
    congr 1
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff, hU_eq]
    constructor
    · intro h
      by_cases h' : t < E.t 0 ω
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr ⟨h, not_lt.mp h'⟩
    · rintro (h | h) <;> exact h.1
  -- Step B: the representation (3·4·1) with `B = univ`
  have hrepr := E.repr z A hA t ht Set.univ MeasurableSet.univ
  have hset1 : {ω | E.x t ω ∈ A ∧ 0 < renewalCount E.t t ω ∧ lastEpoch E.t t ω ∈ Set.univ}
      = {ω | E.x t ω ∈ A} ∩ U := by ext ω; simp [hU]
  have hset2 : {ω | 0 < renewalCount E.t t ω ∧ lastEpoch E.t t ω ∈ Set.univ} = U := by
    ext ω; simp [hU]
  rw [hset1, hset2] at hrepr
  -- Step C: decompose `{n_t > 0}` into the windows
  have hfU : IntegrableOn f U (E.P z) := E.integrable_repr z A hA t ht
  have hSm := measurableSet_S E t
  have hSd := S_disjoint E t
  have hUae : U =ᵐ[E.P z] ⋃ k, S E t k := by
    rw [ae_eq_set]
    constructor
    · apply measure_mono_null _ (measure_all_epoch_le E z t)
      rintro ω ⟨h1, h2⟩
      rcases U_subset E t h1 with h | h
      · exact absurd h h2
      · exact h
    · have : (⋃ k, S E t k) \ U = ∅ := by
        rw [Set.diff_eq_empty]; exact Set.iUnion_subset (S_subset_U E t)
      rw [this, measure_empty]
  have hfUnion : IntegrableOn f (⋃ k, S E t k) (E.P z) :=
    hfU.mono_set (Set.iUnion_subset (S_subset_U E t))
  have hfS : ∀ k, IntegrableOn (fun ω => E.φ A (t - epoch E.t k ω)) (S E t k) (E.P z) := by
    intro k
    refine (hfU.mono_set (S_subset_U E t k)).congr_fun ?_ (hSm k)
    intro ω hω
    simp only [hf]
    rw [lastEpoch_eq' E.t E.t_nonneg hω.1 hω.2]
  have hfS' : ∀ k, IntegrableOn (fun ω => ‖E.φ A (t - epoch E.t k ω)‖) (S E t k) (E.P z) :=
    fun k => (hfS k).norm
  have hW := fun k => integral_window E z t k (E.φ A) hφm (hfS k)
  have hW' : ∀ k,
      IntegrableOn (fun τ => ‖E.φ A (t - τ)‖ * (E.F (Set.Ioi (t - τ))).toReal) (Set.Iic t)
        ((E.P z).map (epoch E.t k)) ∧
      ∫ ω in S E t k, ‖E.φ A (t - epoch E.t k ω)‖ ∂(E.P z)
        = ∫ τ in Set.Iic t, ‖E.φ A (t - τ)‖ * (E.F (Set.Ioi (t - τ))).toReal
            ∂((E.P z).map (epoch E.t k)) :=
    fun k => integral_window E z t k (fun v => ‖E.φ A v‖) hφm.norm (hfS' k)
  -- the laws of the epochs build the renewal measure
  have hlaw : renewalMeasure (E.K z) E.F = Measure.sum (fun k => (E.P z).map (epoch E.t k)) := by
    unfold renewalMeasure
    congr 1
    funext k
    exact (map_epoch_eq E z k).symm
  have hgk : ∀ k, Integrable g (((E.P z).map (epoch E.t k)).restrict (Set.Icc 0 t)) := by
    intro k
    rw [← restrict_Iic_eq_Icc E z t k]
    exact (hW k).1
  have hnorm : ∀ τ, ‖g τ‖ = ‖E.φ A (t - τ)‖ * (E.F (Set.Ioi (t - τ))).toReal := by
    intro τ
    simp only [hg, norm_mul, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  have hsum : HasSum (fun k => ∫ ω in S E t k, ‖f ω‖ ∂(E.P z))
      (∫ ω in ⋃ k, S E t k, ‖f ω‖ ∂(E.P z)) :=
    hasSum_integral_iUnion hSm hSd hfUnion.norm
  have hsummable : Summable
      (fun k => ∫ τ, ‖g τ‖ ∂(((E.P z).map (epoch E.t k)).restrict (Set.Icc 0 t))) := by
    refine hsum.summable.congr fun k => ?_
    rw [← restrict_Iic_eq_Icc E z t k]
    simp_rw [hnorm]
    rw [← (hW' k).2]
    apply setIntegral_congr_fun (hSm k)
    intro ω hω
    simp only [hf]
    rw [lastEpoch_eq' E.t E.t_nonneg hω.1 hω.2]
  have hgint : Integrable g
      (Measure.sum fun k => ((E.P z).map (epoch E.t k)).restrict (Set.Icc 0 t)) :=
    integrable_sum_measure hgk hsummable
  -- assemble
  rw [hsplit, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), hrepr]
  congr 1
  calc ∫ ω in U, f ω ∂(E.P z) = ∫ ω in ⋃ k, S E t k, f ω ∂(E.P z) := setIntegral_congr_set hUae
    _ = ∑' k, ∫ ω in S E t k, f ω ∂(E.P z) := integral_iUnion hSm hSd hfUnion
    _ = ∑' k, ∫ τ in Set.Icc 0 t, g τ ∂((E.P z).map (epoch E.t k)) := by
        congr 1
        funext k
        rw [← restrict_Iic_eq_Icc E z t k, ← (hW k).2]
        apply setIntegral_congr_fun (hSm k)
        intro ω hω
        simp only [hf]
        rw [lastEpoch_eq' E.t E.t_nonneg hω.1 hω.2]
    _ = ∫ τ in Set.Icc 0 t, g τ ∂(renewalMeasure (E.K z) E.F) := by
        rw [hlaw, Measure.restrict_sum_of_countable, integral_sum_measure hgint]

end SmithRegenerative.Equilibrium

open SmithRegenerative.Equilibrium


theorem solution {Ω 𝔛 Z : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝔛]
    (E : EquilibriumProcess Ω 𝔛 Z) (z : Z) (A : Set 𝔛) (hA : A ∈ E.𝒜) (t : ℝ) (ht : 0 ≤ t) :
    (E.P z {ω | E.x t ω ∈ A}).toReal =
      (E.P z {ω | E.x t ω ∈ A ∧ t < E.t 0 ω}).toReal +
        ∫ τ in Set.Icc 0 t, E.φ A (t - τ) * (E.F (Set.Ioi (t - τ))).toReal
          ∂(renewalMeasure (E.K z) E.F) := by
  exact decomposition_core E z A hA t ht
