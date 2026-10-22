-- Prove2me | solution 1 for TwoStageSRO.AsymOpt.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T00:52:40.583223+00:00
-- url     : https://prove2.me/submissions/e7fd9e48-4ee8-4aca-afd8-b591dd38134a

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_TwoStageSRO_AsymOpt_Model
import Definitions.Def_TwoStageSRO_AsymOpt_SampleProblems
import Definitions.Def_TwoStageSRO_AsymOpt_Geometry
import Theorems.Thm_TwoStageSRO_AsymOpt_saa_value_consistency
import Theorems.Thm_TwoStageSRO_AsymOpt_saa_argmin_consistency
import Theorems.Thm_TwoStageSRO_AsymOpt_theorem_1
import Theorems.Thm_TwoStageSRO_AsymOpt_lemma_1
import Theorems.Thm_TwoStageSRO_AsymOpt_lemma_2
import Theorems.Thm_TwoStageSRO_AsymOpt_lemma_3

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal

namespace SROThm2Aux
open TwoStageSRO.AsymOpt
open scoped Pointwise

variable {n d r m mt : ℕ}

theorem coe_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (((∑ i ∈ s, f i : ℝ)) : EReal) = ∑ i ∈ s, ((f i : ℝ) : EReal) :=
  map_sum (⟨⟨((↑) : ℝ → EReal), rfl⟩, EReal.coe_add⟩ : ℝ →+ EReal) f s

theorem measurableSet_of_isSigmaCompact {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [T2Space X] {s : Set X} (hs : IsSigmaCompact s) :
    MeasurableSet s := by
  obtain ⟨K, hK, rfl⟩ := hs
  exact MeasurableSet.iUnion fun n => (hK n).isClosed.measurableSet

/-- The second-stage cost `ζ ↦ Q(x, ζ)` is Borel measurable: its strict sublevel sets are
projections of σ-compact sets. -/
theorem measurable_Q (M : Model n d r m mt) (x : Fin n → ℝ) : Measurable (fun ζ => Q M x ζ) := by
  refine measurable_of_Iio fun t => ?_
  let F : Set ((Fin d → ℝ) × (Fin r → ℝ)) := {z | M.h z.1 ≤ M.T *ᵥ x + M.W *ᵥ z.2}
  have hF : IsClosed F := by
    refine isClosed_le ?_ ?_
    · unfold Model.h
      exact continuous_const.add (continuous_const.matrix_mulVec continuous_fst)
    · exact continuous_const.add (continuous_const.matrix_mulVec continuous_snd)
  let K : ℚ → Set ((Fin d → ℝ) × (Fin r → ℝ)) := fun k => F ∩ {z | M.q ⬝ᵥ z.2 ≤ (k : ℝ)}
  have hK : ∀ k, IsClosed (K k) := fun k =>
    hF.inter (isClosed_le (continuous_const.dotProduct continuous_snd) continuous_const)
  have hset : (fun ζ => Q M x ζ) ⁻¹' Set.Iio t =
      ⋃ (k : ℚ) (_ : (((k : ℝ)) : EReal) < t), Prod.fst '' K k := by
    ext ζ
    simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_iUnion, Set.mem_image, exists_prop]
    constructor
    · intro hQ
      unfold Q at hQ
      rw [sInf_lt_iff] at hQ
      obtain ⟨_, ⟨y, hy, rfl⟩, hlt⟩ := hQ
      obtain ⟨k, hk1, hk2⟩ := EReal.lt_iff_exists_rat_btwn.1 hlt
      refine ⟨k, hk2, (ζ, y), ⟨hy, ?_⟩, rfl⟩
      exact_mod_cast hk1.le
    · rintro ⟨k, hk, ⟨ζ', y⟩, ⟨hy, hyk⟩, rfl⟩
      unfold Q
      refine lt_of_le_of_lt (sInf_le ⟨y, hy, rfl⟩) (lt_of_le_of_lt ?_ hk)
      exact_mod_cast hyk
  rw [hset]
  refine MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ => ?_
  refine measurableSet_of_isSigmaCompact ?_
  exact ((isSigmaCompact_univ.of_isClosed_subset (hK k) (Set.subset_univ _))).image
    continuous_fst

/-- Positive homogeneity of the dual norm. -/
theorem dualNorm_smul (p : ℝ≥0∞) [Fact (1 ≤ p)] {k : ℕ} (a : ℝ) (ha : 0 ≤ a) (v : Fin k → ℝ) :
    dualNorm p (a • v) = a * dualNorm p v := by
  unfold dualNorm
  have : (fun u => u ⬝ᵥ (a • v)) '' {u : Fin k → ℝ | ‖WithLp.toLp p u‖ ≤ 1} =
      a • ((fun u => u ⬝ᵥ v) '' {u : Fin k → ℝ | ‖WithLp.toLp p u‖ ≤ 1}) := by
    rw [← Set.image_smul, Set.image_image]
    congr 1
    ext u
    simp [dotProduct_smul, smul_eq_mul]
  rw [this, Real.sSup_smul_of_nonneg ha, smul_eq_mul]

/-- An extreme point of `D` is determined by (any superset of) its support. -/
theorem eq_of_support (M : Model n d r m mt) {δ δ' : Fin m → ℝ}
    (hδ : δ ∈ Set.extremePoints ℝ (Ddual M)) (hδ' : δ' ∈ Ddual M)
    (hs : ∀ j, δ j = 0 → δ' j = 0) : δ' = δ := by
  obtain ⟨hD, hext⟩ := mem_extremePoints.1 hδ
  set w := δ' - δ with hw
  have hev : ∀ j, ∀ᶠ t in 𝓝[>] (0:ℝ), t * |w j| ≤ δ j := by
    intro j
    by_cases h0 : δ j = 0
    · have : w j = 0 := by simp [hw, hs j h0, h0]
      exact Filter.Eventually.of_forall fun t => by simp [this, h0]
    · have hpos : 0 < δ j := lt_of_le_of_ne (hD.2 j) (Ne.symm h0)
      have ht : Tendsto (fun t : ℝ => t * |w j|) (𝓝[>] 0) (𝓝 0) := by
        have h := (tendsto_id (x := 𝓝 (0:ℝ))).mul_const (|w j|)
        simp only [id, zero_mul] at h
        exact h.mono_left nhdsWithin_le_nhds
      exact (ht.eventually (gt_mem_nhds hpos)).mono fun t ht => ht.le
  obtain ⟨t, ht, htpos⟩ := ((Filter.eventually_all.2 hev).and self_mem_nhdsWithin).exists
  have htpos' : (0:ℝ) < t := htpos
  have mem : ∀ σ : ℝ, |σ| ≤ t → δ + σ • w ∈ Ddual M := by
    intro σ hσ
    refine ⟨?_, ?_⟩
    · rw [Matrix.mulVec_add, Matrix.mulVec_smul, hw, Matrix.mulVec_sub, hδ'.1, hD.1]
      simp
    · intro j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      have h1 := ht j
      have h2 : |σ * w j| ≤ t * |w j| := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_right hσ (abs_nonneg _)
      have h3 := neg_abs_le (σ * w j)
      linarith
  have hseg : δ ∈ openSegment ℝ (δ + t • w) (δ + (-t) • w) := by
    refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have := (hext _ (mem t (by rw [abs_of_pos htpos'])) _
    (mem (-t) (by rw [abs_neg, abs_of_pos htpos'])) hseg).1
  have hw0 : t • w = 0 := by
    have := congrArg (fun z => z - δ) this
    simpa using this
  have : w = 0 := by
    rcases smul_eq_zero.1 hw0 with h | h
    · exact absurd h htpos'.ne'
    · exact h
  rw [hw] at this
  exact sub_eq_zero.1 this

/-- `ext(D)` is finite (an extreme point of a standard-form polyhedron is determined by its
support). -/
theorem extremePoints_Ddual_finite (M : Model n d r m mt) :
    (Set.extremePoints ℝ (Ddual M)).Finite := by
  classical
  let supp : (Fin m → ℝ) → Finset (Fin m) := fun δ => Finset.univ.filter (fun j => δ j ≠ 0)
  refine Set.Finite.of_finite_image (f := supp) (Set.toFinite _) ?_
  intro δ hδ δ' hδ' hsupp
  have h := eq_of_support M hδ hδ'.1 (fun j hj => by
    by_contra hne
    have : j ∈ supp δ' := by simp [supp, hne]
    rw [← hsupp] at this
    simp [supp, hj] at this)
  exact h.symm

/-- For a finite set `C` of recourse matrices, `η^C < ∞`. -/
theorem etaC_lt_top (M : Model n d r m mt) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (C : Set (Matrix (Fin r) (Fin d) ℝ)) (hC : C.Finite) : etaC M p C < ⊤ := by
  let g : Matrix (Fin r) (Fin d) ℝ × (Fin m → ℝ) → ℝ := fun z =>
    dualNorm p (z.1ᵀ *ᵥ M.q) + ∑ j, z.2 j * dualNorm p (M.H j - z.1ᵀ *ᵥ M.W j)
  obtain ⟨K, hK⟩ := ((hC.prod (extremePoints_Ddual_finite M)).image g).bddAbove
  have : etaC M p C ≤ (K : EReal) := by
    unfold etaC
    refine iSup₂_le fun Y hY => iSup₂_le fun δ hδ => ?_
    exact EReal.coe_le_coe_iff.2 (hK ⟨(Y, δ), ⟨hY, hδ⟩, rfl⟩)
  exact lt_of_le_of_lt this (EReal.coe_lt_top K)

/-- `Q^C_ε` is monotone in the radius. -/
theorem QC_mono (M : Model n d r m mt) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (C : Set (Matrix (Fin r) (Fin d) ℝ)) {ε ε' : ℝ} (h : ε' ≤ ε) (x : Fin n → ℝ)
    (zhat : Fin d → ℝ) : QC M p C ε' x zhat ≤ QC M p C ε x zhat := by
  have hsub : ball p zhat ε' ∩ Xi M ⊆ ball p zhat ε ∩ Xi M := fun ζ hζ =>
    ⟨le_trans (show ‖WithLp.toLp p (ζ - zhat)‖ ≤ ε' from hζ.1) h, hζ.2⟩
  unfold QC
  refine le_iInf₂ fun yY hyY => iInf₂_le_of_le yY ⟨hyY.1, fun ζ hζ => hyY.2 ζ (hsub hζ)⟩ ?_
  unfold robCost
  exact iSup₂_le fun ζ hζ => le_iSup₂_of_le ζ (hsub hζ) le_rfl

/-- `V̂^SAA_N ≤ V̂^SRO_N` when all samples lie in `Ξ` and `ε ≥ 0`. -/
theorem VSAA_le_VSRO (M : Model n d r m mt) (p : ℝ≥0∞) [Fact (1 ≤ p)] {ε : ℝ} (hε : 0 ≤ ε)
    (s : ℕ → Fin d → ℝ) (N : ℕ) (hs : ∀ i, s i ∈ Xi M) (x : Fin n → ℝ) :
    VSAA M s N x ≤ VSRO M p ε s N x := by
  have hN : (0 : EReal) ≤ (((N : ℝ)⁻¹ : ℝ) : EReal) := by
    exact_mod_cast inv_nonneg.mpr (Nat.cast_nonneg N)
  unfold VSAA VSRO
  gcongr with i hi
  refine le_iSup₂_of_le (s i) ⟨?_, hs i⟩ le_rfl
  show ‖WithLp.toLp p (s i - s i)‖ ≤ ε
  simpa using hε

/-- Upper bound on `V̂^MP_N(x)` with linear decision rules through `Q^C_ε`. -/
theorem VMP_le (M : Model n d r m mt) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (C : Set (Matrix (Fin r) (Fin d) ℝ)) (ε : ℝ) (s : ℕ → Fin d → ℝ) (N : ℕ) (x : Fin n → ℝ)
    (b : ℕ → ℝ) (hb : ∀ i < N, QC M p C ε x (s i) ≤ (b i : EReal)) :
    VMP M LDR p ε s N x ≤
      ((M.c ⬝ᵥ x + (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, b i : ℝ) : EReal) := by
  have hN : (0 : EReal) ≤ (((N : ℝ)⁻¹ : ℝ) : EReal) := by
    exact_mod_cast inv_nonneg.mpr (Nat.cast_nonneg N)
  have key : ∀ η : ℝ, 0 < η → VMP M LDR p ε s N x ≤
      ((M.c ⬝ᵥ x + (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, b i + η : ℝ) : EReal) := by
    intro η hη
    have hlt : ∀ i : Fin N, ∃ yY : (Fin r → ℝ) × Matrix (Fin r) (Fin d) ℝ,
        (yY.2 ∈ C ∧ robFeas M x (ball p (s i) ε ∩ Xi M) (fun ζ => yY.1 + yY.2 *ᵥ ζ)) ∧
        robCost M (ball p (s i) ε ∩ Xi M) (fun ζ => yY.1 + yY.2 *ᵥ ζ) < ((b i + η : ℝ) : EReal) := by
      intro i
      have h1 : QC M p C ε x (s i) < ((b i + η : ℝ) : EReal) :=
        lt_of_le_of_lt (hb i i.2) (EReal.coe_lt_coe_iff.2 (by linarith))
      unfold QC at h1
      rw [iInf_lt_iff] at h1
      obtain ⟨yY, h1⟩ := h1
      rw [iInf_lt_iff] at h1
      obtain ⟨hyY, h1⟩ := h1
      exact ⟨yY, hyY, h1⟩
    choose yY hyY hcost using hlt
    have hle : VMP M LDR p ε s N x ≤ ((M.c ⬝ᵥ x : ℝ) : EReal) + (((N : ℝ)⁻¹ : ℝ) : EReal) *
        ∑ i : Fin N, robCost M (U M p ε s i) (fun ζ => (yY i).1 + (yY i).2 *ᵥ ζ) := by
      unfold VMP
      refine iInf₂_le_of_le (fun i ζ => (yY i).1 + (yY i).2 *ᵥ ζ) ?_ le_rfl
      intro i
      exact ⟨⟨(yY i).1, (yY i).2, fun ζ => rfl⟩, (hyY i).2⟩
    refine hle.trans ?_
    calc ((M.c ⬝ᵥ x : ℝ) : EReal) + (((N : ℝ)⁻¹ : ℝ) : EReal) *
          ∑ i : Fin N, robCost M (U M p ε s i) (fun ζ => (yY i).1 + (yY i).2 *ᵥ ζ)
        ≤ ((M.c ⬝ᵥ x : ℝ) : EReal) + (((N : ℝ)⁻¹ : ℝ) : EReal) *
          ∑ i : Fin N, ((b i + η : ℝ) : EReal) := by
          gcongr with i hi
          exact (hcost i).le
      _ = ((M.c ⬝ᵥ x + (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, (b i + η) : ℝ) : EReal) := by
          rw [← coe_sum, ← EReal.coe_mul, ← EReal.coe_add,
            Finset.sum_range (fun i => b i + η)]
      _ ≤ ((M.c ⬝ᵥ x + (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, b i + η : ℝ) : EReal) := by
          refine EReal.coe_le_coe_iff.2 ?_
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          rcases Nat.eq_zero_or_pos N with h0 | h0
          · subst h0; simp; linarith
          · have : (N : ℝ)⁻¹ * (N * η) = η := by
              field_simp
            nlinarith [this]
  by_contra hcon
  push Not at hcon
  obtain ⟨z, hz1, hz2⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
  have hz1' : M.c ⬝ᵥ x + (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, b i < z := EReal.coe_lt_coe_iff.1 hz1
  have := key (z - (M.c ⬝ᵥ x + (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, b i)) (by linarith)
  have h3 : ((M.c ⬝ᵥ x + (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, b i +
      (z - (M.c ⬝ᵥ x + (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, b i)) : ℝ) : EReal) = z := by
    congr 1; ring
  rw [h3] at this
  exact absurd (lt_of_lt_of_le hz2 this) (lt_irrefl _)

/-- From value convergence to near-optimality in the SAA problem. -/
theorem argmin_helper {V VS : ℕ → (Fin n → ℝ) → EReal} {a : EReal} (ha : a ≠ ⊤) (ha' : a ≠ ⊥)
    (hV : Tendsto (fun N => ⨅ x, V N x) atTop (𝓝 a))
    (hS : Tendsto (fun N => ⨅ x, VS N x) atTop (𝓝 a))
    (hle : ∀ N x, VS N x ≤ V N x)
    (xh : ℕ → Fin n → ℝ) (hmin : ∀ᶠ N in atTop, IsMinOn (V N) Set.univ (xh N)) :
    ∃ η : ℕ → ℝ, Tendsto η atTop (𝓝 0) ∧
      ∀ᶠ N in atTop, VS N (xh N) ≤ (⨅ x, VS N x) + ((η N : ℝ) : EReal) := by
  refine ⟨fun N => (⨅ x, V N x).toReal - (⨅ x, VS N x).toReal, ?_, ?_⟩
  · have h1 := (EReal.tendsto_toReal ha ha').comp hV
    have h2 := (EReal.tendsto_toReal ha ha').comp hS
    simpa using h1.sub h2
  · filter_upwards [hmin, hV.eventually_ne ha, hV.eventually_ne ha', hS.eventually_ne ha,
      hS.eventually_ne ha'] with N hN h1 h2 h3 h4
    have hVx : V N (xh N) = ⨅ x, V N x :=
      le_antisymm (le_iInf fun x => hN (Set.mem_univ x)) (iInf_le _ _)
    calc VS N (xh N) ≤ V N (xh N) := hle N (xh N)
      _ = ⨅ x, V N x := hVx
      _ = (((⨅ x, V N x).toReal : ℝ) : EReal) := (EReal.coe_toReal h1 h2).symm
      _ = (((⨅ x, VS N x).toReal : ℝ) : EReal) +
            (((⨅ x, V N x).toReal - (⨅ x, VS N x).toReal : ℝ) : EReal) := by
          rw [← EReal.coe_add]; congr 1; ring
      _ = (⨅ x, VS N x) + (((⨅ x, V N x).toReal - (⨅ x, VS N x).toReal : ℝ) : EReal) := by
          rw [EReal.coe_toReal h3 h4]

/-- The pointwise identity `x.toReal = x⁺ - x⁻` for extended reals. -/
theorem toReal_eq_pos_sub_neg (x : EReal) :
    x.toReal = (x.toENNReal).toReal - ((-x).toENNReal).toReal := by
  induction x using EReal.rec with
  | bot => simp
  | top => simp
  | coe r =>
    rw [← EReal.coe_neg, EReal.toENNReal_of_ne_top (EReal.coe_ne_top r),
      EReal.toENNReal_of_ne_top (EReal.coe_ne_top (-r))]
    simp only [EReal.toReal_coe]
    rw [ENNReal.toReal_ofReal', ENNReal.toReal_ofReal']
    rcases le_total 0 r with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring

/-- Integrability of the second-stage cost at an optimal first-stage decision. -/
theorem Q_integrable (M : Model n d r m mt) (μ : Measure (Fin d → ℝ)) (xs : Fin n → ℝ) (v : ℝ)
    (hV : Vstar M μ xs = (v : EReal)) :
    Integrable (fun ζ => (Q M xs ζ).toReal) μ ∧
      ∫ ζ, (Q M xs ζ).toReal ∂μ = v - M.c ⬝ᵥ xs ∧
      ∀ᵐ ζ ∂μ, Q M xs ζ ≠ ⊤ ∧ Q M xs ζ ≠ ⊥ := by
  have hmeas := measurable_Q M xs
  set A := ∫⁻ ζ, (Q M xs ζ).toENNReal ∂μ with hA
  set B := ∫⁻ ζ, (-Q M xs ζ).toENNReal ∂μ with hB
  unfold Vstar DupacovaWets.Consistency.expect at hV
  rw [← hA, ← hB] at hV
  have hAfin : A ≠ ∞ := by
    intro h
    rw [if_pos h] at hV
    simp at hV
  rw [if_neg hAfin] at hV
  have hBfin : B ≠ ∞ := by
    intro h
    rw [h] at hV
    have : ((A : EReal) - ((⊤ : ℝ≥0∞) : EReal)) = ⊥ := by
      rw [EReal.coe_ennreal_top]
      exact EReal.sub_top _
    rw [this] at hV
    simp at hV
  have hpm : Measurable fun ζ => (Q M xs ζ).toENNReal := hmeas.ereal_toENNReal
  have hnm : Measurable fun ζ => (-Q M xs ζ).toENNReal := hmeas.neg.ereal_toENNReal
  have hpi : Integrable (fun ζ => ((Q M xs ζ).toENNReal).toReal) μ :=
    integrable_toReal_of_lintegral_ne_top hpm.aemeasurable hAfin
  have hni : Integrable (fun ζ => ((-Q M xs ζ).toENNReal).toReal) μ :=
    integrable_toReal_of_lintegral_ne_top hnm.aemeasurable hBfin
  have hfeq : (fun ζ => (Q M xs ζ).toReal) =
      fun ζ => ((Q M xs ζ).toENNReal).toReal - ((-Q M xs ζ).toENNReal).toReal :=
    funext fun ζ => toReal_eq_pos_sub_neg _
  have hpa : ∀ᵐ ζ ∂μ, (Q M xs ζ).toENNReal < ∞ := ae_lt_top hpm hAfin
  have hna : ∀ᵐ ζ ∂μ, (-Q M xs ζ).toENNReal < ∞ := ae_lt_top hnm hBfin
  refine ⟨hfeq ▸ hpi.sub hni, ?_, ?_⟩
  · rw [hfeq, integral_sub hpi hni, integral_toReal hpm.aemeasurable hpa,
      integral_toReal hnm.aemeasurable hna, ← hA, ← hB]
    have hA' : ((A : ℝ≥0∞) : EReal) = ((A.toReal : ℝ) : EReal) := by
      rw [← EReal.coe_ennreal_toReal hAfin]
    have hB' : ((B : ℝ≥0∞) : EReal) = ((B.toReal : ℝ) : EReal) := by
      rw [← EReal.coe_ennreal_toReal hBfin]
    rw [hA', hB', ← EReal.coe_sub, ← EReal.coe_add] at hV
    have := EReal.coe_eq_coe_iff.1 hV
    linarith
  · filter_upwards [hpa, hna] with ζ h1 h2
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [h] at h1; simp at h1
    · rw [h] at h2; simp at h2

end SROThm2Aux

open TwoStageSRO.AsymOpt SROThm2Aux in
theorem solution {n d r m mt : ℕ} (M : Model n d r m mt) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure (Fin d → ℝ)) (ξ : ℕ → Ω → (Fin d → ℝ))
    (hind : iIndepFun ξ P) (hlaw : ∀ i, HasLaw (ξ i) μ P) (hsupp : μ (Xi M)ᶜ = 0)
    (ε : ℕ → ℝ) (hε0 : ∀ N, 0 ≤ ε N) (hε : Tendsto ε atTop (𝓝 0))
    (hA2 : vStar M μ ≠ ⊤ ∧ vStar M μ ≠ ⊥ ∧ Integrable id μ)
    (hA3 : (optSet M μ).Nonempty ∧ Bornology.IsBounded (optSet M μ))
    (hA4 : A4 M p) :
    (∀ᵐ ω ∂P,
      Tendsto (fun N => vSRO M p (ε N) (fun i => ξ i ω) N) atTop (𝓝 (vStar M μ)) ∧
      Tendsto (fun N => vMP M LDR p (ε N) (fun i => ξ i ω) N) atTop (𝓝 (vStar M μ))) ∧
    (∀ᵐ ω ∂P, ∀ xh : ℕ → (Fin n → ℝ),
      (∀ᶠ N in atTop, IsMinOn (VSRO M p (ε N) (fun i => ξ i ω) N) Set.univ (xh N)) →
      ∀ xb, MapClusterPt xb atTop xh → xb ∈ optSet M μ) ∧
    (∀ᵐ ω ∂P, ∀ xh : ℕ → (Fin n → ℝ),
      (∀ᶠ N in atTop, IsMinOn (VMP M LDR p (ε N) (fun i => ξ i ω) N) Set.univ (xh N)) →
      ∀ xb, MapClusterPt xb atTop xh → xb ∈ optSet M μ) := by
  classical
  have : IsProbabilityMeasure μ := by
    rw [← (hlaw 0).map_eq]; exact Measure.isProbabilityMeasure_map (hlaw 0).aemeasurable
  obtain ⟨xs, hxs⟩ := hA3.1
  have hVxs : Vstar M μ xs = vStar M μ :=
    le_antisymm (le_iInf fun x => hxs (Set.mem_univ x)) (iInf_le _ _)
  obtain ⟨v, hv⟩ : ∃ v : ℝ, vStar M μ = (v : EReal) :=
    ⟨(vStar M μ).toReal, (EReal.coe_toReal hA2.1 hA2.2.1).symm⟩
  obtain ⟨hfint, hfI, hfin⟩ := Q_integrable M μ xs v (hVxs.trans hv)
  set f : (Fin d → ℝ) → ℝ := fun ζ => (Q M xs ζ).toReal with hf
  have hfmeas : Measurable f := (measurable_Q M xs).ereal_toReal
  -- (E1) the strong law of large numbers for `Q(x*, ξⁱ)`
  have E1 : ∀ᵐ ω ∂P, Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, f (ξ i ω))
      atTop (𝓝 (v - M.c ⬝ᵥ xs)) := by
    have hint : Integrable (fun ω => f (ξ 0 ω)) P := by
      have : Integrable f (P.map (ξ 0)) := by rw [(hlaw 0).map_eq]; exact hfint
      exact this.comp_aemeasurable (hlaw 0).aemeasurable
    have hind' := hind.comp (fun _ => f) (fun _ => hfmeas)
    have hident : ∀ i, IdentDistrib (fun ω => f (ξ i ω)) (fun ω => f (ξ 0 ω)) P P := by
      intro i
      have h : IdentDistrib (ξ i) (ξ 0) P P :=
        ⟨(hlaw i).aemeasurable, (hlaw 0).aemeasurable, by rw [(hlaw i).map_eq, (hlaw 0).map_eq]⟩
      exact h.comp hfmeas
    have hslln := strong_law_ae (fun i ω => f (ξ i ω)) hint (fun i j hij => hind'.indepFun hij) hident
    have hE : ∫ ω, f (ξ 0 ω) ∂P = v - M.c ⬝ᵥ xs := by
      rw [← hfI, ← (hlaw 0).map_eq,
        integral_map (hlaw 0).aemeasurable hfmeas.aestronglyMeasurable]
    filter_upwards [hslln] with ω hω
    rw [← hE]
    simpa [smul_eq_mul] using hω
  -- (E2) all samples lie in `Ξ` and have finite cost at `x*`
  have E2 : ∀ᵐ ω ∂P, ∀ i, ξ i ω ∈ Xi M ∧ Q M xs (ξ i ω) ≠ ⊤ ∧ Q M xs (ξ i ω) ≠ ⊥ := by
    rw [ae_all_iff]
    intro i
    have hgood : ∀ᵐ ζ ∂μ, ζ ∈ Xi M ∧ Q M xs ζ ≠ ⊤ ∧ Q M xs ζ ≠ ⊥ := by
      have hX : ∀ᵐ ζ ∂μ, ζ ∈ Xi M := by
        rw [ae_iff]; exact hsupp
      filter_upwards [hX, hfin] with ζ h1 h2 using ⟨h1, h2⟩
    have : ∀ᵐ ζ ∂(P.map (ξ i)), ζ ∈ Xi M ∧ Q M xs ζ ≠ ⊤ ∧ Q M xs ζ ≠ ⊥ := by
      rw [(hlaw i).map_eq]; exact hgood
    exact ae_of_ae_map (hlaw i).aemeasurable this
  have E3 := saa_value_consistency M P μ ξ hind hlaw hA2 hA3
  have E4 := saa_argmin_consistency M P μ ξ hind hlaw hA2 hA3
  -- condition [A6]
  obtain ⟨xb, εb, hεb, C, hCfin, hQC⟩ := ((lemma_1 M p).out 0 2).1 hA4
  have hη := etaC_lt_top M p C hCfin
  set η0 : ℝ := max 0 (etaC M p C).toReal with hη0
  have hηle : etaC M p C ≤ (η0 : EReal) := by
    by_cases hb : etaC M p C = ⊥
    · rw [hb]; exact bot_le
    · rw [← EReal.coe_toReal hη.ne hb]
      exact EReal.coe_le_coe_iff.2 (le_max_right _ _)
  -- the main almost-sure statement
  have main : ∀ᵐ ω ∂P,
      Tendsto (fun N => vSRO M p (ε N) (fun i => ξ i ω) N) atTop (𝓝 (vStar M μ)) ∧
      Tendsto (fun N => vMP M LDR p (ε N) (fun i => ξ i ω) N) atTop (𝓝 (vStar M μ)) ∧
      Tendsto (fun N => vSAA M (fun i => ξ i ω) N) atTop (𝓝 (vStar M μ)) ∧
      (∀ N x, VSAA M (fun i => ξ i ω) N x ≤ VSRO M p (ε N) (fun i => ξ i ω) N x) ∧
      (∀ N x, VSRO M p (ε N) (fun i => ξ i ω) N x ≤ VMP M LDR p (ε N) (fun i => ξ i ω) N x) := by
    filter_upwards [E1, E2, E3] with ω h1 h2 h3
    set s : ℕ → Fin d → ℝ := fun i => ξ i ω with hs
    have hSAA_SRO : ∀ N x, VSAA M s N x ≤ VSRO M p (ε N) s N x :=
      fun N x => VSAA_le_VSRO M p (hε0 N) s N (fun i => (h2 i).1) x
    have hSRO_MP : ∀ N x, VSRO M p (ε N) s N x ≤ VMP M LDR p (ε N) s N x :=
      fun N x => ((theorem_1 M LDR p (ε N) s N).2 x).1
    have hv1 : ∀ N, vSAA M s N ≤ vSRO M p (ε N) s N := fun N => iInf_mono (hSAA_SRO N)
    have hv2 : ∀ N, vSRO M p (ε N) s N ≤ vMP M LDR p (ε N) s N := fun N => iInf_mono (hSRO_MP N)
    -- upper bound: for every real `B > v*`, eventually `v̂^MP_N < B`
    have upper : ∀ B : ℝ, v < B → ∀ᶠ N in atTop, vMP M LDR p (ε N) s N < (B : EReal) := by
      intro B hB
      set δ : ℝ := (B - v) / 4 with hδ
      have hδpos : 0 < δ := by rw [hδ]; linarith
      set w : Fin n → ℝ := xb - xs with hw
      set K : ℝ := |M.c ⬝ᵥ w| + |Lconst M p * dualNorm p w| with hK
      have hK0 : 0 ≤ K := by positivity
      set θ : ℝ := min (1/2) (δ / (K + 1)) with hθ
      have hθpos : 0 < θ := lt_min (by norm_num) (div_pos hδpos (by linarith))
      have hθhalf : θ ≤ 1/2 := min_le_left _ _
      have hθK : θ * K < δ := by
        have h1 : θ ≤ δ / (K + 1) := min_le_right _ _
        calc θ * K ≤ δ / (K + 1) * K := mul_le_mul_of_nonneg_right h1 hK0
          _ < δ := by
            rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
            nlinarith
      have hlam : (1 - θ) ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
      obtain ⟨ε1, hε1, hfeas1⟩ := lemma_2 M p μ hsupp hA2 hA3 xs hxs xb C εb hεb
        (fun ζ hζ => hQC ζ hζ.1) (1 - θ) hlam
      set x : Fin n → ℝ := (1 - θ) • xs + (1 - (1 - θ)) • xb with hx
      have hxw : x - xs = θ • w := by
        rw [hx, hw]; ext j; simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      have hcx : M.c ⬝ᵥ x = M.c ⬝ᵥ xs + θ * (M.c ⬝ᵥ w) := by
        have : x = xs + θ • w := by rw [← hxw]; abel
        rw [this, dotProduct_add, dotProduct_smul, smul_eq_mul]
      set Lt : ℝ := Lconst M p * dualNorm p (x - xs) with hLt
      have hLt' : Lt = θ * (Lconst M p * dualNorm p w) := by
        rw [hLt, hxw, dualNorm_smul p θ hθpos.le]; ring
      -- membership of samples in `Ξ*`
      have hstar : ∀ i, s i ∈ XiStar M xs := by
        intro i
        refine ⟨(h2 i).1, ?_⟩
        by_contra hno
        push Not at hno
        apply (h2 i).2.1
        unfold Q
        rw [sInf_eq_top]
        rintro _ ⟨y, hy, rfl⟩
        exact absurd hy (hno y)
      -- the per-sample bound
      have hbound : ∀ N, ε N ≤ ε1 → ∀ i, QC M p C (ε N) x (s i) ≤
          ((f (s i) + ε N * η0 + Lt : ℝ) : EReal) := by
        intro N hN i
        have hfeasN : ∀ ζ ∈ XiStar M xs, QC M p C (ε N) x ζ < ⊤ :=
          fun ζ hζ => lt_of_le_of_lt (QC_mono M p C hN x ζ) (hfeas1 ζ hζ)
        have h3' := lemma_3 M p μ hsupp hA2 hA3 xs hxs x C (ε N) (hε0 N) hfeasN (s i) (hstar i)
        refine h3'.trans ?_
        have hQf : Q M xs (s i) = ((f (s i) : ℝ) : EReal) :=
          (EReal.coe_toReal (h2 i).2.1 (h2 i).2.2).symm
        rw [hQf, ← hLt]
        have hmul : ((ε N : ℝ) : EReal) * etaC M p C ≤ ((ε N * η0 : ℝ) : EReal) := by
          rw [EReal.coe_mul]
          exact mul_le_mul_of_nonneg_left hηle (EReal.coe_nonneg.2 (hε0 N))
        calc ((f (s i) : ℝ) : EReal) + ((ε N : ℝ) : EReal) * etaC M p C + ((Lt : ℝ) : EReal)
            ≤ ((f (s i) : ℝ) : EReal) + ((ε N * η0 : ℝ) : EReal) + ((Lt : ℝ) : EReal) := by
              gcongr
          _ = ((f (s i) + ε N * η0 + Lt : ℝ) : EReal) := by
              rw [EReal.coe_add, EReal.coe_add]
      -- the real upper sequence and its limit
      set R : ℕ → ℝ := fun N => M.c ⬝ᵥ x + (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, f (s i) +
        ε N * η0 + Lt with hR
      have hRlim : Tendsto R atTop (𝓝 (M.c ⬝ᵥ x + (v - M.c ⬝ᵥ xs) + 0 * η0 + Lt)) := by
        refine ((tendsto_const_nhds.add h1).add (hε.mul_const η0)).add tendsto_const_nhds
      have hlimlt : M.c ⬝ᵥ x + (v - M.c ⬝ᵥ xs) + 0 * η0 + Lt < B := by
        rw [hcx, hLt']
        have e1 : θ * (M.c ⬝ᵥ w) ≤ θ * |M.c ⬝ᵥ w| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) hθpos.le
        have e2 : θ * (Lconst M p * dualNorm p w) ≤ θ * |Lconst M p * dualNorm p w| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) hθpos.le
        have e3 : θ * |M.c ⬝ᵥ w| + θ * |Lconst M p * dualNorm p w| = θ * K := by rw [hK]; ring
        linarith
      filter_upwards [hRlim.eventually (gt_mem_nhds hlimlt), hε.eventually (Iic_mem_nhds hε1),
        eventually_ge_atTop 1] with N hRN hεN hN1
      have hVMP : VMP M LDR p (ε N) s N x ≤ ((R N : ℝ) : EReal) := by
        have := VMP_le M p C (ε N) s N x (fun i => f (s i) + ε N * η0 + Lt)
          (fun i _ => hbound N hεN i)
        refine this.trans (EReal.coe_le_coe_iff.2 (le_of_eq ?_))
        rw [hR]
        simp only
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const,
          Finset.card_range, nsmul_eq_mul, nsmul_eq_mul]
        have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
        field_simp
        ring
      calc vMP M LDR p (ε N) s N ≤ VMP M LDR p (ε N) s N x := iInf_le _ x
        _ ≤ ((R N : ℝ) : EReal) := hVMP
        _ < (B : EReal) := EReal.coe_lt_coe_iff.2 hRN
    have hMP : Tendsto (fun N => vMP M LDR p (ε N) s N) atTop (𝓝 (vStar M μ)) := by
      rw [tendsto_order]
      refine ⟨fun a ha => ?_, fun b hb => ?_⟩
      · filter_upwards [(tendsto_order.1 h3).1 a ha] with N hN
        exact lt_of_lt_of_le hN ((hv1 N).trans (hv2 N))
      · rw [hv] at hb
        obtain ⟨B, hB1, hB2⟩ := EReal.lt_iff_exists_real_btwn.1 hb
        filter_upwards [upper B (EReal.coe_lt_coe_iff.1 hB1)] with N hN
        exact lt_trans hN hB2
    have hSRO : Tendsto (fun N => vSRO M p (ε N) s N) atTop (𝓝 (vStar M μ)) := by
      rw [tendsto_order]
      refine ⟨fun a ha => ?_, fun b hb => ?_⟩
      · filter_upwards [(tendsto_order.1 h3).1 a ha] with N hN
        exact lt_of_lt_of_le hN (hv1 N)
      · filter_upwards [(tendsto_order.1 hMP).2 b hb] with N hN
        exact lt_of_le_of_lt (hv2 N) hN
    exact ⟨hSRO, hMP, h3, hSAA_SRO, hSRO_MP⟩
  refine ⟨main.mono fun ω h => ⟨h.1, h.2.1⟩, ?_, ?_⟩
  · filter_upwards [main, E4] with ω h h4
    intro xh hmin xb' hxb'
    obtain ⟨η, hη0, hηev⟩ := argmin_helper (V := fun N => VSRO M p (ε N) (fun i => ξ i ω) N)
      (VS := fun N => VSAA M (fun i => ξ i ω) N) hA2.1 hA2.2.1 h.1 h.2.2.1 h.2.2.2.1 xh hmin
    exact h4 xh η hη0 hηev xb' hxb'
  · filter_upwards [main, E4] with ω h h4
    intro xh hmin xb' hxb'
    obtain ⟨η, hη0, hηev⟩ := argmin_helper (V := fun N => VMP M LDR p (ε N) (fun i => ξ i ω) N)
      (VS := fun N => VSAA M (fun i => ξ i ω) N) hA2.1 hA2.2.1 h.2.1 h.2.2.1
      (fun N x => (h.2.2.2.1 N x).trans (h.2.2.2.2 N x)) xh hmin
    exact h4 xh η hη0 hηev xb' hxb'
