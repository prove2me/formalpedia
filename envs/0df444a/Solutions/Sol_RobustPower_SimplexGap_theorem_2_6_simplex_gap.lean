-- Prove2me | solution 1 for RobustPower.SimplexGap.theorem_2_6_simplex_gap
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:39:01.310747+00:00
-- url     : https://prove2.me/submissions/e4e54629-c1a6-40b6-9b27-c027ed7e16d2

import Mathlib
import Definitions.Def_RobustPower_SimplexGap_Problems
import Definitions.Def_RobustPower_SimplexGap_SimplexInstance
import Definitions.Def_RobustPower_SimplexGap_SimplexInstance

set_option autoImplicit false

open MeasureTheory RobustPower.SimplexGap

namespace SimpLib

def S (n : ℕ) (t : ℝ) : Set (Fin n → ℝ) := {x | 0 ≤ x ∧ ∑ j, x j ≤ t}

lemma S_meas (n : ℕ) (t : ℝ) : MeasurableSet (S n t) := by
  have h1 : IsClosed {x : Fin n → ℝ | 0 ≤ x} := isClosed_Ici
  have h2 : IsClosed {x : Fin n → ℝ | ∑ j, x j ≤ t} :=
    isClosed_le (continuous_finset_sum _ fun i _ => continuous_apply i) continuous_const
  exact (h1.inter h2).measurableSet

lemma S_neg (n : ℕ) (t : ℝ) (ht : t < 0) : S n t = ∅ := by
  ext x
  constructor
  · rintro ⟨h0, h⟩
    have : 0 ≤ ∑ j, x j := Finset.sum_nonneg (fun j _ => h0 j)
    linarith
  · intro h; exact h.elim

lemma S_succ (n : ℕ) (i : Fin (n + 1)) (t : ℝ) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm ⁻¹' S (n + 1) t =
      {p : ℝ × (Fin n → ℝ) | 0 ≤ p.1 ∧ p.2 ∈ S n (t - p.1)} := by
  ext ⟨s, y⟩
  simp only [Set.mem_preimage, S, Set.mem_setOf_eq, MeasurableEquiv.piFinSuccAbove_symm_apply]
  rw [Fin.sum_univ_succAbove _ i]
  have hins : (Fin.insertNthEquiv (fun _ : Fin (n + 1) => ℝ) i) (s, y) = Fin.insertNth i s y := rfl
  simp only [hins, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  have : (0 : Fin (n + 1) → ℝ) ≤ Fin.insertNth i s y ↔ 0 ≤ s ∧ 0 ≤ y := by
    simp only [Pi.le_def, Pi.zero_apply]
    rw [Fin.forall_iff_succAbove i]
    simp
  rw [this]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, by linarith⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, by linarith⟩

lemma decomp (n : ℕ) (i : Fin (n + 1)) (t : ℝ) (φ : ℝ → ENNReal) (hφ : Measurable φ) :
    ∫⁻ x in S (n + 1) t, φ (x i) = ∫⁻ s in Set.Icc 0 t, φ s * volume (S n (t - s)) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i with he
  have hmp : MeasurePreserving e volume (volume.prod volume) :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have hT : MeasurableSet {p : ℝ × (Fin n → ℝ) | 0 ≤ p.1 ∧ p.2 ∈ S n (t - p.1)} := by
    rw [← S_succ n i t]
    exact e.symm.measurable (S_meas _ _)
  rw [← lintegral_indicator (S_meas _ _)]
  rw [← hmp.symm.lintegral_comp_emb e.symm.measurableEmbedding]
  have h1 : ∀ p : ℝ × (Fin n → ℝ),
      (S (n + 1) t).indicator (fun x => φ (x i)) (e.symm p) =
        {p : ℝ × (Fin n → ℝ) | 0 ≤ p.1 ∧ p.2 ∈ S n (t - p.1)}.indicator (fun p => φ p.1) p := by
    intro p
    have hmem : e.symm p ∈ S (n + 1) t ↔ p ∈ {p : ℝ × (Fin n → ℝ) | 0 ≤ p.1 ∧ p.2 ∈ S n (t - p.1)} := by
      rw [← S_succ n i t]; rfl
    have hval : (e.symm p) i = p.1 := by
      simp [he, MeasurableEquiv.piFinSuccAbove_symm_apply]
    by_cases h : p ∈ {p : ℝ × (Fin n → ℝ) | 0 ≤ p.1 ∧ p.2 ∈ S n (t - p.1)}
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hmem.2 h), hval]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (hmem.1 h'))]
  simp_rw [h1]
  have hG : Measurable ({p : ℝ × (Fin n → ℝ) | 0 ≤ p.1 ∧ p.2 ∈ S n (t - p.1)}.indicator
      (fun p => φ p.1)) := (hφ.comp measurable_fst).indicator hT
  rw [lintegral_prod _ hG.aemeasurable]
  rw [← lintegral_indicator measurableSet_Icc]
  refine lintegral_congr fun s => ?_
  by_cases hs : 0 ≤ s
  · have h3 : ∀ y : Fin n → ℝ,
        {p : ℝ × (Fin n → ℝ) | 0 ≤ p.1 ∧ p.2 ∈ S n (t - p.1)}.indicator (fun p => φ p.1) (s, y) =
          (S n (t - s)).indicator (fun _ => φ s) y := by
      intro y
      by_cases hy : y ∈ S n (t - s)
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem]
        exact ⟨hs, hy⟩
      · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem]
        exact fun h => hy h.2
    simp_rw [h3]
    rw [lintegral_indicator_const (S_meas _ _)]
    by_cases hst : s ≤ t
    · rw [Set.indicator_of_mem (show s ∈ Set.Icc 0 t from ⟨hs, hst⟩)]
    · have hst' := not_le.1 hst
      rw [S_neg n (t - s) (by linarith), Set.indicator_of_notMem (fun h => absurd h.2 hst)]
      simp
  · have h3 : ∀ y : Fin n → ℝ,
        {p : ℝ × (Fin n → ℝ) | 0 ≤ p.1 ∧ p.2 ∈ S n (t - p.1)}.indicator (fun p => φ p.1) (s, y) = 0 := by
      intro y
      rw [Set.indicator_of_notMem]
      exact fun h => hs h.1
    simp_rw [h3]
    rw [Set.indicator_of_notMem (fun h => hs h.1)]
    simp

lemma int_aux (n : ℕ) (t : ℝ) :
    ∫ s in (0:ℝ)..t, (t - s) ^ n / (n.factorial : ℝ) = t ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  rw [intervalIntegral.integral_div, intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ n) t]
  simp only [sub_self, sub_zero, integral_pow]
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  simp

lemma int_aux2 (n : ℕ) (t : ℝ) :
    ∫ s in (0:ℝ)..t, s * ((t - s) ^ n / (n.factorial : ℝ)) =
      t ^ (n + 2) / ((n + 2).factorial : ℝ) := by
  have h : ∀ s : ℝ, s * ((t - s) ^ n / (n.factorial : ℝ)) =
      t * ((t - s) ^ n / (n.factorial : ℝ)) - ((n : ℝ) + 1) * ((t - s) ^ (n + 1) / ((n + 1).factorial : ℝ)) := by
    intro s
    rw [Nat.factorial_succ]
    push_cast
    have : ((n.factorial : ℝ)) ≠ 0 := by positivity
    field_simp
    ring
  simp_rw [h]
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, int_aux, int_aux]
  · rw [Nat.factorial_succ (n + 1), Nat.factorial_succ n]
    push_cast
    have : ((n.factorial : ℝ)) ≠ 0 := by positivity
    field_simp
    ring
  · exact (Continuous.intervalIntegrable (by fun_prop) _ _)
  · exact (Continuous.intervalIntegrable (by fun_prop) _ _)

lemma lint_to_real (f : ℝ → ℝ) (t : ℝ) (ht : 0 ≤ t) (hf : Continuous f)
    (hnn : ∀ s ∈ Set.Icc 0 t, 0 ≤ f s) :
    ∫⁻ s in Set.Icc 0 t, ENNReal.ofReal (f s) = ENNReal.ofReal (∫ s in (0:ℝ)..t, f s) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (hf.integrableOn_Icc)
    ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall hnn))]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht]

lemma vol_S : ∀ (n : ℕ) (t : ℝ), 0 ≤ t →
    volume (S n t) = ENNReal.ofReal (t ^ n / n.factorial)
  | 0, t, ht => by
      have : S 0 t = Set.univ := by ext x; simp [S, ht]
      rw [this, volume_pi, Measure.pi_univ]; simp
  | n + 1, t, ht => by
      have h := decomp n 0 t (fun _ => 1) measurable_const
      simp only [lintegral_const, Measure.restrict_apply_univ, one_mul] at h
      rw [h]
      have h2 : ∫⁻ s in Set.Icc 0 t, volume (S n (t - s)) =
          ∫⁻ s in Set.Icc 0 t, ENNReal.ofReal ((t - s) ^ n / n.factorial) :=
        setLIntegral_congr_fun measurableSet_Icc (fun s hs => vol_S n (t - s) (by linarith [hs.2]))
      rw [h2, lint_to_real (fun s => (t - s) ^ n / n.factorial) t ht (by fun_prop)
        (fun s hs => by have := hs.2; have : 0 ≤ t - s := by linarith
                        positivity), int_aux]

lemma moment_S (n : ℕ) (i : Fin (n + 1)) (t : ℝ) (ht : 0 ≤ t) :
    ∫⁻ x in S (n + 1) t, ENNReal.ofReal (x i) =
      ENNReal.ofReal (t ^ (n + 2) / ((n + 2).factorial : ℝ)) := by
  rw [decomp n i t ENNReal.ofReal ENNReal.measurable_ofReal]
  have h2 : ∫⁻ s in Set.Icc 0 t, ENNReal.ofReal s * volume (S n (t - s)) =
      ∫⁻ s in Set.Icc 0 t, ENNReal.ofReal (s * ((t - s) ^ n / n.factorial)) := by
    refine setLIntegral_congr_fun measurableSet_Icc (fun s hs => ?_)
    rw [vol_S n (t - s) (by linarith [hs.2]), ENNReal.ofReal_mul hs.1]
  rw [h2, lint_to_real (fun s => s * ((t - s) ^ n / n.factorial)) t ht (by fun_prop)
    (fun s hs => by have := hs.2; have : 0 ≤ t - s := by linarith
                    have := hs.1; positivity), int_aux2]

lemma corner_eq (n : ℕ) : cornerSimplex n = S n 1 := by
  ext x
  exact and_comm

lemma vol_corner (n : ℕ) : volume (cornerSimplex n) = ((n.factorial : ENNReal))⁻¹ := by
  rw [corner_eq, vol_S n 1 zero_le_one]
  rw [one_pow, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos (by positivity)]
  simp

lemma moment_real (n : ℕ) (i : Fin (n + 1)) :
    ∫ x in S (n + 1) 1, x i = 1 / ((n + 2).factorial : ℝ) := by
  have hnn : 0 ≤ᵐ[volume.restrict (S (n + 1) 1)] fun x : Fin (n + 1) → ℝ => x i := by
    refine (ae_restrict_iff' (S_meas _ _)).2 (Filter.Eventually.of_forall fun x hx => ?_)
    exact hx.1 i
  rw [integral_eq_lintegral_of_nonneg_ae hnn (measurable_pi_apply i).aestronglyMeasurable,
    moment_S n i 1 zero_le_one, ENNReal.toReal_ofReal (by positivity), one_pow]

end SimpLib

open SimpLib

theorem rvge1 (n : ℕ) (hn : 3 ≤ n) {Ω : Type*} (b : Ω → Fin n → ℝ)
    (hb : Set.range b = cornerSimplex n) :
    (∀ (x : Fin 0 → ℝ) (y : Fin n → ℝ),
        RobFeasible (0 : Matrix (Fin n) (Fin 0) ℝ) (1 : Matrix (Fin n) (Fin n) ℝ) b ∅ ∅ x y →
          ∀ j, 1 ≤ y j) ∧
      (1 : EReal) ≤ zRob (0 : Matrix (Fin n) (Fin 0) ℝ) (1 : Matrix (Fin n) (Fin n) ℝ)
        (0 : Fin 0 → ℝ) (lastUnit n) b ∅ ∅ := by
  have key : ∀ (x : Fin 0 → ℝ) (y : Fin n → ℝ),
        RobFeasible (0 : Matrix (Fin n) (Fin 0) ℝ) (1 : Matrix (Fin n) (Fin n) ℝ) b ∅ ∅ x y →
          ∀ j, 1 ≤ y j := by
    intro x y hf j
    obtain ⟨-, -, h⟩ := hf
    have hx : (Pi.single j (1 : ℝ) : Fin n → ℝ) ∈ cornerSimplex n := by
      refine ⟨?_, ?_⟩
      · simp
      · intro i; by_cases h : i = j <;> simp [Pi.single_apply, h]
    rw [← hb] at hx
    obtain ⟨ω, hω⟩ := hx
    have := h ω j
    rw [hω] at this
    simpa using this
  refine ⟨key, ?_⟩
  unfold zRob
  refine le_iInf fun x => le_iInf fun y => le_iInf fun hf => ?_
  have hj := key x y hf ⟨n - 1, by omega⟩
  have hd : lastUnit n ⬝ᵥ y = y ⟨n - 1, by omega⟩ := by
    unfold dotProduct
    rw [Finset.sum_eq_single (⟨n - 1, by omega⟩ : Fin n)]
    · simp [lastUnit]
    · intro j _ hj
      have : (j : ℕ) ≠ n - 1 := fun h => hj (Fin.ext h)
      simp [lastUnit, this]
    · simp
  have h0 : (0 : Fin 0 → ℝ) ⬝ᵥ x = 0 := by simp
  rw [hd, h0]
  have : (1 : ℝ) ≤ 0 + y ⟨n - 1, by omega⟩ := by linarith
  exact_mod_cast this

theorem eq230 (n : ℕ) (hn : 3 ≤ n) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (b : Ω → Fin n → ℝ)
    (hμb : IsUniformOnSimplex n μ b) :
    StochFeasible μ (0 : Matrix (Fin n) (Fin 0) ℝ) (1 : Matrix (Fin n) (Fin n) ℝ) b ∅ ∅
        (0 : Fin 0 → ℝ) b ∧
      zStoch μ (0 : Matrix (Fin n) (Fin 0) ℝ) (1 : Matrix (Fin n) (Fin n) ℝ) (0 : Fin 0 → ℝ)
          (lastUnit n) b ∅ ∅ ≤ ((∫ ω, b ω ⟨n - 1, by omega⟩ ∂μ : ℝ) : EReal) := by
  obtain ⟨hmeas, hrange, -⟩ := hμb
  have hmem : ∀ ω, b ω ∈ cornerSimplex n := fun ω => hrange ▸ Set.mem_range_self ω
  have hfeas : StochFeasible μ (0 : Matrix (Fin n) (Fin 0) ℝ) (1 : Matrix (Fin n) (Fin n) ℝ) b
      ∅ ∅ (0 : Fin 0 → ℝ) b := by
    refine ⟨⟨le_refl _, by simp⟩, ?_, fun ω => ⟨⟨(hmem ω).2, by simp⟩, by simp⟩⟩
    refine Integrable.of_bound hmeas.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun ω => ?_)
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    obtain ⟨h1, h2⟩ := hmem ω
    have hi : b ω i ≤ ∑ j, b ω j :=
      Finset.single_le_sum (f := fun j => b ω j) (fun j _ => h2 j) (Finset.mem_univ i)
    rw [Real.norm_eq_abs, abs_of_nonneg (h2 i)]
    linarith
  refine ⟨hfeas, ?_⟩
  have hd : ∀ y : Fin n → ℝ, lastUnit n ⬝ᵥ y = y ⟨n - 1, by omega⟩ := by
    intro y
    unfold dotProduct
    rw [Finset.sum_eq_single (⟨n - 1, by omega⟩ : Fin n)]
    · simp [lastUnit]
    · intro j _ hj
      have : (j : ℕ) ≠ n - 1 := fun h => hj (Fin.ext h)
      simp [lastUnit, this]
    · simp
  unfold zStoch
  refine iInf_le_of_le (0 : Fin 0 → ℝ) (iInf_le_of_le b (iInf_le_of_le hfeas (le_of_eq ?_)))
  have : ∫ ω, lastUnit n ⬝ᵥ b ω ∂μ = ∫ ω, b ω ⟨n - 1, by omega⟩ ∂μ := by
    congr 1; ext ω; exact hd _
  rw [this]
  simp

theorem meanL (n : ℕ) (hn : 3 ≤ n) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (b : Ω → Fin n → ℝ)
    (hμb : IsUniformOnSimplex n μ b) :
    ∫ ω, b ω ⟨n - 1, by omega⟩ ∂μ = 1 / ((n : ℝ) + 1) := by
  obtain ⟨hmeas, -, hmap⟩ := hμb
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [← integral_map hmeas.aemeasurable (measurable_pi_apply _).aestronglyMeasurable, hmap,
    integral_smul_measure, vol_corner, inv_inv, corner_eq]
  have := moment_real m ⟨m + 1 - 1, by omega⟩
  rw [this]
  simp only [ENNReal.toReal_natCast, smul_eq_mul]
  rw [Nat.factorial_succ (m + 1)]
  push_cast
  have : ((m + 1).factorial : ℝ) ≠ 0 := by positivity
  field_simp

theorem solution (n : ℕ) (hn : 3 ≤ n) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (b : Ω → Fin n → ℝ)
    (hμb : IsUniformOnSimplex n μ b) :
    ((((n : ℝ) + 1 : ℝ) : EReal) *
        zStoch μ (0 : Matrix (Fin n) (Fin 0) ℝ) (1 : Matrix (Fin n) (Fin n) ℝ) (0 : Fin 0 → ℝ)
          (lastUnit n) b ∅ ∅) ≤
      zRob (0 : Matrix (Fin n) (Fin 0) ℝ) (1 : Matrix (Fin n) (Fin n) ℝ) (0 : Fin 0 → ℝ)
        (lastUnit n) b ∅ ∅ := by
  have h1 := (eq230 n hn μ b hμb).2
  have h2 := meanL n hn μ b hμb
  have h3 := (rvge1 n hn b hμb.2.1).2
  rw [h2] at h1
  refine le_trans ?_ h3
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  calc (((n : ℝ) + 1 : ℝ) : EReal) * zStoch μ (0 : Matrix (Fin n) (Fin 0) ℝ)
        (1 : Matrix (Fin n) (Fin n) ℝ) (0 : Fin 0 → ℝ) (lastUnit n) b ∅ ∅
      ≤ (((n : ℝ) + 1 : ℝ) : EReal) * ((1 / ((n : ℝ) + 1) : ℝ) : EReal) :=
        mul_le_mul_of_nonneg_left h1 (EReal.coe_nonneg.2 hpos.le)
    _ = 1 := by
        rw [← EReal.coe_mul]
        have : ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1)) = 1 := by field_simp
        rw [this]; rfl
