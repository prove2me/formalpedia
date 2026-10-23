-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P44.modeTransportEquality
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T07:14:52.90066+00:00
-- url     : https://prove2.me/submissions/01464185-05f7-4756-8c59-1ecebc032220

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

namespace QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

lemma X7_shell_apply {d b : ℕ} {E : Fin d → ℝ} {beta : ℝ} (D : ThermalDilation E beta b)
    (r i : Fin d) (a : Fin b × Fin b) :
    (shellVector D r i) a = thermalKraus D a r i := by
  simp only [shellVector]
  split_ifs with h
  · rfl
  · simp only [thermalKraus]
    rw [D.support r i a.2 a.1 (fun h' => h h'), mul_zero]

lemma X7_gibbs_nonneg {n : ℕ} (E : Fin n → ℝ) (beta : ℝ) (i : Fin n) : 0 ≤ gibbsWeight E beta i := by
  unfold gibbsWeight
  exact div_nonneg (Real.exp_nonneg _) (Finset.sum_nonneg fun _ _ => Real.exp_nonneg _)

lemma X7_gibbs_sum {n : ℕ} (hn : 0 < n) (E : Fin n → ℝ) (beta : ℝ) :
    ∑ i, gibbsWeight E beta i = 1 := by
  unfold gibbsWeight
  rw [← Finset.sum_div]
  apply div_self
  apply ne_of_gt
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty


lemma X7_kraus_entry' {d : ℕ} {κ : Type*} [Fintype κ] (K : κ → Mat d) (X : Mat d) (r s : Fin d) :
    krausApply K X r s = ∑ a, ∑ p, ∑ q, K a r p * X p q * conj (K a s q) := by
  simp only [krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.sum_mul, RCLike.star_def]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]

lemma X7_thermal_unit {d b : ℕ} {E : Fin d → ℝ} {beta : ℝ} (D : ThermalDilation E beta b)
    (i j r s : Fin d) :
    thermalApply D (matrixUnit i j) r s = inner ℂ (shellVector D s j) (shellVector D r i) := by
  unfold thermalApply
  rw [X7_kraus_entry', PiLp.inner_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [X7_shell_apply, X7_shell_apply]
  simp only [matrixUnit, Matrix.single_apply, RCLike.inner_apply]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp [mul_comm]
    · intro q _ hq; simp [Ne.symm hq]
    · simp
  · intro p _ hp; simp [Ne.symm hp]
  · simp

lemma X7_thermal_pop {d b : ℕ} {E : Fin d → ℝ} {beta : ℝ} (D : ThermalDilation E beta b)
    (r i : Fin d) : population (thermalApply D) r i = ‖shellVector D r i‖ ^ 2 := by
  unfold population
  rw [X7_thermal_unit, inner_self_eq_norm_sq_to_K]
  norm_cast

lemma X7_collinear_iff {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {v w : V}
    (hv : v ≠ 0) (hw : w ≠ 0) : Collinear v w ↔ ∃ c : ℂ, c ≠ 0 ∧ v = c • w := by
  constructor
  · rintro ⟨a, b, hab, h⟩
    have ha : a ≠ 0 := by
      rintro rfl
      have hb : b ≠ 0 := hab.resolve_left (by simp)
      simp only [zero_smul, zero_add] at h
      exact hw ((smul_eq_zero.mp h).resolve_left hb)
    refine ⟨-b / a, ?_, ?_⟩
    · intro h0
      have hb : b = 0 := by
        rcases div_eq_zero_iff.mp h0 with h1 | h1
        · exact neg_eq_zero.mp h1
        · exact absurd h1 ha
      subst hb
      simp only [zero_smul, add_zero] at h
      exact hv ((smul_eq_zero.mp h).resolve_left ha)
    · have : a • v = -(b • w) := eq_neg_of_add_eq_zero_left h
      calc v = a⁻¹ • (a • v) := by rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
        _ = (-b / a) • w := by rw [this, smul_neg, smul_smul, ← neg_smul]; congr 1; field_simp
  · rintro ⟨c, _, h⟩
    exact ⟨1, -c, Or.inl one_ne_zero, by rw [h, one_smul, neg_smul, add_neg_cancel]⟩


lemma X7_rep {d b : ℕ} {E : Fin d → ℝ} {beta : ℝ} (D : ThermalDilation E beta b) :
    (∀ r i, population (thermalApply D) r i = ‖shellVector D r i‖ ^ 2) ∧
    (∀ i j r s, E i - E j = E r - E s →
      thermalApply D (matrixUnit i j) r s = inner ℂ (shellVector D s j) (shellVector D r i)) ∧
    (∀ i j r s, E i - E j = E r - E s →
      ‖thermalApply D (matrixUnit i j) r s‖ ^ 2 ≤
        population (thermalApply D) r i * population (thermalApply D) s j) ∧
    (∀ i j r s, E i - E j = E r - E s →
      0 < population (thermalApply D) r i * population (thermalApply D) s j →
      (‖thermalApply D (matrixUnit i j) r s‖ ^ 2 =
        population (thermalApply D) r i * population (thermalApply D) s j ↔
          Collinear (shellVector D r i) (shellVector D s j))) := by
  have hprod : ∀ i j r s, population (thermalApply D) r i * population (thermalApply D) s j =
      (‖shellVector D s j‖ * ‖shellVector D r i‖) ^ 2 := by
    intro i j r s; rw [X7_thermal_pop, X7_thermal_pop]; ring
  refine ⟨X7_thermal_pop D, fun i j r s _ => X7_thermal_unit D i j r s, fun i j r s _ => ?_,
    fun i j r s _ hpos => ?_⟩
  · rw [hprod, X7_thermal_unit]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2
  · have hv : shellVector D r i ≠ 0 := by
      intro h0; rw [X7_thermal_pop, h0] at hpos; simp at hpos
    have hw : shellVector D s j ≠ 0 := by
      intro h0; rw [X7_thermal_pop D s j, h0] at hpos; simp at hpos
    rw [hprod, X7_thermal_unit, X7_collinear_iff hv hw, ← norm_inner_eq_norm_iff hw hv]
    constructor
    · intro h; exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h
    · intro h; rw [h]


lemma X7_unit_entry {d b : ℕ} {E : Fin d → ℝ} {beta : ℝ} (D : ThermalDilation E beta b)
    (i j r s : Fin d) :
    thermalApply D (matrixUnit i j) r s = ∑ a, thermalKraus D a r i * conj (thermalKraus D a s j) := by
  unfold thermalApply
  rw [X7_kraus_entry']
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [matrixUnit, Matrix.single_apply]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro q _ hq; simp [Ne.symm hq]
    · simp
  · intro p _ hp; simp [Ne.symm hp]
  · simp

lemma X7_expand {d b : ℕ} {E : Fin d → ℝ} {beta : ℝ} (D : ThermalDilation E beta b)
    (rho : Mat d) (r s : Fin d) :
    thermalApply D rho r s = ∑ a : Fin d × Fin d,
      rho a.1 a.2 * inner ℂ (shellVector D s a.2) (shellVector D r a.1) := by
  simp_rw [← X7_thermal_unit, X7_unit_entry]
  unfold thermalApply
  rw [X7_kraus_entry']
  conv_rhs => rw [Fintype.sum_prod_type]
  simp_rw [Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun a _ => ?_
  ring

lemma X7_inner_gap {d b : ℕ} {E : Fin d → ℝ} {beta : ℝ} (D : ThermalDilation E beta b)
    (i j r s : Fin d) (h : E i - E j ≠ E r - E s) :
    inner ℂ (shellVector D s j) (shellVector D r i) = 0 := by
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro a _
  simp only [shellVector, PiLp.toLp_apply]
  split_ifs with h1 h2
  · exact absurd (by linarith) h
  · simp
  · simp
  · simp

lemma X7_triangle_eq {ι : Type*} (S : Finset ι) (t : ι → ℂ) :
    ‖∑ a ∈ S, t a‖ = ∑ a ∈ S, ‖t a‖ ↔
      ∃ z : ℂ, ‖z‖ = 1 ∧ ∀ a ∈ S, t a ≠ 0 → ∃ l : ℝ, 0 ≤ l ∧ t a = (l : ℂ) * z := by
  constructor
  · intro h
    by_cases hS : ∑ a ∈ S, t a = 0
    · refine ⟨1, by simp, fun a ha hta => ?_⟩
      rw [hS, norm_zero, eq_comm, Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => norm_nonneg _)] at h
      exact absurd (norm_eq_zero.mp (h a ha)) hta
    · set T := ∑ a ∈ S, t a with hT
      have hTn : 0 < ‖T‖ := norm_pos_iff.mpr hS
      set z : ℂ := T / (‖T‖ : ℂ) with hz
      have hz1 : ‖z‖ = 1 := by
        rw [hz, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hTn, div_self hTn.ne']
      refine ⟨z, hz1, fun a ha _ => ?_⟩
      have hle : ∀ a ∈ S, (conj z * t a).re ≤ ‖t a‖ := by
        intro a _
        calc (conj z * t a).re ≤ ‖conj z * t a‖ := Complex.re_le_norm _
          _ = ‖t a‖ := by rw [norm_mul, Complex.norm_conj, hz1, one_mul]
      have hsum : ∑ a ∈ S, (conj z * t a).re = ∑ a ∈ S, ‖t a‖ := by
        rw [← Complex.re_sum, ← Finset.mul_sum, ← hT, ← h, hz]
        rw [map_div₀, Complex.conj_ofReal, div_mul_eq_mul_div, mul_comm (conj T), Complex.mul_conj']
        rw [← Complex.ofReal_pow, ← Complex.ofReal_div, Complex.ofReal_re, sq, mul_div_assoc,
          div_self hTn.ne', mul_one]
      have heq : (conj z * t a).re = ‖t a‖ := by
        have := (Finset.sum_eq_sum_iff_of_le hle).mp hsum
        exact this a ha
      have hn : ‖conj z * t a‖ = ‖t a‖ := by rw [norm_mul, Complex.norm_conj, hz1, one_mul]
      rw [← hn, Complex.re_eq_norm] at heq
      refine ⟨‖t a‖, norm_nonneg _, ?_⟩
      have hreal : conj z * t a = (‖t a‖ : ℂ) := by
        rw [← hn]
        apply Complex.ext
        · simp only [Complex.ofReal_re]
          exact (Complex.re_eq_norm.mpr heq)
        · simp only [Complex.ofReal_im]
          exact ((Complex.nonneg_iff.mp heq).2).symm
      have hzz : z * conj z = 1 := by
        rw [Complex.mul_conj', hz1]; simp
      calc t a = (z * conj z) * t a := by rw [hzz, one_mul]
        _ = z * (conj z * t a) := by ring
        _ = (‖t a‖ : ℂ) * z := by rw [hreal, mul_comm]
  · rintro ⟨z, hz1, hz⟩
    have key : ∀ a ∈ S, t a = (‖t a‖ : ℂ) * z := by
      intro a ha
      by_cases hta : t a = 0
      · simp [hta]
      · obtain ⟨l, hl, hlt⟩ := hz a ha hta
        have : ‖t a‖ = l := by rw [hlt, norm_mul, hz1, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hl]
        rw [this, hlt]
    rw [Finset.sum_congr rfl key, ← Finset.sum_mul, norm_mul, hz1, mul_one, ← Complex.ofReal_sum,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]

lemma X7_mode_main {d b : ℕ} {E : Fin d → ℝ} {beta : ℝ} (D : ThermalDilation E beta b)
    (rho : Mat d) (r s : Fin d) :
    ‖thermalApply D rho r s‖ ≤ modeBound E (thermalApply D) rho r s ∧
    (‖thermalApply D rho r s‖ = modeBound E (thermalApply D) rho r s ↔
      (∀ a ∈ contributors E (thermalApply D) rho r s,
        Collinear (shellVector D r a.1) (shellVector D s a.2)) ∧
      ∃ z : ℂ, ‖z‖ = 1 ∧ ∀ a ∈ contributors E (thermalApply D) rho r s,
        rho a.1 a.2 * inner ℂ (shellVector D s a.2) (shellVector D r a.1) ≠ 0 →
          ∃ l : ℝ, 0 ≤ l ∧
            rho a.1 a.2 * inner ℂ (shellVector D s a.2) (shellVector D r a.1) = (l : ℂ) * z) := by
  set C := contributors E (thermalApply D) rho r s with hC
  set t : Fin d × Fin d → ℂ := fun a =>
    rho a.1 a.2 * inner ℂ (shellVector D s a.2) (shellVector D r a.1) with ht
  set bd : Fin d × Fin d → ℝ := fun a =>
    ‖rho a.1 a.2‖ * Real.sqrt (population (thermalApply D) r a.1 * population (thermalApply D) s a.2)
    with hbd
  have hbdC : modeBound E (thermalApply D) rho r s = ∑ a ∈ C, bd a := rfl
  have hsq : ∀ a : Fin d × Fin d,
      Real.sqrt (population (thermalApply D) r a.1 * population (thermalApply D) s a.2) =
        ‖shellVector D s a.2‖ * ‖shellVector D r a.1‖ := by
    intro a
    rw [X7_thermal_pop, X7_thermal_pop, ← mul_pow, Real.sqrt_sq (by positivity), mul_comm]
  have hsumC : thermalApply D rho r s = ∑ a ∈ C, t a := by
    rw [X7_expand]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro a _ haC
    simp only [hC, contributors, Finset.mem_filter, Finset.mem_univ, true_and, not_and] at haC
    simp only [ht]
    by_cases hg : E a.1 - E a.2 = E r - E s
    · by_cases hr0 : rho a.1 a.2 = 0
      · simp [hr0]
      · have hpp := haC hg hr0
        rw [X7_thermal_pop, X7_thermal_pop] at hpp
        have : ‖shellVector D r a.1‖ ^ 2 * ‖shellVector D s a.2‖ ^ 2 = 0 := by
          apply le_antisymm (not_lt.mp hpp) (by positivity)
        rcases mul_eq_zero.mp this with h0 | h0
        · rw [norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h0)]; simp
        · rw [norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h0)]; simp
    · rw [X7_inner_gap D a.1 a.2 r s hg, mul_zero]
  have hle : ∀ a, ‖t a‖ ≤ bd a := by
    intro a
    simp only [ht, hbd, norm_mul, hsq]
    exact mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (norm_nonneg _)
  have hnz : ∀ a ∈ C, rho a.1 a.2 ≠ 0 ∧ shellVector D r a.1 ≠ 0 ∧ shellVector D s a.2 ≠ 0 := by
    intro a ha
    simp only [hC, contributors, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    obtain ⟨_, hr0, hpp⟩ := ha
    refine ⟨hr0, fun h0 => ?_, fun h0 => ?_⟩
    · rw [X7_thermal_pop, h0] at hpp; simp at hpp
    · rw [X7_thermal_pop D s, h0] at hpp; simp at hpp
  have heqiff : ∀ a ∈ C, (‖t a‖ = bd a ↔ Collinear (shellVector D r a.1) (shellVector D s a.2)) := by
    intro a ha
    obtain ⟨hr0, hv, hw⟩ := hnz a ha
    simp only [ht, hbd, norm_mul, hsq]
    rw [mul_right_inj' (norm_ne_zero_iff.mpr hr0), X7_collinear_iff hv hw,
      ← norm_inner_eq_norm_iff hw hv]
  have part1 : ‖thermalApply D rho r s‖ ≤ ∑ a ∈ C, ‖t a‖ := by
    rw [hsumC]; exact norm_sum_le _ _
  have part1' : ∑ a ∈ C, ‖t a‖ ≤ ∑ a ∈ C, bd a := Finset.sum_le_sum fun a _ => hle a
  refine ⟨hbdC ▸ part1.trans part1', ?_⟩
  rw [hbdC]
  constructor
  · intro h
    have h1 : ∑ a ∈ C, ‖t a‖ = ∑ a ∈ C, bd a := le_antisymm part1' (h ▸ part1)
    have h2 : ‖∑ a ∈ C, t a‖ = ∑ a ∈ C, ‖t a‖ := by rw [← hsumC, h1, h]
    refine ⟨fun a ha => (heqiff a ha).mp ((Finset.sum_eq_sum_iff_of_le fun a _ => hle a).mp h1 a ha), ?_⟩
    exact (X7_triangle_eq C t).mp h2
  · rintro ⟨hcol, hz⟩
    have h1 : ∑ a ∈ C, ‖t a‖ = ∑ a ∈ C, bd a :=
      Finset.sum_congr rfl fun a ha => (heqiff a ha).mpr (hcol a ha)
    rw [hsumC, (X7_triangle_eq C t).mpr hz, h1]

end

end QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P44 in
theorem solution {d b : ℕ} (hd : 0 < d) (E : Fin d → ℝ)
    (beta : ℝ) (D : ThermalDilation E beta b) (rho : Mat d)
    (hrho : IsDensityMatrix rho) (r s : Fin d) :
    ‖thermalApply D rho r s‖ ≤ modeBound E (thermalApply D) rho r s ∧
    (‖thermalApply D rho r s‖ = modeBound E (thermalApply D) rho r s ↔
      (∀ a ∈ contributors E (thermalApply D) rho r s,
        QAlgorithms.Papers.Independent.Information100.P44.Collinear (shellVector D r a.1) (shellVector D s a.2)) ∧
      ∃ z : ℂ, ‖z‖ = 1 ∧ ∀ a ∈ contributors E (thermalApply D) rho r s,
        let t := rho a.1 a.2 * inner ℂ (shellVector D s a.2) (shellVector D r a.1)
        t ≠ 0 → ∃ l : ℝ, 0 ≤ l ∧ t = (l : ℂ) * z) :=
  X7_mode_main D rho r s

end
