-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P44.saturationComponents
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T07:20:08.752919+00:00
-- url     : https://prove2.me/submissions/f59a2e5d-dff2-49a3-b0ab-adc135ed07ec

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

end

end QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P44 in
theorem solution {d b : ℕ} (hd : 0 < d) (E : Fin d → ℝ)
    (beta : ℝ) (D : ThermalDilation E beta b) (edges : TransferEdges d)
    (hgaps : ∀ e ∈ edges, E e.1.2 - E e.2.2 = E e.1.1 - E e.2.1)
    (hsat : JointElementary (thermalApply D) edges)
    (u : {a : Fin d × Fin d // shellVector D a.1 a.2 ≠ 0}) :
    ∃ v : EuclideanSpace ℂ (Fin b × Fin b), v ≠ 0 ∧
      ∀ z : {a : Fin d × Fin d // shellVector D a.1 a.2 ≠ 0},
        Relation.ReflTransGen (saturationAdj D edges) u z →
        ∃ c : ℂ, shellVector D z.val.1 z.val.2 = c • v := by
  -- along any selected edge the two shell vectors are proportional
  have hedge : ∀ y z : {a : Fin d × Fin d // shellVector D a.1 a.2 ≠ 0}, (y.val, z.val) ∈ edges →
      ∃ c : ℂ, c ≠ 0 ∧ shellVector D y.val.1 y.val.2 = c • shellVector D z.val.1 z.val.2 := by
    intro y z he
    have hpos : 0 < population (thermalApply D) y.val.1 y.val.2 *
        population (thermalApply D) z.val.1 z.val.2 := by
      rw [X7_thermal_pop, X7_thermal_pop]
      have := norm_pos_iff.mpr y.2
      have := norm_pos_iff.mpr z.2
      positivity
    have hg : E y.val.2 - E z.val.2 = E y.val.1 - E z.val.1 := hgaps _ he
    have hs := hsat (y.val, z.val) he
    have hcol := ((X7_rep D).2.2.2 y.val.2 z.val.2 y.val.1 z.val.1 hg hpos).mp hs
    exact (X7_collinear_iff y.2 z.2).mp hcol
  refine ⟨shellVector D u.val.1 u.val.2, u.2, fun z hz => ?_⟩
  induction hz with
  | refl => exact ⟨1, by rw [one_smul]⟩
  | @tail y z _ hyz ih =>
    obtain ⟨c, hc⟩ := ih
    rcases hyz.2 with he | he
    · obtain ⟨c', hc', h'⟩ := hedge y z he
      refine ⟨c'⁻¹ * c, ?_⟩
      rw [mul_smul, ← hc, h', smul_smul, inv_mul_cancel₀ hc', one_smul]
    · obtain ⟨c', _, h'⟩ := hedge z y he
      exact ⟨c' * c, by rw [h', hc, smul_smul]⟩

end
