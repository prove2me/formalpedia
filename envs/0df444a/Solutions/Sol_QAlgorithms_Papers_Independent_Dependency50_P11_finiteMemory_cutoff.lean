-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P11.finiteMemory_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T19:16:14.975983+00:00
-- url     : https://prove2.me/submissions/c448f79b-bb7a-478f-9134-835c63d9ff56

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P11
import Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P11_entropy_budget
noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P11

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P23 (Operator)

lemma S173D_cfc_trace {n : Type} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma S173D_ent_eq {d : ℕ} (σ : Operator d) (hσ : σ.IsHermitian) :
    vonNeumannEntropy σ = -∑ i, hσ.eigenvalues i * Real.log (hσ.eigenvalues i) := by
  unfold vonNeumannEntropy Information100.P39.quantumEntropy
  have h1 : ((1 : Information100.P39.Order) = ⊤) = False := by
    apply propext; constructor
    · intro h; exact WithTop.coe_ne_top h
    · intro h; exact h.elim
  rw [if_neg (by simp [h1]), if_pos (by rfl), S173D_cfc_trace hσ, Complex.re_sum]
  simp

lemma S173D_eig_sum {d : ℕ} (σ : Operator d) (hσ : IsDensityMatrix σ) :
    ∑ i, hσ.1.1.eigenvalues i = 1 := by
  have := hσ.1.1.trace_eq_sum_eigenvalues
  have h2 := hσ.2
  rw [this] at h2
  have h := congrArg Complex.re h2.symm
  simp only [Complex.one_re, Complex.re_sum, Complex.ofReal_re] at h
  exact h.symm

/-- pointwise: -λ log λ ≤ λ log d + (1/d - λ), strict unless λ = 1/d. -/
lemma S173D_pt {d : ℝ} (hd : 0 < d) {x : ℝ} (hx : 0 ≤ x) :
    -(x * Real.log x) ≤ x * Real.log d + (1 / d - x) := by
  rcases hx.lt_or_eq with hx | hx
  · have h := Real.log_le_sub_one_of_pos (show 0 < 1 / (d * x) by positivity)
    rw [Real.log_div (by norm_num) (by positivity), Real.log_one, Real.log_mul hd.ne' hx.ne'] at h
    have : x * (1 / (d * x)) = 1 / d := by field_simp
    nlinarith
  · subst hx; simp; positivity

lemma S173D_pt_strict {d : ℝ} (hd : 0 < d) {x : ℝ} (hx : 0 ≤ x) (hne : x ≠ 1 / d) :
    -(x * Real.log x) < x * Real.log d + (1 / d - x) := by
  rcases hx.lt_or_eq with hx | hx
  · have hne' : 1 / (d * x) ≠ 1 := by
      intro h; apply hne; field_simp at h ⊢; linarith
    have h := Real.log_lt_sub_one_of_pos (show 0 < 1 / (d * x) by positivity) hne'
    rw [Real.log_div (by norm_num) (by positivity), Real.log_one, Real.log_mul hd.ne' hx.ne'] at h
    have : x * (1 / (d * x)) = 1 / d := by field_simp
    nlinarith
  · subst hx; simp; positivity

lemma S173D_ent_le {d : ℕ} (hd : 0 < d) (σ : Operator d) (hσ : IsDensityMatrix σ) :
    vonNeumannEntropy σ ≤ Real.log d := by
  rw [S173D_ent_eq σ hσ.1.1]
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hs := S173D_eig_sum σ hσ
  have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
    S173D_pt hdr (hσ.1.eigenvalues_nonneg i)
  have h2 : ∑ i, (hσ.1.1.eigenvalues i * Real.log d + (1 / d - hσ.1.1.eigenvalues i)) = Real.log d := by
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib, hs]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp; ring
  rw [← Finset.sum_neg_distrib]
  linarith

lemma S173D_ent_lt {d : ℕ} (hd : 0 < d) (σ : Operator d) (hσ : IsDensityMatrix σ)
    (hne : σ ≠ totalMixture d) : vonNeumannEntropy σ < Real.log d := by
  rw [S173D_ent_eq σ hσ.1.1]
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hs := S173D_eig_sum σ hσ
  have hex : ∃ i, hσ.1.1.eigenvalues i ≠ 1 / d := by
    by_contra hall
    push_neg at hall
    apply hne
    rw [hσ.1.1.spectral_theorem, Unitary.conjStarAlgAut_apply]
    have : (Matrix.diagonal (RCLike.ofReal ∘ hσ.1.1.eigenvalues) : Operator d) =
        ((d : ℂ)⁻¹) • (1 : Operator d) := by
      ext i j
      simp only [Matrix.diagonal_apply, Function.comp_apply, hall, Matrix.smul_apply,
        Matrix.one_apply, smul_eq_mul]
      split_ifs <;> simp
    rw [this, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      Unitary.mul_star_self_of_mem hσ.1.1.eigenvectorUnitary.2]
    rfl
  obtain ⟨i0, hi0⟩ := hex
  have := Finset.sum_lt_sum (fun i (_ : i ∈ Finset.univ) => S173D_pt hdr (hσ.1.eigenvalues_nonneg i))
    ⟨i0, Finset.mem_univ _, S173D_pt_strict hdr (hσ.1.eigenvalues_nonneg i0) hi0⟩
  have h2 : ∑ i, (hσ.1.1.eigenvalues i * Real.log d + (1 / d - hσ.1.1.eigenvalues i)) = Real.log d := by
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib, hs]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp; ring
  rw [← Finset.sum_neg_distrib]
  linarith

lemma S173D_ent_nonneg {d : ℕ} (σ : Operator d) (hσ : IsDensityMatrix σ) :
    0 ≤ vonNeumannEntropy σ := by
  rw [S173D_ent_eq σ hσ.1.1, neg_nonneg]
  have hs := S173D_eig_sum σ hσ
  refine Finset.sum_nonpos fun i _ => Real.mul_log_nonpos (hσ.1.eigenvalues_nonneg i) ?_
  rw [← hs]
  exact Finset.single_le_sum (fun j _ => hσ.1.eigenvalues_nonneg j) (Finset.mem_univ i)

lemma S173D_ent_mix {d : ℕ} (hd : 0 < d) : vonNeumannEntropy (totalMixture d) = Real.log d := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  unfold vonNeumannEntropy Information100.P39.quantumEntropy totalMixture
  have h1 : ((1 : Information100.P39.Order) = ⊤) = False := by
    apply propext; constructor
    · intro h; exact WithTop.coe_ne_top h
    · intro h; exact h.elim
  rw [if_neg (by simp [h1]), if_pos (by rfl)]
  have e : ((d : ℂ)⁻¹ • (1 : Operator d)) = algebraMap ℝ (Operator d) ((d : ℝ)⁻¹) := by
    rw [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul]; push_cast; rfl
  rw [e, cfc_algebraMap, Algebra.algebraMap_eq_smul_one, Matrix.trace_smul, Matrix.trace_one]
  simp only [Fintype.card_fin]
  rw [Real.log_inv]
  simp
  rw [← Complex.ofReal_natCast, Complex.log_ofReal_re]
  field_simp

lemma S173D_kraus_dens {d : ℕ} (E : Superop (Fin d) (Fin d)) (hE : IsChannel E) (ρ : Operator d)
    (hρ : IsDensityMatrix ρ) : IsDensityMatrix (E ρ) := by
  obtain ⟨k, K, hK, hEK⟩ := hE
  rw [hEK]
  refine ⟨Matrix.posSemidef_sum _ fun j _ => hρ.1.mul_mul_conjTranspose_same (K j), ?_⟩
  unfold krausApply
  rw [Matrix.trace_sum]
  simp_rw [Matrix.trace_mul_cycle (K _) ρ]
  rw [← Matrix.trace_sum, ← Finset.sum_mul]
  have : ∑ j, (K j)ᴴ * K j = 1 := hK
  rw [this, Matrix.one_mul, hρ.2]

lemma S173D_mix_dens {d : ℕ} (hd : 0 < d) : IsDensityMatrix (totalMixture d) := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  unfold totalMixture
  refine ⟨?_, ?_⟩
  · have : ((d : ℂ)⁻¹) = (((d : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    rw [this]
    exact Matrix.PosSemidef.one.smul (by positivity)
  · rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
    exact inv_mul_cancel₀ (by exact_mod_cast hd.ne')

lemma S173D_mix_ne {d : ℕ} (hd : 0 < d) (E : Superop (Fin d) (Fin d)) (hE : IsChannel E)
    (hNU : ¬ IsUnital E) : E (totalMixture d) ≠ totalMixture d := by
  intro h
  apply hNU
  obtain ⟨k, K, hK, hEK⟩ := hE
  have hlin : E (totalMixture d) = ((d : ℂ)⁻¹) • E 1 := by
    rw [hEK, hEK]; unfold krausApply totalMixture
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [hlin] at h
  unfold totalMixture at h
  have hd' : (d : ℂ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast hd.ne')
  exact smul_right_injective _ hd' h

lemma S173D_delta_pos {d : ℕ} (hd : 0 < d) (E : Superop (Fin d) (Fin d)) (hE : IsChannel E)
    (hNU : ¬ IsUnital E) : 0 < entropyDecrease E (totalMixture d) := by
  unfold entropyDecrease
  rw [S173D_ent_mix hd]
  have := S173D_ent_lt hd _ (S173D_kraus_dens E hE _ (S173D_mix_dens hd)) (S173D_mix_ne hd E hE hNU)
  linarith

end QAlgorithms.Papers.Independent.Dependency50.P11

open QAlgorithms
open QAlgorithms.Papers.Independent.Information100.P23 (Operator)
open QAlgorithms.Papers.Independent.Dependency50.P11 in
theorem solution {d : ℕ} (hd : 0 < d)
    (E : Superop (Fin d) (Fin d)) (hE : IsChannel E) (hNU : ¬ IsUnital E)
    (m : ℕ) (hm : 0 < m) :
    ∃ n : ℕ, 0 < n ∧ Real.log (m : ℝ) / maxEntropyDecrease E < (n : ℝ) ∧
      ¬ ∃ D : MemoryDevice d m, RepeatableFor D E n := by
  have hΔ := S173D_delta_pos hd E hE hNU
  have hbdd : BddAbove {t : ℝ | ∃ rho : Operator d, IsDensityMatrix rho ∧ t = entropyDecrease E rho} := by
    refine ⟨Real.log d, ?_⟩
    rintro t ⟨ρ, hρ, rfl⟩
    unfold entropyDecrease
    have := S173D_ent_le hd ρ hρ
    have := S173D_ent_nonneg (E ρ) (S173D_kraus_dens E hE ρ hρ)
    linarith
  have hmax : entropyDecrease E (totalMixture d) ≤ maxEntropyDecrease E :=
    le_csSup hbdd ⟨totalMixture d, S173D_mix_dens hd, rfl⟩
  have hpos : 0 < maxEntropyDecrease E := lt_of_lt_of_le hΔ hmax
  refine ⟨⌊Real.log m / maxEntropyDecrease E⌋₊ + 1, Nat.succ_pos _, ?_, ?_⟩
  · push_cast; exact Nat.lt_floor_add_one _
  · rintro ⟨D, hD⟩
    set n := ⌊Real.log m / maxEntropyDecrease E⌋₊ + 1
    have hnpos : (0 : ℝ) < n := by positivity
    have hle : maxEntropyDecrease E ≤ Real.log m / n := by
      unfold maxEntropyDecrease
      refine csSup_le ⟨entropyDecrease E (totalMixture d), totalMixture d, S173D_mix_dens hd, rfl⟩ ?_
      rintro t ⟨ρ, hρ, rfl⟩
      have h := entropy_budget hd D E hE n hD ρ hρ
      rw [le_div_iff₀ hnpos]
      linarith [h.1, h.2]
    have hlt : Real.log m / maxEntropyDecrease E < n := by
      simp only [n]; push_cast; exact Nat.lt_floor_add_one _
    rw [div_lt_iff₀ hpos] at hlt
    rw [le_div_iff₀ hnpos] at hle
    linarith
