-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P38.coherence_robustness_advantage_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T06:48:29.865806+00:00
-- url     : https://prove2.me/submissions/ed37805d-0762-4cf7-a1c5-040b2f0fcd4e

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P38
noncomputable section
namespace QAlgorithms.Papers.Independent.Information100.P38
open scoped ComplexConjugate Matrix ComplexOrder

lemma s199a_energy_lb {d : ℕ} (E : Fin d → ℝ) (Y : Matrix (Fin d) (Fin d) ℂ)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    -((∑ i, |E i|) * ∑ k, ∑ l, ‖Y k l‖) ≤ energyExpectation E (U * Y * Uᴴ) := by
  unfold energyExpectation
  rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum (fun i _ => ?_)
  have hb : ‖(U * Y * Uᴴ) i i‖ ≤ ∑ k, ∑ l, ‖Y k l‖ := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    calc ‖∑ l, (∑ k, U i k * Y k l) * star (U i l)‖ ≤ ∑ l, ‖(∑ k, U i k * Y k l) * star (U i l)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ l, ∑ k, ‖Y k l‖ := by
          refine Finset.sum_le_sum (fun l _ => ?_)
          rw [norm_mul, norm_star]
          have h1 : ‖U i l‖ ≤ 1 := entry_norm_bound_of_unitary hU i l
          calc ‖∑ k, U i k * Y k l‖ * ‖U i l‖ ≤ ‖∑ k, U i k * Y k l‖ * 1 := by gcongr
            _ ≤ ∑ k, ‖Y k l‖ := by
              rw [mul_one]
              refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k _ => ?_))
              rw [norm_mul]
              have h2 : ‖U i k‖ ≤ 1 := entry_norm_bound_of_unitary hU i k
              calc ‖U i k‖ * ‖Y k l‖ ≤ 1 * ‖Y k l‖ := by gcongr
                _ = ‖Y k l‖ := one_mul _
      _ = ∑ k, ∑ l, ‖Y k l‖ := Finset.sum_comm
  have hre : |((U * Y * Uᴴ) i i).re| ≤ ∑ k, ∑ l, ‖Y k l‖ := (Complex.abs_re_le_norm _).trans hb
  have hE : -(|E i| * ∑ k, ∑ l, ‖Y k l‖) ≤ E i * ((U * Y * Uᴴ) i i).re := by
    have := abs_mul (E i) ((U * Y * Uᴴ) i i).re
    have h3 : |E i * ((U * Y * Uᴴ) i i).re| ≤ |E i| * ∑ k, ∑ l, ‖Y k l‖ := by
      rw [this]; exact mul_le_mul_of_nonneg_left hre (abs_nonneg _)
    linarith [neg_abs_le (E i * ((U * Y * Uᴴ) i i).re)]
  exact hE

lemma s199a_bdd {d : ℕ} (E : Fin d → ℝ) (Y : Matrix (Fin d) (Fin d) ℂ) :
    BddBelow {r | ∃ U : Matrix.unitaryGroup (Fin d) ℂ,
      r = energyExpectation E ((U : Matrix (Fin d) (Fin d) ℂ) * Y * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ)} := by
  refine ⟨-((∑ i, |E i|) * ∑ k, ∑ l, ‖Y k l‖), ?_⟩
  rintro r ⟨U, rfl⟩
  exact s199a_energy_lb E Y U U.2

lemma s199a_passive_le_U {d : ℕ} (E : Fin d → ℝ) (Y U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    passiveEnergy E Y ≤ energyExpectation E (U * Y * Uᴴ) := by
  unfold passiveEnergy
  exact csInf_le (s199a_bdd E Y) ⟨⟨U, hU⟩, rfl⟩

lemma s199a_energy_sub {d : ℕ} (E : Fin d → ℝ) (A B : Matrix (Fin d) (Fin d) ℂ) :
    energyExpectation E (A - B) = energyExpectation E A - energyExpectation E B := by
  unfold energyExpectation
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [Matrix.sub_apply]; ring

/-- Lipschitz bound for passive energy. -/
lemma s199a_passive_lip {d : ℕ} (E : Fin d → ℝ) (Y Y' : Matrix (Fin d) (Fin d) ℂ) :
    passiveEnergy E Y ≤ passiveEnergy E Y' + (∑ i, |E i|) * ∑ k, ∑ l, ‖Y k l - Y' k l‖ := by
  have key : ∀ U : Matrix.unitaryGroup (Fin d) ℂ,
      passiveEnergy E Y - (∑ i, |E i|) * ∑ k, ∑ l, ‖Y k l - Y' k l‖ ≤
        energyExpectation E ((U : Matrix (Fin d) (Fin d) ℂ) * Y' * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) := by
    intro U
    have h1 := s199a_passive_le_U E Y U U.2
    have h2 := s199a_energy_lb E (Y' - Y) U U.2
    have h3 : (U : Matrix (Fin d) (Fin d) ℂ) * (Y' - Y) * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ =
        U * Y' * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ - U * Y * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ := by
      rw [Matrix.mul_sub, Matrix.sub_mul]
    rw [h3, s199a_energy_sub] at h2
    have h4 : ∑ k, ∑ l, ‖(Y' - Y) k l‖ = ∑ k, ∑ l, ‖Y k l - Y' k l‖ := by
      refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
      rw [Matrix.sub_apply, norm_sub_rev]
    rw [h4] at h2
    linarith
  have : passiveEnergy E Y - (∑ i, |E i|) * ∑ k, ∑ l, ‖Y k l - Y' k l‖ ≤ passiveEnergy E Y' := by
    conv_rhs => unfold passiveEnergy
    refine le_csInf ⟨_, 1, rfl⟩ ?_
    rintro r ⟨U, rfl⟩
    exact key U
  linarith

lemma s199a_passive_cont {d : ℕ} (E : Fin d → ℝ) : Continuous (passiveEnergy E (d := d)) := by
  rw [continuous_iff_continuousAt]
  intro Y0
  set K := ∑ i, |E i|
  have hh : Continuous (fun Y : Matrix (Fin d) (Fin d) ℂ => ∑ k, ∑ l, ‖Y k l - Y0 k l‖) := by
    fun_prop
  have hlo : Filter.Tendsto (fun Y : Matrix (Fin d) (Fin d) ℂ =>
      passiveEnergy E Y0 - K * ∑ k, ∑ l, ‖Y k l - Y0 k l‖) (nhds Y0) (nhds (passiveEnergy E Y0)) := by
    have hc : Continuous (fun Y : Matrix (Fin d) (Fin d) ℂ =>
        passiveEnergy E Y0 - K * ∑ k, ∑ l, ‖Y k l - Y0 k l‖) := by fun_prop
    simpa using hc.tendsto Y0
  have hhi : Filter.Tendsto (fun Y : Matrix (Fin d) (Fin d) ℂ =>
      passiveEnergy E Y0 + K * ∑ k, ∑ l, ‖Y k l - Y0 k l‖) (nhds Y0) (nhds (passiveEnergy E Y0)) := by
    have hc : Continuous (fun Y : Matrix (Fin d) (Fin d) ℂ =>
        passiveEnergy E Y0 + K * ∑ k, ∑ l, ‖Y k l - Y0 k l‖) := by fun_prop
    simpa using hc.tendsto Y0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi (fun Y => ?_) (fun Y => ?_)
  · have := s199a_passive_lip E Y0 Y
    have h4 : ∑ k, ∑ l, ‖Y0 k l - Y k l‖ = ∑ k, ∑ l, ‖Y k l - Y0 k l‖ := by
      refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
      rw [norm_sub_rev]
    rw [h4] at this
    change _ ≤ _ + K * _ at this
    simp only; linarith
  · exact s199a_passive_lip E Y Y0

lemma s199a_nonneg {z : ℂ} (h : 0 ≤ z) : 0 ≤ z.re ∧ z.im = 0 := by
  obtain ⟨a, b⟩ := Complex.nonneg_iff.1 h
  exact ⟨a, b.symm⟩

lemma s199a_diag {d : ℕ} {Y : Matrix (Fin d) (Fin d) ℂ} (hY : IsDensityMatrix Y) :
    (∀ i, 0 ≤ (Y i i).re ∧ (Y i i).im = 0) ∧ ∑ i, (Y i i).re = 1 := by
  refine ⟨fun i => s199a_nonneg hY.1.diag_nonneg, ?_⟩
  have := congrArg Complex.re hY.2
  simpa [Matrix.trace, Complex.re_sum] using this

lemma s199a_diag_le {d : ℕ} {Y : Matrix (Fin d) (Fin d) ℂ} (hY : IsDensityMatrix Y) (i : Fin d) :
    (Y i i).re ≤ 1 := by
  obtain ⟨h0, h1⟩ := s199a_diag hY
  rw [← h1]
  exact Finset.single_le_sum (f := fun i => (Y i i).re) (fun j _ => (h0 j).1) (Finset.mem_univ i)

lemma s199a_conj_density {d : ℕ} {Y : Matrix (Fin d) (Fin d) ℂ} (hY : IsDensityMatrix Y)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    IsDensityMatrix (U * Y * Uᴴ) := by
  refine ⟨hY.1.mul_mul_conjTranspose_same U, ?_⟩
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose,
    Matrix.mem_unitaryGroup_iff'.1 hU, Matrix.one_mul, hY.2]

lemma s199a_entry_sq {d : ℕ} {X : Matrix (Fin d) (Fin d) ℂ} (hX : X.PosSemidef) (k l : Fin d) :
    Complex.normSq (X k l) ≤ (X k k).re * (X l l).re := by
  by_cases hkl : k = l
  · subst hkl
    have := s199a_nonneg (hX.diag_nonneg (i := k))
    rw [Complex.normSq_apply, this.2]; simp
  · have h2 := (hX.submatrix ![k, l]).det_nonneg
    rw [Matrix.det_fin_two] at h2
    simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h2
    have hh : X l k = star (X k l) := (hX.1.apply l k).symm
    rw [hh] at h2
    have h3 := (s199a_nonneg h2).1
    have hk := s199a_nonneg (hX.diag_nonneg (i := k))
    have hl := s199a_nonneg (hX.diag_nonneg (i := l))
    simp only [Complex.sub_re, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im,
      hk.2, hl.2] at h3
    rw [Complex.normSq_apply]
    nlinarith

lemma s199a_entry_le {d : ℕ} {X : Matrix (Fin d) (Fin d) ℂ} (hX : IsDensityMatrix X) (k l : Fin d) :
    ‖X k l‖ ≤ 1 := by
  have h1 := s199a_entry_sq hX.1 k l
  have h2 := s199a_diag_le hX k
  have h3 := s199a_diag_le hX l
  have h4 := ((s199a_diag hX).1 k).1
  have h5 := ((s199a_diag hX).1 l).1
  have h6 : ‖X k l‖ ^ 2 ≤ 1 := by
    rw [← Complex.normSq_eq_norm_sq]
    nlinarith
  nlinarith [norm_nonneg (X k l)]

lemma s199a_dens_closed (d : ℕ) : IsClosed {X : Matrix (Fin d) (Fin d) ℂ | IsDensityMatrix X} := by
  have : {X : Matrix (Fin d) (Fin d) ℂ | IsDensityMatrix X} =
      ({X | Xᴴ = X} ∩ ⋂ x : Fin d → ℂ, {X | 0 ≤ star x ⬝ᵥ (X *ᵥ x)}) ∩ {X | X.trace = 1} := by
    ext X
    simp [IsDensityMatrix, Matrix.posSemidef_iff_dotProduct_mulVec, Matrix.IsHermitian]
  rw [this]
  refine IsClosed.inter (IsClosed.inter ?_ (isClosed_iInter (fun x => ?_))) ?_
  · exact isClosed_eq (by fun_prop) continuous_id
  · exact isClosed_le continuous_const (by fun_prop)
  · exact isClosed_eq (by fun_prop) continuous_const

lemma s199a_dens_compact (d : ℕ) : IsCompact {X : Matrix (Fin d) (Fin d) ℂ | IsDensityMatrix X} := by
  have hK : IsCompact (Set.univ.pi fun _ : Fin d => Set.univ.pi fun _ : Fin d => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_closedBall _ _))
  refine IsCompact.of_isClosed_subset hK (s199a_dens_closed d) ?_
  intro X hX
  exact Set.mem_univ_pi.2 (fun k => Set.mem_univ_pi.2 (fun l => by
    rw [Metric.mem_closedBall, dist_zero_right]; exact s199a_entry_le hX k l))

def s199a_perm {d : ℕ} (σ : Equiv.Perm (Fin d)) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun k l => if l = σ k then 1 else 0

lemma s199a_perm_diag {d : ℕ} (σ : Equiv.Perm (Fin d)) (a : Fin d → ℂ) :
    s199a_perm σ * Matrix.diagonal a * (s199a_perm σ)ᴴ = Matrix.diagonal (fun k => a (σ k)) := by
  ext k m
  simp only [s199a_perm, Matrix.mul_apply, Matrix.of_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply]
  simp [Finset.sum_ite_eq', ite_mul, mul_ite, σ.injective.eq_iff]
  split_ifs <;> simp_all

lemma s199a_perm_unitary {d : ℕ} (σ : Equiv.Perm (Fin d)) : s199a_perm σ ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have := s199a_perm_diag σ (fun _ => 1)
  simpa [Matrix.diagonal_one, Matrix.star_eq_conjTranspose] using this

lemma s199a_energy_diag {d : ℕ} (E : Fin d → ℝ) (b : Fin d → ℂ) :
    energyExpectation E (Matrix.diagonal b) = ∑ k, E k * (b k).re := by
  simp [energyExpectation]

lemma s199a_PD_perm {d : ℕ} (E : Fin d → ℝ) (X : Matrix (Fin d) (Fin d) ℂ) (σ : Equiv.Perm (Fin d)) :
    passiveEnergy E (energyDephasing X) ≤ ∑ k, E k * (X (σ k) (σ k)).re := by
  have := s199a_passive_le_U E (energyDephasing X) (s199a_perm σ) (s199a_perm_unitary σ)
  rwa [energyDephasing, s199a_perm_diag, s199a_energy_diag] at this

lemma s199a_perm_avg {d : ℕ} [NeZero d] (E p : Fin d → ℝ) (τ : Equiv.Perm (Fin d)) :
    ∑ c : Fin d, ∑ k, E k * p ((τ.trans (Equiv.addRight c)) k) = (∑ k, E k) * ∑ k, p k := by
  simp only [Equiv.trans_apply, Equiv.coe_addRight]
  rw [Finset.sum_comm, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← Finset.mul_sum]
  congr 1
  exact Fintype.sum_equiv (Equiv.addLeft (τ k)) _ _ (fun c => rfl)

lemma s199a_PD_le {d : ℕ} [NeZero d] (E : Fin d → ℝ) {X : Matrix (Fin d) (Fin d) ℂ}
    (hX : IsDensityMatrix X) : passiveEnergy E (energyDephasing X) * d ≤ ∑ k, E k := by
  have h := s199a_perm_avg E (fun k => (X k k).re) 1
  rw [(s199a_diag hX).2, mul_one] at h
  rw [← h]
  calc passiveEnergy E (energyDephasing X) * d = ∑ _c : Fin d, passiveEnergy E (energyDephasing X) := by
        simp [mul_comm]
    _ ≤ _ := Finset.sum_le_sum (fun c _ => s199a_PD_perm E X _)

lemma s199a_ground {d : ℕ} (hd : 0 < d) (E : Fin d → ℝ) (hE : Monotone E)
    {ρ : Matrix (Fin d) (Fin d) ℂ} (hρ : IsDensityMatrix ρ) : E ⟨0, hd⟩ ≤ passiveEnergy E ρ := by
  unfold passiveEnergy
  refine le_csInf ⟨_, 1, rfl⟩ ?_
  rintro r ⟨U, rfl⟩
  have hY := s199a_conj_density hρ U U.2
  obtain ⟨h0, h1⟩ := s199a_diag hY
  unfold energyExpectation
  calc E ⟨0, hd⟩ = ∑ i, E ⟨0, hd⟩ * (((U : Matrix (Fin d) (Fin d) ℂ) * ρ * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) i i).re := by
        rw [← Finset.mul_sum, h1, mul_one]
    _ ≤ _ := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right
        (hE (show (⟨0, hd⟩ : Fin d) ≤ i from Nat.zero_le _)) (h0 i).1)


open scoped MatrixOrder in
lemma s199a_trace_nonneg {d : ℕ} {M X : Matrix (Fin d) (Fin d) ℂ} (hM : M.PosSemidef) (hX : X.PosSemidef) :
    0 ≤ (M * X).trace := by
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM.nonneg
  rw [Matrix.star_eq_conjTranspose, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc]
  exact (hX.mul_mul_conjTranspose_same B).trace_nonneg


def s199a_t {d n : ℕ} (M : Fin n → Matrix (Fin d) (Fin d) ℂ) (X : Matrix (Fin d) (Fin d) ℂ) (u : Fin n) : ℂ :=
  if (M u).trace = 0 then 0 else (M u * X).trace / (M u).trace

lemma s199a_CG_eq {d n : ℕ} (M : Fin n → Matrix (Fin d) (Fin d) ℂ) (X : Matrix (Fin d) (Fin d) ℂ) :
    ergotropicCoarseGraining M X = ∑ u, s199a_t M X u • M u := by
  unfold ergotropicCoarseGraining s199a_t
  refine Finset.sum_congr rfl (fun u _ => ?_)
  split_ifs <;> simp

lemma s199a_t_nonneg {d n : ℕ} {M : Fin n → Matrix (Fin d) (Fin d) ℂ} (hM : IsPOVM M)
    {X : Matrix (Fin d) (Fin d) ℂ} (hX : X.PosSemidef) (u : Fin n) : 0 ≤ s199a_t M X u := by
  unfold s199a_t
  split_ifs with h
  · exact le_refl _
  · exact div_nonneg (s199a_trace_nonneg (hM.1 u) hX) (hM.1 u).trace_nonneg

lemma s199a_t_mul {d n : ℕ} {M : Fin n → Matrix (Fin d) (Fin d) ℂ} (hM : IsPOVM M)
    (X : Matrix (Fin d) (Fin d) ℂ) (u : Fin n) : s199a_t M X u * (M u).trace = (M u * X).trace := by
  unfold s199a_t
  split_ifs with h
  · have : M u = 0 := ((hM.1 u).trace_eq_zero_iff).1 h
    simp [this]
  · field_simp

lemma s199a_sum_trace {d n : ℕ} {M : Fin n → Matrix (Fin d) (Fin d) ℂ} (hM : IsPOVM M)
    (X : Matrix (Fin d) (Fin d) ℂ) : ∑ u, (M u * X).trace = X.trace := by
  rw [← Matrix.trace_sum, ← Finset.sum_mul, hM.2, Matrix.one_mul]

lemma s199a_CG_density {d n : ℕ} {M : Fin n → Matrix (Fin d) (Fin d) ℂ} (hM : IsPOVM M)
    {X : Matrix (Fin d) (Fin d) ℂ} (hX : IsDensityMatrix X) : IsDensityMatrix (ergotropicCoarseGraining M X) := by
  rw [s199a_CG_eq]
  refine ⟨Matrix.posSemidef_sum _ (fun u _ => (hM.1 u).smul (s199a_t_nonneg hM hX.1 u)), ?_⟩
  rw [Matrix.trace_sum]
  simp only [Matrix.trace_smul, smul_eq_mul, s199a_t_mul hM]
  rw [s199a_sum_trace hM, hX.2]

lemma s199a_val {d n : ℕ} (E : Fin d → ℝ) (M : Fin n → Matrix (Fin d) (Fin d) ℂ) (X : Matrix (Fin d) (Fin d) ℂ) :
    observationalErgotropy E M X - incoherentErgotropy E X =
      passiveEnergy E (energyDephasing X) - passiveEnergy E (ergotropicCoarseGraining M X) := by
  unfold observationalErgotropy incoherentErgotropy
  have : energyExpectation E (energyDephasing X) = energyExpectation E X := by
    simp [energyExpectation, energyDephasing]
  rw [this]; ring

lemma s199c_off0 {d : ℕ} (hd : 0 < d) {G X : Matrix (Fin d) (Fin d) ℂ} (hG : G.PosSemidef)
    (hG1 : (1 - G).PosSemidef) (hX : IsDensityMatrix X) :
    (G * X).trace.re - ∑ i, (G i i).re * (X i i).re ≤ ((d : ℝ) - 1) / d := by
  have hg0 : ∀ i, 0 ≤ (G i i).re := fun i => (s199a_nonneg (hG.diag_nonneg (i := i))).1
  have hp0 : ∀ i, 0 ≤ (X i i).re := fun i => ((s199a_diag hX).1 i).1
  let b : Fin d → ℝ := fun i => Real.sqrt ((G i i).re * (X i i).re)
  have hb0 : ∀ i, 0 ≤ b i := fun i => Real.sqrt_nonneg _
  have hb2 : ∀ i, b i ^ 2 = (G i i).re * (X i i).re := fun i => Real.sq_sqrt (mul_nonneg (hg0 i) (hp0 i))
  have hT1 : (G * X).trace.re ≤ 1 := by
    have h := s199a_trace_nonneg hG1 hX.1
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, hX.2] at h
    have := (s199a_nonneg h).1
    simp only [Complex.sub_re, Complex.one_re] at this
    linarith
  have hT2 : (G * X).trace.re ≤ (∑ i, b i) ^ 2 := by
    calc (G * X).trace.re ≤ ‖(G * X).trace‖ := Complex.re_le_norm _
      _ ≤ ∑ i, ∑ k, ‖G i k‖ * ‖X k i‖ := by
          simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => (norm_sum_le _ _).trans
            (le_of_eq ?_)))
          simp
      _ ≤ ∑ i, ∑ k, b i * b k := by
          refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun k _ => ?_))
          have h1 := s199a_entry_sq hG i k
          have h2 := s199a_entry_sq hX.1 k i
          rw [Complex.normSq_eq_norm_sq] at h1 h2
          have hbb : (b i * b k) ^ 2 = ((G i i).re * (G k k).re) * ((X k k).re * (X i i).re) := by
            rw [mul_pow, hb2, hb2]; ring
          have : (‖G i k‖ * ‖X k i‖) ^ 2 ≤ (b i * b k) ^ 2 := by
            rw [hbb, mul_pow]
            exact mul_le_mul h1 h2 (sq_nonneg _) (mul_nonneg (hg0 _) (hg0 _))
          exact (pow_le_pow_iff_left₀ (by positivity) (mul_nonneg (hb0 i) (hb0 k)) two_ne_zero).1 this
      _ = (∑ i, b i) ^ 2 := by rw [sq, Finset.sum_mul_sum]
  have hS : ∑ i, (G i i).re * (X i i).re = ∑ i, b i ^ 2 := by simp only [hb2]
  have hC : (∑ i, b i) ^ 2 ≤ d * ∑ i, b i ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := b)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  rw [le_div_iff₀ hdR, hS]
  set s := (∑ i, b i) ^ 2
  set t := ∑ i, b i ^ 2
  rcases le_or_gt s 1 with h | h
  · nlinarith
  · nlinarith

lemma s199c_off {d : ℕ} (hd : 0 < d) {G X : Matrix (Fin d) (Fin d) ℂ} (hG : G.PosSemidef)
    (hG1 : (1 - G).PosSemidef) (hX : IsDensityMatrix X) :
    ∑ i, (G i i).re * (X i i).re - (G * X).trace.re ≤ ((d : ℝ) - 1) / d := by
  have h := s199c_off0 hd hG1 (by rw [sub_sub_cancel]; exact hG) hX
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, hX.2] at h
  have hs := (s199a_diag hX).2
  simp only [Matrix.sub_apply, Matrix.one_apply_eq, Complex.sub_re, Complex.one_re, sub_mul, one_mul,
    Finset.sum_sub_distrib, hs] at h
  linarith

lemma s199c_selfadj {d n : ℕ} (M : Fin n → Matrix (Fin d) (Fin d) ℂ) (Q X : Matrix (Fin d) (Fin d) ℂ) :
    (Q * ergotropicCoarseGraining M X).trace = (ergotropicCoarseGraining M Q * X).trace := by
  rw [s199a_CG_eq, s199a_CG_eq, Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]
  unfold s199a_t
  split_ifs with h
  · simp
  · rw [Matrix.trace_mul_comm Q (M u)]; ring

lemma s199c_t_le {d n : ℕ} {M : Fin n → Matrix (Fin d) (Fin d) ℂ} (hM : IsPOVM M)
    {Q : Matrix (Fin d) (Fin d) ℂ} (hQ : Q.PosSemidef) (hQ1 : (1 - Q).PosSemidef) (u : Fin n) :
    0 ≤ 1 - s199a_t M Q u := by
  have ht := s199a_t_nonneg hM hQ u
  obtain ⟨ht0, hti⟩ := s199a_nonneg ht
  have hmul := s199a_t_mul hM Q u
  have h1 := s199a_trace_nonneg (hM.1 u) hQ1
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, ← hmul] at h1
  obtain ⟨hc0, hci⟩ := s199a_nonneg (hM.1 u).trace_nonneg
  have h1' := (s199a_nonneg h1).1
  simp only [Complex.sub_re, Complex.mul_re, hti, hci, mul_zero, sub_zero] at h1'
  by_cases hc : (M u).trace = 0
  · unfold s199a_t; rw [if_pos hc, sub_zero]; exact zero_le_one
  · have hcpos : 0 < ((M u).trace).re := by
      rcases hc0.lt_or_eq with h | h
      · exact h
      · exact absurd (Complex.ext h.symm hci) hc
    have : (s199a_t M Q u).re ≤ 1 := by nlinarith
    exact Complex.nonneg_iff.2 ⟨by simp; linarith, by simp [hti]⟩

lemma s199c_top {d : ℕ} (p q : Fin d → ℝ) (σ : Equiv.Perm (Fin d)) (hσ : Antitone (p ∘ σ)) (k : ℕ)
    (hk : k < d) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (hqs : ∑ i, q i = ∑ i : Fin d, if i.val < k then (1 : ℝ) else 0) :
    ∑ i, q i * p i ≤ ∑ i : Fin d, if i.val < k then p (σ i) else 0 := by
  rw [← Equiv.sum_comp σ (fun i => q i * p i)]
  rw [← Equiv.sum_comp σ q] at hqs
  set c := p (σ ⟨k, hk⟩)
  have key : ∀ j : Fin d, q (σ j) * p (σ j) - (if j.val < k then p (σ j) else 0) ≤
      (q (σ j) - if j.val < k then (1 : ℝ) else 0) * c := by
    intro j
    by_cases hj : j.val < k
    · have : c ≤ p (σ j) := hσ (show j ≤ ⟨k, hk⟩ from Fin.le_def.2 (le_of_lt hj))
      simp only [hj, if_true]
      nlinarith [hq1 (σ j)]
    · have : p (σ j) ≤ c := hσ (show (⟨k, hk⟩ : Fin d) ≤ j from Fin.le_def.2 (by simp; omega))
      simp only [hj, if_false, sub_zero]
      nlinarith [hq0 (σ j)]
  have := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => key j)
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib, hqs, sub_self, zero_mul] at this
  linarith

lemma s199c_abel_id (m : ℕ) (e z : ℕ → ℝ) :
    ∑ i ∈ Finset.range (m + 1), e i * z i = e m * ∑ i ∈ Finset.range (m + 1), z i -
      ∑ k ∈ Finset.range m, (e (k + 1) - e k) * ∑ i ∈ Finset.range (k + 1), z i := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (fun k => (e (k + 1) - e k) * _),
      Finset.sum_range_succ z (m + 1)]
    ring

lemma s199c_abel (m : ℕ) (e z : ℕ → ℝ) (c : ℝ) (he : ∀ k < m, e k ≤ e (k + 1))
    (hS : ∀ k < m, -c ≤ ∑ i ∈ Finset.range (k + 1), z i) (h0 : ∑ i ∈ Finset.range (m + 1), z i = 0) :
    ∑ i ∈ Finset.range (m + 1), e i * z i ≤ c * (e m - e 0) := by
  rw [s199c_abel_id, h0, mul_zero, zero_sub, ← Finset.sum_range_sub, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum (fun k hk => ?_)
  have hk' := Finset.mem_range.1 hk
  have h1 := he k hk'
  have h2 := hS k hk'
  nlinarith

lemma s199c_decomp {d n : ℕ} {M P N : Fin n → Matrix (Fin d) (Fin d) ℂ} (r : ℝ)
    (hN : measurementIncoherent N) (hrel : ∀ u, M u + (r : ℂ) • P u = ((1 + r : ℝ) : ℂ) • N u)
    (Q : Matrix (Fin d) (Fin d) ℂ) :
    ergotropicCoarseGraining M Q - energyDephasing (ergotropicCoarseGraining M Q) =
      (r : ℂ) • (energyDephasing (∑ u, s199a_t M Q u • P u) - ∑ u, s199a_t M Q u • P u) := by
  have hM : ∀ u, M u = ((1 + r : ℝ) : ℂ) • N u - (r : ℂ) • P u := fun u => by rw [← hrel u]; abel
  have hN0 : ∀ u a b, a ≠ b → N u a b = 0 := by
    intro u a b hab
    have := congrFun (congrFun (hN u) a) b
    rw [← this]; simp [energyDephasing, Matrix.diagonal_apply, hab]
  ext a b
  rw [s199a_CG_eq]
  by_cases hab : a = b
  · subst hab; simp [energyDephasing]
  · simp only [Matrix.sub_apply, Matrix.smul_apply, energyDephasing, Matrix.diagonal_apply, hab, if_false,
      sub_zero, zero_sub, Matrix.sum_apply, smul_eq_mul, hM, hN0 _ _ _ hab, mul_zero]
    rw [← Finset.sum_neg_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun u _ => by ring)

lemma s199c_G {d n : ℕ} {M P : Fin n → Matrix (Fin d) (Fin d) ℂ} (hM : IsPOVM M) (hP : IsPOVM P)
    {Q : Matrix (Fin d) (Fin d) ℂ} (hQ : Q.PosSemidef) (hQ1 : (1 - Q).PosSemidef) :
    (∑ u, s199a_t M Q u • P u).PosSemidef ∧ (1 - ∑ u, s199a_t M Q u • P u).PosSemidef := by
  refine ⟨Matrix.posSemidef_sum _ (fun u _ => (hP.1 u).smul (s199a_t_nonneg hM hQ u)), ?_⟩
  have : 1 - ∑ u, s199a_t M Q u • P u = ∑ u, (1 - s199a_t M Q u) • P u := by
    simp only [sub_smul, one_smul, Finset.sum_sub_distrib, hP.2]
  rw [this]
  exact Matrix.posSemidef_sum _ (fun u _ => (hP.1 u).smul (s199c_t_le hM hQ hQ1 u))

lemma s199c_stepU {d n : ℕ} (hd : 0 < d) {M P N : Fin n → Matrix (Fin d) (Fin d) ℂ} (hM : IsPOVM M)
    (hP : IsPOVM P) (r : ℝ) (hr : 0 ≤ r) (hN : measurementIncoherent N)
    (hrel : ∀ u, M u + (r : ℂ) • P u = ((1 + r : ℝ) : ℂ) • N u)
    {X : Matrix (Fin d) (Fin d) ℂ} (hX : IsDensityMatrix X) (σ : Equiv.Perm (Fin d))
    (hσ : Antitone ((fun i => (X i i).re) ∘ σ)) (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (k : ℕ) (hk : k < d) :
    ∑ i : Fin d, (if i.val < k then ((U * ergotropicCoarseGraining M X * Uᴴ) i i).re else 0) ≤
      ∑ i : Fin d, (if i.val < k then (X (σ i) (σ i)).re else 0) + r * (((d : ℝ) - 1) / d) := by
  set C := ergotropicCoarseGraining M X
  set Pi : Matrix (Fin d) (Fin d) ℂ := Matrix.diagonal (fun i => if i.val < k then 1 else 0) with hPi
  set Q := Uᴴ * Pi * U with hQdef
  have hPi0 : Pi.PosSemidef := Matrix.posSemidef_diagonal_iff.2 (fun i => by split_ifs <;> simp)
  have hPi1 : (1 - Pi).PosSemidef := by
    have : 1 - Pi = Matrix.diagonal (fun i : Fin d => if i.val < k then (0 : ℂ) else 1) := by
      ext a b
      by_cases h : a = b
      · subst h; simp only [hPi, Matrix.sub_apply, Matrix.one_apply_eq, Matrix.diagonal_apply_eq]
        split_ifs <;> simp
      · simp [hPi, Matrix.one_apply, Matrix.diagonal_apply, h]
    rw [this]; exact Matrix.posSemidef_diagonal_iff.2 (fun i => by split_ifs <;> simp)
  have hUU : Uᴴ * U = 1 := by rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.1 hU
  have hUU' : U * Uᴴ = 1 := by rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff.1 hU
  have hQ : Q.PosSemidef := hPi0.conjTranspose_mul_mul_same U
  have hQ1 : (1 - Q).PosSemidef := by
    have h := hPi1.conjTranspose_mul_mul_same U
    have : Uᴴ * (1 - Pi) * U = 1 - Q := by rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hUU]
    rwa [this] at h
  have hL : ∑ i : Fin d, (if i.val < k then ((U * C * Uᴴ) i i).re else 0) = (Q * C).trace.re := by
    have e1 : (Q * C).trace = (Pi * (U * C * Uᴴ)).trace := by
      rw [show Q * C = Uᴴ * (Pi * U * C) by simp only [hQdef, Matrix.mul_assoc], Matrix.trace_mul_comm,
        show Pi * U * C * Uᴴ = Pi * (U * C * Uᴴ) by simp only [Matrix.mul_assoc]]
    rw [e1]
    simp only [hPi, Matrix.trace, Matrix.diag, Matrix.diagonal_mul, Complex.re_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    split_ifs <;> simp
  rw [hL, s199c_selfadj]
  set Y := ergotropicCoarseGraining M Q with hY
  set G := ∑ u, s199a_t M Q u • P u with hG
  obtain ⟨hG0, hG1⟩ := s199c_G hM hP hQ hQ1
  obtain ⟨hY0, hY1⟩ := s199c_G hM hM hQ hQ1
  rw [← s199a_CG_eq] at hY0 hY1
  have hXim : ∀ i, (X i i).im = 0 := fun i => ((s199a_diag hX).1 i).2
  have hdiagtr : ∀ A : Matrix (Fin d) (Fin d) ℂ, (energyDephasing A * X).trace.re =
      ∑ i, (A i i).re * (X i i).re := by
    intro A
    simp only [energyDephasing, Matrix.trace, Matrix.diag, Matrix.diagonal_mul, Complex.re_sum,
      Complex.mul_re, hXim, mul_zero, sub_zero]
  have hsplit : (Y * X).trace.re = ∑ i, (Y i i).re * (X i i).re +
      r * (∑ i, (G i i).re * (X i i).re - (G * X).trace.re) := by
    have e : Y = energyDephasing Y + (r : ℂ) • (energyDephasing G - G) := by
      rw [← s199c_decomp r hN hrel Q]; abel
    conv_lhs => rw [e]
    rw [Matrix.add_mul, Matrix.trace_add, Complex.add_re, hdiagtr, Matrix.smul_mul, Matrix.trace_smul,
      Matrix.sub_mul, Matrix.trace_sub, smul_eq_mul, Complex.re_ofReal_mul, Complex.sub_re, hdiagtr]
  rw [hsplit]
  have hoff := s199c_off hd hG0 hG1 hX
  have hq0 : ∀ i, 0 ≤ (Y i i).re := fun i => (s199a_nonneg (hY0.diag_nonneg (i := i))).1
  have hq1 : ∀ i, (Y i i).re ≤ 1 := by
    intro i
    have := (s199a_nonneg (hY1.diag_nonneg (i := i))).1
    simp only [Matrix.sub_apply, Matrix.one_apply_eq, Complex.sub_re, Complex.one_re] at this
    linarith
  have htrY : Y.trace = Q.trace := by
    rw [hY, s199a_CG_eq, Matrix.trace_sum]
    simp only [Matrix.trace_smul, smul_eq_mul, s199a_t_mul hM]
    exact s199a_sum_trace hM Q
  have htrQ : Q.trace = Pi.trace := by
    rw [hQdef, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hUU', Matrix.mul_one]
  have hqs : ∑ i, (Y i i).re = ∑ i : Fin d, if i.val < k then (1 : ℝ) else 0 := by
    have := congrArg Complex.re (htrY.trans htrQ)
    simp only [Matrix.trace, Matrix.diag, Complex.re_sum, hPi, Matrix.diagonal_apply_eq] at this
    rw [this]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    split_ifs <;> simp
  have htop := s199c_top (fun i => (X i i).re) (fun i => (Y i i).re) σ hσ k hk hq0 hq1 hqs
  have : r * (∑ i, (G i i).re * (X i i).re - (G * X).trace.re) ≤ r * (((d : ℝ) - 1) / d) :=
    mul_le_mul_of_nonneg_left hoff hr
  linarith

lemma s199c_range {m : ℕ} (z : ℕ → ℝ) (j : ℕ) (hj : j ≤ m + 1) :
    ∑ i ∈ Finset.range j, z i = ∑ i : Fin (m + 1), if i.val < j then z i else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < j then z i else 0), ← Finset.sum_filter]
  congr 1
  ext i; simp only [Finset.mem_range, Finset.mem_filter]; omega

lemma s199c_value {d n : ℕ} (hd : 0 < d) (E : Fin d → ℝ) (hE : Monotone E)
    {M P N : Fin n → Matrix (Fin d) (Fin d) ℂ} (hM : IsPOVM M) (hP : IsPOVM P) (r : ℝ) (hr : 0 ≤ r)
    (hN : measurementIncoherent N) (hrel : ∀ u, M u + (r : ℂ) • P u = ((1 + r : ℝ) : ℂ) • N u)
    {X : Matrix (Fin d) (Fin d) ℂ} (hX : IsDensityMatrix X) :
    passiveEnergy E (energyDephasing X) - passiveEnergy E (ergotropicCoarseGraining M X) ≤
      ((d : ℝ) - 1) / d * (E ⟨d - 1, by omega⟩ - E ⟨0, hd⟩) * r := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  set p : Fin (m + 1) → ℝ := fun i => (X i i).re with hp
  set σ := Tuple.sort (fun i => -p i)
  have hσ : Antitone (p ∘ σ) := by
    intro a b hab
    have := Tuple.monotone_sort (fun i => -p i) hab
    simp only [Function.comp_apply] at this ⊢
    linarith
  set c := r * (((m + 1 : ℕ) : ℝ) - 1) / (m + 1 : ℕ)
  have hc : r * ((((m + 1 : ℕ) : ℝ) - 1) / (m + 1 : ℕ)) = c := by simp only [c]; ring
  have hPD := s199a_PD_perm E X σ
  have hC := s199a_CG_density hM hX
  have key : ∀ U : Matrix.unitaryGroup (Fin (m + 1)) ℂ,
      passiveEnergy E (energyDephasing X) - c * (E ⟨m + 1 - 1, by omega⟩ - E ⟨0, hd⟩) ≤
        energyExpectation E ((U : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) * ergotropicCoarseGraining M X *
          (U : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)ᴴ) := by
    intro U
    set Z := (U : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) * ergotropicCoarseGraining M X *
      (U : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)ᴴ with hZ
    have hZd := s199a_diag (s199a_conj_density hC _ U.2)
    let e : ℕ → ℝ := fun i => if h : i < m + 1 then E ⟨i, h⟩ else 0
    let z : ℕ → ℝ := fun i => if h : i < m + 1 then (X (σ ⟨i, h⟩) (σ ⟨i, h⟩)).re - (Z ⟨i, h⟩ ⟨i, h⟩).re
      else 0
    have hez : ∑ i ∈ Finset.range (m + 1), e i * z i =
        ∑ k, E k * (X (σ k) (σ k)).re - energyExpectation E Z := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => e i * z i), energyExpectation, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [e, z, dif_pos i.isLt, Fin.eta]; ring
    have hS : ∀ k < m, -c ≤ ∑ i ∈ Finset.range (k + 1), z i := by
      intro k hk
      rw [s199c_range (m := m) z (k + 1) (by omega)]
      have h := s199c_stepU hd hM hP r hr hN hrel hX σ hσ _ U.2 (k + 1) (by omega)
      have : ∑ i : Fin (m + 1), (if i.val < k + 1 then z i else 0) =
          ∑ i : Fin (m + 1), (if i.val < k + 1 then (X (σ i) (σ i)).re else 0) -
          ∑ i : Fin (m + 1), (if i.val < k + 1 then (Z i i).re else 0) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        simp only [z, dif_pos i.isLt, Fin.eta]
        split_ifs <;> simp
      rw [this]
      rw [hc] at h
      linarith
    have h0 : ∑ i ∈ Finset.range (m + 1), z i = 0 := by
      rw [← Fin.sum_univ_eq_sum_range z]
      have : ∑ i : Fin (m + 1), z i = ∑ i : Fin (m + 1), ((X (σ i) (σ i)).re - (Z i i).re) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        simp only [z, dif_pos i.isLt, Fin.eta]
      rw [this, Finset.sum_sub_distrib, hZd.2,
        Equiv.sum_comp σ (fun i => (X i i).re), (s199a_diag hX).2, sub_self]
    have he : ∀ k < m, e k ≤ e (k + 1) := by
      intro k hk
      simp only [e, dif_pos (show k < m + 1 by omega), dif_pos (show k + 1 < m + 1 by omega)]
      exact hE (Fin.le_def.2 (show k ≤ k + 1 by omega))
    have hab := s199c_abel m e z c he hS h0
    rw [hez] at hab
    have hem : e m = E ⟨m + 1 - 1, by omega⟩ := by
      simp only [e, dif_pos (show m < m + 1 by omega)]
      congr 1
    have he0 : e 0 = E ⟨0, hd⟩ := by simp only [e, dif_pos (show 0 < m + 1 by omega)]
    rw [hem, he0] at hab
    linarith
  have hlow : passiveEnergy E (energyDephasing X) - c * (E ⟨m + 1 - 1, by omega⟩ - E ⟨0, hd⟩) ≤
      passiveEnergy E (ergotropicCoarseGraining M X) := by
    conv_rhs => unfold passiveEnergy
    refine le_csInf ⟨_, 1, rfl⟩ ?_
    rintro _ ⟨U, rfl⟩
    exact key U
  have : c * (E ⟨m + 1 - 1, by omega⟩ - E ⟨0, hd⟩) =
      ((((m + 1 : ℕ) : ℝ) - 1) / ((m + 1 : ℕ) : ℝ)) * (E ⟨m + 1 - 1, by omega⟩ - E ⟨0, hd⟩) * r := by
    simp only [c]; ring
  linarith

lemma s199c_feas {d n : ℕ} (hn : 0 < n) {M : Fin n → Matrix (Fin d) (Fin d) ℂ} (hM : IsPOVM M) :
    ∃ P N : Fin n → Matrix (Fin d) (Fin d) ℂ, IsPOVM P ∧ IsPOVM N ∧ measurementIncoherent N ∧
      ∀ u, M u + ((n : ℝ) : ℂ) • P u = ((1 + n : ℝ) : ℂ) • N u := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hc : (0 : ℂ) ≤ 1 / (n : ℂ) := by
    have : (1 / (n : ℂ)) = ((1 / (n : ℝ) : ℝ) : ℂ) := by push_cast; rfl
    rw [this]; exact Complex.zero_le_real.2 (by positivity)
  have hsum : ∀ u, (1 - M u).PosSemidef := by
    intro u
    rw [← hM.2, ← Finset.add_sum_erase _ _ (Finset.mem_univ u), add_sub_cancel_left]
    exact Matrix.posSemidef_sum _ (fun i _ => hM.1 i)
  refine ⟨fun u => (1 / (n : ℂ)) • ((1 - M u) + (1 / (n : ℂ)) • 1), fun _ => (1 / (n : ℂ)) • 1,
    ⟨fun u => ((hsum u).add (Matrix.PosSemidef.one.smul hc)).smul hc, ?_⟩,
    ⟨fun _ => Matrix.PosSemidef.one.smul hc, ?_⟩, fun _ => ?_, fun u => ?_⟩
  · rw [← Finset.smul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib, hM.2]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ]
    ext a b
    by_cases h : a = b
    · subst h; simp; field_simp; ring
    · simp [h]
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    ext a b
    by_cases h : a = b
    · subst h; simp; field_simp
    · simp [h, Matrix.one_apply]
  · ext a b
    by_cases h : a = b <;> simp [energyDephasing, h]
  · ext a b
    by_cases h : a = b
    · subst h; simp; field_simp; ring
    · simp [h]; field_simp; ring

end QAlgorithms.Papers.Independent.Information100.P38

open scoped ComplexConjugate Matrix ComplexOrder

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100
  QAlgorithms.Papers.Independent.Information100.P38 in
theorem solution {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (E : Fin d → ℝ) (hE : Monotone E)
    (M : Fin n → Matrix (Fin d) (Fin d) ℂ) (hM : IsPOVM M) :
    observationalAdvantage E M ≤ ((d : ℝ) - 1) / (d : ℝ) *
      (E ⟨d - 1, by omega⟩ - E ⟨0, hd⟩) * measurementCoherenceRobustness M := by
  set K := ((d : ℝ) - 1) / (d : ℝ) * (E ⟨d - 1, by omega⟩ - E ⟨0, hd⟩) with hK
  have hK0 : 0 ≤ K := by
    have h1 : (0 : ℝ) ≤ ((d : ℝ) - 1) / d := by
      have : (1 : ℝ) ≤ d := by exact_mod_cast hd
      exact div_nonneg (by linarith) (by linarith)
    have h2 : 0 ≤ E ⟨d - 1, by omega⟩ - E ⟨0, hd⟩ :=
      sub_nonneg.2 (hE (Fin.le_def.2 (Nat.zero_le _)))
    exact mul_nonneg h1 h2
  have hX0 : IsDensityMatrix (Matrix.diagonal (Pi.single (⟨0, hd⟩ : Fin d) (1 : ℂ))) :=
    ⟨Matrix.posSemidef_diagonal_iff.2 (fun j => by by_cases h : j = ⟨0, hd⟩ <;> simp [h]),
      by simp [Matrix.trace_diagonal]⟩
  have hne : Set.Nonempty {r | ∃ X : Matrix (Fin d) (Fin d) ℂ, IsDensityMatrix X ∧
      r = observationalErgotropy E M X - incoherentErgotropy E X} := ⟨_, _, hX0, rfl⟩
  have hfeas : ∀ r : ℝ, r ∈ {r : ℝ | 0 ≤ r ∧ ∃ P N : Fin n → Matrix (Fin d) (Fin d) ℂ,
      IsPOVM P ∧ IsPOVM N ∧ measurementIncoherent N ∧
        ∀ u, M u + (r : ℂ) • P u = ((1 + r : ℝ) : ℂ) • N u} → observationalAdvantage E M ≤ K * r := by
    rintro r ⟨hr, P, N, hP, hN, hNi, hrel⟩
    refine csSup_le hne ?_
    rintro _ ⟨X, hX, rfl⟩
    rw [s199a_val]
    exact s199c_value hd E hE hM hP r hr hNi hrel hX
  obtain ⟨P, N, hP, hN, hNi, hrel⟩ := s199c_feas hn hM
  have hFne : Set.Nonempty {r : ℝ | 0 ≤ r ∧ ∃ P N : Fin n → Matrix (Fin d) (Fin d) ℂ,
      IsPOVM P ∧ IsPOVM N ∧ measurementIncoherent N ∧
        ∀ u, M u + (r : ℂ) • P u = ((1 + r : ℝ) : ℂ) • N u} :=
    ⟨n, Nat.cast_nonneg n, P, N, hP, hN, hNi, hrel⟩
  rcases hK0.lt_or_eq with hKp | hKz
  · have : observationalAdvantage E M / K ≤ measurementCoherenceRobustness M := by
      unfold measurementCoherenceRobustness
      refine le_csInf hFne (fun r hr => ?_)
      rw [div_le_iff₀ hKp, mul_comm]
      exact hfeas r hr
    rw [div_le_iff₀ hKp, mul_comm] at this
    exact this
  · rw [← hKz, zero_mul]
    have := hfeas n ⟨Nat.cast_nonneg n, P, N, hP, hN, hNi, hrel⟩
    rw [← hKz, zero_mul] at this
    exact this
