-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P38.advantage_definition_properties
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T06:35:34.385119+00:00
-- url     : https://prove2.me/submissions/b1c2e763-dcee-4341-b8ea-3f4cac5b1d51

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

lemma s199b_row {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (k : Fin d) :
    ∑ l, Complex.normSq (U k l) = 1 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.1 hU) k) k
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at h
  have h2 := congrArg Complex.re h
  simp only [Complex.re_sum, Complex.one_re] at h2
  rw [← h2]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Complex.normSq_apply]; simp [Complex.mul_re]

lemma s199b_col {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (l : Fin d) :
    ∑ k, Complex.normSq (U k l) = 1 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.1 hU) l) l
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at h
  have h2 := congrArg Complex.re h
  simp only [Complex.re_sum, Complex.one_re] at h2
  rw [← h2]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Complex.normSq_apply]; simp [Complex.mul_re]

lemma s199b_birk {d : ℕ} (E : Fin d → ℝ) (X : Matrix (Fin d) (Fin d) ℂ) (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A ∈ doublyStochastic ℝ (Fin d)) :
    passiveEnergy E (energyDephasing X) ≤ ∑ k, E k * ∑ j, A k j * (X j j).re := by
  have hA' : A ∈ (doublyStochastic ℝ (Fin d) : Set (Matrix (Fin d) (Fin d) ℝ)) := hA
  rw [doublyStochastic_eq_convexHull_permMatrix] at hA'
  have hconv : Convex ℝ {B : Matrix (Fin d) (Fin d) ℝ | passiveEnergy E (energyDephasing X) ≤
      ∑ k, E k * ∑ j, B k j * (X j j).re} := by
    refine convex_halfSpace_ge ⟨fun B C => ?_, fun c B => ?_⟩ _
    · simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib, mul_add]
    · simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun j _ => by ring))
  refine convexHull_min ?_ hconv hA'
  rintro _ ⟨σ, rfl⟩
  simp only [Set.mem_setOf_eq, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_def, Option.some.injEq, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact s199a_PD_perm E X σ

lemma s199b_incoh_le {d m : ℕ} (E : Fin d → ℝ) {N : Fin m → Matrix (Fin d) (Fin d) ℂ} (hN : IsPOVM N)
    (hNi : measurementIncoherent N) {X : Matrix (Fin d) (Fin d) ℂ} (hX : IsDensityMatrix X) :
    passiveEnergy E (energyDephasing X) ≤ passiveEnergy E (ergotropicCoarseGraining N X) := by
  have hn0 : ∀ u j, 0 ≤ (N u j j).re := fun u j => (s199a_nonneg ((hN.1 u).diag_nonneg (i := j))).1
  have hNd : ∀ u, N u = Matrix.diagonal (fun j => (((N u j j).re : ℝ) : ℂ)) := by
    intro u
    conv_lhs => rw [← hNi u]
    unfold energyDephasing
    congr 1; funext j
    apply Complex.ext <;> simp [(s199a_nonneg ((hN.1 u).diag_nonneg (i := j))).2]
  have hXd : ∀ j, X j j = (((X j j).re : ℝ) : ℂ) := fun j =>
    Complex.ext (by simp) (by simp [((s199a_diag hX).1 j).2])
  have hsum1 : ∀ j, ∑ u, (N u j j).re = 1 := by
    intro j
    have := congrArg (fun A => (A j j).re) hN.2
    simpa [Matrix.sum_apply, Complex.re_sum] using this
  let c : Fin m → ℝ := fun u => ∑ j, (N u j j).re
  let r : Fin m → ℝ := fun u => if c u = 0 then 0 else (c u)⁻¹
  have hc0 : ∀ u j, c u = 0 → (N u j j).re = 0 := fun u j h =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hn0 u j)).1 h j (Finset.mem_univ _)
  have hrc : ∀ u j, r u * c u * (N u j j).re = (N u j j).re := by
    intro u j
    by_cases h : c u = 0
    · simp [hc0 u j h]
    · simp only [r, if_neg h]; field_simp
  have htr : ∀ u, (N u).trace = ((c u : ℝ) : ℂ) := by
    intro u; conv_lhs => rw [hNd u]
    simp [Matrix.trace_diagonal, c]
  have htrX : ∀ u, (N u * X).trace = ((∑ j, (N u j j).re * (X j j).re : ℝ) : ℂ) := by
    intro u; conv_lhs => rw [hNd u]
    simp only [Matrix.trace, Matrix.diag, Matrix.diagonal_mul]
    push_cast
    refine Finset.sum_congr rfl (fun j _ => by rw [← hXd j])
  have ht : ∀ u, s199a_t N X u = ((r u * ∑ j, (N u j j).re * (X j j).re : ℝ) : ℂ) := by
    intro u
    unfold s199a_t
    rw [htr, htrX]
    by_cases h : c u = 0
    · simp [r, h]
    · simp only [r, if_neg h, Complex.ofReal_eq_zero]
      push_cast; field_simp
  conv_rhs => unfold passiveEnergy
  refine le_csInf ⟨_, 1, rfl⟩ ?_
  rintro _ ⟨U, rfl⟩
  set V : Matrix (Fin d) (Fin d) ℂ := (U : Matrix (Fin d) (Fin d) ℂ)
  have hentry : ∀ u k, (V * N u * Vᴴ) k k = ((∑ l, Complex.normSq (V k l) * (N u l l).re : ℝ) : ℂ) := by
    intro u k
    conv_lhs => rw [hNd u]
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
    push_cast
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [← Complex.mul_conj]; simp only [Complex.star_def]; ring
  have hdiag : ∀ k, ((V * ergotropicCoarseGraining N X * Vᴴ) k k).re =
      ∑ u, (r u * ∑ j, (N u j j).re * (X j j).re) * ∑ l, Complex.normSq (V k l) * (N u l l).re := by
    intro k
    rw [s199a_CG_eq, Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply, Complex.re_sum]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, hentry, ht, smul_eq_mul, ← Complex.ofReal_mul,
      Complex.ofReal_re]
  let A : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun k j =>
    ∑ u, r u * (N u j j).re * ∑ l, Complex.normSq (V k l) * (N u l l).re
  have hA : A ∈ doublyStochastic ℝ (Fin d) := by
    rw [mem_doublyStochastic_iff_sum]
    refine ⟨fun k j => ?_, fun k => ?_, fun j => ?_⟩
    · simp only [A, Matrix.of_apply]
      refine Finset.sum_nonneg (fun u _ => mul_nonneg (mul_nonneg ?_ (hn0 u j))
        (Finset.sum_nonneg (fun l _ => mul_nonneg (Complex.normSq_nonneg _) (hn0 u l))))
      simp only [r]; split_ifs
      · exact le_refl _
      · exact inv_nonneg.2 (Finset.sum_nonneg (fun j _ => hn0 u j))
    · simp only [A, Matrix.of_apply]
      rw [Finset.sum_comm]
      have : ∀ u, ∑ j, r u * (N u j j).re * ∑ l, Complex.normSq (V k l) * (N u l l).re =
          ∑ l, Complex.normSq (V k l) * (N u l l).re := by
        intro u
        rw [← Finset.sum_mul, ← Finset.mul_sum]
        by_cases h : c u = 0
        · have : ∀ l, (N u l l).re = 0 := fun l => hc0 u l h
          simp [this]
        · simp only [r, if_neg h]
          change (c u)⁻¹ * c u * _ = _
          rw [inv_mul_cancel₀ h, one_mul]
      rw [Finset.sum_congr rfl (fun u _ => this u), Finset.sum_comm]
      simp_rw [← Finset.mul_sum, hsum1, mul_one]
      exact s199b_row V U.2 k
    · simp only [A, Matrix.of_apply]
      rw [Finset.sum_comm]
      have : ∀ u, ∑ k, r u * (N u j j).re * ∑ l, Complex.normSq (V k l) * (N u l l).re = (N u j j).re := by
        intro u
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp_rw [← Finset.sum_mul, s199b_col V U.2, one_mul]
        change r u * (N u j j).re * c u = _
        linear_combination hrc u j
      rw [Finset.sum_congr rfl (fun u _ => this u), hsum1]
  have key := s199b_birk E X A hA
  refine key.trans (le_of_eq ?_)
  unfold energyExpectation
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [hdiag k]
  congr 1
  have e1 : ∑ u, (r u * ∑ j, (N u j j).re * (X j j).re) * ∑ l, Complex.normSq (V k l) * (N u l l).re =
      ∑ u, ∑ j, ∑ l, r u * (N u j j).re * (X j j).re * (Complex.normSq (V k l) * (N u l l).re) := by
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [Finset.mul_sum (a := r u), Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => by ring)
  have e2 : ∑ j, A k j * (X j j).re =
      ∑ j, ∑ u, ∑ l, r u * (N u j j).re * (X j j).re * (Complex.normSq (V k l) * (N u l l).re) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [A, Matrix.of_apply]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [Finset.mul_sum (a := r u * (N u j j).re), Finset.sum_mul]
    refine Finset.sum_congr rfl (fun l _ => by ring)
  rw [e1, e2, Finset.sum_comm]

def s199b_N (d : ℕ) (i : Fin d) : Matrix (Fin d) (Fin d) ℂ := Matrix.diagonal (Pi.single i 1)

lemma s199b_proj {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) :
    IsPOVM (s199b_N d) ∧ measurementIncoherent (s199b_N d) ∧
      ergotropicCoarseGraining (s199b_N d) X = energyDephasing X := by
  refine ⟨⟨fun i => ?_, ?_⟩, fun i => ?_, ?_⟩
  · refine Matrix.posSemidef_diagonal_iff.2 (fun j => ?_)
    by_cases h : j = i
    · subst h; simp
    · simp [Pi.single_apply, h]
  · ext a b
    simp only [s199b_N, Matrix.sum_apply, Matrix.diagonal_apply, Matrix.one_apply, Pi.single_apply]
    by_cases h : a = b
    · subst h; simp
    · simp [h]
  · ext a b
    simp [s199b_N, energyDephasing, Matrix.diagonal_apply]
  · ext a b
    have htr : ∀ i, (s199b_N d i).trace = 1 := by
      intro i; simp [s199b_N, Matrix.trace_diagonal]
    have htrX : ∀ i, (s199b_N d i * X).trace = X i i := by
      intro i
      simp [s199b_N, Matrix.trace, Matrix.diagonal_mul, Pi.single_apply]
    unfold ergotropicCoarseGraining
    simp only [htr, htrX, one_ne_zero, if_false, div_one]
    simp only [Matrix.sum_apply, Matrix.smul_apply, s199b_N, energyDephasing, Matrix.diagonal_apply,
      Pi.single_apply, smul_eq_mul]
    by_cases h : a = b
    · subst h; simp
    · simp [h]

lemma s199b_mixed {d n : ℕ} (hd : 0 < d) {M : Fin n → Matrix (Fin d) (Fin d) ℂ} (hM : IsPOVM M) :
    IsDensityMatrix ((1 / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ)) ∧
      ergotropicCoarseGraining M ((1 / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ)) =
        (1 / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ) ∧
      energyDephasing ((1 / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ)) =
        (1 / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hc : (0 : ℂ) ≤ 1 / (d : ℂ) := by
    have : (1 / (d : ℂ)) = ((1 / (d : ℝ) : ℝ) : ℂ) := by push_cast; rfl
    rw [this]; exact Complex.zero_le_real.2 (by positivity)
  refine ⟨⟨Matrix.PosSemidef.one.smul hc, ?_⟩, ?_, ?_⟩
  · rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]; field_simp
  · rw [s199a_CG_eq]
    have : ∀ u, s199a_t M ((1 / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ)) u • M u = (1 / (d : ℂ)) • M u := by
      intro u
      by_cases h : (M u).trace = 0
      · rw [((hM.1 u).trace_eq_zero_iff).1 h]; simp
      · unfold s199a_t
        rw [if_neg h, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul, mul_div_assoc,
          div_self h, mul_one]
    rw [Finset.sum_congr rfl (fun u _ => this u), ← Finset.smul_sum, hM.2]
  · ext a b
    by_cases h : a = b <;> simp [energyDephasing, Matrix.diagonal_apply, Matrix.one_apply, h]

end QAlgorithms.Papers.Independent.Information100.P38

open scoped ComplexConjugate Matrix ComplexOrder

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100
  QAlgorithms.Papers.Independent.Information100.P38 in
theorem solution {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (E : Fin d → ℝ) (hE : Monotone E)
    (M : Fin n → Matrix (Fin d) (Fin d) ℂ) (hM : IsPOVM M) :
    0 ≤ observationalAdvantage E M ∧
    (∃ X, IsDensityMatrix X ∧ observationalAdvantage E M =
      observationalErgotropy E M X - incoherentErgotropy E X) ∧
    observationalAdvantage E M = sSup {r | ∃ X, IsDensityMatrix X ∧
      r = observationalErgotropy E M X - incoherentWorkBenchmark E X} ∧
    observationalAdvantage E M = sSup {r | ∃ X, IsDensityMatrix X ∧
      r = passiveEnergy E (energyDephasing X) - passiveEnergy E (ergotropicCoarseGraining M X)} ∧
    (∀ X, IsDensityMatrix X → incoherentWorkBenchmark E X = incoherentErgotropy E X ∧
      ∃ m : ℕ, 0 < m ∧ ∃ N : Fin m → Matrix (Fin d) (Fin d) ℂ,
        IsPOVM N ∧ measurementIncoherent N ∧
        observationalErgotropy E N X = incoherentWorkBenchmark E X) := by
  have : NeZero d := ⟨hd.ne'⟩
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hEX : ∀ X : Matrix (Fin d) (Fin d) ℂ,
      energyExpectation E (energyDephasing X) = energyExpectation E X := by
    intro X; simp [energyExpectation, energyDephasing]
  have hbench : ∀ X, IsDensityMatrix X → incoherentWorkBenchmark E X = incoherentErgotropy E X ∧
      ∃ m : ℕ, 0 < m ∧ ∃ N : Fin m → Matrix (Fin d) (Fin d) ℂ,
        IsPOVM N ∧ measurementIncoherent N ∧
        observationalErgotropy E N X = incoherentWorkBenchmark E X := by
    intro X hX
    obtain ⟨hP, hI, hC⟩ := s199b_proj X
    have hval : observationalErgotropy E (s199b_N d) X = incoherentErgotropy E X := by
      unfold observationalErgotropy incoherentErgotropy; rw [hC, hEX]
    have hG : IsGreatest {r | ∃ n : ℕ, 0 < n ∧ ∃ N : Fin n → Matrix (Fin d) (Fin d) ℂ,
        IsPOVM N ∧ measurementIncoherent N ∧ r = observationalErgotropy E N X}
        (incoherentErgotropy E X) := by
      refine ⟨⟨d, hd, s199b_N d, hP, hI, hval.symm⟩, ?_⟩
      rintro r ⟨m, -, N', hP', hI', rfl⟩
      have := s199b_incoh_le E hP' hI' hX
      unfold observationalErgotropy incoherentErgotropy
      rw [hEX]
      linarith
    have hb : incoherentWorkBenchmark E X = incoherentErgotropy E X := hG.csSup_eq
    exact ⟨hb, d, hd, s199b_N d, hP, hI, by rw [hb, hval]⟩
  set ceiling := (∑ i, E i) / (d : ℝ) - E ⟨0, hd⟩
  have hle : ∀ X, IsDensityMatrix X →
      observationalErgotropy E M X - incoherentErgotropy E X ≤ ceiling := by
    intro X hX
    rw [s199a_val]
    have h1 := s199a_PD_le E hX
    have h2 := s199a_ground hd E hE (s199a_CG_density hM hX)
    have h3 : passiveEnergy E (energyDephasing X) ≤ (∑ i, E i) / d := by
      rw [le_div_iff₀ hdR]; exact h1
    linarith
  have hbdd : BddAbove {r | ∃ X : Matrix (Fin d) (Fin d) ℂ, IsDensityMatrix X ∧
      r = observationalErgotropy E M X - incoherentErgotropy E X} :=
    ⟨ceiling, by rintro r ⟨X, hX, rfl⟩; exact hle X hX⟩
  obtain ⟨hX0, hC0, hD0⟩ := s199b_mixed hd hM
  have hv0 : observationalErgotropy E M ((1 / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ)) -
      incoherentErgotropy E ((1 / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ)) = 0 := by
    rw [s199a_val, hC0, hD0, sub_self]
  have hne : Set.Nonempty {r | ∃ X : Matrix (Fin d) (Fin d) ℂ, IsDensityMatrix X ∧
      r = observationalErgotropy E M X - incoherentErgotropy E X} := ⟨_, _, hX0, rfl⟩
  have hD : Continuous (fun X : Matrix (Fin d) (Fin d) ℂ => energyDephasing X) := by
    unfold energyDephasing; fun_prop
  have hCg : Continuous (fun X => ergotropicCoarseGraining M X) := by
    unfold ergotropicCoarseGraining
    refine continuous_finsetSum _ (fun u _ => ?_)
    by_cases h : (M u).trace = 0
    · simp only [h, if_true]; exact continuous_const
    · simp only [h, if_false]
      exact ((Continuous.matrix_trace (continuous_const.matrix_mul continuous_id)).div_const _).smul
        continuous_const
  have hcont : Continuous (fun X => passiveEnergy E (energyDephasing X) -
      passiveEnergy E (ergotropicCoarseGraining M X)) :=
    ((s199a_passive_cont E).comp hD).sub ((s199a_passive_cont E).comp hCg)
  obtain ⟨X, hX, hmax⟩ := (s199a_dens_compact d).exists_isMaxOn ⟨_, hX0⟩ hcont.continuousOn
  have hatt : observationalAdvantage E M = observationalErgotropy E M X - incoherentErgotropy E X := by
    refine le_antisymm (csSup_le hne ?_) (le_csSup hbdd ⟨X, hX, rfl⟩)
    rintro r ⟨Y, hY, rfl⟩
    rw [s199a_val, s199a_val]
    exact isMaxOn_iff.1 hmax Y hY
  refine ⟨le_csSup hbdd ⟨_, hX0, hv0.symm⟩, ⟨X, hX, hatt⟩, ?_, ?_, hbench⟩
  · unfold observationalAdvantage
    congr 1
    ext r
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨Y, hY, rfl⟩; exact ⟨Y, hY, by rw [(hbench Y hY).1]⟩
    · rintro ⟨Y, hY, rfl⟩; exact ⟨Y, hY, by rw [(hbench Y hY).1]⟩
  · unfold observationalAdvantage
    congr 1
    ext r
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨Y, hY, rfl⟩; exact ⟨Y, hY, s199a_val E M Y⟩
    · rintro ⟨Y, hY, rfl⟩; exact ⟨Y, hY, (s199a_val E M Y).symm⟩
