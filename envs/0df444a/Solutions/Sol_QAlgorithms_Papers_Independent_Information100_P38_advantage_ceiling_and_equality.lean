-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P38.advantage_ceiling_and_equality
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T06:20:22.333019+00:00
-- url     : https://prove2.me/submissions/13d0daa0-75b5-4d31-86b6-1dd5f16eb653

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

lemma s199a_ground2 {d : ℕ} (h1 : 1 < d) (E : Fin d → ℝ) (hE : Monotone E)
    {ρ : Matrix (Fin d) (Fin d) ℂ} (hρ : IsDensityMatrix ρ) (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    E ⟨0, by omega⟩ + (E ⟨1, h1⟩ - E ⟨0, by omega⟩) * (1 - ((U * ρ * Uᴴ) ⟨0, by omega⟩ ⟨0, by omega⟩).re) ≤
      energyExpectation E (U * ρ * Uᴴ) := by
  set i0 : Fin d := ⟨0, by omega⟩
  have hY := s199a_conj_density hρ U hU
  obtain ⟨h0, hs⟩ := s199a_diag hY
  set q := fun i => ((U * ρ * Uᴴ) i i).re with hq
  unfold energyExpectation
  have e1 := Finset.add_sum_erase Finset.univ (fun i => E i * q i) (Finset.mem_univ i0)
  have e2 := Finset.add_sum_erase Finset.univ q (Finset.mem_univ i0)
  have hb : ∑ i ∈ Finset.univ.erase i0, E ⟨1, h1⟩ * q i ≤ ∑ i ∈ Finset.univ.erase i0, E i * q i := by
    refine Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_right (hE ?_) (h0 i).1)
    have : i ≠ i0 := Finset.ne_of_mem_erase hi
    have : i.val ≠ 0 := fun h => this (Fin.ext h)
    show 1 ≤ i.val; omega
  rw [← Finset.mul_sum] at hb
  simp only [hq] at e1 e2 hb hs ⊢
  have : ∑ i ∈ Finset.univ.erase i0, ((U * ρ * Uᴴ) i i).re = 1 - ((U * ρ * Uᴴ) i0 i0).re := by linarith
  rw [this] at hb
  nlinarith

lemma s199a_uniform {d : ℕ} [NeZero d] (E : Fin d → ℝ) (hE : StrictMono E) {X : Matrix (Fin d) (Fin d) ℂ}
    (hX : IsDensityMatrix X) (h : passiveEnergy E (energyDephasing X) * d = ∑ k, E k) :
    ∀ i, (X i i).re = 1 / d := by
  set p : Fin d → ℝ := fun k => (X k k).re with hp
  set P := passiveEnergy E (energyDephasing X) with hP
  have hV : ∀ σ : Equiv.Perm (Fin d), P ≤ ∑ k, E k * p (σ k) := fun σ => s199a_PD_perm E X σ
  have hps : ∑ k, p k = 1 := (s199a_diag hX).2
  have hall : ∀ τ : Equiv.Perm (Fin d), ∑ k, E k * p (τ k) = P := by
    intro τ
    have havg := s199a_perm_avg E p τ
    rw [hps, mul_one, ← h] at havg
    have hz : ∑ c : Fin d, (∑ k, E k * p ((τ.trans (Equiv.addRight c)) k) - P) = 0 := by
      rw [Finset.sum_sub_distrib, havg]; simp [mul_comm]
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun c _ => sub_nonneg.2 (hV _))).1 hz 0 (Finset.mem_univ _)
    simp only [Equiv.trans_apply, Equiv.coe_addRight, add_zero] at this
    linarith
  have heq : ∀ i j, p i = p j := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    have h3 : ∑ k, E k * p (Equiv.swap i j k) - ∑ k, E k * p ((1 : Equiv.Perm (Fin d)) k) = 0 := by
      rw [hall, hall, sub_self]
    rw [← Finset.sum_sub_distrib] at h3
    simp only [Equiv.Perm.one_apply] at h3
    rw [Fintype.sum_eq_add i j hij (fun k hk => by simp [Equiv.swap_apply_of_ne_of_ne hk.1 hk.2])] at h3
    simp only [Equiv.swap_apply_left, Equiv.swap_apply_right] at h3
    have h4 : (E i - E j) * (p j - p i) = 0 := by linarith
    rcases mul_eq_zero.1 h4 with h5 | h5
    · exact absurd (sub_eq_zero.1 h5) (hE.injective.ne hij)
    · linarith
  intro i
  have hsum : ∑ k, p k = d * p i := by
    rw [Finset.sum_congr rfl (fun k _ => heq k i)]; simp
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  show p i = 1 / d
  rw [hps] at hsum
  field_simp
  linarith

/-- quadratic form -/
def s199a_q {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) (y : Fin d → ℂ) : ℂ := star y ⬝ᵥ (ρ *ᵥ y)

def s199a_pd {d : ℕ} (y : Fin d → ℂ) : Matrix (Fin d) (Fin d) ℂ := Matrix.of fun a b => y a * conj (y b)

lemma s199a_sumsq_le {d : ℕ} {ρ : Matrix (Fin d) (Fin d) ℂ} (hρ : IsDensityMatrix ρ) :
    ∑ a, ∑ b, Complex.normSq (ρ a b) ≤ 1 := by
  obtain ⟨h0, h1⟩ := s199a_diag hρ
  calc ∑ a, ∑ b, Complex.normSq (ρ a b) ≤ ∑ a, ∑ b, (ρ a a).re * (ρ b b).re :=
        Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => s199a_entry_sq hρ.1 a b))
    _ = 1 := by simp_rw [← Finset.mul_sum, ← Finset.sum_mul, h1, one_mul]

lemma s199a_expand {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) (y : Fin d → ℂ)
    (hy : ∑ i, Complex.normSq (y i) = 1) :
    ∑ a, ∑ b, Complex.normSq (ρ a b - y a * conj (y b)) =
      ∑ a, ∑ b, Complex.normSq (ρ a b) - 2 * (s199a_q ρ y).re + 1 := by
  have e1 : ∀ a b, Complex.normSq (ρ a b - y a * conj (y b)) = Complex.normSq (ρ a b) +
      Complex.normSq (y a) * Complex.normSq (y b) - 2 * (conj (y a) * ρ a b * y b).re := by
    intro a b
    rw [Complex.normSq_sub, Complex.normSq_mul, Complex.normSq_conj]
    simp only [map_mul, Complex.conj_conj, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  simp_rw [e1, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hy,
    one_mul]
  have e2 : (s199a_q ρ y).re = ∑ a, ∑ b, (conj (y a) * ρ a b * y b).re := by
    simp only [s199a_q, dotProduct, Matrix.mulVec, Pi.star_apply, Complex.star_def, Finset.mul_sum,
      Complex.re_sum]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by ring_nf))
  rw [e2, Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  ring

/-- lemma (a): quadratic form of a density matrix at a unit vector is at most one, with equality only
for the corresponding pure state -/
lemma s199a_q_le {d : ℕ} {ρ : Matrix (Fin d) (Fin d) ℂ} (hρ : IsDensityMatrix ρ) (y : Fin d → ℂ)
    (hy : ∑ i, Complex.normSq (y i) = 1) : (s199a_q ρ y).re ≤ 1 := by
  have h1 := s199a_expand ρ y hy
  have h2 := s199a_sumsq_le hρ
  have h3 : 0 ≤ ∑ a, ∑ b, Complex.normSq (ρ a b - y a * conj (y b)) :=
    Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => Complex.normSq_nonneg _))
  linarith

lemma s199a_q_eq {d : ℕ} {ρ : Matrix (Fin d) (Fin d) ℂ} (hρ : IsDensityMatrix ρ) (y : Fin d → ℂ)
    (hy : ∑ i, Complex.normSq (y i) = 1) (hq : 1 ≤ (s199a_q ρ y).re) : ρ = s199a_pd y := by
  have h1 := s199a_expand ρ y hy
  have h2 := s199a_sumsq_le hρ
  have h3 : ∑ a, ∑ b, Complex.normSq (ρ a b - y a * conj (y b)) = 0 := by
    have : 0 ≤ ∑ a, ∑ b, Complex.normSq (ρ a b - y a * conj (y b)) :=
      Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => Complex.normSq_nonneg _))
    linarith
  ext a b
  have h4 := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => Finset.sum_nonneg
    (fun b _ => Complex.normSq_nonneg _))).1 h3 a (Finset.mem_univ _)
  have h5 := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => Complex.normSq_nonneg _)).1 h4 b
    (Finset.mem_univ _)
  rw [Complex.normSq_eq_zero, sub_eq_zero] at h5
  simpa [s199a_pd] using h5

lemma s199a_q_cont {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) :
    Continuous (fun y : Fin d → ℂ => (s199a_q ρ y).re) := by
  unfold s199a_q
  exact Complex.continuous_re.comp ((continuous_star).dotProduct (continuous_const.matrix_mulVec continuous_id))

lemma s199a_sphere_compact (d : ℕ) : IsCompact {y : Fin d → ℂ | ∑ i, Complex.normSq (y i) = 1} := by
  have hK : IsCompact (Set.univ.pi fun _ : Fin d => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi (fun _ => isCompact_closedBall _ _)
  refine IsCompact.of_isClosed_subset hK (isClosed_eq (by fun_prop) continuous_const) ?_
  intro y hy
  refine Set.mem_univ_pi.2 (fun k => ?_)
  rw [Metric.mem_closedBall, dist_zero_right]
  have h1 : Complex.normSq (y k) ≤ 1 := by
    rw [← hy]
    exact Finset.single_le_sum (f := fun i => Complex.normSq (y i)) (fun j _ => Complex.normSq_nonneg _)
      (Finset.mem_univ k)
  rw [Complex.normSq_eq_norm_sq] at h1
  nlinarith [norm_nonneg (y k)]

lemma s199a_row {d : ℕ} (ρ U : Matrix (Fin d) (Fin d) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (i : Fin d) :
    (U * ρ * Uᴴ) i i = s199a_q ρ (fun k => star (U i k)) ∧
      ∑ k, Complex.normSq (star (U i k)) = 1 := by
  constructor
  · simp only [s199a_q, Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct, Matrix.mulVec,
      Pi.star_apply, star_star, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by ring))
  · have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.1 hU) i) i
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at h
    have h2 := congrArg Complex.re h
    simp only [Complex.re_sum, Complex.one_re] at h2
    rw [← h2]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Complex.normSq_apply]
    simp [Complex.mul_re]

/-- Step B: a density matrix of ground passive energy is pure. -/
lemma s199a_stepB {d : ℕ} (hd : 0 < d) (E : Fin d → ℝ) (hE : StrictMono E)
    {ρ : Matrix (Fin d) (Fin d) ℂ} (hρ : IsDensityMatrix ρ) (hP : passiveEnergy E ρ ≤ E ⟨0, hd⟩) :
    ∃ y : Fin d → ℂ, ∑ i, Complex.normSq (y i) = 1 ∧ ρ = s199a_pd y := by
  by_cases h1 : 1 < d
  · obtain ⟨y, hy, hmax⟩ := (s199a_sphere_compact d).exists_isMaxOn
      (show Set.Nonempty {y : Fin d → ℂ | ∑ i, Complex.normSq (y i) = 1} from
        ⟨(Pi.single (⟨0, hd⟩ : Fin d) (1 : ℂ) : Fin d → ℂ), by simp [Pi.single_apply, Finset.sum_ite_eq']⟩)
      (s199a_q_cont ρ).continuousOn
    refine ⟨y, hy, s199a_q_eq hρ y hy ?_⟩
    by_contra hlt
    push Not at hlt
    have hδ : 0 < E ⟨1, h1⟩ - E ⟨0, hd⟩ := sub_pos.2 (hE (show (⟨0, hd⟩ : Fin d) < ⟨1, h1⟩ from by
      simp [Fin.lt_def]))
    have hlt2 : passiveEnergy E ρ < E ⟨0, hd⟩ + (E ⟨1, h1⟩ - E ⟨0, hd⟩) * (1 - (s199a_q ρ y).re) := by
      have : 0 < (E ⟨1, h1⟩ - E ⟨0, hd⟩) * (1 - (s199a_q ρ y).re) := mul_pos hδ (by linarith)
      linarith
    unfold passiveEnergy at hlt2
    obtain ⟨r, ⟨U, rfl⟩, hr⟩ := exists_lt_of_csInf_lt (s := {r | ∃ U : Matrix.unitaryGroup (Fin d) ℂ,
      r = energyExpectation E ((U : Matrix (Fin d) (Fin d) ℂ) * ρ * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ)})
      ⟨_, 1, rfl⟩ hlt2
    have hg := s199a_ground2 h1 E hE.monotone hρ U U.2
    obtain ⟨hrow, hnorm⟩ := s199a_row ρ U U.2 ⟨0, hd⟩
    have hm := hmax (show (fun k => star ((U : Matrix (Fin d) (Fin d) ℂ) ⟨0, hd⟩ k)) ∈
      {y : Fin d → ℂ | ∑ i, Complex.normSq (y i) = 1} from hnorm)
    simp only [Set.mem_setOf_eq] at hm
    rw [hrow] at hg
    nlinarith
  · obtain rfl : d = 1 := by omega
    refine ⟨fun _ => 1, by simp, s199a_q_eq hρ _ (by simp) ?_⟩
    have := hρ.2
    simp [s199a_q, dotProduct, Matrix.mulVec, Matrix.trace] at this ⊢
    rw [this]; simp

lemma s199a_dot_self {d : ℕ} (w : Fin d → ℂ) (hw : ∑ i, Complex.normSq (w i) = 1) : star w ⬝ᵥ w = 1 := by
  simp only [dotProduct, Pi.star_apply, Complex.star_def]
  have : ∀ i, conj (w i) * w i = (Complex.normSq (w i) : ℂ) := by
    intro i; rw [mul_comm, Complex.mul_conj]
  simp_rw [this]
  exact_mod_cast hw

lemma s199a_trace_pd {d : ℕ} (w : Fin d → ℂ) (hw : ∑ i, Complex.normSq (w i) = 1) :
    (s199a_pd w).trace = 1 := by
  have := s199a_dot_self w hw
  simp only [dotProduct, Pi.star_apply, Complex.star_def] at this
  rw [← this]
  simp [Matrix.trace, s199a_pd, mul_comm]

lemma s199a_trace_mul_pd {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) (w : Fin d → ℂ) :
    (M * s199a_pd w).trace = s199a_q M w := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, s199a_pd, Matrix.of_apply, s199a_q, dotProduct,
    Matrix.mulVec, Pi.star_apply, Complex.star_def, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by ring))

lemma s199a_pd_mulVec {d : ℕ} (w x : Fin d → ℂ) : s199a_pd w *ᵥ x = (star w ⬝ᵥ x) • w := by
  ext a
  simp only [s199a_pd, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul,
    Pi.star_apply, Complex.star_def, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => by ring)

/-- rank-one domination -/
lemma s199a_dom {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.PosSemidef) (w : Fin d → ℂ)
    (hw : ∑ i, Complex.normSq (w i) = 1) (hB : (s199a_pd w - A).PosSemidef) :
    ∃ β : ℂ, A = β • s199a_pd w := by
  have hww := s199a_dot_self w hw
  have hker : ∀ x, star w ⬝ᵥ x = 0 → A *ᵥ x = 0 := by
    intro x hx
    have h1 := (Matrix.posSemidef_iff_dotProduct_mulVec.1 hB).2 x
    rw [Matrix.sub_mulVec, s199a_pd_mulVec, hx, zero_smul, zero_sub, dotProduct_neg] at h1
    have h2 := (Matrix.posSemidef_iff_dotProduct_mulVec.1 hA).2 x
    have h3 : star x ⬝ᵥ A *ᵥ x = 0 := le_antisymm (neg_nonneg.1 h1) h2
    exact (hA.dotProduct_mulVec_zero_iff x).1 h3
  set z := A *ᵥ w with hz
  have hcol : ∀ x, A *ᵥ x = (star w ⬝ᵥ x) • z := by
    intro x
    have h := hker (x - (star w ⬝ᵥ x) • w) (by
      rw [dotProduct_sub, dotProduct_smul, hww, smul_eq_mul, mul_one, sub_self])
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_eq_zero] at h
    exact h
  have hent : ∀ a b, A a b = conj (w b) * z a := by
    intro a b
    have h := congrFun (hcol (Pi.single b 1)) a
    simp [Matrix.mulVec, dotProduct, Pi.single_apply] at h
    linear_combination h
  have hherm : ∀ a b, conj (w b) * z a = w a * conj (z b) := by
    intro a b
    rw [← hent, ← hA.1.apply a b, hent]
    simp [mul_comm]
  set β : ℂ := ∑ b, conj (z b) * w b
  have hzw : ∀ a, z a = w a * β := by
    intro a
    have : ∑ b, conj (w b) * z a * w b = ∑ b, w a * conj (z b) * w b :=
      Finset.sum_congr rfl (fun b _ => by rw [hherm])
    have e1 : ∑ b, conj (w b) * z a * w b = z a * (star w ⬝ᵥ w) := by
      simp only [dotProduct, Pi.star_apply, Complex.star_def, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun b _ => by ring)
    rw [e1, hww, mul_one] at this
    rw [this, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => by ring)
  refine ⟨β, ?_⟩
  ext a b
  rw [hent, hzw]
  simp [s199a_pd]; ring

open scoped MatrixOrder in
lemma s199a_trace_nonneg {d : ℕ} {M X : Matrix (Fin d) (Fin d) ℂ} (hM : M.PosSemidef) (hX : X.PosSemidef) :
    0 ≤ (M * X).trace := by
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM.nonneg
  rw [Matrix.star_eq_conjTranspose, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc]
  exact (hX.mul_mul_conjTranspose_same B).trace_nonneg

/-- a pure state has ground passive energy -/
lemma s199a_pure_passive {d : ℕ} (hd : 0 < d) (E : Fin d → ℝ) (w : Fin d → ℂ)
    (hw : ∑ i, Complex.normSq (w i) = 1) : passiveEnergy E (s199a_pd w) ≤ E ⟨0, hd⟩ := by
  set i0 : Fin d := ⟨0, hd⟩
  set v : EuclideanSpace ℂ (Fin d) := WithLp.toLp 2 w
  have hv : ‖v‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    have : ∑ i, ‖v.ofLp i‖ ^ 2 = 1 := by
      rw [← hw]; refine Finset.sum_congr rfl (fun i _ => ?_)
      simp [v, Complex.normSq_eq_norm_sq]
    rw [this, Real.sqrt_one]
  have hon : Orthonormal ℂ (({i0} : Set (Fin d)).restrict (fun _ => v)) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Set.mem_singleton_iff] at hi hj
    subst hi; subst hj
    simp [inner_self_eq_norm_sq_to_K]
    left; exact hv
  obtain ⟨b, hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq (by simp)
  have hb0 : b i0 = v := hb i0 (Set.mem_singleton _)
  set Q := (EuclideanSpace.basisFun (Fin d) ℂ).toBasis.toMatrix b
  have hQ : Q ∈ Matrix.unitaryGroup (Fin d) ℂ :=
    (EuclideanSpace.basisFun (Fin d) ℂ).toMatrix_orthonormalBasis_mem_unitary b
  have hQe : ∀ a i, Q a i = b i a := by intro a i; simp [Q, Module.Basis.toMatrix_apply]
  have hQh : Qᴴ ∈ Matrix.unitaryGroup (Fin d) ℂ := by
    rw [← Matrix.star_eq_conjTranspose]; exact Unitary.star_mem hQ
  have h := s199a_passive_le_U E (s199a_pd w) Qᴴ hQh
  rw [Matrix.conjTranspose_conjTranspose] at h
  refine h.trans (le_of_eq ?_)
  have hinner : ∀ i, ∑ a, conj (Q a i) * w a = if i = i0 then 1 else 0 := by
    intro i
    have := b.inner_eq_ite i i0
    rw [hb0, EuclideanSpace.inner_eq_star_dotProduct] at this
    rw [← this]
    simp only [dotProduct, Pi.star_apply, Complex.star_def, hQe, v]
    refine Finset.sum_congr rfl (fun a _ => by simp [mul_comm])
  have hdiag : ∀ i, (Qᴴ * s199a_pd w * Q) i i = if i = i0 then 1 else 0 := by
    intro i
    have e : (Qᴴ * s199a_pd w * Q) i i = (∑ a, conj (Q a i) * w a) * conj (∑ a, conj (Q a i) * w a) := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, s199a_pd, Matrix.of_apply, map_sum, map_mul,
        Complex.conj_conj, Finset.sum_mul, Finset.mul_sum, Complex.star_def]
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun c _ => by ring))
    rw [e, hinner]
    split_ifs <;> simp
  unfold energyExpectation
  simp only [hdiag, apply_ite Complex.re, Complex.one_re, Complex.zero_re, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

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

lemma s199a_pd_density {d : ℕ} (w : Fin d → ℂ) (hw : ∑ i, Complex.normSq (w i) = 1) :
    IsDensityMatrix (s199a_pd w) := by
  refine ⟨?_, s199a_trace_pd w hw⟩
  have h := Matrix.posSemidef_vecMulVec_self_star w
  convert h using 1
  ext a b
  simp [s199a_pd, Matrix.vecMulVec_apply, Complex.star_def]

lemma s199a_norm_toLp {d : ℕ} (w : Fin d → ℂ) (hw : ∑ i, Complex.normSq (w i) = 1) :
    ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin d))‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have : ∑ i, ‖(WithLp.toLp 2 w : EuclideanSpace ℂ (Fin d)).ofLp i‖ ^ 2 = 1 := by
    rw [← hw]; refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [Complex.normSq_eq_norm_sq]
  rw [this, Real.sqrt_one]

lemma s199a_unit_of_state {d : ℕ} (v : EuclideanSpace ℂ (Fin d)) (hv : IsState v) :
    ∑ i, Complex.normSq (v.ofLp i) = 1 := by
  have h := hv
  unfold IsState at h
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at h
  rw [← h]; refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [Complex.normSq_eq_norm_sq]

lemma s199a_pureDensity {d : ℕ} (v : EuclideanSpace ℂ (Fin d)) : pureDensity v = s199a_pd v.ofLp := by
  ext a b; simp [pureDensity, s199a_pd]

lemma s199a_q_pd_self {d : ℕ} (w : Fin d → ℂ) (hw : ∑ i, Complex.normSq (w i) = 1) :
    s199a_q (s199a_pd w) w = 1 := by
  unfold s199a_q
  rw [s199a_pd_mulVec, s199a_dot_self w hw, one_smul, s199a_dot_self w hw]

/-- maximally mixed passive energy -/
lemma s199a_PD_mixed {d : ℕ} (hd : 0 < d) (E : Fin d → ℝ) (X : Matrix (Fin d) (Fin d) ℂ)
    (hX : ∀ i, X i i = 1 / (d : ℂ)) : passiveEnergy E (energyDephasing X) = (∑ i, E i) / d := by
  have hD : energyDephasing X = (1 / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
    ext a b
    simp [energyDephasing, Matrix.diagonal_apply, Matrix.one_apply, hX]
  have hconj : ∀ U : Matrix.unitaryGroup (Fin d) ℂ, (U : Matrix (Fin d) (Fin d) ℂ) * energyDephasing X *
      (U : Matrix (Fin d) (Fin d) ℂ)ᴴ = (1 / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
    intro U
    rw [hD, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← Matrix.star_eq_conjTranspose,
      Matrix.mem_unitaryGroup_iff.1 U.2]
  have hval : energyExpectation E ((1 / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ)) = (∑ i, E i) / d := by
    have hd' : (d : ℝ) ≠ 0 := by positivity
    simp [energyExpectation, div_eq_mul_inv]
    rw [Finset.sum_mul]; refine Finset.sum_congr rfl (fun i _ => ?_); field_simp
  unfold passiveEnergy
  have : {r | ∃ U : Matrix.unitaryGroup (Fin d) ℂ, r = energyExpectation E ((U : Matrix (Fin d) (Fin d) ℂ) *
      energyDephasing X * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ)} = {(∑ i, E i) / d} := by
    ext r
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, hconj, hval]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨1, h⟩⟩
  rw [this, csInf_singleton]

/-- witness implies the coarse-grained pure state is itself -/
lemma s199a_wit_C {d n : ℕ} {M : Fin n → Matrix (Fin d) (Fin d) ℂ} (hM : IsPOVM M)
    (v : EuclideanSpace ℂ (Fin d)) (S : Finset (Fin n)) (hW : advantageCeilingWitness M v S) :
    ergotropicCoarseGraining M (pureDensity v) = pureDensity v := by
  obtain ⟨hst, -, hsum, hout⟩ := hW
  set w := v.ofLp
  have hw := s199a_unit_of_state v hst
  rw [s199a_pureDensity] at hsum ⊢
  have hin : ∀ u ∈ S, s199a_t M (s199a_pd w) u • M u = M u := by
    intro u hu
    have hB : (s199a_pd w - M u).PosSemidef := by
      rw [← hsum, ← Finset.add_sum_erase S M hu, add_sub_cancel_left]
      exact Matrix.posSemidef_sum _ (fun i _ => hM.1 i)
    obtain ⟨β, hβ⟩ := s199a_dom (hM.1 u) w hw hB
    unfold s199a_t
    split_ifs with h
    · rw [((hM.1 u).trace_eq_zero_iff).1 h]; simp
    · have htr : (M u * s199a_pd w).trace = (M u).trace := by
        rw [hβ, Matrix.smul_mul, Matrix.trace_smul, Matrix.trace_smul, s199a_trace_mul_pd,
          s199a_q_pd_self w hw, s199a_trace_pd w hw]
      rw [htr, div_self h, one_smul]
  have hnot : ∀ u ∉ S, s199a_t M (s199a_pd w) u = 0 := by
    intro u hu
    have h0 : M u *ᵥ w = 0 := by
      have := hout u hu
      simpa [act] using this
    have : (M u * s199a_pd w).trace = 0 := by
      rw [s199a_trace_mul_pd]; unfold s199a_q; rw [h0, dotProduct_zero]
    unfold s199a_t; rw [this]; simp
  rw [s199a_CG_eq]
  rw [Finset.sum_congr rfl (fun u _ => show s199a_t M (s199a_pd w) u • M u = if u ∈ S then M u else 0 by
    split_ifs with h
    · exact hin u h
    · rw [hnot u h, zero_smul])]
  rw [Finset.sum_ite_mem, Finset.univ_inter, hsum]

/-- Step C: from a maximizer with pure coarse-grained output, build the witness. -/
lemma s199a_stepC {d n : ℕ} {M : Fin n → Matrix (Fin d) (Fin d) ℂ} (hM : IsPOVM M)
    {X : Matrix (Fin d) (Fin d) ℂ} (hX : IsDensityMatrix X) (hu : ∀ i, (X i i).re = 1 / d)
    (w : Fin d → ℂ) (hw : ∑ i, Complex.normSq (w i) = 1)
    (hC : ergotropicCoarseGraining M X = s199a_pd w) : ∃ v S, advantageCeilingWitness M v S := by
  set S := Finset.univ.filter (fun u => s199a_t M X u ≠ 0) with hSdef
  rw [s199a_CG_eq] at hC
  have ht0 := s199a_t_nonneg hM hX.1
  have hMu : ∀ u ∈ S, M u = (M u).trace • s199a_pd w := by
    intro u hu
    have hune : s199a_t M X u ≠ 0 := (Finset.mem_filter.1 hu).2
    have hB : (s199a_pd w - s199a_t M X u • M u).PosSemidef := by
      rw [← hC, ← Finset.add_sum_erase _ _ (Finset.mem_univ u), add_sub_cancel_left]
      exact Matrix.posSemidef_sum _ (fun i _ => (hM.1 i).smul (ht0 i))
    obtain ⟨β, hβ⟩ := s199a_dom ((hM.1 u).smul (ht0 u)) w hw hB
    have hM' : M u = (β / s199a_t M X u) • s199a_pd w := by
      rw [div_eq_mul_inv, mul_comm, ← smul_smul, ← hβ, smul_smul, inv_mul_cancel₀ hune, one_smul]
    have htr : (M u).trace = β / s199a_t M X u := by
      rw [hM', Matrix.trace_smul, s199a_trace_pd w hw, smul_eq_mul, mul_one]
    rw [htr]; exact hM'
  have hnot : ∀ u, u ∉ S → (M u * X).trace = 0 := by
    intro u hu
    have : s199a_t M X u = 0 := by simpa [S] using hu
    rw [← s199a_t_mul hM, this, zero_mul]
  set q := s199a_q X w with hqdef
  have hinS : ∀ u ∈ S, (M u * X).trace = (M u).trace * q := by
    intro u hu
    conv_lhs => rw [hMu u hu]
    rw [Matrix.smul_mul, Matrix.trace_smul, Matrix.trace_mul_comm, s199a_trace_mul_pd, smul_eq_mul]
  set c := ∑ u ∈ S, (M u).trace with hcdef
  have hsplit : ∀ f : Fin n → ℂ, (∀ u, u ∉ S → f u = 0) → ∑ u, f u = ∑ u ∈ S, f u := by
    intro f hf
    exact (Finset.sum_subset (Finset.subset_univ S) (fun u _ hu => hf u hu)).symm
  have hcq : c * q = 1 := by
    have h := s199a_sum_trace hM X
    rw [hX.2, hsplit _ hnot] at h
    rw [← h, hcdef, Finset.sum_mul]
    exact (Finset.sum_congr rfl (fun u hu => hinS u hu)).symm
  have hSsum : ∑ u ∈ S, M u = c • s199a_pd w := by
    rw [hcdef, Finset.sum_smul]; exact Finset.sum_congr rfl (fun u hu => hMu u hu)
  have hc1 : c.re ≤ 1 := by
    have hrest : (1 - c • s199a_pd w).PosSemidef := by
      rw [← hSsum, ← hM.2, ← Finset.sum_compl_add_sum S, add_sub_cancel_right]
      exact Matrix.posSemidef_sum _ (fun i _ => hM.1 i)
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.1 hrest).2 w
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, s199a_pd_mulVec, dotProduct_sub,
      dotProduct_smul, dotProduct_smul, s199a_dot_self w hw] at h
    have := (s199a_nonneg h).1
    simp at this; linarith
  have hc0 : 0 ≤ c := Finset.sum_nonneg (fun u _ => (hM.1 u).trace_nonneg)
  have hq0 : 0 ≤ q := (Matrix.posSemidef_iff_dotProduct_mulVec.1 hX.1).2 w
  have hqle := s199a_q_le hX w hw
  obtain ⟨hc0r, hc0i⟩ := s199a_nonneg hc0
  obtain ⟨hq0r, hq0i⟩ := s199a_nonneg hq0
  have hre := congrArg Complex.re hcq
  simp only [Complex.mul_re, hc0i, hq0i, mul_zero, sub_zero, Complex.one_re] at hre
  have hq1 : 1 ≤ q.re := by nlinarith
  have hXw := s199a_q_eq hX w hw hq1
  have hc : c = 1 := by
    apply Complex.ext
    · simp only [Complex.one_re]; nlinarith
    · simp [hc0i]
  refine ⟨WithLp.toLp 2 w, S, s199a_norm_toLp w hw, ?_, ?_, ?_⟩
  · intro i
    have := hu i
    rw [hXw] at this
    simp only [s199a_pd, Matrix.of_apply, Complex.mul_conj, Complex.ofReal_re] at this
    simpa using this
  · rw [s199a_pureDensity, hSsum, hc, one_smul]
  · intro u hu
    have h := hnot u hu
    rw [hXw, s199a_trace_mul_pd] at h
    have h0 : M u *ᵥ w = 0 := ((hM.1 u).dotProduct_mulVec_zero_iff w).1 h
    simp [act, h0]

end QAlgorithms.Papers.Independent.Information100.P38

open scoped ComplexConjugate Matrix ComplexOrder

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100
  QAlgorithms.Papers.Independent.Information100.P38 in
theorem solution {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (E : Fin d → ℝ) (hE : StrictMono E)
    (M : Fin n → Matrix (Fin d) (Fin d) ℂ) (hM : IsPOVM M) :
    let ceiling := (∑ i, E i) / (d : ℝ) - E ⟨0, hd⟩
    observationalAdvantage E M ≤ ceiling ∧
    (observationalAdvantage E M = ceiling ↔ ∃ v S, advantageCeilingWitness M v S) ∧
    (∀ v S, advantageCeilingWitness M v S →
      observationalErgotropy E M (pureDensity v) - incoherentErgotropy E (pureDensity v) =
        observationalAdvantage E M) := by
  intro ceiling
  haveI : NeZero d := ⟨hd.ne'⟩
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hle : ∀ X, IsDensityMatrix X →
      observationalErgotropy E M X - incoherentErgotropy E X ≤ ceiling := by
    intro X hX
    rw [s199a_val]
    have h1 := s199a_PD_le E hX
    have h2 := s199a_ground hd E hE.monotone (s199a_CG_density hM hX)
    have h3 : passiveEnergy E (energyDephasing X) ≤ (∑ i, E i) / d := by
      rw [le_div_iff₀ hdR]; exact h1
    show _ ≤ (∑ i, E i) / (d : ℝ) - E ⟨0, hd⟩
    linarith
  have hbdd : BddAbove {r | ∃ X : Matrix (Fin d) (Fin d) ℂ, IsDensityMatrix X ∧
      r = observationalErgotropy E M X - incoherentErgotropy E X} :=
    ⟨ceiling, by rintro r ⟨X, hX, rfl⟩; exact hle X hX⟩
  have hw0 : ∑ i, Complex.normSq ((Pi.single (⟨0, hd⟩ : Fin d) (1 : ℂ) : Fin d → ℂ) i) = 1 := by
    simp [Pi.single_apply, Finset.sum_ite_eq']
  have hX0 := s199a_pd_density _ hw0
  have hne : Set.Nonempty {r | ∃ X : Matrix (Fin d) (Fin d) ℂ, IsDensityMatrix X ∧
      r = observationalErgotropy E M X - incoherentErgotropy E X} := ⟨_, _, hX0, rfl⟩
  have h1 : observationalAdvantage E M ≤ ceiling :=
    csSup_le hne (by rintro r ⟨X, hX, rfl⟩; exact hle X hX)
  have hwv : ∀ v S, advantageCeilingWitness M v S →
      observationalErgotropy E M (pureDensity v) - incoherentErgotropy E (pureDensity v) = ceiling := by
    intro v S hW
    have hw := s199a_unit_of_state v hW.1
    rw [s199a_val, s199a_wit_C hM v S hW, s199a_pureDensity]
    have hP1 : passiveEnergy E (s199a_pd v.ofLp) = E ⟨0, hd⟩ :=
      le_antisymm (s199a_pure_passive hd E _ hw) (s199a_ground hd E hE.monotone (s199a_pd_density _ hw))
    have hP2 : passiveEnergy E (energyDephasing (s199a_pd v.ofLp)) = (∑ i, E i) / d := by
      refine s199a_PD_mixed hd E _ (fun i => ?_)
      have := hW.2.1 i
      simp only [s199a_pd, Matrix.of_apply, Complex.mul_conj, this]
      push_cast; ring
    rw [hP1, hP2]
  have hadv_wit : ∀ v S, advantageCeilingWitness M v S → observationalAdvantage E M = ceiling := by
    intro v S hW
    refine le_antisymm h1 (le_csSup hbdd ⟨pureDensity v, ?_, (hwv v S hW).symm⟩)
    rw [s199a_pureDensity]; exact s199a_pd_density _ (s199a_unit_of_state v hW.1)
  refine ⟨h1, ⟨fun heq => ?_, fun ⟨v, S, hW⟩ => hadv_wit v S hW⟩,
    fun v S hW => by rw [hwv v S hW, hadv_wit v S hW]⟩
  have hD : Continuous (fun X : Matrix (Fin d) (Fin d) ℂ => energyDephasing X) := by
    unfold energyDephasing; fun_prop
  have hCg : Continuous (fun X => ergotropicCoarseGraining M X) := by
    unfold ergotropicCoarseGraining
    refine continuous_finset_sum _ (fun u _ => ?_)
    by_cases h : (M u).trace = 0
    · simp only [h, if_true]; exact continuous_const
    · simp only [h, if_false]
      exact ((Continuous.matrix_trace (continuous_const.matrix_mul continuous_id)).div_const _).smul
        continuous_const
  have hcont : Continuous (fun X => passiveEnergy E (energyDephasing X) -
      passiveEnergy E (ergotropicCoarseGraining M X)) :=
    ((s199a_passive_cont E).comp hD).sub ((s199a_passive_cont E).comp hCg)
  obtain ⟨X, hX, hmax⟩ := (s199a_dens_compact d).exists_isMaxOn ⟨_, hX0⟩ hcont.continuousOn
  have hvalX : ceiling ≤ passiveEnergy E (energyDephasing X) - passiveEnergy E (ergotropicCoarseGraining M X) := by
    rw [← heq]
    refine csSup_le hne ?_
    rintro r ⟨Y, hY, rfl⟩
    rw [s199a_val]
    exact isMaxOn_iff.1 hmax Y hY
  have hA := s199a_PD_le E hX
  have hB := s199a_ground hd E hE.monotone (s199a_CG_density hM hX)
  have hA' : passiveEnergy E (energyDephasing X) ≤ (∑ i, E i) / d := by
    rw [le_div_iff₀ hdR]; exact hA
  change (∑ i, E i) / (d : ℝ) - E ⟨0, hd⟩ ≤ _ at hvalX
  have hPD : passiveEnergy E (energyDephasing X) * d = ∑ i, E i := by
    have : passiveEnergy E (energyDephasing X) = (∑ i, E i) / d := by linarith
    rw [this]; field_simp
  have hu := s199a_uniform E hE hX hPD
  obtain ⟨w, hw, hCw⟩ := s199a_stepB hd E hE (s199a_CG_density hM hX) (by linarith)
  exact s199a_stepC hM hX hu w hw hCw
