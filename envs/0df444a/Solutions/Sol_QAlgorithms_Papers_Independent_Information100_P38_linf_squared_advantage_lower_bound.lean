-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P38.linf_squared_advantage_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T07:02:35.613398+00:00
-- url     : https://prove2.me/submissions/0f7a3048-28c7-4230-a6b9-144683301266

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

lemma lsq_perm_conj_diag {d : ℕ} (σ : Equiv.Perm (Fin d)) (Z : Matrix (Fin d) (Fin d) ℂ) (k : Fin d) :
    (s199a_perm σ * Z * (s199a_perm σ)ᴴ) k k = Z (σ k) (σ k) := by
  simp [s199a_perm, Matrix.mul_apply, Matrix.conjTranspose_apply, ite_mul, mul_ite, Finset.sum_ite_eq',
    Finset.sum_ite_eq]

lemma lsq_unitary_col {d : ℕ} (hd : 0 < d) (w : Fin d → ℂ) (hw : ∑ i, Complex.normSq (w i) = 1) :
    ∃ Q ∈ Matrix.unitaryGroup (Fin d) ℂ, ∀ a, Q a ⟨0, hd⟩ = w a := by
  set i0 : Fin d := ⟨0, hd⟩
  set v : EuclideanSpace ℂ (Fin d) := WithLp.toLp 2 w
  have hv : ‖v‖ = 1 := s199a_norm_toLp w hw
  have hon : Orthonormal ℂ (({i0} : Set (Fin d)).restrict (fun _ => v)) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Set.mem_singleton_iff] at hi hj
    subst hi; subst hj
    simp [inner_self_eq_norm_sq_to_K]
    left; exact hv
  obtain ⟨b, hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq (by simp)
  have hb0 : b i0 = v := hb i0 (Set.mem_singleton _)
  refine ⟨(EuclideanSpace.basisFun (Fin d) ℂ).toBasis.toMatrix b,
    (EuclideanSpace.basisFun (Fin d) ℂ).toMatrix_orthonormalBasis_mem_unitary b, fun a => ?_⟩
  simp [Module.Basis.toMatrix_apply, hb0, v]

lemma lsq_sorted {d : ℕ} (h1 : 1 < d) (E : Fin d → ℝ) (hE : Monotone E) (p : Fin d → ℝ)
    (hp : Antitone p) (hs : ∑ k, p k = 1) :
    ∑ k, E k * p k ≤ (∑ k, E k) / d - (E ⟨1, h1⟩ - E ⟨0, by omega⟩) * (p ⟨0, by omega⟩ - 1 / d) := by
  set i0 : Fin d := ⟨0, by omega⟩
  set i1 : Fin d := ⟨1, h1⟩
  set E' : Fin d → ℝ := fun k => if k = i0 then E i1 else E k with hE'def
  have hE' : Monotone E' := by
    intro a b hab
    simp only [E']
    split_ifs with ha hb hb
    · exact le_rfl
    · apply hE
      have : b.val ≠ 0 := fun h => hb (Fin.ext h)
      show 1 ≤ b.val; omega
    · exfalso
      have h2 := Fin.le_def.1 hab
      rw [hb] at h2
      exact ha (Fin.ext (by simp [i0] at h2 ⊢; omega))
    · exact hE hab
  have hch := (hE'.antivary hp).card_mul_sum_le_sum_mul_sum
  rw [Fintype.card_fin, hs, mul_one] at hch
  have e1 : ∑ k, E' k * p k = ∑ k, E k * p k + (E i1 - E i0) * p i0 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0),
      ← Finset.add_sum_erase _ (fun k => E k * p k) (Finset.mem_univ i0)]
    have : ∑ k ∈ Finset.univ.erase i0, E' k * p k = ∑ k ∈ Finset.univ.erase i0, E k * p k :=
      Finset.sum_congr rfl (fun k hk => by simp [E', Finset.ne_of_mem_erase hk])
    rw [this]; simp only [E', if_true]; ring
  have e2 : ∑ k, E' k = ∑ k, E k + (E i1 - E i0) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0),
      ← Finset.add_sum_erase _ (fun k => E k) (Finset.mem_univ i0)]
    have : ∑ k ∈ Finset.univ.erase i0, E' k = ∑ k ∈ Finset.univ.erase i0, E k :=
      Finset.sum_congr rfl (fun k hk => by simp [E', Finset.ne_of_mem_erase hk])
    rw [this]; simp only [E', if_true]; ring
  rw [e1, e2] at hch
  have hd : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have : (∑ k, E k) / d - (E i1 - E i0) * (p i0 - 1 / d) =
      (∑ k, E k - (E i1 - E i0) * (d * p i0 - 1)) / d := by field_simp
  rw [this, le_div_iff₀ hd]
  nlinarith

lemma lsq_passive {d : ℕ} (h1 : 1 < d) (E : Fin d → ℝ) (hE : Monotone E)
    {Y : Matrix (Fin d) (Fin d) ℂ} (hY : IsDensityMatrix Y) (w : Fin d → ℂ)
    (hw : ∑ i, Complex.normSq (w i) = 1) :
    passiveEnergy E Y ≤ (∑ k, E k) / d - (E ⟨1, h1⟩ - E ⟨0, by omega⟩) * ((s199a_q Y w).re - 1 / d) := by
  have hd : 0 < d := by omega
  obtain ⟨Q, hQ, hQw⟩ := lsq_unitary_col hd w hw
  have hQh : Qᴴ ∈ Matrix.unitaryGroup (Fin d) ℂ := by
    rw [← Matrix.star_eq_conjTranspose]; exact Unitary.star_mem hQ
  set Z := Qᴴ * Y * Q with hZdef
  have hZ : IsDensityMatrix Z := by
    have := s199a_conj_density hY Qᴴ hQh; rwa [Matrix.conjTranspose_conjTranspose] at this
  have hZ0 : Z ⟨0, hd⟩ ⟨0, hd⟩ = s199a_q Y w := by
    simp only [Z, Matrix.mul_apply, Matrix.conjTranspose_apply, hQw, s199a_q, dotProduct, Matrix.mulVec,
      Pi.star_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by ring))
  set z : Fin d → ℝ := fun k => (Z k k).re with hzdef
  set σ := Tuple.sort (fun k => -z k)
  have hσ : Antitone (z ∘ σ) := by
    intro a b hab
    have := Tuple.monotone_sort (fun k => -z k) hab
    simp only [Function.comp] at this ⊢; linarith
  have hU : s199a_perm σ * Qᴴ ∈ Matrix.unitaryGroup (Fin d) ℂ :=
    Submonoid.mul_mem _ (s199a_perm_unitary σ) hQh
  have h := s199a_passive_le_U E Y _ hU
  have hconj : s199a_perm σ * Qᴴ * Y * (s199a_perm σ * Qᴴ)ᴴ = s199a_perm σ * Z * (s199a_perm σ)ᴴ := by
    simp only [Z, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [hconj] at h
  have hen : energyExpectation E (s199a_perm σ * Z * (s199a_perm σ)ᴴ) = ∑ k, E k * (z ∘ σ) k := by
    unfold energyExpectation; simp only [lsq_perm_conj_diag]; rfl
  rw [hen] at h
  have hs : ∑ k, (z ∘ σ) k = 1 := by
    show ∑ k, z (σ k) = 1
    rw [Equiv.sum_comp σ z]; exact (s199a_diag hZ).2
  have hs2 := lsq_sorted h1 E hE _ hσ hs
  have hp0 : (s199a_q Y w).re ≤ (z ∘ σ) ⟨0, by omega⟩ := by
    have e : (s199a_q Y w).re = (z ∘ σ) (σ.symm ⟨0, hd⟩) := by
      simp only [Function.comp, Equiv.apply_symm_apply, z, hZ0]
    rw [e]; exact hσ (Fin.le_def.2 (Nat.zero_le _))
  have hEm : 0 ≤ E ⟨1, h1⟩ - E ⟨0, by omega⟩ := sub_nonneg.2 (hE (Fin.le_def.2 (by simp)))
  nlinarith


def lsq_v {d : ℕ} (i j : Fin d) (ζ : ℂ) : Fin d → ℂ := Pi.single i 1 + Pi.single j (conj ζ)
def lsq_f {d : ℕ} (i j : Fin d) : Fin d → ℂ := fun k => if k = i ∨ k = j then 0 else 1
def lsq_X {d : ℕ} (i j : Fin d) (ζ : ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  (1 / (d : ℂ)) • (Matrix.diagonal (lsq_f i j) + s199a_pd (lsq_v i j ζ))

lemma lsq_X_diag {d : ℕ} {i j : Fin d} (hij : i ≠ j) {ζ : ℂ} (hζ : ζ * conj ζ = 1) (k : Fin d) :
    lsq_X i j ζ k k = 1 / (d : ℂ) := by
  by_cases hi : k = i
  · subst hi; simp [lsq_X, lsq_f, lsq_v, s199a_pd, Pi.single_apply, hij]
  by_cases hj : k = j
  · have hζ' : conj ζ * ζ = 1 := by rw [mul_comm]; exact hζ
    subst hj; simp [lsq_X, lsq_f, lsq_v, s199a_pd, Pi.single_apply, Ne.symm hij, hζ']
  · simp [lsq_X, lsq_f, lsq_v, s199a_pd, Pi.single_apply, hi, hj]

lemma lsq_X_density {d : ℕ} {i j : Fin d} (hij : i ≠ j) {ζ : ℂ} (hζ : ζ * conj ζ = 1) :
    IsDensityMatrix (lsq_X i j ζ) := by
  refine ⟨?_, ?_⟩
  · unfold lsq_X
    refine Matrix.PosSemidef.smul ?_ ?_
    · refine Matrix.PosSemidef.add (Matrix.PosSemidef.diagonal (fun k => ?_)) ?_
      · simp only [lsq_f, Pi.zero_apply]; split_ifs <;> simp
      · have h := Matrix.posSemidef_vecMulVec_self_star (lsq_v i j ζ)
        convert h using 1
        ext a b
        simp [s199a_pd, Matrix.vecMulVec_apply]
    · have : (0 : ℝ) ≤ 1 / (d : ℝ) := by positivity
      have h2 : (1 / (d : ℂ)) = ((1 / (d : ℝ) : ℝ) : ℂ) := by push_cast; rfl
      rw [h2]; exact_mod_cast this
  · have hd : (d : ℂ) ≠ 0 := by
      have : 0 < d := lt_of_le_of_lt (Nat.zero_le _) (Fin.pos_iff_nonempty.2 ⟨i⟩)
      exact_mod_cast this.ne'
    simp only [Matrix.trace, Matrix.diag, lsq_X_diag hij hζ, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp

lemma lsq_trMX {d : ℕ} {i j : Fin d} (hij : i ≠ j) (ζ : ℂ) (M : Matrix (Fin d) (Fin d) ℂ) :
    (M * lsq_X i j ζ).trace = (1 / (d : ℂ)) * (M.trace - M i i - M j j + s199a_q M (lsq_v i j ζ)) := by
  rw [lsq_X, Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_add, Matrix.trace_add, s199a_trace_mul_pd,
    smul_eq_mul]
  congr 1
  have : (M * Matrix.diagonal (lsq_f i j)).trace = ∑ k, (M k k - (if k = i then M k k else 0) -
      (if k = j then M k k else 0)) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_diagonal]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases hi : k = i
    · subst hi; simp [lsq_f, hij]
    by_cases hj : k = j
    · subst hj; simp [lsq_f, hi]
    · simp [lsq_f, hi, hj]
  rw [this, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  simp [Matrix.trace]

lemma lsq_P {d : ℕ} {i j : Fin d} (hij : i ≠ j) {ζ : ℂ} (hζ : ζ * conj ζ = 1)
    {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.IsHermitian) :
    (s199a_q M (lsq_v i j ζ)).re = (M i i).re + (M j j).re + 2 * (M i j * conj ζ).re := by
  have hji : M j i = conj (M i j) := by
    have := hM.apply i j; rw [← this]; simp
  have e : s199a_q M (lsq_v i j ζ) = M i i + M i j * conj ζ + ζ * M j i + ζ * conj ζ * M j j := by
    simp [s199a_q, dotProduct, Matrix.mulVec, lsq_v, Pi.single_apply, add_mul, mul_add,
      Finset.sum_add_distrib, ite_mul, mul_ite, Finset.sum_ite_eq', apply_ite (starRingEnd ℂ),
      Finset.sum_ite_eq, hij, Ne.symm hij]
    ring
  rw [e, hζ, hji]
  simp only [Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im, one_mul, Complex.one_re,
    Complex.one_im, zero_mul, sub_zero]
  ring


lemma lsq_t_re {d n : ℕ} {M : Fin n → Matrix (Fin d) (Fin d) ℂ} (hM : IsPOVM M)
    (X : Matrix (Fin d) (Fin d) ℂ) (u : Fin n) :
    (s199a_t M X u).re = ((M u * X).trace).re / ((M u).trace).re := by
  obtain ⟨hT0, hTi⟩ := s199a_nonneg (hM.1 u).trace_nonneg
  have hmul := congrArg Complex.re (s199a_t_mul hM X u)
  simp only [Complex.mul_re, hTi, mul_zero, sub_zero] at hmul
  by_cases h : (M u).trace = 0
  · have : s199a_t M X u = 0 := by unfold s199a_t; simp [h]
    rw [this, h]; simp
  · have hT : ((M u).trace).re ≠ 0 := fun h' => h (Complex.ext h' hTi)
    rw [← hmul]; field_simp

lemma lsq_q_CG {d n : ℕ} (M : Fin n → Matrix (Fin d) (Fin d) ℂ) (X : Matrix (Fin d) (Fin d) ℂ)
    (v : Fin d → ℂ) :
    s199a_q (ergotropicCoarseGraining M X) v = ∑ u, s199a_t M X u * s199a_q (M u) v := by
  rw [← s199a_trace_mul_pd, s199a_CG_eq, Finset.sum_mul, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [Matrix.smul_mul, Matrix.trace_smul, s199a_trace_mul_pd, smul_eq_mul]

lemma lsq_qv {d n : ℕ} {M : Fin n → Matrix (Fin d) (Fin d) ℂ} (hM : IsPOVM M) {i j : Fin d}
    (hij : i ≠ j) (ζ : ℂ) :
    (s199a_q (ergotropicCoarseGraining M (lsq_X i j ζ)) (lsq_v i j ζ)).re =
      ∑ u, (((M u).trace.re - (M u i i).re - (M u j j).re + (s199a_q (M u) (lsq_v i j ζ)).re) / d
        / (M u).trace.re) * (s199a_q (M u) (lsq_v i j ζ)).re := by
  rw [lsq_q_CG, Complex.re_sum]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  have hq := s199a_nonneg ((Matrix.posSemidef_iff_dotProduct_mulVec.1 (hM.1 u)).2 (lsq_v i j ζ))
  have hq2 : (s199a_q (M u) (lsq_v i j ζ)).im = 0 := hq.2
  rw [Complex.mul_re, hq2, mul_zero, sub_zero, lsq_t_re hM, lsq_trMX hij]
  congr 2
  have : (1 / (d : ℂ)) = ((1 / (d : ℝ) : ℝ) : ℂ) := by push_cast; rfl
  rw [this, Complex.re_ofReal_mul]
  simp only [Complex.add_re, Complex.sub_re]
  ring

lemma lsq_q_smul {d : ℕ} (Y : Matrix (Fin d) (Fin d) ℂ) (v : Fin d → ℂ) (c : ℝ) :
    s199a_q Y ((c : ℂ) • v) = ((c ^ 2 : ℝ) : ℂ) * s199a_q Y v := by
  simp only [s199a_q, Matrix.mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct, smul_eq_mul]
  simp [Complex.conj_ofReal]; ring

lemma lsq_v_norm {d : ℕ} {i j : Fin d} (hij : i ≠ j) {ζ : ℂ} (hζ : ζ * conj ζ = 1) :
    ∑ k, Complex.normSq (lsq_v i j ζ k) = 2 := by
  rw [Fintype.sum_eq_add i j hij (fun k hk => by simp [lsq_v, Pi.single_apply, hk.1, hk.2])]
  have : Complex.normSq ζ = 1 := by
    have := congrArg Complex.re hζ; rw [Complex.mul_conj] at this; simpa using this
  simp [lsq_v, Pi.single_apply, hij, Ne.symm hij, this]; norm_num

lemma lsq_zeta {d n : ℕ} (h1 : 1 < d) (E : Fin d → ℝ) (hE : Monotone E)
    {M : Fin n → Matrix (Fin d) (Fin d) ℂ} (hM : IsPOVM M) {i j : Fin d} (hij : i ≠ j) {ζ : ℂ}
    (hζ : ζ * conj ζ = 1) :
    (E ⟨1, h1⟩ - E ⟨0, by omega⟩) *
      ((s199a_q (ergotropicCoarseGraining M (lsq_X i j ζ)) (lsq_v i j ζ)).re / 2 - 1 / d) ≤
      observationalAdvantage E M := by
  have hd : 0 < d := by omega
  haveI : NeZero d := ⟨hd.ne'⟩
  have hX := lsq_X_density hij hζ
  have hbdd : BddAbove {r | ∃ X : Matrix (Fin d) (Fin d) ℂ, IsDensityMatrix X ∧
      r = observationalErgotropy E M X - incoherentErgotropy E X} := by
    refine ⟨(∑ k, E k) / d - E ⟨0, hd⟩, ?_⟩
    rintro r ⟨Y, hY, rfl⟩
    rw [s199a_val]
    have h1 := s199a_PD_le E hY
    have h2 := s199a_ground hd E hE (s199a_CG_density hM hY)
    have hdR : (0:ℝ) < d := by exact_mod_cast hd
    have h3 : passiveEnergy E (energyDephasing Y) ≤ (∑ i, E i) / d := by
      rw [le_div_iff₀ hdR]; exact h1
    linarith
  refine le_trans ?_ (le_csSup hbdd ⟨_, hX, rfl⟩)
  rw [s199a_val, s199a_PD_mixed hd E _ (lsq_X_diag hij hζ)]
  set c : ℝ := (Real.sqrt 2)⁻¹
  set w : Fin d → ℂ := (c : ℂ) • lsq_v i j ζ
  have hc2 : c ^ 2 = 1 / 2 := by simp [c, inv_pow]
  have hw : ∑ k, Complex.normSq (w k) = 1 := by
    simp only [w, Pi.smul_apply, smul_eq_mul, Complex.normSq_mul, Complex.normSq_ofReal,
      ← Finset.mul_sum, lsq_v_norm hij hζ]
    nlinarith [hc2]
  have hP := lsq_passive h1 E hE (s199a_CG_density hM hX) w hw
  have hqw : (s199a_q (ergotropicCoarseGraining M (lsq_X i j ζ)) w).re =
      (s199a_q (ergotropicCoarseGraining M (lsq_X i j ζ)) (lsq_v i j ζ)).re / 2 := by
    rw [lsq_q_smul, hc2, Complex.re_ofReal_mul]; ring
  rw [hqw] at hP
  linarith

lemma lsq_four (T D a b d : ℝ) (hd : d ≠ 0) (hT : T = 0 → D = 0 ∧ a = 0 ∧ b = 0) :
    ((T - D + (D + 2 * a)) / d / T) * (D + 2 * a) + ((T - D + (D + 2 * -a)) / d / T) * (D + 2 * -a) +
      (((T - D + (D + 2 * b)) / d / T) * (D + 2 * b) + ((T - D + (D + 2 * -b)) / d / T) * (D + 2 * -b)) =
      (4 * D + 8 * ((a ^ 2 + b ^ 2) / T)) / d := by
  by_cases h : T = 0
  · obtain ⟨h1, h2, h3⟩ := hT h; subst h1 h2 h3; simp [h]
  · field_simp; ring

end QAlgorithms.Papers.Independent.Information100.P38

open scoped ComplexConjugate Matrix ComplexOrder

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100
  QAlgorithms.Papers.Independent.Information100.P38 in
theorem solution {d n : ℕ} (hd : 2 ≤ d) (hn : 0 < n)
    (E : Fin d → ℝ) (hE : Monotone E)
    (M : Fin n → Matrix (Fin d) (Fin d) ℂ) (hM : IsPOVM M) :
    minimumAdjacentEnergyGap E / (d : ℝ)^2 * (measurementLinfCoherence M)^2 ≤
      observationalAdvantage E M := by
  have h1 : 1 < d := by omega
  have hd0 : 0 < d := by omega
  set i0 : Fin d := ⟨0, hd0⟩
  set i1 : Fin d := ⟨1, h1⟩
  have hg : minimumAdjacentEnergyGap E ≤ E i1 - E i0 := by
    unfold minimumAdjacentEnergyGap
    refine csInf_le ?_ ⟨i0, i1, rfl, rfl⟩
    refine ((Set.finite_range (fun p : Fin d × Fin d => E p.2 - E p.1)).subset ?_).bddBelow
    rintro r ⟨a, b, -, rfl⟩; exact ⟨(a, b), rfl⟩
  obtain ⟨i, j, hij, hc⟩ : ∃ i j : Fin d, i < j ∧ measurementLinfCoherence M = ∑ u, ‖M u i j‖ := by
    have hne : Set.Nonempty {r | ∃ i j : Fin d, i < j ∧ r = ∑ u, ‖M u i j‖} :=
      ⟨_, i0, i1, Fin.lt_def.2 (by simp [i0, i1]), rfl⟩
    have hfin : Set.Finite {r | ∃ i j : Fin d, i < j ∧ r = ∑ u, ‖M u i j‖} :=
      (Set.finite_range (fun p : Fin d × Fin d => ∑ u, ‖M u p.1 p.2‖)).subset
        (by rintro r ⟨a, b, -, rfl⟩; exact ⟨(a, b), rfl⟩)
    exact hne.csSup_mem hfin
  have hij' : i ≠ j := ne_of_lt hij
  set c := measurementLinfCoherence M
  set A := E i1 - E i0 with hAdef
  have hA : 0 ≤ A := sub_nonneg.2 (hE (Fin.le_def.2 (by simp [i0, i1])))
  set T : Fin n → ℝ := fun u => (M u).trace.re with hTdef
  set W : ℝ := ∑ u, ‖M u i j‖ ^ 2 / T u with hWdef
  have hdR : (0:ℝ) < d := by exact_mod_cast hd0
  have hT0 : ∀ u, T u = 0 → M u = 0 := by
    intro u hu
    obtain ⟨-, hTi⟩ := s199a_nonneg (hM.1 u).trace_nonneg
    exact ((hM.1 u).trace_eq_zero_iff).1 (Complex.ext hu hTi)
  have hTnn : ∀ u, 0 ≤ T u := fun u => (s199a_nonneg (hM.1 u).trace_nonneg).1
  have hTsum : ∑ u, T u = d := by
    simp only [T]; rw [← Complex.re_sum, ← Matrix.trace_sum, hM.2]; simp
  have hDsum : ∑ u, ((M u i i).re + (M u j j).re) = 2 := by
    rw [Finset.sum_add_distrib, ← Complex.re_sum, ← Complex.re_sum, ← Matrix.sum_apply,
      ← Matrix.sum_apply, hM.2]
    simp; norm_num
  have hW : c ^ 2 / d ≤ W := by
    set l := c / d
    have key : ∀ u, 2 * l * ‖M u i j‖ - l ^ 2 * T u ≤ ‖M u i j‖ ^ 2 / T u := by
      intro u
      by_cases h : T u = 0
      · simp [h, hT0 u h]
      · have hTp : 0 < T u := lt_of_le_of_ne (hTnn u) (Ne.symm h)
        rw [le_div_iff₀ hTp]; nlinarith [sq_nonneg (‖M u i j‖ - l * T u)]
    have hs := Finset.sum_le_sum (fun u (_ : u ∈ Finset.univ) => key u)
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hTsum, ← hc] at hs
    have : c ^ 2 / d = 2 * l * c - l ^ 2 * d := by simp only [l]; field_simp; ring
    linarith
  have hq : ∀ ζ : ℂ, ζ * conj ζ = 1 →
      (s199a_q (ergotropicCoarseGraining M (lsq_X i j ζ)) (lsq_v i j ζ)).re =
      ∑ u, ((T u - ((M u i i).re + (M u j j).re) + ((M u i i).re + (M u j j).re +
        2 * (M u i j * conj ζ).re)) / d / T u) *
        ((M u i i).re + (M u j j).re + 2 * (M u i j * conj ζ).re) := by
    intro ζ hζ
    rw [lsq_qv hM hij']
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [lsq_P hij' hζ (hM.1 u).1]; simp only [T]; ring
  have e1 : (1 : ℂ) * conj 1 = 1 := by simp
  have e2 : (-1 : ℂ) * conj (-1) = 1 := by simp
  have e3 : Complex.I * conj Complex.I = 1 := by simp
  have e4 : (-Complex.I) * conj (-Complex.I) = 1 := by simp
  have z1 := lsq_zeta h1 E hE hM hij' e1
  have z2 := lsq_zeta h1 E hE hM hij' e2
  have z3 := lsq_zeta h1 E hE hM hij' e3
  have z4 := lsq_zeta h1 E hE hM hij' e4
  rw [hq _ e1] at z1
  rw [hq _ e2] at z2
  rw [hq _ e3] at z3
  rw [hq _ e4] at z4
  set Q1 := ∑ u, ((T u - ((M u i i).re + (M u j j).re) + ((M u i i).re + (M u j j).re +
        2 * (M u i j * conj 1).re)) / d / T u) * ((M u i i).re + (M u j j).re + 2 * (M u i j * conj 1).re)
  set Q2 := ∑ u, ((T u - ((M u i i).re + (M u j j).re) + ((M u i i).re + (M u j j).re +
        2 * (M u i j * conj (-1)).re)) / d / T u) *
        ((M u i i).re + (M u j j).re + 2 * (M u i j * conj (-1)).re)
  set Q3 := ∑ u, ((T u - ((M u i i).re + (M u j j).re) + ((M u i i).re + (M u j j).re +
        2 * (M u i j * conj Complex.I).re)) / d / T u) *
        ((M u i i).re + (M u j j).re + 2 * (M u i j * conj Complex.I).re)
  set Q4 := ∑ u, ((T u - ((M u i i).re + (M u j j).re) + ((M u i i).re + (M u j j).re +
        2 * (M u i j * conj (-Complex.I)).re)) / d / T u) *
        ((M u i i).re + (M u j j).re + 2 * (M u i j * conj (-Complex.I)).re)
  have hsum : Q1 + Q2 + (Q3 + Q4) = (8 + 8 * W) / d := by
    simp only [Q1, Q2, Q3, Q4]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    have : ∀ u, ((T u - ((M u i i).re + (M u j j).re) + ((M u i i).re + (M u j j).re +
        2 * (M u i j * conj 1).re)) / d / T u) * ((M u i i).re + (M u j j).re + 2 * (M u i j * conj 1).re) +
        ((T u - ((M u i i).re + (M u j j).re) + ((M u i i).re + (M u j j).re +
        2 * (M u i j * conj (-1)).re)) / d / T u) *
        ((M u i i).re + (M u j j).re + 2 * (M u i j * conj (-1)).re) +
        (((T u - ((M u i i).re + (M u j j).re) + ((M u i i).re + (M u j j).re +
        2 * (M u i j * conj Complex.I).re)) / d / T u) *
        ((M u i i).re + (M u j j).re + 2 * (M u i j * conj Complex.I).re) +
        ((T u - ((M u i i).re + (M u j j).re) + ((M u i i).re + (M u j j).re +
        2 * (M u i j * conj (-Complex.I)).re)) / d / T u) *
        ((M u i i).re + (M u j j).re + 2 * (M u i j * conj (-Complex.I)).re)) =
        (4 * ((M u i i).re + (M u j j).re) + 8 * (‖M u i j‖ ^ 2 / T u)) / d := by
      intro u
      have c1 : (M u i j * conj 1).re = (M u i j).re := by simp
      have c2 : (M u i j * conj (-1)).re = -(M u i j).re := by simp
      have c3 : (M u i j * conj Complex.I).re = (M u i j).im := by simp
      have c4 : (M u i j * conj (-Complex.I)).re = -(M u i j).im := by simp
      rw [c1, c2, c3, c4, Complex.sq_norm, Complex.normSq_apply, ← sq, ← sq]
      exact lsq_four _ _ _ _ _ hdR.ne' (fun h => by
        have h0 := hT0 u h
        simp [h0])
    rw [Finset.sum_congr rfl (fun u _ => this u), ← Finset.sum_div, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, hDsum]
    rw [hWdef]; ring
  have hmain : A * W / d ≤ observationalAdvantage E M := by
    have hs2 : A * (Q1 + Q2 + (Q3 + Q4)) = A * ((8 + 8 * W) / d) := by rw [hsum]
    have f1 : A * ((8 + 8 * W) / d) = 8 * (A / d) + 8 * (A * W / d) := by ring
    have g1 : A * (Q1 / 2 - 1 / d) = A * Q1 / 2 - A / d := by ring
    have g2 : A * (Q2 / 2 - 1 / d) = A * Q2 / 2 - A / d := by ring
    have g3 : A * (Q3 / 2 - 1 / d) = A * Q3 / 2 - A / d := by ring
    have g4 : A * (Q4 / 2 - 1 / d) = A * Q4 / 2 - A / d := by ring
    have g5 : A * (Q1 + Q2 + (Q3 + Q4)) = A * Q1 + A * Q2 + A * Q3 + A * Q4 := by ring
    linarith
  calc minimumAdjacentEnergyGap E / (d : ℝ)^2 * c^2 ≤ A / (d : ℝ)^2 * c^2 := by gcongr
    _ = A * (c ^ 2 / d) / d := by field_simp
    _ ≤ A * W / d := by gcongr
    _ ≤ observationalAdvantage E M := hmain
