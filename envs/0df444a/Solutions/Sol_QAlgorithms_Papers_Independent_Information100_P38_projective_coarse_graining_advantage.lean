-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P38.projective_coarse_graining_advantage
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T18:14:30.141146+00:00
-- url     : https://prove2.me/submissions/b0e5850c-eb75-4ad7-977b-4160349f1ac1

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P38
noncomputable section
namespace QAlgorithms.Papers.Independent.Information100.P38
open scoped ComplexConjugate Matrix ComplexOrder

lemma S172_energy_lb {d : ℕ} (E : Fin d → ℝ) (Y : Matrix (Fin d) (Fin d) ℂ)
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

lemma S172_bdd {d : ℕ} (E : Fin d → ℝ) (Y : Matrix (Fin d) (Fin d) ℂ) :
    BddBelow {r | ∃ U : Matrix.unitaryGroup (Fin d) ℂ,
      r = energyExpectation E ((U : Matrix (Fin d) (Fin d) ℂ) * Y * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ)} := by
  refine ⟨-((∑ i, |E i|) * ∑ k, ∑ l, ‖Y k l‖), ?_⟩
  rintro r ⟨U, rfl⟩
  exact S172_energy_lb E Y U U.2

lemma S172_passive_lb {d : ℕ} (E : Fin d → ℝ) (Y : Matrix (Fin d) (Fin d) ℂ) :
    -((∑ i, |E i|) * ∑ k, ∑ l, ‖Y k l‖) ≤ passiveEnergy E Y := by
  unfold passiveEnergy
  refine le_csInf ⟨_, 1, rfl⟩ ?_
  rintro r ⟨U, rfl⟩
  exact S172_energy_lb E Y U U.2

lemma S172_passive_le {d : ℕ} (E : Fin d → ℝ) (Y : Matrix (Fin d) (Fin d) ℂ) :
    passiveEnergy E Y ≤ energyExpectation E Y := by
  unfold passiveEnergy
  refine csInf_le (S172_bdd E Y) ⟨1, ?_⟩
  simp

lemma S172_energy_sum {d : ℕ} {ι : Type*} (E : Fin d → ℝ) (s : Finset ι) (w : ι → ℝ)
    (Y : ι → Matrix (Fin d) (Fin d) ℂ) :
    energyExpectation E (∑ σ ∈ s, (w σ : ℂ) • Y σ) = ∑ σ ∈ s, w σ * energyExpectation E (Y σ) := by
  unfold energyExpectation
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Complex.re_sum, Complex.re_ofReal_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun σ _ => Finset.sum_congr rfl (fun i _ => ?_))
  ring

/-- mixing unitary conjugates can only raise passive energy -/
lemma S172_passive_mix {d : ℕ} {ι : Type*} [Fintype ι] (E : Fin d → ℝ) (w : ι → ℝ)
    (hw : ∀ σ, 0 ≤ w σ) (hw1 : ∑ σ, w σ = 1) (V : ι → Matrix (Fin d) (Fin d) ℂ)
    (hV : ∀ σ, V σ ∈ Matrix.unitaryGroup (Fin d) ℂ) (Y : Matrix (Fin d) (Fin d) ℂ) :
    passiveEnergy E Y ≤ passiveEnergy E (∑ σ, (w σ : ℂ) • (V σ * Y * (V σ)ᴴ)) := by
  conv_rhs => unfold passiveEnergy
  refine le_csInf ⟨_, 1, rfl⟩ ?_
  rintro r ⟨U, rfl⟩
  have hexp : (U : Matrix (Fin d) (Fin d) ℂ) * (∑ σ, (w σ : ℂ) • (V σ * Y * (V σ)ᴴ)) *
      (U : Matrix (Fin d) (Fin d) ℂ)ᴴ =
      ∑ σ, (w σ : ℂ) • (((U : Matrix (Fin d) (Fin d) ℂ) * V σ) * Y * ((U : Matrix (Fin d) (Fin d) ℂ) * V σ)ᴴ) := by
    rw [Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  rw [hexp, S172_energy_sum]
  calc passiveEnergy E Y = ∑ σ, w σ * passiveEnergy E Y := by rw [← Finset.sum_mul, hw1, one_mul]
    _ ≤ _ := by
      refine Finset.sum_le_sum (fun σ _ => mul_le_mul_of_nonneg_left ?_ (hw σ))
      unfold passiveEnergy
      exact csInf_le (S172_bdd E Y) ⟨⟨_, Submonoid.mul_mem _ U.2 (hV σ)⟩, rfl⟩


/-- rank-one projectors of the columns of `Q` -/
def S172_P {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℂ) (i : Fin d) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun a b => Q a i * star (Q b i)

def S172_perm {d : ℕ} (σ : Equiv.Perm (Fin d)) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun k l => if l = σ k then 1 else 0

lemma S172_diag_sum {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℂ) (a : Fin d → ℂ) :
    ∑ k, a k • S172_P Q k = Q * Matrix.diagonal a * Qᴴ := by
  ext x y
  simp [S172_P, Matrix.sum_apply, Matrix.mul_apply, Matrix.diagonal, Finset.sum_ite_eq']
  refine Finset.sum_congr rfl (fun c _ => by ring)

lemma S172_perm_diag {d : ℕ} (σ : Equiv.Perm (Fin d)) (a : Fin d → ℂ) :
    S172_perm σ * Matrix.diagonal a * (S172_perm σ)ᴴ = Matrix.diagonal (fun k => a (σ k)) := by
  ext k m
  simp only [S172_perm, Matrix.mul_apply, Matrix.of_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply]
  simp [Finset.sum_ite_eq', Finset.sum_ite_eq, ite_mul, mul_ite, σ.injective.eq_iff]
  split_ifs <;> simp_all

lemma S172_perm_unitary {d : ℕ} (σ : Equiv.Perm (Fin d)) : S172_perm σ ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have := S172_perm_diag σ (fun _ => 1)
  simpa [Matrix.diagonal_one, Matrix.star_eq_conjTranspose] using this

lemma S172_conj_unitary {d : ℕ} (Q V : Matrix (Fin d) (Fin d) ℂ) (hQ : Q ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ) : Q * V * Qᴴ ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  have h3 : Qᴴ ∈ Matrix.unitaryGroup (Fin d) ℂ := by
    rw [← Matrix.star_eq_conjTranspose]; exact Unitary.star_mem hQ
  exact Submonoid.mul_mem _ (Submonoid.mul_mem _ hQ hV) h3


lemma S172_trace_P {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℂ) (hQ : Q ∈ Matrix.unitaryGroup (Fin d) ℂ) (u : Fin d) :
    (S172_P Q u).trace = 1 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.1 hQ) u) u
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at h
  rw [← h]
  simp [Matrix.trace, S172_P, mul_comm]

lemma S172_trace_PX {d : ℕ} (Q X : Matrix (Fin d) (Fin d) ℂ) (u : Fin d) :
    (S172_P Q u * X).trace = (Qᴴ * X * Q) u u := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, S172_P, Matrix.of_apply, Matrix.conjTranspose_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by ring))

lemma S172_CG_M {d : ℕ} (Q X : Matrix (Fin d) (Fin d) ℂ) (hQ : Q ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    ergotropicCoarseGraining (S172_P Q) X = Q * Matrix.diagonal (fun i => (Qᴴ * X * Q) i i) * Qᴴ := by
  rw [← S172_diag_sum]
  unfold ergotropicCoarseGraining
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [S172_trace_P Q hQ, S172_trace_PX]
  simp

lemma S172_CG_D {d n : ℕ} (Q X : Matrix (Fin d) (Fin d) ℂ) (hQ : Q ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (D : Fin n → Fin d → ℝ) :
    ergotropicCoarseGraining (postprocessedEnergyMeasurement D (S172_P Q)) X =
      Q * Matrix.diagonal (fun k => ∑ j, if (∑ i, D j i : ℝ) = 0 then 0 else
        ((∑ i, (D j i : ℂ) * (Qᴴ * X * Q) i i) / ((∑ i, D j i : ℝ) : ℂ) * (D j k : ℂ))) * Qᴴ := by
  rw [← S172_diag_sum]
  unfold ergotropicCoarseGraining postprocessedEnergyMeasurement
  have htr : ∀ j, (∑ i, (D j i : ℂ) • S172_P Q i).trace = ((∑ i, D j i : ℝ) : ℂ) := by
    intro j; rw [Matrix.trace_sum]; simp [Matrix.trace_smul, S172_trace_P Q hQ]
  have htrX : ∀ j, ((∑ i, (D j i : ℂ) • S172_P Q i) * X).trace = ∑ i, (D j i : ℂ) * (Qᴴ * X * Q) i i := by
    intro j; rw [Matrix.sum_mul, Matrix.trace_sum]
    simp [Matrix.smul_mul, Matrix.trace_smul, S172_trace_PX]
  simp only [htr, htrX, Complex.ofReal_eq_zero]
  simp only [Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs with h
  · simp
  · rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [smul_smul]


lemma S172_birkhoff {d n : ℕ} (D : Fin n → Fin d → ℝ) (hD : ∀ j i, 0 ≤ D j i)
    (hcol : ∀ i, ∑ j, D j i = 1) (p : Fin d → ℂ) :
    ∃ w : Equiv.Perm (Fin d) → ℝ, (∀ σ, 0 ≤ w σ) ∧ ∑ σ, w σ = 1 ∧
      (fun k => ∑ j, if (∑ i, D j i : ℝ) = 0 then 0 else
        ((∑ i, (D j i : ℂ) * p i) / ((∑ i, D j i : ℝ) : ℂ) * (D j k : ℂ))) =
      fun k => ∑ σ, (w σ : ℂ) * p (σ k) := by
  set c : Fin n → ℝ := fun j => ∑ i, D j i with hc
  have hc0 : ∀ j, 0 ≤ c j := fun j => Finset.sum_nonneg (fun i _ => hD j i)
  have hzero : ∀ j i, c j = 0 → D j i = 0 := by
    intro j i h
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hD j i)).1 h i (Finset.mem_univ _)
  let S : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun k i => ∑ j, if c j = 0 then 0 else D j k * D j i / c j
  have hrow : ∀ k, ∑ i, S k i = 1 := by
    intro k
    simp only [S, Matrix.of_apply]
    rw [Finset.sum_comm, ← hcol k]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs with h
    · simp [hzero j k h]
    · rw [← Finset.sum_div, ← Finset.mul_sum]; show D j k * c j / c j = D j k; field_simp
  have hsymm : ∀ k i, S k i = S i k := by
    intro k i; simp only [S, Matrix.of_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_); rw [mul_comm (D j k)]
  have hS : S ∈ doublyStochastic ℝ (Fin d) := by
    rw [mem_doublyStochastic_iff_sum]
    refine ⟨fun k i => ?_, hrow, fun i => ?_⟩
    · simp only [S, Matrix.of_apply]
      refine Finset.sum_nonneg (fun j _ => ?_)
      split_ifs
      · exact le_refl _
      · exact div_nonneg (mul_nonneg (hD j k) (hD j i)) (hc0 j)
    · rw [← hrow i]; exact Finset.sum_congr rfl (fun k _ => hsymm k i)
  obtain ⟨w, hw0, hw1, hwS⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hS
  refine ⟨w, hw0, hw1, ?_⟩
  funext k
  have hSk : ∀ i, S k i = ∑ σ, w σ * (if σ k = i then 1 else 0) := by
    intro i
    rw [← hwS]
    simp [Matrix.sum_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
  have h1 : (∑ j, if c j = 0 then (0 : ℂ) else
        ((∑ i, (D j i : ℂ) * p i) / ((c j : ℝ) : ℂ) * (D j k : ℂ))) = ∑ i, (S k i : ℂ) * p i := by
    simp only [S, Matrix.of_apply, Complex.ofReal_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs with h
    · simp
    · rw [Finset.sum_div, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      push_cast; ring
  simp only [hc] at h1
  rw [h1]
  simp only [hSk, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  simp only [apply_ite (fun x : ℝ => (x : ℂ)), Complex.ofReal_one, Complex.ofReal_zero, ite_mul, one_mul, zero_mul,
    mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]; simp


lemma S172_mix_eq {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℂ) (hQ : Q ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (w : Equiv.Perm (Fin d) → ℝ) (p : Fin d → ℂ) :
    Q * Matrix.diagonal (fun k => ∑ σ, (w σ : ℂ) * p (σ k)) * Qᴴ =
      ∑ σ, (w σ : ℂ) • ((Q * S172_perm σ * Qᴴ) * (Q * Matrix.diagonal p * Qᴴ) * (Q * S172_perm σ * Qᴴ)ᴴ) := by
  have hQQ : Qᴴ * Q = 1 := by rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.1 hQ
  have hd : Matrix.diagonal (fun k => ∑ σ, (w σ : ℂ) * p (σ k)) =
      ∑ σ, (w σ : ℂ) • Matrix.diagonal (fun k => p (σ k)) := by
    ext a b
    simp [Matrix.diagonal_apply, Matrix.sum_apply]
  rw [hd, Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [← S172_perm_diag σ p]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  simp only [Matrix.mul_assoc]
  first
  | rfl
  | simp only [← Matrix.mul_assoc Qᴴ Q, hQQ, Matrix.one_mul]

lemma S172_pointwise {d n : ℕ} (E : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℂ)
    (hQ : Q ∈ Matrix.unitaryGroup (Fin d) ℂ) (D : Fin n → Fin d → ℝ) (hD : ∀ j i, 0 ≤ D j i)
    (hcol : ∀ i, ∑ j, D j i = 1) (X : Matrix (Fin d) (Fin d) ℂ) :
    passiveEnergy E (ergotropicCoarseGraining (S172_P Q) X) ≤
      passiveEnergy E (ergotropicCoarseGraining (postprocessedEnergyMeasurement D (S172_P Q)) X) := by
  obtain ⟨w, hw0, hw1, hwq⟩ := S172_birkhoff D hD hcol (fun i => (Qᴴ * X * Q) i i)
  rw [S172_CG_D Q X hQ D, hwq, S172_CG_M Q X hQ, S172_mix_eq Q hQ w (fun i => (Qᴴ * X * Q) i i)]
  exact S172_passive_mix E w hw0 hw1 _ (fun σ => S172_conj_unitary Q _ hQ (S172_perm_unitary σ)) _



lemma S172_diag_norm {d : ℕ} (Y : Matrix (Fin d) (Fin d) ℂ) (hY : IsDensityMatrix Y) :
    ∑ i, ‖Y i i‖ = 1 ∧ ∀ i, ‖Y i i‖ ≤ 1 := by
  have hn : ∀ i, ‖Y i i‖ = (Y i i).re := by
    intro i
    have h0 : 0 ≤ Y i i := hY.1.diag_nonneg
    obtain ⟨hre, him⟩ := Complex.nonneg_iff.1 h0
    rw [← Complex.re_add_im (Y i i), ← him]
    simp [abs_of_nonneg hre]
  have hs : ∑ i, ‖Y i i‖ = 1 := by
    simp only [hn, ← Complex.re_sum]
    have := hY.2; simp only [Matrix.trace, Matrix.diag] at this; rw [this]; simp
  refine ⟨hs, fun i => ?_⟩
  rw [← hs]
  exact Finset.single_le_sum (f := fun i => ‖Y i i‖) (fun i _ => norm_nonneg _) (Finset.mem_univ i)

lemma S172_GM_entry {d : ℕ} (Q X : Matrix (Fin d) (Fin d) ℂ) (hQ : Q ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hX : IsDensityMatrix X) (a b : Fin d) :
    ‖(Q * Matrix.diagonal (fun i => (Qᴴ * X * Q) i i) * Qᴴ) a b‖ ≤ 1 := by
  have hY : IsDensityMatrix (Qᴴ * X * Q) := by
    refine ⟨hX.1.conjTranspose_mul_mul_same Q, ?_⟩
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose,
      Matrix.mem_unitaryGroup_iff.1 hQ, Matrix.one_mul, hX.2]
  obtain ⟨hs, -⟩ := S172_diag_norm _ hY
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  calc ‖∑ k, Q a k * (Qᴴ * X * Q) k k * star (Q b k)‖ ≤ ∑ k, ‖Q a k * (Qᴴ * X * Q) k k * star (Q b k)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ k, ‖(Qᴴ * X * Q) k k‖ := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        rw [norm_mul, norm_mul, norm_star]
        have h1 := entry_norm_bound_of_unitary hQ a k
        have h2 := entry_norm_bound_of_unitary hQ b k
        have h3 := norm_nonneg ((Qᴴ * X * Q) k k)
        nlinarith [norm_nonneg (Q a k), norm_nonneg (Q b k), mul_le_mul h1 h2 (norm_nonneg _) zero_le_one]
    _ = 1 := hs


lemma S172_M_eq {d : ℕ} (M : Fin d → Matrix (Fin d) (Fin d) ℂ) (hM : rankOneEnergyMeasurement M) :
    ∃ Q : Matrix (Fin d) (Fin d) ℂ, Q ∈ Matrix.unitaryGroup (Fin d) ℂ ∧ M = S172_P Q := by
  obtain ⟨B, hB⟩ := hM
  refine ⟨(EuclideanSpace.basisFun (Fin d) ℂ).toBasis.toMatrix B.toBasis,
    (EuclideanSpace.basisFun (Fin d) ℂ).toMatrix_orthonormalBasis_mem_unitary B, ?_⟩
  funext i
  ext a b
  rw [hB i]
  simp [pureDensity, S172_P, Module.Basis.toMatrix_apply]

lemma S172_energy_deph {d : ℕ} (E : Fin d → ℝ) (X : Matrix (Fin d) (Fin d) ℂ) :
    energyExpectation E (energyDephasing X) = energyExpectation E X := by
  simp [energyExpectation, energyDephasing]

end QAlgorithms.Papers.Independent.Information100.P38

open scoped ComplexConjugate Matrix ComplexOrder

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100
  QAlgorithms.Papers.Independent.Information100.P38 in
theorem solution {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (E : Fin d → ℝ) (hE : Monotone E)
    (M : Fin d → Matrix (Fin d) (Fin d) ℂ) (hM : rankOneEnergyMeasurement M)
    (D : Fin n → Fin d → ℝ) (hD : ∀ j i, 0 ≤ D j i) (hcol : ∀ i, ∑ j, D j i = 1) :
    (∀ X, IsDensityMatrix X →
      observationalErgotropy E (postprocessedEnergyMeasurement D M) X ≤ observationalErgotropy E M X) ∧
    observationalAdvantage E (postprocessedEnergyMeasurement D M) ≤ observationalAdvantage E M := by
  obtain ⟨Q, hQ, rfl⟩ := S172_M_eq M hM
  have hpt : ∀ X : Matrix (Fin d) (Fin d) ℂ,
      observationalErgotropy E (postprocessedEnergyMeasurement D (S172_P Q)) X ≤
        observationalErgotropy E (S172_P Q) X := by
    intro X
    unfold observationalErgotropy
    linarith [S172_pointwise E Q hQ D hD hcol X]
  refine ⟨fun X _ => hpt X, ?_⟩
  -- nonempty: a pure diagonal state
  let i0 : Fin d := ⟨0, hd⟩
  let X0 : Matrix (Fin d) (Fin d) ℂ := Matrix.diagonal (Pi.single i0 1)
  have hX0 : IsDensityMatrix X0 := by
    refine ⟨Matrix.posSemidef_diagonal_iff.2 (fun i => ?_), ?_⟩
    · by_cases h : i = i0
      · subst h; simp
      · simp [Pi.single_apply, h]
    · simp [X0, Matrix.trace_diagonal, i0]
  -- bounded above
  have hbdd : BddAbove {r | ∃ X : Matrix (Fin d) (Fin d) ℂ, IsDensityMatrix X ∧
      r = observationalErgotropy E (S172_P Q) X - incoherentErgotropy E X} := by
    refine ⟨(∑ i, |E i|) + (∑ i, |E i|) * ∑ k : Fin d, ∑ l : Fin d, (1 : ℝ), ?_⟩
    rintro r ⟨X, hX, rfl⟩
    unfold observationalErgotropy incoherentErgotropy
    rw [S172_energy_deph, S172_CG_M Q X hQ]
    have h1 := S172_passive_le E (energyDephasing X)
    have h2 := S172_passive_lb E (Q * Matrix.diagonal (fun i => (Qᴴ * X * Q) i i) * Qᴴ)
    have h3 : (∑ i, |E i|) * ∑ k, ∑ l, ‖(Q * Matrix.diagonal (fun i => (Qᴴ * X * Q) i i) * Qᴴ) k l‖ ≤
        (∑ i, |E i|) * ∑ k : Fin d, ∑ l : Fin d, (1 : ℝ) := by
      refine mul_le_mul_of_nonneg_left ?_ (Finset.sum_nonneg (fun i _ => abs_nonneg _))
      exact Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun l _ => S172_GM_entry Q X hQ hX k l))
    have h4 : energyExpectation E (energyDephasing X) ≤ ∑ i, |E i| := by
      rw [S172_energy_deph]
      unfold energyExpectation
      refine Finset.sum_le_sum (fun i _ => ?_)
      have hb := (S172_diag_norm X hX).2 i
      have : |E i * (X i i).re| ≤ |E i| := by
        rw [abs_mul]
        calc |E i| * |(X i i).re| ≤ |E i| * 1 :=
              mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans hb) (abs_nonneg _)
          _ = |E i| := mul_one _
      exact (le_abs_self _).trans this
    linarith
  unfold observationalAdvantage
  refine csSup_le ⟨_, X0, hX0, rfl⟩ ?_
  rintro r ⟨X, hX, rfl⟩
  exact le_csSup_of_le hbdd ⟨X, hX, rfl⟩ (by linarith [hpt X])
