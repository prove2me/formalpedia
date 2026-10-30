-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P03.orthogonal_block_sdp
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:29:47.912389+00:00
-- url     : https://prove2.me/submissions/67aa8024-3695-41f7-926f-4c9225c555fc

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P03
noncomputable section

namespace S110sdp
open Matrix
open scoped Matrix ComplexOrder

lemma herm_le_smul {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) : ∃ c : ℝ, 0 ≤ c ∧ (((c : ℂ) • (1 : Matrix n n ℂ)) - A).PosSemidef := by
  refine ⟨∑ i, |hA.eigenvalues i|, Finset.sum_nonneg (fun i _ => abs_nonneg _), ?_⟩
  set c : ℝ := ∑ i, |hA.eigenvalues i|
  have hspec := hA.spectral_theorem
  have : ((c : ℂ) • (1 : Matrix n n ℂ)) - A =
      Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
        (diagonal (fun i => ((c - hA.eigenvalues i : ℝ) : ℂ))) := by
    conv_lhs => rw [hspec]
    rw [← map_one (Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary), ← map_smul, ← map_sub]
    congr 1
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [h, one_apply_ne h]
  rw [this, Unitary.conjStarAlgAut_apply, star_eq_conjTranspose]
  apply PosSemidef.mul_mul_conjTranspose_same
  apply PosSemidef.diagonal
  intro i
  simp only [Pi.zero_apply]
  have : hA.eigenvalues i ≤ c :=
    (le_abs_self _).trans (Finset.single_le_sum (f := fun i => |hA.eigenvalues i|)
      (fun i _ => abs_nonneg _) (Finset.mem_univ i))
  exact_mod_cast (show (0:ℝ) ≤ c - hA.eigenvalues i by linarith)

def E {P1 P2 Q : Type*} (A : Matrix P1 P1 ℂ) (X : Matrix (P2 × Q) (P2 × Q) ℂ) :
    Matrix ((P1 × P2) × Q) ((P1 × P2) × Q) ℂ :=
  Matrix.of fun p q => A p.1.1 q.1.1 * X (p.1.2, p.2) (q.1.2, q.2)

lemma E_psd {P1 P2 Q : Type*} [Fintype P1] [Fintype P2] [Fintype Q]
    {A : Matrix P1 P1 ℂ} {X : Matrix (P2 × Q) (P2 × Q) ℂ}
    (hA : A.PosSemidef) (hX : X.PosSemidef) : (E A X).PosSemidef := by
  have := (hA.kronecker hX).submatrix (fun p : (P1 × P2) × Q => (p.1.1, (p.1.2, p.2)))
  exact this

def Vm {P1 P2 Q : Type*} [DecidableEq P2] [DecidableEq Q] (u : P1 → ℂ) :
    Matrix ((P1 × P2) × Q) (P2 × Q) ℂ :=
  Matrix.of fun p r => u p.1.1 * (if (p.1.2, p.2) = r then 1 else 0)

lemma compress {P1 P2 Q : Type*} [Fintype P1] [Fintype P2] [Fintype Q]
    [DecidableEq P2] [DecidableEq Q] (u : P1 → ℂ)
    (A : Matrix P1 P1 ℂ) (X : Matrix (P2 × Q) (P2 × Q) ℂ) :
    (Vm (P2 := P2) (Q := Q) u)ᴴ * E A X * Vm (P2 := P2) (Q := Q) u = (∑ x, ∑ y, star (u x) * A x y * u y) • X := by
  ext r s
  obtain ⟨b0, q0⟩ := r
  obtain ⟨b1, q1⟩ := s
  have hs : ∀ (c : Prop) [Decidable c] (a b : ℂ),
      star (if c then a else b) = if c then star a else star b := by
    intro c _ a b; split_ifs <;> rfl
  simp only [Vm, E, Matrix.mul_apply, conjTranspose_apply, of_apply, Fintype.sum_prod_type,
    Matrix.smul_apply, smul_eq_mul, Finset.sum_mul, star_mul', hs, Prod.mk.injEq, ite_and]
  simp only [hs, star_one, star_zero, mul_ite, ite_mul, mul_zero, zero_mul, mul_one,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  ring


open QAlgorithms.Papers.Independent.Extend50.P03

lemma kron_one_eq {P1 P2 Q : Type*} [DecidableEq P1] [DecidableEq P2]
    (σ : Matrix Q Q ℂ) :
    Matrix.kronecker (1 : Matrix (P1 × P2) (P1 × P2) ℂ) σ =
      E (1 : Matrix P1 P1 ℂ) (Matrix.kronecker (1 : Matrix P2 P2 ℂ) σ) := by
  ext ⟨⟨a, b⟩, q⟩ ⟨⟨a', b'⟩, q'⟩
  simp only [E, of_apply, kronecker, kroneckerMap_apply, one_apply, Prod.mk.injEq]
  split_ifs <;> simp_all

lemma block_eq {P1 P2 Q : Type*} {m : ℕ} (Pi : Fin m → Matrix P1 P1 ℂ)
    (rho : Fin m → Matrix (P2 × Q) (P2 × Q) ℂ) :
    orthogonalBlockOperator Pi rho = ∑ i, E (Pi i) (rho i) := by
  ext p q
  simp [orthogonalBlockOperator, E, Matrix.sum_apply]

lemma minSdp_le {P Q : Type*} [Fintype P] [Fintype Q] [DecidableEq P] [DecidableEq Q]
    (rho : Matrix (P × Q) (P × Q) ℂ) (σ : Matrix Q Q ℂ) (hσ : σ.PosSemidef)
    (hf : (Matrix.kronecker (1 : Matrix P P ℂ) σ - rho).PosSemidef) :
    minSdp rho ≤ σ.trace.re := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro s ⟨τ, hτ, -, rfl⟩
    exact (Complex.nonneg_iff.mp hτ.trace_nonneg).1
  · exact ⟨σ, hσ, hf, rfl⟩

lemma minSdp_nonempty {P Q : Type*} [Fintype P] [Fintype Q] [DecidableEq P] [DecidableEq Q]
    (rho : Matrix (P × Q) (P × Q) ℂ) (hr : rho.IsHermitian) :
    {s : ℝ | ∃ sigma : Matrix Q Q ℂ, sigma.PosSemidef ∧
      (Matrix.kronecker (1 : Matrix P P ℂ) sigma - rho).PosSemidef ∧ s = sigma.trace.re}.Nonempty := by
  obtain ⟨c, hc, h⟩ := herm_le_smul hr
  refine ⟨_, (c : ℂ) • (1 : Matrix Q Q ℂ), PosSemidef.one.smul (by exact_mod_cast hc), ?_, rfl⟩
  have hk : Matrix.kronecker (1 : Matrix P P ℂ) ((c : ℂ) • (1 : Matrix Q Q ℂ)) =
      (c : ℂ) • (1 : Matrix (P × Q) (P × Q) ℂ) := by
    ext ⟨a, b⟩ ⟨a', b'⟩
    simp only [kronecker, kroneckerMap_apply, one_apply, Prod.mk.injEq, Matrix.smul_apply]
    split_ifs <;> simp_all
  rw [hk]
  exact h

lemma minSdp_ge {P Q : Type*} [Fintype P] [Fintype Q] [DecidableEq P] [DecidableEq Q]
    (rho : Matrix (P × Q) (P × Q) ℂ) (hr : rho.IsHermitian) (t : ℝ)
    (h : ∀ σ : Matrix Q Q ℂ, σ.PosSemidef →
      (Matrix.kronecker (1 : Matrix P P ℂ) σ - rho).PosSemidef → t ≤ σ.trace.re) :
    t ≤ minSdp rho := by
  apply le_csInf (minSdp_nonempty rho hr)
  rintro s ⟨σ, h1, h2, rfl⟩
  exact h σ h1 h2

end S110sdp


open MeasureTheory Filter

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Extend50.P03

open QAlgorithms.Papers.Independent.Support50.P23 (minEntropy)

attribute [local instance] Classical.propDecidable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P03.matrixContinuousENorm

end QAlgorithms.Papers.Independent.Extend50.P03


open QAlgorithms QAlgorithms.Papers.Independent.Extend50.P03 S110sdp Matrix

theorem solution {P1 P2 Q : Type*}
    [Fintype P1] [Fintype P2] [Fintype Q]
    [DecidableEq P1] [DecidableEq P2] [DecidableEq Q]
    [Nonempty P1] [Nonempty P2] [Nonempty Q]
    {m : ℕ} (hm : 1 ≤ m) (Pi : Fin m → Matrix P1 P1 ℂ)
    (rho : Fin m → Matrix (P2 × Q) (P2 × Q) ℂ)
    (hPi : ∀ i, (Pi i).IsHermitian ∧ Pi i * Pi i = Pi i ∧ Pi i ≠ 0)
    (horth : ∀ i j, i ≠ j → Pi i * Pi j = 0)
    (hrho : ∀ i, (rho i).PosSemidef)
    (hnorm : IsDensityMatrix (orthogonalBlockOperator Pi rho)) :
    (∑ i, minSdp (rho i)) / (m : ℝ) ≤ minSdp (orthogonalBlockOperator Pi rho) ∧
      minSdp (orthogonalBlockOperator Pi rho) ≤ ∑ i, minSdp (rho i) := by
  have hB : (orthogonalBlockOperator Pi rho).IsHermitian := hnorm.1.1
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  constructor
  · -- lower bound
    have key : ∀ i, minSdp (rho i) ≤ minSdp (orthogonalBlockOperator Pi rho) := by
      intro i
      apply minSdp_ge _ hB
      intro σ hσ hf
      apply minSdp_le _ σ hσ
      -- compress
      obtain ⟨a, b, hab⟩ : ∃ a b, Pi i a b ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact (hPi i).2.2 (Matrix.ext hcon)
      set u : P1 → ℂ := fun x => Pi i x b with hu
      have hcol : ∀ j, ∀ x, ∑ y, Pi j x y * u y = (Pi j * Pi i) x b := by
        intro j x; simp [hu, Matrix.mul_apply]
      have hcj : ∀ j, j ≠ i → (∑ x, ∑ y, star (u x) * Pi j x y * u y) = 0 := by
        intro j hj
        have : ∀ x, ∑ y, star (u x) * Pi j x y * u y = 0 := by
          intro x
          simp_rw [mul_assoc, ← Finset.mul_sum, hcol, horth j i hj]
          simp
        exact Finset.sum_eq_zero (fun x _ => this x)
      have hci : (∑ x, ∑ y, star (u x) * Pi i x y * u y) = ∑ x, star (u x) * u x := by
        refine Finset.sum_congr rfl (fun x _ => ?_)
        simp_rw [mul_assoc, ← Finset.mul_sum, hcol, (hPi i).2.1]
        rfl
      have hc1 : (∑ x, ∑ y, star (u x) * (1 : Matrix P1 P1 ℂ) x y * u y) =
          ∑ x, star (u x) * u x := by
        refine Finset.sum_congr rfl (fun x _ => ?_)
        simp [one_apply]
      set r : ℝ := ∑ x, ‖u x‖ ^ 2 with hr
      have hcr : (∑ x, star (u x) * u x) = (r : ℂ) := by
        simp only [hr, Complex.ofReal_sum, Complex.ofReal_pow]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [Complex.star_def, Complex.conj_mul']
      have hrpos : 0 < r := by
        have : 0 < ‖u a‖ ^ 2 := by
          have : u a ≠ 0 := hab
          positivity
        exact lt_of_lt_of_le this (Finset.single_le_sum (f := fun x => ‖u x‖ ^ 2)
          (fun x _ => by positivity) (Finset.mem_univ a))
      have hcomp := hf.conjTranspose_mul_mul_same (Vm (P2 := P2) (Q := Q) u)
      rw [kron_one_eq, block_eq, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_sum, Matrix.sum_mul,
        compress u] at hcomp
      simp_rw [compress u] at hcomp
      rw [Finset.sum_eq_single i (fun j _ hj => by rw [hcj j hj, zero_smul])
        (by simp), hci, hc1, hcr, ← smul_sub] at hcomp
      have := hcomp.smul (show (0 : ℂ) ≤ ((r⁻¹ : ℝ) : ℂ) from by
        exact_mod_cast (inv_nonneg.mpr hrpos.le))
      rw [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hrpos.ne', Complex.ofReal_one,
        one_smul] at this
      exact this
    have hsum : ∑ i, minSdp (rho i) ≤ m * minSdp (orthogonalBlockOperator Pi rho) := by
      calc ∑ i, minSdp (rho i) ≤ ∑ _i : Fin m, minSdp (orthogonalBlockOperator Pi rho) :=
            Finset.sum_le_sum (fun i _ => key i)
        _ = m * minSdp (orthogonalBlockOperator Pi rho) := by simp
    rw [div_le_iff₀ hmpos]
    linarith
  · -- upper bound
    -- projector complement
    set S : Matrix P1 P1 ℂ := ∑ i, Pi i with hS
    have hSS : S * S = S := by
      rw [hS, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.sum_eq_single i (fun j _ hj => horth i j (Ne.symm hj)) (by simp), (hPi i).2.1]
    have hSH : Sᴴ = S := by
      rw [hS, conjTranspose_sum]
      exact Finset.sum_congr rfl (fun i _ => (hPi i).1.eq)
    have hQ : (1 - S).PosSemidef := by
      have : (1 - S) = (1 - S)ᴴ * (1 - S) := by
        rw [conjTranspose_sub, conjTranspose_one, hSH, Matrix.sub_mul, Matrix.mul_sub,
          Matrix.mul_sub, hSS]
        simp
      rw [this]
      exact posSemidef_conjTranspose_mul_self _
    apply le_of_forall_pos_lt_add
    intro ε hε
    have hδ : 0 < ε / m := div_pos hε hmpos
    have hch : ∀ i, ∃ σ : Matrix Q Q ℂ, σ.PosSemidef ∧
        (Matrix.kronecker (1 : Matrix P2 P2 ℂ) σ - rho i).PosSemidef ∧
        σ.trace.re < minSdp (rho i) + ε / m := by
      intro i
      obtain ⟨s, ⟨σ, h1, h2, rfl⟩, hlt⟩ :=
        Real.lt_sInf_add_pos (minSdp_nonempty (rho i) (hrho i).1) hδ
      exact ⟨σ, h1, h2, hlt⟩
    choose σ hσ1 hσ2 hσ3 using hch
    have hσsum : (∑ i, σ i).PosSemidef := posSemidef_sum _ (fun i _ => hσ1 i)
    set K : Matrix (P2 × Q) (P2 × Q) ℂ := Matrix.kronecker (1 : Matrix P2 P2 ℂ) (∑ i, σ i) with hK
    have hKpsd : K.PosSemidef := PosSemidef.one.kronecker hσsum
    have hKi : ∀ i, (K - rho i).PosSemidef := by
      intro i
      have : K - rho i = (Matrix.kronecker (1 : Matrix P2 P2 ℂ) (σ i) - rho i) +
          Matrix.kronecker (1 : Matrix P2 P2 ℂ) (∑ j ∈ Finset.univ.erase i, σ j) := by
        rw [hK, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
        ext p q
        simp only [kronecker, kroneckerMap_apply, Matrix.sub_apply, Matrix.add_apply, mul_add]
        ring
      rw [this]
      exact (hσ2 i).add (PosSemidef.one.kronecker
        (posSemidef_sum _ (fun j _ => hσ1 j)))
    have hfeas : (Matrix.kronecker (1 : Matrix (P1 × P2) (P1 × P2) ℂ) (∑ i, σ i) -
        orthogonalBlockOperator Pi rho).PosSemidef := by
      have : Matrix.kronecker (1 : Matrix (P1 × P2) (P1 × P2) ℂ) (∑ i, σ i) -
          orthogonalBlockOperator Pi rho = E (1 - S) K + ∑ i, E (Pi i) (K - rho i) := by
        rw [kron_one_eq, block_eq]
        ext p q
        simp only [E, of_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.sum_apply, hS, ← hK]
        simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
        ring
      rw [this]
      refine (E_psd hQ hKpsd).add (posSemidef_sum _ (fun i _ => E_psd ?_ (hKi i)))
      have : Pi i = (Pi i)ᴴ * Pi i := by rw [(hPi i).1.eq, (hPi i).2.1]
      rw [this]
      exact posSemidef_conjTranspose_mul_self _
    calc minSdp (orthogonalBlockOperator Pi rho) ≤ (∑ i, σ i).trace.re :=
          minSdp_le _ _ hσsum hfeas
      _ = ∑ i, (σ i).trace.re := by rw [trace_sum, Complex.re_sum]
      _ < ∑ i, (minSdp (rho i) + ε / m) := by
          apply Finset.sum_lt_sum_of_nonempty
          · exact Finset.univ_nonempty_iff.mpr ⟨⟨0, hm⟩⟩
          · intro i _; exact hσ3 i
      _ = ∑ i, minSdp (rho i) + ε := by
          rw [Finset.sum_add_distrib]
          simp [Finset.card_univ]
          field_simp

end
