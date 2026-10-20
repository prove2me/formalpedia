-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P44.alignedThermalUnitaries
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T03:47:02.533881+00:00
-- url     : https://prove2.me/submissions/d29e8e65-4700-4697-92a8-15df2948fa55

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

open scoped Matrix

lemma g53h_spec_mul {m n l : Type*} [Fintype m] [Fintype n] [Fintype l] [DecidableEq n] [DecidableEq l]
    (A : Matrix m n ℂ) (B : Matrix n l ℂ) :
    QAlgorithms.specNorm (A * B) ≤ QAlgorithms.specNorm A * QAlgorithms.specNorm B := by
  unfold QAlgorithms.specNorm; exact Matrix.l2_opNorm_mul A B

lemma g53h_spec_nonneg {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (U : Matrix m n ℂ) : 0 ≤ QAlgorithms.specNorm U := by
  unfold QAlgorithms.specNorm
  let _ := Matrix.instL2OpNormedAddCommGroup (m := m) (n := n) (𝕜 := ℂ)
  exact norm_nonneg _

lemma g53h_spec_isom_le {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (U : Matrix m n ℂ) (hU : Uᴴ * U = 1) : QAlgorithms.specNorm U ≤ 1 := by
  unfold QAlgorithms.specNorm
  have h := Matrix.l2_opNorm_conjTranspose_mul_self U
  have h1 := Matrix.l2_opNorm_conjTranspose_mul_self (1 : Matrix n n ℂ)
  rw [hU] at h
  rw [Matrix.conjTranspose_one, one_mul] at h1
  have h0 := g53h_spec_nonneg U
  have h0' := g53h_spec_nonneg (1 : Matrix n n ℂ)
  unfold QAlgorithms.specNorm at h0 h0'
  generalize @Norm.norm (Matrix n n ℂ) (Matrix.instL2OpNormedAddCommGroup).toNorm 1 = z at *
  generalize @Norm.norm (Matrix m n ℂ) (Matrix.instL2OpNormedAddCommGroup).toNorm U = w at *
  have hz : z ≤ 1 := by
    rcases eq_or_lt_of_le h0' with h2 | h2
    · linarith
    · nlinarith
  nlinarith

lemma g53h_spec_unitary_invariant {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (U : Matrix m m ℂ) (W : Matrix n n ℂ) (X : Matrix m n ℂ)
    (hU1 : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1) (hW1 : Wᴴ * W = 1) (hW2 : W * Wᴴ = 1) :
    QAlgorithms.specNorm (U * X * Wᴴ) = QAlgorithms.specNorm X := by
  have nU := g53h_spec_isom_le U hU1
  have nUh := g53h_spec_isom_le Uᴴ (by rw [Matrix.conjTranspose_conjTranspose]; exact hU2)
  have nW := g53h_spec_isom_le W hW1
  have nWh := g53h_spec_isom_le Wᴴ (by rw [Matrix.conjTranspose_conjTranspose]; exact hW2)
  apply le_antisymm
  · calc QAlgorithms.specNorm (U * X * Wᴴ) ≤ QAlgorithms.specNorm (U * X) * QAlgorithms.specNorm Wᴴ :=
          g53h_spec_mul _ _
      _ ≤ QAlgorithms.specNorm U * QAlgorithms.specNorm X * 1 := by
          apply mul_le_mul (g53h_spec_mul _ _) nWh (g53h_spec_nonneg _)
          exact mul_nonneg (g53h_spec_nonneg _) (g53h_spec_nonneg _)
      _ ≤ QAlgorithms.specNorm X := by nlinarith [g53h_spec_nonneg X, g53h_spec_nonneg U]
  · have hX : X = Uᴴ * (U * X * Wᴴ) * W := by
      simp only [← Matrix.mul_assoc, hU1, Matrix.one_mul]
      rw [Matrix.mul_assoc, hW1, Matrix.mul_one]
    calc QAlgorithms.specNorm X = QAlgorithms.specNorm (Uᴴ * (U * X * Wᴴ) * W) := by rw [← hX]
      _ ≤ QAlgorithms.specNorm (Uᴴ * (U * X * Wᴴ)) * QAlgorithms.specNorm W := g53h_spec_mul _ _
      _ ≤ QAlgorithms.specNorm Uᴴ * QAlgorithms.specNorm (U * X * Wᴴ) * 1 := by
          apply mul_le_mul (g53h_spec_mul _ _) nW (g53h_spec_nonneg _)
          exact mul_nonneg (g53h_spec_nonneg _) (g53h_spec_nonneg _)
      _ ≤ QAlgorithms.specNorm (U * X * Wᴴ) := by
          nlinarith [g53h_spec_nonneg (U * X * Wᴴ), g53h_spec_nonneg Uᴴ]

lemma g53h_sum_restrict {ι : Type*} [Fintype ι] (p : ι → Prop) [DecidablePred p] (f : ι → ℂ)
    (h : ∀ x, ¬ p x → f x = 0) : ∑ x, f x = ∑ x : {x // p x}, f x := by
  rw [← Fintype.sum_subtype_add_sum_subtype p f]
  simp [Finset.sum_eq_zero (fun (x : {x // ¬ p x}) _ => h x.1 x.2)]

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P44 in
lemma g53h_thermal_of_comm {d : ℕ} (E : Fin d → ℝ) (beta : ℝ) (V : Matrix.unitaryGroup (Fin d) ℂ)
    (hV0 : ∀ i k, E i ≠ E k → (V : Mat d) i k = 0) :
    IsFiniteThermal E beta (conjSuperop (V : Mat d)) := by
  classical
  let U : Matrix.unitaryGroup (Fin d × Fin 1) ℂ :=
    ⟨Matrix.kronecker (V : Mat d) (1 : Matrix (Fin 1) (Fin 1) ℂ),
      Matrix.kronecker_mem_unitary V.2 (one_mem _)⟩
  let D : ThermalDilation E beta 1 :=
    { bathPositive := one_pos
      bathEnergy := fun _ => 0
      U := U
      support := by
        intro r i nu mu h
        have : E r ≠ E i := by intro h'; apply h; simp [h']
        show (V : Mat d) r i * (1 : Matrix (Fin 1) (Fin 1) ℂ) nu mu = 0
        rw [hV0 r i this, zero_mul] }
  refine ⟨1, D, fun X => ?_⟩
  have hK : ∀ a, thermalKraus D a = (V : Mat d) := by
    intro a; funext r i
    have hg : gibbsWeight D.bathEnergy beta a.1 = 1 := by
      simp [gibbsWeight, D]
    simp only [thermalKraus, hg, Real.sqrt_one, Complex.ofReal_one, one_mul]
    show (V : Mat d) r i * (1 : Matrix (Fin 1) (Fin 1) ℂ) a.2 a.1 = _
    rw [Subsingleton.elim a.2 a.1, Matrix.one_apply_eq, mul_one]
  simp only [thermalApply, krausApply, hK, conjSuperop]
  simp

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- PDF p.11, III C: identity and commuting unitaries are finite TO; every inter-energy
block retains its operator norm under a commuting system unitary. -/
theorem solution {d : ℕ} (hd : 0 < d) (E : Fin d → ℝ) (beta : ℝ) :
    (IsFiniteThermal E beta (fun X => X) ∧
      ∀ (rho : Mat d), IsDensityMatrix rho → ∀ (a b : ℝ), energyBlock E a b ((fun X => X) rho) = energyBlock E a b rho) ∧
    ∀ V : Matrix.unitaryGroup (Fin d) ℂ,
      (V : Mat d) * Matrix.diagonal (fun i => (E i : ℂ)) =
        Matrix.diagonal (fun i => (E i : ℂ)) * (V : Mat d) →
      IsFiniteThermal E beta (conjSuperop (V : Mat d)) ∧
      ∀ (rho : Mat d), IsDensityMatrix rho → ∀ (a b : ℝ), a ≠ b →
        specNorm (energyBlock E a b (conjSuperop (V : Mat d) rho)) =
          specNorm (energyBlock E a b rho) := by
  have hid : conjSuperop (1 : Mat d) = fun X => X := by
    funext X; simp [conjSuperop]
  have hV0 : ∀ V : Matrix.unitaryGroup (Fin d) ℂ,
      (V : Mat d) * Matrix.diagonal (fun i => (E i : ℂ)) =
        Matrix.diagonal (fun i => (E i : ℂ)) * (V : Mat d) →
      ∀ i k, E i ≠ E k → (V : Mat d) i k = 0 := by
    intro V hc i k hne
    have := congrFun (congrFun hc i) k
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at this
    have h2 : (V : Mat d) i k * ((E k : ℂ) - E i) = 0 := by linear_combination this
    rcases mul_eq_zero.1 h2 with h | h
    · exact h
    · exact absurd (by exact_mod_cast (sub_eq_zero.1 h).symm) hne
  refine ⟨⟨?_, fun _ _ _ _ => rfl⟩, fun V hc => ⟨g53h_thermal_of_comm E beta V (hV0 V hc), ?_⟩⟩
  · rw [← hid]
    exact g53h_thermal_of_comm E beta 1 (fun i k h => by simp [Matrix.one_apply]; intro h'; exact h (h' ▸ rfl))
  · intro rho _ a b _
    have h0 := hV0 V hc
    have hu1 : (V : Mat d)ᴴ * (V : Mat d) = 1 := by
      have := Matrix.mem_unitaryGroup_iff'.1 V.2; rwa [Matrix.star_eq_conjTranspose] at this
    have hu2 : (V : Mat d) * (V : Mat d)ᴴ = 1 := by
      have := Matrix.mem_unitaryGroup_iff.1 V.2; rwa [Matrix.star_eq_conjTranspose] at this
    let Vb : ∀ c : ℝ, Matrix {i : Fin d // E i = c} {i : Fin d // E i = c} ℂ :=
      fun c i j => (V : Mat d) i.1 j.1
    have hblk : ∀ c : ℝ, (Vb c)ᴴ * Vb c = 1 ∧ Vb c * (Vb c)ᴴ = 1 := by
      intro c
      constructor
      · ext i j
        have e := congrFun (congrFun hu1 i.1) j.1
        rw [Matrix.mul_apply] at e ⊢
        rw [g53h_sum_restrict (fun k => E k = c) _ (fun k hk => by
          rw [Matrix.conjTranspose_apply, h0 k i.1 (by rw [i.2]; exact hk), star_zero, zero_mul])] at e
        rw [Matrix.one_apply] at e ⊢
        simp only [Matrix.conjTranspose_apply] at e ⊢
        convert e using 2
        simp [Subtype.ext_iff]
      · ext i j
        have e := congrFun (congrFun hu2 i.1) j.1
        rw [Matrix.mul_apply] at e ⊢
        rw [g53h_sum_restrict (fun k => E k = c) _ (fun k hk => by
          rw [h0 i.1 k (by rw [i.2]; exact Ne.symm hk), zero_mul])] at e
        rw [Matrix.one_apply] at e ⊢
        simp only [Matrix.conjTranspose_apply] at e ⊢
        convert e using 2
        simp [Subtype.ext_iff]
    have hE : energyBlock E a b (conjSuperop (V : Mat d) rho) =
        Vb a * energyBlock E a b rho * (Vb b)ᴴ := by
      ext i j
      simp only [energyBlock, conjSuperop, Matrix.mul_apply, Matrix.conjTranspose_apply]
      rw [g53h_sum_restrict (fun l => E l = b) _ (fun l hl => by
        rw [h0 j.1 l (by rw [j.2]; exact Ne.symm hl), star_zero, mul_zero])]
      apply Finset.sum_congr rfl; intro l _
      congr 1
      rw [g53h_sum_restrict (fun k => E k = a) _ (fun k hk => by
        rw [h0 i.1 k (by rw [i.2]; exact Ne.symm hk), zero_mul])]
    rw [hE]
    exact g53h_spec_unitary_invariant _ _ _ (hblk a).1 (hblk a).2 (hblk b).1 (hblk b).2


end


