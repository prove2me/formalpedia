-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P02.point_extreme_iff_pure
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T12:20:41.549742+00:00
-- url     : https://prove2.me/submissions/c1b535ce-e825-4a5b-91fa-bf1ae0627025

import Definitions.Def_QAlgorithms_Defs_HolevoMatrixMaps
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P02_Model
set_option autoImplicit false

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Independent1.P02

namespace A3PE

theorem point_apply {d : ℕ} (R X : Algebra d) : pointEndomorphism R X = X.trace • R := by
  simp [pointEndomorphism, Entanglement.holevoMap]

open scoped MatrixOrder in
theorem fac {d : ℕ} (A : Algebra d) (h : A.PosSemidef) : ∃ B : Algebra d, A = Bᴴ * B := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp h.nonneg
  exact ⟨B, hB⟩

theorem polar {d : ℕ} (u w : Fin d → ℂ) :
    (4 : ℂ) • Matrix.vecMulVec u (star w) =
      Matrix.vecMulVec (u + w) (star (u + w)) - Matrix.vecMulVec (u - w) (star (u - w)) +
      Complex.I • Matrix.vecMulVec (u + Complex.I • w) (star (u + Complex.I • w)) -
      Complex.I • Matrix.vecMulVec (u - Complex.I • w) (star (u - Complex.I • w)) := by
  ext a b
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.vecMulVec_apply,
    Pi.star_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, star_add, star_sub,
    star_mul', Complex.star_def, Complex.conj_I]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem psd_ext {d : ℕ} (L : Endomorphism d) (h : ∀ X : Algebra d, X.PosSemidef → L X = 0) :
    L = 0 := by
  have hv : ∀ u w : Fin d → ℂ, L (Matrix.vecMulVec u (star w)) = 0 := by
    intro u w
    have h4 := congrArg L (polar u w)
    simp only [map_add, map_sub, map_smul, h _ (Matrix.posSemidef_vecMulVec_self_star _),
      smul_zero, sub_zero, add_zero] at h4
    have h4' : (4 : ℂ) • L (Matrix.vecMulVec u (star w)) = 0 := h4
    exact (smul_eq_zero.mp h4').resolve_left (by norm_num)
  ext X : 1
  rw [Matrix.matrix_eq_sum_single X, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  have : Matrix.single i j (X i j) = Matrix.vecMulVec (Pi.single i (X i j)) (star (Pi.single j 1)) := by
    ext a b
    rw [Matrix.single_apply, Matrix.vecMulVec_apply, Pi.star_apply]
    by_cases ha : i = a <;> by_cases hb : j = b
    · subst ha hb; simp
    · rw [Pi.single_eq_of_ne (Ne.symm hb)]; simp [hb]
    · rw [Pi.single_eq_of_ne (Ne.symm ha)]; simp [ha]
    · rw [Pi.single_eq_of_ne (Ne.symm ha)]; simp [ha]
  rw [this, hv]


theorem cpt_props {d : ℕ} {Φ : Endomorphism d} (h : Φ ∈ cptSet d) :
    (∀ X : Algebra d, X.PosSemidef → (Φ X).PosSemidef) ∧ ∀ X, (Φ X).trace = X.trace := by
  obtain ⟨m, E, hE, hΦ⟩ := h
  refine ⟨fun X hX => ?_, fun X => ?_⟩
  · rw [hΦ X]; unfold krausApply
    exact Matrix.posSemidef_sum _ fun k _ => hX.mul_mul_conjTranspose_same (E k)
  · rw [hΦ X]; unfold krausApply
    rw [Matrix.trace_sum]
    have : ∀ k, (E k * X * (E k)ᴴ).trace = ((E k)ᴴ * E k * X).trace := fun k => by
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
    simp_rw [this, ← Matrix.trace_sum, ← Finset.sum_mul]
    unfold IsKrausFamily at hE
    rw [hE, Matrix.one_mul]

theorem ebt_psd {d : ℕ} {Φ : Endomorphism d} (h : Φ ∈ ebtSet d) :
    ∀ X : Algebra d, X.PosSemidef → (Φ X).PosSemidef := by
  obtain ⟨hEB, -⟩ := h
  have hden : ∀ ρ : Algebra d, IsDensityMatrix ρ → (Φ ρ).PosSemidef := by
    intro ρ hρ
    let Y : Matrix (Fin 1 × Fin d) (Fin 1 × Fin d) ℂ := ρ.submatrix Prod.snd Prod.snd
    have hY : IsDensityMatrix Y := by
      refine ⟨hρ.1.submatrix _, ?_⟩
      rw [← hρ.2]
      simp [Y, Matrix.trace, Fintype.sum_prod_type]
    obtain ⟨q, w, A, B, hw, hAB, heq⟩ := hEB 1 one_pos Y hY
    have hpsd : (idTensorSuperop (⇑Φ) Y).PosSemidef := by
      rw [heq]
      refine Matrix.posSemidef_sum _ fun j _ => ?_
      exact ((hAB j).1.1.kronecker (hAB j).2.1).smul (by exact_mod_cast hw j)
    exact hpsd.submatrix (fun i : Fin d => ((0 : Fin 1), i))
  intro X hX
  by_cases h0 : X.trace = 0
  · rw [(hX.trace_eq_zero_iff).mp h0, map_zero]; exact Matrix.PosSemidef.zero
  · have hnn := Complex.nonneg_iff.mp hX.trace_nonneg
    set r : ℝ := X.trace.re with hr
    have hre : X.trace = (r : ℂ) := by
      apply Complex.ext <;> simp [hr, hnn.2.symm]
    have hpos : 0 < r := by
      rcases hnn.1.lt_or_eq with h1 | h1
      · exact h1
      · exact absurd (by rw [hre, ← h1]; simp) h0
    have hρ : IsDensityMatrix (((r⁻¹ : ℝ) : ℂ) • X) := by
      refine ⟨hX.smul (by exact_mod_cast (inv_pos.mpr hpos).le), ?_⟩
      rw [Matrix.trace_smul, smul_eq_mul, hre, ← Complex.ofReal_mul, inv_mul_cancel₀ hpos.ne',
        Complex.ofReal_one]
    have := (hden _ hρ).smul (show (0 : ℂ) ≤ (r : ℂ) by exact_mod_cast hpos.le)
    rwa [← map_smul, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hpos.ne',
      Complex.ofReal_one, one_smul] at this

theorem point_mem {d : ℕ} (R : Algebra d) (hR : IsDensityMatrix R) :
    pointEndomorphism R ∈ cptSet d ∧ pointEndomorphism R ∈ ebtSet d := by
  constructor
  · obtain ⟨B, hB⟩ := fac R hR.1
    let E : Fin d × Fin d → Algebra d := fun p => Bᴴ * Matrix.single p.1 p.2 1
    refine ⟨d * d, fun k => E (finProdFinEquiv.symm k), ?_, ?_⟩
    · unfold IsKrausFamily
      rw [finProdFinEquiv.symm.sum_comp (fun p => (E p)ᴴ * E p)]
      have key : ∀ p : Fin d × Fin d, (E p)ᴴ * E p = Matrix.single p.2 p.2 ((B * Bᴴ) p.1 p.1) := by
        intro p
        simp only [E, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          Matrix.conjTranspose_single, star_one]
        rw [show Matrix.single p.2 p.1 (1 : ℂ) * B * (Bᴴ * Matrix.single p.1 p.2 1) =
          Matrix.single p.2 p.1 (1 : ℂ) * (B * Bᴴ) * Matrix.single p.1 p.2 1 by
            simp [Matrix.mul_assoc]]
        simp
      simp_rw [key]
      have htr : (B * Bᴴ).trace = 1 := by
        rw [Matrix.trace_mul_comm, ← hB, hR.2]
      ext i j
      rw [Matrix.sum_apply, Fintype.sum_prod_type]
      simp only [Matrix.single_apply, Matrix.one_apply]
      by_cases hij : i = j
      · subst hij
        simp only [and_self, if_true]
        rw [← htr, Matrix.trace]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_eq_single i]
        · simp
        · intro b _ hb; simp [hb]
        · simp
      · have hn : ∀ x : Fin d, ¬ (x = i ∧ x = j) := fun x h => hij (h.1.symm.trans h.2)
        simp [hij, hn]
    · intro ρ
      rw [point_apply]
      unfold krausApply
      rw [finProdFinEquiv.symm.sum_comp (fun p => E p * ρ * (E p)ᴴ)]
      have key : ∀ p : Fin d × Fin d, E p * ρ * (E p)ᴴ =
          Bᴴ * Matrix.single p.1 p.1 (ρ p.2 p.2) * B := by
        intro p
        simp only [E, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          Matrix.conjTranspose_single, star_one]
        rw [show Bᴴ * Matrix.single p.1 p.2 (1 : ℂ) * ρ * (Matrix.single p.2 p.1 1 * B) =
          Bᴴ * (Matrix.single p.1 p.2 (1 : ℂ) * ρ * Matrix.single p.2 p.1 1) * B by
            simp [Matrix.mul_assoc]]
        simp
      simp_rw [key]
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
      have : ∑ x : Fin d, ∑ y : Fin d, Matrix.single x x (ρ y y) = ρ.trace • (1 : Algebra d) := by
        ext i j
        simp only [Matrix.sum_apply, Matrix.single_apply, Matrix.smul_apply, Matrix.one_apply,
          smul_eq_mul, Matrix.trace, Matrix.diag]
        by_cases hij : i = j
        · subst hij
          rw [Finset.sum_eq_single i]
          · simp
          · intro b _ hb; simp [hb]
          · simp
        · have hn : ∀ x : Fin d, ¬ (x = i ∧ x = j) := fun x h => hij (h.1.symm.trans h.2)
          simp [hij, hn]
      rw [this, hB]
      simp
  · refine ⟨fun a ha X hX => ?_, fun X => ?_⟩
    · let A : Matrix (Fin a) (Fin a) ℂ := ∑ i : Fin d, X.submatrix (fun x => (x, i)) (fun x => (x, i))
      refine ⟨1, fun _ => 1, fun _ => A, fun _ => R, fun _ => zero_le_one, fun _ => ⟨⟨?_, ?_⟩, hR⟩, ?_⟩
      · exact Matrix.posSemidef_sum _ fun i _ => hX.1.submatrix _
      · rw [← hX.2]
        simp only [A, Matrix.trace, Matrix.diag, Matrix.sum_apply, Matrix.submatrix_apply]
        rw [Fintype.sum_prod_type]
      · ext p q
        simp [idTensorSuperop, point_apply, A, Matrix.kronecker, Matrix.kroneckerMap_apply,
          Matrix.sum_apply, Matrix.trace, Finset.sum_mul]
    · rw [point_apply, Matrix.trace_smul, hR.2, smul_eq_mul, mul_one]

theorem pd_norm {d : ℕ} (ψ : StateVector d) (hψ : IsState ψ) :
    ∑ k, ψ k * conj (ψ k) = 1 := by
  have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) ψ
  unfold IsState at hψ
  rw [hψ] at h
  simp only [PiLp.inner_apply, RCLike.inner_apply] at h
  convert h using 1
  simp

theorem pd_density {d : ℕ} (ψ : StateVector d) (hψ : IsState ψ) :
    IsDensityMatrix (pureDensity ψ) := by
  refine ⟨?_, ?_⟩
  · have := Matrix.posSemidef_vecMulVec_self_star (WithLp.ofLp ψ)
    convert this using 1
    ext i j
    simp [pureDensity, Matrix.vecMulVec_apply]
  · rw [← pd_norm ψ hψ]; rfl

theorem pd_mul {d : ℕ} (ψ : StateVector d) (hψ : IsState ψ) :
    pureDensity ψ * pureDensity ψ = pureDensity ψ := by
  ext i j
  simp only [Matrix.mul_apply, pureDensity, Matrix.of_apply]
  have := pd_norm ψ hψ
  calc ∑ k, ψ i * conj (ψ k) * (ψ k * conj (ψ j))
      = ψ i * conj (ψ j) * ∑ k, ψ k * conj (ψ k) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    _ = _ := by rw [this, mul_one]

theorem pd_herm {d : ℕ} (ψ : StateVector d) : (pureDensity ψ)ᴴ = pureDensity ψ := by
  ext i j
  simp [pureDensity, mul_comm]

theorem pd_sandwich {d : ℕ} (ψ : StateVector d) (Y : Algebra d) :
    pureDensity ψ * Y * pureDensity ψ = (pureDensity ψ * Y).trace • pureDensity ψ := by
  ext i j
  simp only [Matrix.mul_apply, pureDensity, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.trace, Matrix.diag, Finset.sum_mul]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem rigid {d : ℕ} (ψ : StateVector d) (hψ : IsState ψ) (Φ1 Φ2 : Endomorphism d)
    (h1 : ∀ X : Algebra d, X.PosSemidef → (Φ1 X).PosSemidef) (t1 : ∀ X, (Φ1 X).trace = X.trace)
    (h2 : ∀ X : Algebra d, X.PosSemidef → (Φ2 X).PosSemidef)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a • Φ1 + b • Φ2 = pointEndomorphism (pureDensity ψ)) :
    Φ1 = pointEndomorphism (pureDensity ψ) := by
  set P := pureDensity ψ with hPdef
  have hPP : P * P = P := pd_mul ψ hψ
  have hPH : Pᴴ = P := pd_herm ψ
  set Q : Algebra d := 1 - P with hQdef
  have hQH : Qᴴ = Q := by simp [Q, hPH]
  have hQP : Q * P = 0 := by simp [Q, Matrix.sub_mul, hPP]
  rw [← sub_eq_zero]
  apply psd_ext
  intro X hX
  rw [LinearMap.sub_apply, sub_eq_zero, point_apply]
  have hA := h1 X hX
  have hB := h2 X hX
  set A := Φ1 X with hAdef
  set B := Φ2 X with hBdef
  have heq : (a : ℂ) • A + (b : ℂ) • B = X.trace • P := by
    have := LinearMap.congr_fun hab X
    simp only [LinearMap.add_apply, LinearMap.smul_apply, point_apply] at this
    rw [← this, ← hAdef, ← hBdef, Complex.coe_smul, Complex.coe_smul]
  have hQAQ : (a : ℂ) • (Q * A * Q) + (b : ℂ) • (Q * B * Q) = 0 := by
    have := congrArg (fun M => Q * M * Q) heq
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul] at this
    rw [this, hQP, Matrix.zero_mul, smul_zero]
  have hpA : (Q * A * Q).PosSemidef := by
    simpa [hQH] using hA.mul_mul_conjTranspose_same Q
  have hpB : (Q * B * Q).PosSemidef := by
    simpa [hQH] using hB.mul_mul_conjTranspose_same Q
  have htr : (Q * A * Q).trace = 0 := by
    have := congrArg Matrix.trace hQAQ
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_zero,
      smul_eq_mul, smul_eq_mul] at this
    have n1 : 0 ≤ (a : ℂ) * (Q * A * Q).trace :=
      mul_nonneg (by exact_mod_cast ha.le) hpA.trace_nonneg
    have n2 : 0 ≤ (b : ℂ) * (Q * B * Q).trace :=
      mul_nonneg (by exact_mod_cast hb.le) hpB.trace_nonneg
    have := ((add_eq_zero_iff_of_nonneg n1 n2).mp this).1
    exact (mul_eq_zero.mp this).resolve_left (by exact_mod_cast ha.ne')
  have h0 : Q * A * Q = 0 := hpA.trace_eq_zero_iff.mp htr
  obtain ⟨C, hC⟩ := fac A hA
  have hCQ : C * Q = 0 := by
    have : (C * Q)ᴴ * (C * Q) = 0 := by
      rw [Matrix.conjTranspose_mul, hQH, ← h0, hC]; simp [Matrix.mul_assoc]
    exact Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp (by rw [this, Matrix.trace_zero])
  have hAQ : A * Q = 0 := by rw [hC, Matrix.mul_assoc, hCQ, Matrix.mul_zero]
  have hAP : A = A * P := by
    have : A * Q = A - A * P := by simp [Q, Matrix.mul_sub]
    rw [hAQ] at this
    exact sub_eq_zero.mp this.symm
  have hPA : A = P * A := by
    have := congrArg Matrix.conjTranspose hAP
    rw [Matrix.conjTranspose_mul, hPH, hA.1.eq] at this
    exact this
  have e : (P * A).trace = X.trace := by rw [← hPA]; exact t1 X
  calc A = P * A * P := by rw [← hPA]; exact hAP
    _ = (P * A).trace • P := pd_sandwich ψ A
    _ = X.trace • P := by rw [e]

theorem split {d : ℕ} (R : Algebra d) (hR : IsDensityMatrix R) (hnp : ¬ IsPureDensity R) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ ∃ R1 R2 : Algebra d, IsDensityMatrix R1 ∧ IsDensityMatrix R2 ∧
      R1 ≠ R2 ∧ R = (t : ℂ) • R1 + ((1 - t : ℝ) : ℂ) • R2 := by
  have hH : R.IsHermitian := hR.1.1
  set U : Algebra d := (hH.eigenvectorUnitary : Algebra d) with hUdef
  set lam := hH.eigenvalues with hlam
  let cj : (Fin d → ℝ) → Algebra d := fun f => U * Matrix.diagonal (fun i => (f i : ℂ)) * star U
  have hUU : star U * U = 1 := Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
  have hRU : R = cj lam := by
    conv_lhs => rw [hH.spectral_theorem]
    simp only [Unitary.conjStarAlgAut_apply, cj, U, lam]
    rfl
  have cj_psd : ∀ f : Fin d → ℝ, (∀ i, 0 ≤ f i) → (cj f).PosSemidef := by
    intro f hf
    have hD : (Matrix.diagonal fun i => (f i : ℂ)).PosSemidef :=
      Matrix.posSemidef_diagonal_iff.mpr (fun i => by exact_mod_cast hf i)
    simpa [cj, Matrix.star_eq_conjTranspose] using hD.mul_mul_conjTranspose_same U
  have cj_tr : ∀ f : Fin d → ℝ, (cj f).trace = ∑ i, (f i : ℂ) := by
    intro f
    simp only [cj]
    rw [Matrix.trace_mul_cycle, hUU, Matrix.one_mul, Matrix.trace_diagonal]
  have cj_inj : ∀ f g : Fin d → ℝ, cj f = cj g → f = g := by
    intro f g h
    have e : ∀ f : Fin d → ℝ, star U * cj f * U = Matrix.diagonal (fun i => (f i : ℂ)) := by
      intro f
      simp only [cj]
      rw [show star U * (U * Matrix.diagonal (fun i => (f i : ℂ)) * star U) * U =
        (star U * U) * Matrix.diagonal (fun i => (f i : ℂ)) * (star U * U) by
          simp [Matrix.mul_assoc]]
      rw [hUU, Matrix.one_mul, Matrix.mul_one]
    have := congrArg (fun M => star U * M * U) h
    simp only [e] at this
    funext i
    have := congrFun (congrFun this i) i
    simpa using this
  have cj_lin : ∀ (s r : ℝ) (f g : Fin d → ℝ),
      cj (fun i => s * f i + r * g i) = (s : ℂ) • cj f + (r : ℂ) • cj g := by
    intro s r f g
    have : Matrix.diagonal (fun i => ((s * f i + r * g i : ℝ) : ℂ)) =
        (s : ℂ) • Matrix.diagonal (fun i => (f i : ℂ)) + (r : ℂ) • Matrix.diagonal (fun i => (g i : ℂ)) := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · simp [Matrix.diagonal_apply_ne _ hij]
    simp only [cj]
    rw [this, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.smul_mul]
  have hlam0 : ∀ i, 0 ≤ lam i := hR.1.eigenvalues_nonneg
  have hsum : ∑ i, lam i = 1 := by
    have := hH.trace_eq_sum_eigenvalues
    rw [hR.2] at this
    have h2 : ((∑ i, lam i : ℝ) : ℂ) = 1 := by rw [hlam]; push_cast; exact this.symm
    exact_mod_cast h2
  obtain ⟨k, hk⟩ : ∃ k, 0 < lam k := by
    by_contra h
    push Not at h
    have : ∑ i, lam i = 0 := Finset.sum_eq_zero fun i _ => le_antisymm (h i) (hlam0 i)
    linarith
  have hk1 : lam k < 1 := by
    by_contra hge
    push Not at hge
    have hle : lam k ≤ 1 := hsum ▸ Finset.single_le_sum (fun i _ => hlam0 i) (Finset.mem_univ k)
    have heq1 : lam k = 1 := le_antisymm hle hge
    have hrest : ∑ i ∈ Finset.univ.erase k, lam i = 0 := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k), heq1] at hsum
      linarith
    have hzero : ∀ i, i ≠ k → lam i = 0 := by
      intro i hi
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hlam0 j)).mp hrest i
        (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)
    apply hnp
    refine ⟨hH.eigenvectorBasis k, hH.eigenvectorBasis.orthonormal.1 k, ?_⟩
    refine hRU.trans ?_
    ext i j
    simp only [cj, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.star_apply, pureDensity,
      Matrix.of_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [Finset.sum_eq_single k]
    · simp [U, heq1, Matrix.IsHermitian.eigenvectorUnitary_apply]
    · intro b _ hb; simp [hzero b hb]
    · simp
  set t := lam k with ht
  let f1 : Fin d → ℝ := Pi.single k 1
  let f2 : Fin d → ℝ := fun i => (lam i - t * f1 i) / (1 - t)
  have h1t : (1 - t) ≠ 0 := by linarith
  have hf1 : ∀ i, 0 ≤ f1 i := by
    intro i; by_cases hi : i = k
    · subst hi; simp [f1]
    · simp [f1, hi]
  have hf2 : ∀ i, 0 ≤ f2 i := by
    intro i
    apply div_nonneg _ (by linarith)
    by_cases hi : i = k
    · subst hi; simp [f1, ht]
    · simp [f1, hi, hlam0 i]
  have hsf1 : ∑ i, f1 i = 1 := by simp [f1]
  have hsf2 : ∑ i, f2 i = 1 := by
    simp only [f2]
    rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, hsf1, hsum, mul_one,
      div_self h1t]
  refine ⟨t, hk, hk1, cj f1, cj f2, ⟨cj_psd f1 hf1, ?_⟩, ⟨cj_psd f2 hf2, ?_⟩, ?_, ?_⟩
  · rw [cj_tr]; exact_mod_cast hsf1
  · rw [cj_tr]; exact_mod_cast hsf2
  · intro h
    have := congrFun (cj_inj _ _ h) k
    simp [f1, f2, ht] at this
  · rw [← cj_lin, hRU]
    congr 1
    funext i
    simp only [f2]
    field_simp
    ring

theorem extreme_iff {d : ℕ} (hd : 0 < d) (S : Set (Endomorphism d))
    (hS : ∀ Φ ∈ S, (∀ X : Algebra d, X.PosSemidef → (Φ X).PosSemidef) ∧
      ∀ X, (Φ X).trace = X.trace)
    (hmem : ∀ R : Algebra d, IsDensityMatrix R → pointEndomorphism R ∈ S)
    (R : Algebra d) (hR : IsDensityMatrix R) :
    pointEndomorphism R ∈ S.extremePoints ℝ ↔ IsPureDensity R := by
  constructor
  · intro hext
    by_contra hnp
    obtain ⟨t, ht0, ht1, R1, R2, h1, h2, hne, hRe⟩ := split R hR hnp
    have hseg : pointEndomorphism R ∈
        openSegment ℝ (pointEndomorphism R1) (pointEndomorphism R2) := by
      refine ⟨t, 1 - t, ht0, by linarith, by ring, ?_⟩
      ext X i j
      simp only [LinearMap.add_apply, LinearMap.smul_apply, point_apply, hRe, Matrix.add_apply,
        Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
      push_cast
      ring
    obtain ⟨e1, e2⟩ := (mem_extremePoints.mp hext).2 _ (hmem R1 h1) _ (hmem R2 h2) hseg
    apply hne
    have := LinearMap.congr_fun (e1.trans e2.symm)
      (Matrix.single (⟨0, hd⟩ : Fin d) (⟨0, hd⟩ : Fin d) 1)
    simpa [point_apply] using this
  · rintro ⟨ψ, hψ, rfl⟩
    refine mem_extremePoints.mpr ⟨hmem _ (pd_density ψ hψ), ?_⟩
    rintro x1 hx1 x2 hx2 ⟨a, b, ha, hb, -, heq⟩
    exact ⟨rigid ψ hψ x1 x2 (hS x1 hx1).1 (hS x1 hx1).2 (hS x2 hx2).1 a b ha hb heq,
      rigid ψ hψ x2 x1 (hS x2 hx2).1 (hS x2 hx2).2 (hS x1 hx1).1 b a hb ha
        (by rw [add_comm]; exact heq)⟩

theorem main (d : ℕ) (hd : 0 < d) (R : Algebra d)
    (hR : IsDensityMatrix R) :
    (pointEndomorphism R ∈ (cptSet d).extremePoints ℝ ↔ IsPureDensity R) ∧
    (pointEndomorphism R ∈ (ebtSet d).extremePoints ℝ ↔ IsPureDensity R) :=
  ⟨extreme_iff hd (cptSet d) (fun _ h => cpt_props h) (fun R h => (point_mem R h).1) R hR,
    extreme_iff hd (ebtSet d) (fun _ h => ⟨ebt_psd h, h.2⟩) (fun R h => (point_mem R h).2) R hR⟩

end A3PE

end QAlgorithms.Papers.Independent.Independent1.P02

end

theorem solution (d : ℕ) (hd : 0 < d) (R : QAlgorithms.Papers.Independent.Independent1.P02.Algebra d)
    (hR : QAlgorithms.IsDensityMatrix R) :
    (QAlgorithms.Papers.Independent.Independent1.P02.pointEndomorphism R ∈
        (QAlgorithms.Papers.Independent.Independent1.P02.cptSet d).extremePoints ℝ ↔
      QAlgorithms.Papers.Independent.Independent1.P02.IsPureDensity R) ∧
    (QAlgorithms.Papers.Independent.Independent1.P02.pointEndomorphism R ∈
        (QAlgorithms.Papers.Independent.Independent1.P02.ebtSet d).extremePoints ℝ ↔
      QAlgorithms.Papers.Independent.Independent1.P02.IsPureDensity R) :=
  QAlgorithms.Papers.Independent.Independent1.P02.A3PE.main d hd R hR
