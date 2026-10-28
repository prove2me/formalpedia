-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P02.holevo_iff_entanglementBreaking
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T16:43:33.628351+00:00
-- url     : https://prove2.me/submissions/7237a695-934d-4258-9ccc-c92da57af027

import Definitions.Def_QAlgorithms_Defs_HolevoMatrixMaps
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P02_Model
set_option autoImplicit false

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Independent1.P02

open scoped MatrixOrder in
theorem p02s204_factor {n : Type*} [Fintype n] [DecidableEq n] (F : Matrix n n ℂ)
    (hF : F.PosSemidef) : ∃ G : Matrix n n ℂ, F = Gᴴ * G := by
  obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hF.nonneg
  exact ⟨C, hC⟩

theorem p02s204_normalize {a : ℕ} (ha : 0 < a) (A : Matrix (Fin a) (Fin a) ℂ)
    (hA : A.PosSemidef) : ∃ w : ℝ, 0 ≤ w ∧ ∃ A', IsDensityMatrix A' ∧ A = (w : ℂ) • A' := by
  have ht := hA.trace_nonneg
  obtain ⟨t, ht0, htr⟩ : ∃ t : ℝ, 0 ≤ t ∧ A.trace = t := by
    refine ⟨A.trace.re, ?_, ?_⟩
    · exact (Complex.nonneg_iff.mp ht).1
    · exact Complex.ext rfl (Complex.nonneg_iff.mp ht).2.symm
  by_cases h0 : t = 0
  · subst h0
    have : A = 0 := (hA.trace_eq_zero_iff).mp (by simpa using htr)
    refine ⟨0, le_rfl, Matrix.diagonal (Pi.single ⟨0, ha⟩ 1), ⟨?_, ?_⟩, by simp [this]⟩
    · refine Matrix.PosSemidef.diagonal fun i => ?_
      by_cases hi : i = ⟨0, ha⟩
      · subst hi; simp
      · simp [hi]
    · simp [Matrix.trace_diagonal]
  · refine ⟨t, ht0, ((t : ℂ)⁻¹) • A, ⟨hA.smul ?_, ?_⟩, ?_⟩
    · rw [← Complex.ofReal_inv]; exact Complex.zero_le_real.mpr (inv_nonneg.mpr ht0)
    · rw [Matrix.trace_smul, htr, smul_eq_mul, inv_mul_cancel₀ (by exact_mod_cast h0)]
    · rw [smul_smul, mul_inv_cancel₀ (by exact_mod_cast h0), one_smul]

theorem p02s204_sep_of_sum {a d m : ℕ} (ha : 0 < a) (A : Fin m → Matrix (Fin a) (Fin a) ℂ)
    (R : Fin m → Algebra d) (hA : ∀ k, (A k).PosSemidef) (hR : ∀ k, IsDensityMatrix (R k)) :
    Entanglement.IsSeparablePositive (∑ k, Matrix.kronecker (A k) (R k)) := by
  choose w hw A' hA' hAe using fun k => p02s204_normalize ha (A k) (hA k)
  refine ⟨m, w, A', R, hw, fun k => ⟨hA' k, hR k⟩, ?_⟩
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hAe k]; ext p q; simp [Matrix.kronecker, Matrix.kroneckerMap_apply, mul_assoc]

theorem p02s204_coeff_psd {a d : ℕ} (X : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ)
    (hX : X.PosSemidef) (F : Algebra d) (hF : F.PosSemidef) :
    (Matrix.of fun b c => (F * Matrix.of fun i i' => X (b, i) (c, i')).trace).PosSemidef := by
  obtain ⟨G, rfl⟩ := p02s204_factor F hF
  let W : Fin d → Matrix (Fin a) (Fin a × Fin d) ℂ :=
    fun r => Matrix.of fun c p => if p.1 = c then G r p.2 else 0
  have e : (Matrix.of fun b c => (Gᴴ * G * Matrix.of fun i i' => X (b, i) (c, i')).trace) =
      ∑ r, W r * X * (W r)ᴴ := by
    ext b c
    have hs : ∀ (P : Prop) [Decidable P] (x : ℂ), star (if P then x else 0) = if P then star x else 0 := by
      intros; split_ifs <;> simp
    simp [W, Matrix.sum_apply, Matrix.mul_apply, Matrix.trace, Fintype.sum_prod_type, hs,
      Finset.sum_mul]
    conv_rhs => rw [Finset.sum_comm]; enter [2, i]; rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun r _ => ?_
    ring
  rw [e]
  exact Matrix.posSemidef_sum _ fun r _ => hX.mul_mul_conjTranspose_same (W r)

theorem p02s204_holevo_eb {d m : ℕ} (R F : Fin m → Algebra d)
    (hR : ∀ k, IsDensityMatrix (R k)) (hF : ∀ k, (F k).PosSemidef) :
    Entanglement.IsEntanglementBreakingPositive (Entanglement.holevoMap R F) := by
  intro a ha X hX
  have e : idTensorSuperop (Entanglement.holevoMap R F) X =
      ∑ k, Matrix.kronecker (Matrix.of fun b c => (F k * Matrix.of fun i i' => X (b, i) (c, i')).trace)
        (R k) := by
    ext p q
    simp [idTensorSuperop, Entanglement.holevoMap, Matrix.sum_apply, Matrix.kronecker,
      Matrix.kroneckerMap_apply]
  rw [e]
  exact p02s204_sep_of_sum ha _ R (fun k => p02s204_coeff_psd X hX.1 (F k) (hF k)) hR

theorem p02s204_tp {d m : ℕ} (R F : Fin m → Algebra d) (hR : ∀ k, (R k).trace = 1) :
    PreservesTrace (Entanglement.holevoMap R F) ↔ ∑ k, F k = 1 := by
  have e : ∀ X, (Entanglement.holevoMap R F X).trace = ((∑ k, F k) * X).trace := by
    intro X
    simp [Entanglement.holevoMap, Matrix.trace_sum, Matrix.trace_smul, hR, Finset.sum_mul]
  rw [Matrix.ext_iff_trace_mul_right]
  simp only [PreservesTrace, e, one_mul]

theorem p02s204_eb_holevo {d : ℕ} (hd : 0 < d) (Phi : Endomorphism d)
    (hEB : Entanglement.IsEntanglementBreakingPositive Phi) : HasHolevoRepresentation Phi false := by
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  let e : Fin d × Fin d → ℂ := fun p => if p.1 = p.2 then 1 else 0
  let X0 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ := (1 / (d : ℂ)) • Matrix.vecMulVec e (star e)
  have hX0 : IsDensityMatrix X0 := by
    refine ⟨(Matrix.posSemidef_vecMulVec_self_star e).smul ?_, ?_⟩
    · rw [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_div]
      exact Complex.zero_le_real.mpr (by positivity)
    · simp [X0, e, Matrix.trace, Matrix.vecMulVec_apply, Fintype.sum_prod_type]
      field_simp
  obtain ⟨q, w, A, B, hw, hAB, hY⟩ := hEB d hd X0 hX0
  have hblk : ∀ a b, Phi (Matrix.single a b 1) =
      ∑ j, ((d : ℂ) * (w j * A j a b)) • B j := by
    intro a b
    have hs : Matrix.single a b (1 : ℂ) =
        (d : ℂ) • Matrix.of fun i i' => X0 (a, i) (b, i') := by
      ext i i'
      simp only [X0, e, Matrix.smul_apply, Matrix.of_apply, Matrix.vecMulVec_apply, Pi.star_apply,
        Matrix.single_apply, smul_eq_mul]
      by_cases h1 : a = i <;> by_cases h2 : b = i' <;> simp [h1, h2, hd0]
    rw [hs, map_smul]
    ext i i'
    have := congrFun (congrFun hY (a, i)) (b, i')
    simp only [idTensorSuperop, Matrix.of_apply] at this
    simp only [Matrix.smul_apply, this, Matrix.sum_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
      smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  refine ⟨q, B, fun j => ((d : ℂ) * w j) • (A j)ᵀ, fun j => (hAB j).2, fun j => ?_,
    fun h => absurd h (by simp), ?_⟩
  · refine (hAB j).1.1.transpose.smul ?_
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul]
    exact Complex.zero_le_real.mpr (mul_nonneg (by positivity) (hw j))
  · apply LinearMap.ext
    intro X
    have hX : X = ∑ a, ∑ b, X a b • Matrix.single a b (1 : ℂ) := by
      conv_lhs => rw [Matrix.matrix_eq_sum_single X]
      simp [Matrix.smul_single]
    conv_lhs => rw [hX]
    simp only [map_sum, map_smul, hblk]
    ext i i'
    simp only [Entanglement.holevoMap, LinearMap.coe_mk, AddHom.coe_mk, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
    conv_rhs => rw [Finset.sum_comm]; enter [2, a]; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun j _ => ?_
    ring

end QAlgorithms.Papers.Independent.Independent1.P02

open QAlgorithms QAlgorithms.Papers.Independent.Independent1.P02 in
/-- Theorem 2, PDF p.2, proof pp.5–6: general equivalence and normalization
for each supplied Holevo or rank-one representation. -/
theorem solution (d : ℕ) (hd : 0 < d) (Phi : Endomorphism d) :
    (HasHolevoRepresentation Phi false ↔ Entanglement.IsEntanglementBreakingPositive Phi) ∧
    (∀ (m : ℕ) (R F : Fin m → Algebra d), (∀ k, IsDensityMatrix (R k)) →
      (∀ k, (F k).PosSemidef) → Phi = Entanglement.holevoMap R F →
      (PreservesTrace Phi ↔ IsPOVM F)) ∧
    (∀ (m : ℕ) (psi phi : Fin m → StateVector d), (∀ k, IsState (psi k)) →
      Phi = Entanglement.holevoMap (fun k => pureDensity (psi k)) (fun k => pureDensity (phi k)) →
      (PreservesTrace Phi ↔ ∑ k, pureDensity (phi k) = 1)) := by
  refine ⟨⟨?_, p02s204_eb_holevo hd Phi⟩, ?_, ?_⟩
  · rintro ⟨m, R, F, hR, hF, -, rfl⟩
    exact p02s204_holevo_eb R F hR hF
  · rintro m R F hR hF rfl
    rw [p02s204_tp R F (fun k => (hR k).2)]
    exact ⟨fun h => ⟨hF, h⟩, fun h => h.2⟩
  · rintro m psi phi hpsi rfl
    apply p02s204_tp
    intro k
    have h1 : ‖psi k‖ = 1 := hpsi k
    have h2 := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (psi k)
    rw [h1] at h2
    simp only [PiLp.inner_apply, RCLike.inner_apply] at h2
    simp only [pureDensity, Matrix.trace, Matrix.diag, Matrix.of_apply]
    simpa [mul_comm] using h2

#print axioms solution
