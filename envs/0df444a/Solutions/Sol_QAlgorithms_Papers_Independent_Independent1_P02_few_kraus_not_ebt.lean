-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P02.few_kraus_not_ebt
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T18:01:26.370427+00:00
-- url     : https://prove2.me/submissions/bb1de813-ba30-407d-8c54-b12d24cd705c

import Definitions.Def_QAlgorithms_Defs_HolevoMatrixMaps
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P02_Model
set_option autoImplicit false

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Independent1.P02

theorem p02s204_Q2 {d : ℕ} (u v y z : Fin d → ℂ) :
    star y ⬝ᵥ (Matrix.vecMulVec u (star v) *ᵥ z) = (star y ⬝ᵥ u) * (star v ⬝ᵥ z) := by
  rw [Matrix.vecMulVec_mulVec]
  simp [dotProduct_smul, mul_comm]

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

theorem p02s204_KV {d n : ℕ} (K : Fin n → Algebra d) (u v : Fin d → ℂ) :
    krausApply K (Matrix.vecMulVec u (star v)) =
      ∑ i, Matrix.vecMulVec (K i *ᵥ u) (star (K i *ᵥ v)) := by
  unfold krausApply
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]

theorem p02s204_trF {d : ℕ} (F : Algebra d) (u v : Fin d → ℂ) :
    (F * Matrix.vecMulVec u (star v)).trace = star v ⬝ᵥ F *ᵥ u := by
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]

theorem p02s204_holevo_vv {d m : ℕ} (R F : Fin m → Algebra d) (u v : Fin d → ℂ) :
    Entanglement.holevoMap R F (Matrix.vecMulVec u (star v)) =
      ∑ k, (star v ⬝ᵥ F k *ᵥ u) • R k := by
  simp only [Entanglement.holevoMap, LinearMap.coe_mk, AddHom.coe_mk, p02s204_trF]


theorem p02s204_fk_main (d m : ℕ) (hd : 0 < d) (A : Fin m → Algebra d)
    (hFew : m < d) : krausEndomorphism A ∉ ebtSet d := by
  intro h
  obtain ⟨n, R, F, hR, hF, -, hP⟩ := p02s204_eb_holevo hd _ h.1
  have hsum : ∑ k, F k = 1 := by
    have := h.2; rw [hP] at this
    exact (p02s204_tp R F (fun k => (hR k).2)).mp this
  have cover : ∀ u : Fin d → ℂ, ∃ k, R k *ᵥ u = 0 := by
    intro u
    let L : (Fin d → ℂ) →ₗ[ℂ] (Fin m → ℂ) :=
      (Matrix.of fun i b => (star u ᵥ* A i) b).mulVecLin
    have hker : LinearMap.ker L ≠ ⊥ :=
      LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hFew)
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hker
    have hAv : ∀ i, star u ⬝ᵥ A i *ᵥ v = 0 := by
      intro i
      have := congrFun (LinearMap.mem_ker.mp hv) i
      simpa [L, Matrix.mulVec, Matrix.dotProduct_mulVec] using this
    have hq := congrArg (fun M => star u ⬝ᵥ (M *ᵥ u))
      (LinearMap.congr_fun hP (Matrix.vecMulVec v (star v)))
    change star u ⬝ᵥ (krausApply A (Matrix.vecMulVec v (star v)) *ᵥ u) = _ at hq
    rw [p02s204_KV, p02s204_holevo_vv] at hq
    simp only [Matrix.sum_mulVec, dotProduct_sum, p02s204_Q2, hAv, zero_mul, Finset.sum_const_zero,
      Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at hq
    have nn : ∀ k, 0 ≤ (star v ⬝ᵥ F k *ᵥ v) * (star u ⬝ᵥ R k *ᵥ u) := fun k =>
      mul_nonneg ((hF k).dotProduct_mulVec_nonneg _) ((hR k).1.dotProduct_mulVec_nonneg _)
    have hz := (Finset.sum_eq_zero_iff_of_nonneg fun k (_ : k ∈ Finset.univ) => nn k).mp hq.symm
    have hvv : ∑ k, star v ⬝ᵥ F k *ᵥ v ≠ 0 := by
      rw [← dotProduct_sum, ← Matrix.sum_mulVec, hsum, Matrix.one_mulVec]
      exact fun h0 => hv0 (dotProduct_star_self_eq_zero.mp h0)
    obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hvv
    refine ⟨k, ((hR k).1.dotProduct_mulVec_zero_iff u).mp ?_⟩
    exact (mul_eq_zero.mp (hz k (Finset.mem_univ _))).resolve_left hk
  have hcov : ⋃ k, ((LinearMap.ker (R k).mulVecLin : Subspace ℂ (Fin d → ℂ)) : Set (Fin d → ℂ)) =
      Set.univ := by
    apply Set.eq_univ_of_forall
    intro u
    obtain ⟨k, hk⟩ := cover u
    exact Set.mem_iUnion.mpr ⟨k, by simpa using hk⟩
  obtain ⟨k, hk⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ hcov
  have h0 : R k = 0 := by
    rw [Matrix.ext_iff_mulVec]
    intro x
    have : x ∈ LinearMap.ker (R k).mulVecLin := by rw [hk]; trivial
    simpa using this
  have := (hR k).2
  rw [h0, Matrix.trace_zero] at this
  exact zero_ne_one this

end QAlgorithms.Papers.Independent.Independent1.P02

open QAlgorithms QAlgorithms.Papers.Independent.Independent1.P02 in
/-- Theorem 6, PDF p.9: actual Kraus-list length less than d.
The cited rank/separability ingredients are [11], or [8] with [2]. -/
theorem solution (d m : ℕ) (hd : 0 < d) (A : Fin m → Algebra d)
    (hNormalized : IsKrausFamily A) (hFew : m < d) :
    krausEndomorphism A ∉ ebtSet d :=
  p02s204_fk_main d m hd A hFew
