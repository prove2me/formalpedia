-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P41.unitaryRepresentation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T00:13:25.845589+00:00
-- url     : https://prove2.me/submissions/7e5473ed-efc2-4073-94f2-932c77695648

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P41

-- ===== P41CKLib =====

noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P41
open QAlgorithms.Entanglement (IsCompletelyPositive)
open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq
local instance (priority := 2000) (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

namespace X4P41C
open Matrix

variable {d : ℕ}

/-- unnormalized maximally entangled projector on (Fin d × Fin d) -/
def omega (d : ℕ) : Fin d × Fin d → ℂ := fun p => if p.1 = p.2 then 1 else 0

lemma choi_psd (Phi : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hCP : IsCompletelyPositive Phi) :
    (idTensorSuperop Phi (vecMulVec (omega d) (star (omega d)))).PosSemidef :=
  hCP d _ (posSemidef_vecMulVec_self_star _)

lemma choi_entry (Phi : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (i a j b : Fin d) :
    idTensorSuperop Phi (vecMulVec (omega d) (star (omega d))) (i, a) (j, b) =
      Phi (Matrix.single i j 1) a b := by
  simp only [idTensorSuperop, Matrix.of_apply]
  have h : (Matrix.of fun x y => vecMulVec (omega d) (star (omega d)) (i, x) (j, y)) =
      Matrix.single i j (1 : ℂ) := by
    ext x y
    simp only [Matrix.of_apply, vecMulVec_apply, omega, Pi.star_apply, Matrix.single_apply]
    by_cases h1 : i = x <;> by_cases h2 : j = y <;> simp [h1, h2]
  rw [h]

theorem kraus_exists (Phi : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hCP : IsCompletelyPositive Phi) :
    ∃ A : Fin d × Fin d → Matrix (Fin d) (Fin d) ℂ, ∀ X, Phi X = ∑ k, A k * X * (A k)ᴴ := by
  set C := idTensorSuperop Phi (vecMulVec (omega d) (star (omega d)))
  have hC : C.PosSemidef := choi_psd Phi hCP
  set U := hC.1.eigenvectorUnitary
  set lam := hC.1.eigenvalues
  have hspec := hC.1.spectral_theorem
  have hentry : ∀ p q, C p q = ∑ k, (U : Matrix _ _ ℂ) p k * (lam k : ℂ) * conj ((U : Matrix _ _ ℂ) q k) := by
    intro p q
    have := congrFun (congrFun hspec p) q
    rw [this]
    simp only [Unitary.conjStarAlgAut_apply, Matrix.mul_apply, diagonal_apply, Function.comp_apply,
      star_apply, RCLike.star_def, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rfl
  have hentry' : ∀ i a j b, Phi (Matrix.single i j 1) a b =
      ∑ k, (U : Matrix _ _ ℂ) (i, a) k * (lam k : ℂ) * conj ((U : Matrix _ _ ℂ) (j, b) k) := by
    intro i a j b
    rw [← choi_entry Phi i a j b]
    exact hentry (i, a) (j, b)
  refine ⟨fun k => Matrix.of fun a i => ((Real.sqrt (lam k) : ℝ) : ℂ) * (U : Matrix _ _ ℂ) (i, a) k, ?_⟩
  intro X
  have hX : X = ∑ i, ∑ j, X i j • Matrix.single i j (1 : ℂ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    simp [Matrix.smul_single]
  ext a b
  conv_lhs => rw [hX]
  simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    conjTranspose_apply, RCLike.star_def, map_mul, Complex.conj_ofReal, Matrix.of_apply]
  simp_rw [hentry']
  simp only [Finset.mul_sum, Finset.sum_mul]
  have perm : ∀ f : Fin d → Fin d → Fin d × Fin d → ℂ,
      (∑ i, ∑ j, ∑ k, f i j k) = ∑ k, ∑ j, ∑ i, f i j k := by
    intro f
    rw [Finset.sum_congr rfl (fun i _ => (Finset.sum_comm : (∑ j, ∑ k, f i j k) = _))]
    rw [(Finset.sum_comm : (∑ i, ∑ k, ∑ j, f i j k) = _)]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_comm
  rw [perm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun i _ => ?_
  have hl : 0 ≤ lam k := hC.eigenvalues_nonneg k
  have : ((Real.sqrt (lam k) : ℝ) : ℂ) * ((Real.sqrt (lam k) : ℝ) : ℂ) = (lam k : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hl]
  linear_combination (X i j * (U : Matrix _ _ ℂ) (i, a) k * conj ((U : Matrix _ _ ℂ) (j, b) k)) * this.symm

end X4P41C

-- ===== P41UR =====

noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P41
open QAlgorithms.Entanglement (IsCompletelyPositive)
open QAlgorithms.Papers.Independent.Gap20.P06 (dilationChannel)
open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq
local instance (priority := 2000) (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

namespace X4P41U
open Matrix

lemma tp_kraus {d m : ℕ} (A : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (hTP : ∀ X, (krausApply A X).trace = X.trace) : IsKrausFamily A := by
  unfold IsKrausFamily
  set M := ∑ k, (A k)ᴴ * A k
  have hM : ∀ X, (M * X).trace = X.trace := by
    intro X
    rw [← hTP X, krausApply, Matrix.trace_sum, Matrix.sum_mul, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.trace_mul_comm (X * (A k)ᴴ) (A k),
      ← Matrix.mul_assoc]
  ext i j
  have := hM (Matrix.single j i 1)
  rw [Matrix.trace_mul_single] at this
  have ht : (Matrix.single j i (1 : ℂ)).trace = if i = j then 1 else 0 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.single_apply]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [ht] at this
  simp only [one_apply]
  simpa using this

variable {d e : ℕ}

theorem dilation (A : Fin e → Matrix (Fin d) (Fin d) ℂ) (hA : IsKrausFamily A) (he : 0 < e) :
    ∃ U : Matrix.unitaryGroup (Fin d × Fin e) ℂ,
      ∀ X, krausApply A X = dilationChannel U (EuclideanSpace.single ⟨0, he⟩ 1) X := by
  set z : Fin e := ⟨0, he⟩
  let v : Fin d × Fin e → EuclideanSpace ℂ (Fin d × Fin e) :=
    fun p => WithLp.toLp 2 fun q => A q.2 q.1 p.1
  have hv : Orthonormal ℂ (({p | p.2 = z} : Set (Fin d × Fin e)).restrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨⟨i, k⟩, hk⟩ ⟨⟨i', k'⟩, hk'⟩
    simp only [Set.mem_setOf_eq] at hk hk'
    subst hk; subst hk'
    simp only [Set.restrict_apply, v, PiLp.inner_apply, PiLp.toLp_apply, RCLike.inner_apply,
      Fintype.sum_prod_type]
    have h := congrFun (congrFun hA i) i'
    simp only [Matrix.sum_apply, Matrix.mul_apply, conjTranspose_apply, RCLike.star_def,
      one_apply] at h
    rw [Finset.sum_comm]
    convert h using 1
    · refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
      show A k j i' * conj (A k j i) = _
      ring
    · simp only [Subtype.mk.injEq, Prod.mk.injEq, and_true]
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp)
  let U : Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ := Matrix.of fun q p => b p q
  have hU : U ∈ Matrix.unitaryGroup (Fin d × Fin e) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    ext p p'
    have := (orthonormal_iff_ite.1 b.orthonormal) p p'
    simp only [PiLp.inner_apply, RCLike.inner_apply] at this
    simp only [Matrix.mul_apply, star_apply, U, Matrix.of_apply, RCLike.star_def, one_apply]
    rw [← this]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  have hcol : ∀ i q, U q (i, z) = A q.2 q.1 i := by
    intro i q
    simp only [U, Matrix.of_apply]
    rw [hb (i, z) rfl]
  refine ⟨⟨U, hU⟩, fun X => ?_⟩
  ext j j'
  simp only [dilationChannel, traceRight, conjSuperop, krausApply, Matrix.of_apply,
    Matrix.sum_apply, Matrix.mul_apply, conjTranspose_apply, RCLike.star_def, Matrix.kronecker,
    kroneckerMap_apply, pureDensity, PiLp.single_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [apply_ite (starRingEnd ℂ), map_one, map_zero, mul_ite, ite_mul, mul_one, mul_zero,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, hcol]
  rw [Finset.sum_congr rfl fun x _ => Finset.sum_eq_single z (fun b _ hb => by simp [hb]) (by simp)]
  simp only [if_true, Finset.sum_ite_eq', Finset.mem_univ, hcol]

end X4P41U

theorem solution {d : ℕ} [NeZero d]
    (Phi : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hCP : IsCompletelyPositive Phi) (hTP : ∀ X, (Phi X).trace = X.trace) :
    ∃ e : ℕ, 0 < e ∧ e ≤ d^2 ∧
      ∃ eta : EuclideanSpace ℂ (Fin e), IsState eta ∧
        ∃ U : Matrix.unitaryGroup (Fin d × Fin e) ℂ,
          ∀ X, Phi X = dilationChannel U eta X := by
  obtain ⟨A, hA⟩ := X4P41C.kraus_exists Phi hCP
  let e : Fin d × Fin d ≃ Fin (d^2) := finProdFinEquiv.trans (finCongr (by ring))
  have hk : ∀ X, Phi X = krausApply (fun k => A (e.symm k)) X := by
    intro X
    rw [hA X, krausApply]
    exact (e.symm.sum_comp (fun k => A k * X * (A k)ᴴ)).symm
  have hK : IsKrausFamily (fun k => A (e.symm k)) :=
    X4P41U.tp_kraus _ fun X => by rw [← hk X, hTP]
  have hd : 0 < d^2 := pow_pos (Nat.pos_of_ne_zero (NeZero.ne d)) 2
  obtain ⟨U, hU⟩ := X4P41U.dilation _ hK hd
  refine ⟨d^2, hd, le_rfl, EuclideanSpace.single ⟨0, hd⟩ 1, ?_, U, fun X => by rw [hk X, hU X]⟩
  simp [IsState]

#print axioms solution
