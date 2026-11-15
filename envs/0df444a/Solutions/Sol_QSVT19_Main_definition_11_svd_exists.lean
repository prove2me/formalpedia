-- Prove2me | solution 1 for QSVT19.Main.definition_11_svd_exists
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-15T04:17:23.326498+00:00
-- url     : https://prove2.me/submissions/56145897-b36c-468a-963b-42c6c7696616

import Mathlib.Analysis.InnerProductSpace.SingularValues
import Theorems.Thm_QuantumLinearAlgebra_sorted_svd_of_finrank_le
import Definitions.Def_QSVT19_Main_Setting

noncomputable section
open Matrix
open scoped InnerProduct ComplexConjugate
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace QSVTSVD
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
abbrev Space := EuclideanSpace ℂ ι
abbrev image (M : Matrix ι ι ℂ) := LinearMap.range M.toEuclideanLin
lemma image_fixed (M : Matrix ι ι ℂ) (hM : IsStarProjection M) (x : image M) :
    M.toEuclideanLin x = (x : Space (ι:=ι)) := by
  obtain ⟨y,hy⟩ := x.property
  rw [← hy]
  have hh := congrArg (fun N : Matrix ι ι ℂ => N.toEuclideanLin) hM.isIdempotentElem.eq
  have hh' : M.toEuclideanLin ∘ₗ M.toEuclideanLin = M.toEuclideanLin := by
    simpa only [Matrix.toLpLin_mul_same] using hh
  exact LinearMap.congr_fun hh' y
lemma image_projection_inner (M : Matrix ι ι ℂ) (hM : IsStarProjection M)
    (x : image M) (y : Space (ι:=ι)) :
    inner ℂ (x:Space (ι:=ι)) (M.toEuclideanLin y) = inner ℂ (x:Space (ι:=ι)) y := by
  have hs : M.IsHermitian := hM.isSelfAdjoint
  have hh : M.toEuclideanLin.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hs
  rw [← hh, image_fixed M hM x]
lemma image_expand (M : Matrix ι ι ℂ) (hM : IsStarProjection M) {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ (image M)) (y : Space (ι:=ι)) :
    M.toEuclideanLin y = ∑ i, inner ℂ (b i : Space (ι:=ι)) y • (b i : Space (ι:=ι)) := by
  let z : image M := ⟨M.toEuclideanLin y,⟨y,rfl⟩⟩
  have hh := congrArg (fun x : image M => (x : Space (ι:=ι))) (b.sum_repr' z)
  simp only [Submodule.coe_sum,Submodule.coe_smul] at hh
  change (∑ i, inner ℂ (b i : Space (ι:=ι)) (M.toEuclideanLin y) • (b i : Space (ι:=ι))) = M.toEuclideanLin y at hh
  simpa only [image_projection_inner M hM] using hh.symm
lemma image_frame (M : Matrix ι ι ℂ) (hM : IsStarProjection M) {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ (image M)) :
    M = ∑ i, vecMulVec (fun a => (b i : Space (ι:=ι)) a) (star (fun a => (b i : Space (ι:=ι)) a)) := by
  apply Matrix.toEuclideanLin.injective
  apply LinearMap.ext
  intro y
  rw [image_expand M hM b y]
  simp only [map_sum,LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  have hh := InnerProductSpace.symm_toEuclideanLin_rankOne (b i : Space (ι:=ι)) (b i : Space (ι:=ι))
  have hh' := congrArg Matrix.toEuclideanLin hh
  rw [LinearEquiv.apply_symm_apply] at hh'
  rw [← hh']
  rfl
lemma image_orthonormal {M : Matrix ι ι ℂ} {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ (image M)) (i j : Fin n) :
    star (fun a => (b i : Space (ι:=ι)) a) ⬝ᵥ (fun a => (b j : Space (ι:=ι)) a) = if i=j then 1 else 0 := by
  have hh := b.inner_eq_ite i j
  change inner ℂ (b i : Space (ι:=ι)) (b j : Space (ι:=ι)) = _ at hh
  rw [EuclideanSpace.inner_eq_star_dotProduct] at hh
  simpa only [dotProduct_comm] using hh
lemma image_finrank (M : Matrix ι ι ℂ) : Module.finrank ℂ (image M) = M.rank := by
  rw [Matrix.rank_eq_finrank_range_toLin M (EuclideanSpace.basisFun ι ℂ).toBasis (EuclideanSpace.basisFun ι ℂ).toBasis]
  rfl
end QSVTSVD

noncomputable section
open Matrix QSVT19.Main
open scoped InnerProduct ComplexConjugate
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace QSVTSVD
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def projectedMap (U P Q : Matrix ι ι ℂ) : image P →ₗ[ℂ] image Q :=
  ((Q.toEuclideanLin ∘ₗ U.toEuclideanLin) ∘ₗ (image P).subtype).codRestrict (image Q)
    (fun x => ⟨U.toEuclideanLin (x : Space (ι:=ι)),rfl⟩)
lemma projectedMap_apply (U P Q : Matrix ι ι ℂ) (x : image P) :
    ((projectedMap U P Q x : image Q) : Space (ι:=ι)) =
      Q.toEuclideanLin (U.toEuclideanLin (x : Space (ι:=ι))) := rfl
lemma svd_le (U P Q : Matrix ι ι ℂ) (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hle : Module.finrank ℂ (image P) ≤ Module.finrank ℂ (image Q)) :
    ∃ S : ProjUnitarySVD U P Q, S.d = P.rank ∧ S.dt = Q.rank := by
  obtain ⟨b,c,s,hs,hanti,hsvd⟩ := @QuantumLinearAlgebra.sorted_svd_of_finrank_le (image P) (image Q) inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance (projectedMap U P Q) hle
  let r : Fin (Module.finrank ℂ (image P)) → ι → ℂ := fun i a => (b i : Space (ι:=ι)) a
  let l : Fin (Module.finrank ℂ (image Q)) → ι → ℂ := fun i a => (c i : Space (ι:=ι)) a
  have hmin : min (Module.finrank ℂ (image P)) (Module.finrank ℂ (image Q)) = Module.finrank ℂ (image P) := min_eq_left hle
  let S : ProjUnitarySVD U P Q := {
    d := Module.finrank ℂ (image P)
    dt := Module.finrank ℂ (image Q)
    ψ := r
    ψt := l
    ς := fun i => s (Fin.cast hmin i)
    orthonormal_ψ := image_orthonormal b
    orthonormal_ψt := image_orthonormal c
    span_ψ := image_frame P hP b
    span_ψt := image_frame Q hQ c
    ς_nonneg := fun i => hs _
    ς_antitone := fun i j hij => hanti (by simpa only [Fin.le_def,Fin.val_cast] using hij)
    svd := by
      have heval (i : Fin (Module.finrank ℂ (image P))) :
          (Q*U)*ᵥ(r i) = (s i:ℂ) • l (Fin.castLE hle i) := by
        have hh := congrArg (fun z : image Q => (z : Space (ι:=ι))) (hsvd i)
        have hh' := congrArg (WithLp.ofLp) hh
        simpa only [projectedMap_apply,Matrix.ofLp_toLpLin,Matrix.toLin'_apply,
          Submodule.coe_smul,WithLp.ofLp_smul,← Matrix.mulVec_mulVec] using hh'
      calc
        _ = (Q*U)*(∑ i, vecMulVec (r i) (star (r i))) :=
          congrArg (fun N : Matrix ι ι ℂ => (Q*U)*N) (image_frame P hP b)
        _ = ∑ i, (s i:ℂ) • vecMulVec (l (Fin.castLE hle i)) (star (r i)) := by
          simp only [Finset.mul_sum,mul_vecMulVec,heval,smul_vecMulVec]
        _ = _ := by
          apply Finset.sum_bij (fun i _ => Fin.cast hmin.symm i)
          · intro i _;exact Finset.mem_univ _
          · intro i hi j hj hij
            exact Fin.cast_injective _ hij
          · intro j _;exact ⟨Fin.cast hmin j,Finset.mem_univ _,by simp⟩
          · intro i _
            have hsi : Fin.cast hmin (Fin.cast hmin.symm i) = i := Fin.ext rfl
            have hri : Fin.castLE (min_le_left _ _) (Fin.cast hmin.symm i) = i := Fin.ext rfl
            have hli : Fin.castLE (min_le_right _ _) (Fin.cast hmin.symm i) = Fin.castLE hle i := Fin.ext rfl
            rw [hsi,hri,hli]

  }
  exact ⟨S,image_finrank P,image_finrank Q⟩
end QSVTSVD

noncomputable section
open Matrix QSVT19.Main
open scoped ComplexConjugate
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace QSVTSVD
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma svd_adjoint (U P Q : Matrix ι ι ℂ) (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (T : ProjUnitarySVD Uᴴ Q P) :
    ∃ S : ProjUnitarySVD U P Q, S.d = T.dt ∧ S.dt = T.d := by
  let hm : min T.dt T.d = min T.d T.dt := min_comm _ _
  have hstarP : Pᴴ=P := hP.isSelfAdjoint
  have hstarQ : Qᴴ=Q := hQ.isSelfAdjoint
  refine ⟨{
    d := T.dt
    dt := T.d
    ψ := T.ψt
    ψt := T.ψ
    ς := fun i => T.ς (Fin.cast hm i)
    orthonormal_ψ := T.orthonormal_ψt
    orthonormal_ψt := T.orthonormal_ψ
    span_ψ := T.span_ψt
    span_ψt := T.span_ψ
    ς_nonneg := fun i => T.ς_nonneg _
    ς_antitone := fun i j hij => T.ς_antitone (by simpa only [Fin.le_def,Fin.val_cast] using hij)
    svd := by
      have hh := congrArg Matrix.conjTranspose T.svd
      simp only [conjTranspose_mul,conjTranspose_conjTranspose,hstarP,hstarQ,
        conjTranspose_sum,conjTranspose_smul,conjTranspose_vecMulVec,star_star,
        Complex.star_def,Complex.conj_ofReal] at hh
      rw [← mul_assoc] at hh
      rw [hh]
      apply Finset.sum_bij (fun i _ => Fin.cast hm.symm i)
      · intro i _;exact Finset.mem_univ _
      · intro i hi j hj hij
        exact Fin.cast_injective _ hij
      · intro j _;exact ⟨Fin.cast hm j,Finset.mem_univ _,by simp⟩
      · intro i _
        have hsi : Fin.cast hm (Fin.cast hm.symm i)=i := Fin.ext rfl
        have hli : Fin.castLE (min_le_right _ _) (Fin.cast hm.symm i) = Fin.castLE (min_le_left _ _) i := Fin.ext rfl
        have hri : Fin.castLE (min_le_left _ _) (Fin.cast hm.symm i) = Fin.castLE (min_le_right _ _) i := Fin.ext rfl
        rw [hsi,hli,hri]

  },rfl,rfl⟩
theorem svd_exists {ι : Type*} [Fintype ι] [DecidableEq ι] (U P Q : Matrix ι ι ℂ)
    (_hU : U ∈ Matrix.unitaryGroup ι ℂ) (hP : IsStarProjection P) (hQ : IsStarProjection Q) :
    ∃ S : ProjUnitarySVD U P Q, S.d=P.rank ∧ S.dt=Q.rank := by
  by_cases hle : Module.finrank ℂ (image P) ≤ Module.finrank ℂ (image Q)
  · exact svd_le U P Q hP hQ hle
  · obtain ⟨T,hTd,hTdt⟩ := svd_le Uᴴ Q P hQ hP (le_of_not_ge hle)
    obtain ⟨S,hSd,hSdt⟩ := svd_adjoint U P Q hP hQ T
    exact ⟨S,hSd.trans hTdt,hSdt.trans hTd⟩
end QSVTSVD

set_option autoImplicit false
open QSVT19.Main


/-- Gilyén, Su, Low, Wiebe, arXiv:1806.01838v1, Definition 11, p. 15 (existence claim): "Let H_U be a finite-dimensional Hilbert space and
let U, Π, Π̃ ∈ End(H_U) be linear operators on H_U such that U is a unitary, and Π, Π̃ are
orthogonal projectors, and let A = Π̃UΠ. Let d := rank(Π), d̃ := rank(Π̃), d_min := min(d, d̃). By
singular value decomposition we know that there exist orthonormal bases (|ψ_i⟩ : i ∈ [d]),
(|ψ̃_i⟩ : i ∈ [d̃]) of the subspaces img(Π) and img(Π̃) respectively, such that
A = ∑_{i=1}^{d_min} ς_i|ψ̃_i⟩⟨ψ_i|, (17) and for all i ∈ [d_min]: ς_i ∈ R^+_0. Moreover,
ς_i ≥ ς_j for all i ≤ j ∈ [d_min]."

**Formalization Note.** `H_U` is `ι → ℂ` for a finite type `ι`, with inner product
`star v ⬝ᵥ w`; `Π, Π̃` are `Proj, Projt`; "unitary" is `U ∈ Matrix.unitaryGroup ι ℂ` and
"orthogonal projector" is `IsStarProjection` (self-adjoint idempotent). A term of `ProjUnitarySVD U Proj Projt` is exactly such a decomposition (see its
docstring); the statement also records `d = rank Π` and `d̃ = rank Π̃`. This claim shows that the
quantification over decompositions in Theorem 17 and Corollary 18 is not vacuous. -/
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] (U Proj Projt : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ) (hProj : IsStarProjection Proj) (hProjt : IsStarProjection Projt) :
    ∃ S : ProjUnitarySVD U Proj Projt, S.d = Proj.rank ∧ S.dt = Projt.rank := by
  exact QSVTSVD.svd_exists U Proj Projt hU hProj hProjt