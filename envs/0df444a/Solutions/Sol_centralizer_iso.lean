-- Prove2me | solution 1 for centralizer_iso
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T23:24:33.688798+00:00
-- url     : https://prove2.me/submissions/cb03ba7d-6f76-4629-b862-862bd3419685

import Mathlib
import Definitions.Def_OAIQ093D001
import Definitions.Def_OAIQ093D005
import Theorems.Thm_eigenspace_orthogonal
import Theorems.Thm_ofIsCompl_adjoint_comp
import Theorems.Thm_star_normal_maxGenEigenspace_eq_eigenspace

section
-- module Solutions.OAIQ093_PR.ToMathlib_Analysis_Matrix_UnitaryAux
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Unitary matrices: helper lemmas

General-purpose material extracted from the Gromov development, destined for mathlib.
-/


lemma diag_of_eigenspace_span {A: Type*} [Nontrivial A] [AddCommGroup A] [Module ℂ A] (g: A →ₗ[ℂ] A) (k: ℂ) (hg: Module.End.eigenspace g k = ⊤):
  g = k • 1 := by

  rw [LinearMap.ext_iff]
  intro x
  simp


  have x_mem: x ∈ Module.End.eigenspace g k := by
    simp [hg]

  rw [Module.End.mem_eigenspace_iff] at x_mem
  exact x_mem



lemma linearmap_comp_toContinuousLinearMap {P: Type*} [AddCommGroup P] [Module ℂ P] [TopologicalSpace P] [IsTopologicalAddGroup P] [ContinuousSMul ℂ P] [T2Space P]  [FiniteDimensional ℂ P]  (a b: P →ₗ[ℂ] P):
  (a.comp b).toContinuousLinearMap = a.toContinuousLinearMap * b.toContinuousLinearMap := rfl

lemma unitary_preserves_norm (n: ℕ) (h: Matrix.unitaryGroup (Fin n) ℂ) (x: EuclideanSpace ℂ (Fin n)): ‖(Matrix.toEuclideanLin h.val) x‖ = ‖x‖ := by
  have h_unitary := Unitary.star_mul_self_of_mem h.property
  apply_fun Matrix.toEuclideanLin at h_unitary
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal] at h_unitary
  conv at h_unitary =>
    lhs
    equals (Matrix.toEuclideanLin (star h.val)) ∘ₗ (Matrix.toEuclideanLin (h.val)) =>
      rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
      rw [← Matrix.toLin_mul]
  rw [← Matrix.toEuclideanLin_eq_toLin_orthonormal] at h_unitary
  rw [Matrix.star_eq_conjTranspose] at h_unitary
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint] at h_unitary

  apply_fun (fun f => LinearMap.toContinuousLinearMap f) at h_unitary
  simp [-EmbeddingLike.apply_eq_iff_eq] at h_unitary
  conv at h_unitary =>
    lhs
    rw [linearmap_comp_toContinuousLinearMap]
    rw [ContinuousLinearMap.mul_def]
    lhs
    rw [LinearMap.adjoint_toContinuousLinearMap]

  conv at h_unitary =>
    rhs
    equals 1 =>
      ext x
      simp
  rw [← ContinuousLinearMap.norm_map_iff_adjoint_comp_self] at h_unitary
  specialize h_unitary x
  simp at h_unitary
  exact h_unitary


lemma ofIsCompl_commute {P: Type*} [NormedAddCommGroup P] [CompleteSpace P] [InnerProductSpace ℂ P] [FiniteDimensional ℂ P]  {p q : Submodule ℂ P} (h : IsCompl p q)
    (φ : p →ₗ[ℂ] P) (ψ : q →ₗ[ℂ] P)
    (a: P →ₗ[ℂ] P) (a_map_p: ∀ x: p, a x ∈ p) (a_map_q: ∀ x: q, a x ∈ q)
    (phi_a_comm: ∀ x: p, φ ⟨a x, a_map_p x⟩ = a (φ x))
    (psi_a_comm: ∀ x: q, ψ ⟨a x, a_map_q x⟩ = a (ψ x))
    : (LinearMap.ofIsCompl h (φ) (ψ)) * a = a * (LinearMap.ofIsCompl h (φ) (ψ)) := by

  rw [LinearMap.ext_iff]
  intro v
  obtain ⟨x, y, v_eq, other⟩ := Submodule.existsUnique_add_of_isCompl h v
  rw [← v_eq]
  simp

  have a_x: a x = (⟨a x, a_map_p x⟩ : p).val := by simp
  have a_y: a y = (⟨a y, a_map_q y⟩ : q).val := by simp

  rw [a_x, a_y]
  rw [LinearMap.ofIsCompl_apply_left, LinearMap.ofIsCompl_apply_right]
  rw [phi_a_comm]
  rw [psi_a_comm]
end

section
-- module Solutions.OAIQ093_PR.ToMathlib_Analysis_Matrix_Unitary
attribute [-instance] _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The centralizer of a non-scalar unitary matrix

`centralizer_iso`: a subgroup of the unitary group containing a non-scalar element splits as a
direct sum of the eigenspaces of that element.
-/


-- The rewrites below name their scalar field, source and target explicitly. Left implicit,
-- each would leave a metavariable whose instances sit across a diamond on these spaces
-- (`Submodule`'s subtype/`addCommGroup`/`module` vs the `NormedAddCommGroup`/
-- `InnerProductSpace` structures), which only reconciles at a raised `maxSynthPendingDepth`.
-- Note the two rewrites in each block act on *different* spaces: the restricted eigenspace
-- and the ambient `EuclideanSpace ℂ (Fin n)`.
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 100000 in
lemma centralizer_iso_oai {n: ℕ} [hn: NeZero n] (G: Subgroup (Matrix.unitaryGroup (Fin n) ℂ)) (g: G) (g_not: ∀ z: ℂ, g.val.val ≠ z • 1):
    Nonempty (IsoData g) := by


  obtain ⟨k, hk⟩ := Module.End.exists_eigenvalue g.val.val.toEuclideanLin
  by_cases gen_eigenspace_top: Module.End.maxGenEigenspace g.val.val.toEuclideanLin k = ⊤
  .
    rw [star_normal_maxGenEigenspace_eq_eigenspace (by simp)] at gen_eigenspace_top
    apply Module.End.HasEigenvalue.exists_hasEigenvector at hk

    have eq_diag := diag_of_eigenspace_span g.val.val.toEuclideanLin k gen_eigenspace_top
    specialize g_not k
    apply_fun (fun f =>  LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℂ).toBasis (EuclideanSpace.basisFun (Fin n) ℂ).toBasis f) at eq_diag
    simp [Matrix.toEuclideanLin_eq_toLin_orthonormal] at eq_diag
    contradiction
  .
    have span := Module.End.iSup_maxGenEigenspace_eq_top g.val.val.toEuclideanLin
    rw [iSup_split_single _ k] at span
    rw [← codisjoint_iff] at span

    have a_b_compl: IsCompl _ _ := {
      disjoint := by
        have foo := Module.End.independent_genEigenspace (g.val.val.toEuclideanLin) ⊤
        rw [iSupIndep_def] at foo
        apply foo
      codisjoint := span
    }

    have other_ne_bot := Codisjoint.ne_bot_of_ne_top span gen_eigenspace_top
    rw [codisjoint_iff] at span

    have preserves := Module.End.mapsTo_genEigenspace_of_comm (f := g.val.val.toEuclideanLin) (g := g.val.val.toEuclideanLin) (by simp) k (Module.End.maxGenEigenspaceIndex g.val.val.toEuclideanLin k)
    rw [← Module.End.maxGenEigenspace_eq] at preserves
    rw [← iSup_ne_bot_subtype] at span


    have comm_g_h (h: Subgroup.centralizer {g.val}): Commute (Matrix.toEuclideanLin g.val.val) (Matrix.toEuclideanLin h.val.val) := by
      have foo := h.property
      rw [Subgroup.mem_centralizer_iff] at foo
      rw [commute_iff_eq]
      simp at foo
      rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
      rw [Module.End.mul_eq_comp]
      rw [← Matrix.toLin_mul]
      rw [Module.End.mul_eq_comp]
      rw [← Matrix.toLin_mul]
      apply_fun (fun f => f.val) at foo
      simp at foo
      rw [foo]

    have other_invariant (h: Subgroup.centralizer {g.val}):  ⨆ (i : { i : Module.End.Eigenvalues g.val.val.toEuclideanLin // i.val ≠ k }), Module.End.maxGenEigenspace h.val.val.toEuclideanLin i ∈ (Module.End.invtSubmodule g.val.val.toEuclideanLin) := by
      apply SupClosed.iSup_mem
      . simp
      . simp
      .
        intro i
        simp
        apply Module.End.mapsTo_genEigenspace_of_comm
        rw [Commute.symm_iff]
        apply comm_g_h

    --simp_rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem] at other_invariant


    let map_first (h: Subgroup.centralizer {g.val}) := h.val.val.toEuclideanLin.restrict (Module.End.mapsTo_genEigenspace_of_comm (f := g.val.val.toEuclideanLin) (g := h.val.val.toEuclideanLin) (by
      apply comm_g_h
    ) k ⊤)


    let d := (Module.finrank ℂ ↥((Module.End.genEigenspace (Matrix.toEuclideanLin g.val.val) k) ⊤))
    let map_first_unitary (h: Subgroup.centralizer {g.val}): Matrix.unitaryGroup (Fin d) ℂ := {
      val := LinearMap.toMatrixOrthonormal (stdOrthonormalBasis ℂ ↥((Module.End.genEigenspace (Matrix.toEuclideanLin g.val.val) k) ⊤)) (map_first h)
      property := by


        rw [Matrix.mem_unitaryGroup_iff']

        conv =>
          lhs
          lhs
          -- TODO - why does this timeout when not inside 'conv'?
          rw [Matrix.star_eq_conjTranspose]

        simp only [LinearMap.toMatrixOrthonormal_apply]
        simp []
        conv =>
          lhs
          lhs
          -- TODO - why does this timeout when not inside 'conv'?
          rw [← LinearMap.toMatrix_adjoint]
          arg 2
        rw [← LinearMap.toMatrix_mul]

        apply_fun Matrix.toLin (stdOrthonormalBasis ℂ _).toBasis (stdOrthonormalBasis ℂ _).toBasis
        rw [Matrix.toLin_toMatrix]
        rw [Matrix.toLin_one]
        conv =>
          rhs
          equals 1 =>
            ext a
            simp

        simp [map_first]
        have h_unitary := Unitary.star_mul_self_of_mem h.val.property
        apply_fun Matrix.toEuclideanLin at h_unitary
        rw [Matrix.toEuclideanLin_eq_toLin_orthonormal] at h_unitary
        conv at h_unitary =>
          lhs
          equals (Matrix.toEuclideanLin (star h.val.val)) ∘ₗ (Matrix.toEuclideanLin (h.val.val)) =>
            rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
            rw [← Matrix.toLin_mul]
        rw [← Matrix.toEuclideanLin_eq_toLin_orthonormal] at h_unitary
        rw [Matrix.star_eq_conjTranspose] at h_unitary
        rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint] at h_unitary
        conv at h_unitary =>
          rhs
          rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
          equals 1 =>
            ext z
            simp

        apply_fun (fun f => LinearMap.toContinuousLinearMap f)
        simp [-EmbeddingLike.apply_eq_iff_eq]
        conv =>
          lhs
          rw [Module.End.mul_eq_comp]
          rw [linearmap_comp_toContinuousLinearMap]
          rw [ContinuousLinearMap.mul_def]
          lhs
          rw [LinearMap.adjoint_toContinuousLinearMap (𝕜 := ℂ) (E := ↥((Module.End.genEigenspace (Matrix.toEuclideanLin g.val.val) k) ⊤)) (F := ↥((Module.End.genEigenspace (Matrix.toEuclideanLin g.val.val) k) ⊤))]

        conv =>
          rhs
          equals 1 =>
            ext z
            simp
        rw [← ContinuousLinearMap.norm_map_iff_adjoint_comp_self]
        simp only [LinearMap.coe_toContinuousLinearMap']
        conv =>
          intro x
          rw [LinearMap.restrict_apply (by
            apply Module.End.mapsTo_genEigenspace_of_comm (by
              apply comm_g_h
            )
          )]
          simp
          rw [← LinearMap.coe_toContinuousLinearMap']


        apply_fun (fun f => LinearMap.toContinuousLinearMap f) at h_unitary
        simp [-EmbeddingLike.apply_eq_iff_eq] at h_unitary
        conv at h_unitary =>
          lhs
          rw [linearmap_comp_toContinuousLinearMap]
          rw [ContinuousLinearMap.mul_def]
          lhs
          rw [LinearMap.adjoint_toContinuousLinearMap (𝕜 := ℂ) (E := EuclideanSpace ℂ (Fin n)) (F := EuclideanSpace ℂ (Fin n))]

        conv at h_unitary =>
          rhs
          equals 1 =>
            ext x
            simp
        rw [← ContinuousLinearMap.norm_map_iff_adjoint_comp_self] at h_unitary
        intro x
        specialize h_unitary x.val
        exact h_unitary
        . exact LinearEquiv.injective LinearMap.toContinuousLinearMap
        . intro x y hxy
          simpa using hxy
    }


    let map_first_hom: MonoidHom (Subgroup.centralizer {g.val}) _ := {
      toFun := map_first_unitary
      map_one' := by
        simp [map_first_unitary, map_first]
        apply_fun Matrix.toLin (stdOrthonormalBasis ℂ _).toBasis (stdOrthonormalBasis ℂ _).toBasis
        .
          simp
          simp_rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
          ext a
          rfl
        . intro x y hxy
          simpa using hxy
      map_mul' := by
        intro x y
        simp [map_first_unitary, map_first]
        apply_fun Matrix.toLin (stdOrthonormalBasis ℂ _).toBasis (stdOrthonormalBasis ℂ _).toBasis
        .
          simp
          rw [LinearMap.ext_iff]
          intro a
          rw [← LinearMap.toMatrix_mul]
          simp
          simp_rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
          conv =>
            lhs
            arg 1
            arg 1
            -- TODO - figure out why toLin_mul doesn't work here
            equals ((Matrix.toLin (EuclideanSpace.basisFun (Fin n) ℂ).toBasis (EuclideanSpace.basisFun (Fin n) ℂ).toBasis) (↑↑↑x)) ∘ₗ (((Matrix.toLin (EuclideanSpace.basisFun (Fin n) ℂ).toBasis (EuclideanSpace.basisFun (Fin n) ℂ).toBasis) (↑↑↑y))) =>
              rw [← Matrix.toLin_mul]

          rfl
        . intro x y hxy
          simpa using hxy
    }

    let first_range := map_first_hom.range


    let map_second (h: Subgroup.centralizer {g.val}) := h.val.val.toEuclideanLin.restrict
      (p :=  ↑((iSup fun (i : ℂ) ↦ ⨆ (_ : i ≠ k), Module.End.maxGenEigenspace (Matrix.toEuclideanLin g.val.val) i)))
      (q :=  ↑((iSup fun (i : ℂ) ↦ ⨆ (_ : i ≠ k), Module.End.maxGenEigenspace (Matrix.toEuclideanLin g.val.val) i)))
      (by
        intro x hx
        apply LinearMap.mapsTo_biSup_of_mapsTo
        .
          intro z
          apply Module.End.mapsTo_maxGenEigenspace_of_comm
          apply comm_g_h
        . exact hx
      )


    let map_second_unitary (h: Subgroup.centralizer {g.val}): Matrix.unitaryGroup _ ℂ := {
      val := LinearMap.toMatrixOrthonormal (stdOrthonormalBasis ℂ ↥((iSup fun (i : ℂ) ↦ ⨆ (_ : i ≠ k), Module.End.maxGenEigenspace (Matrix.toEuclideanLin g.val.val) i))) (map_second h)
      property := by
        -- TODO - deduplicate this with 'map_first_unitary'
        rw [Matrix.mem_unitaryGroup_iff']

        conv =>
          lhs
          lhs
          -- TODO - why does this timeout when not inside 'conv'?
          rw [Matrix.star_eq_conjTranspose]

        simp only [LinearMap.toMatrixOrthonormal_apply]
        simp []
        conv =>
          lhs
          lhs
          -- TODO - why does this timeout when not inside 'conv'?
          rw [← LinearMap.toMatrix_adjoint]
          arg 2
        rw [← LinearMap.toMatrix_mul]

        apply_fun Matrix.toLin (stdOrthonormalBasis ℂ _).toBasis (stdOrthonormalBasis ℂ _).toBasis
        rw [Matrix.toLin_toMatrix]
        rw [Matrix.toLin_one]
        conv =>
          rhs
          equals 1 =>
            ext a
            simp

        simp [map_second]
        have h_unitary := Unitary.star_mul_self_of_mem h.val.property
        apply_fun Matrix.toEuclideanLin at h_unitary
        rw [Matrix.toEuclideanLin_eq_toLin_orthonormal] at h_unitary
        conv at h_unitary =>
          lhs
          equals (Matrix.toEuclideanLin (star h.val.val)) ∘ₗ (Matrix.toEuclideanLin (h.val.val)) =>
            rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
            rw [← Matrix.toLin_mul]
        rw [← Matrix.toEuclideanLin_eq_toLin_orthonormal] at h_unitary
        rw [Matrix.star_eq_conjTranspose] at h_unitary
        rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint] at h_unitary
        conv at h_unitary =>
          rhs
          rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
          equals 1 =>
            ext z
            simp

        apply_fun (fun f => LinearMap.toContinuousLinearMap f)
        simp [-EmbeddingLike.apply_eq_iff_eq]
        conv =>
          lhs
          rw [Module.End.mul_eq_comp]
          rw [linearmap_comp_toContinuousLinearMap]
          rw [ContinuousLinearMap.mul_def]
          lhs
          rw [LinearMap.adjoint_toContinuousLinearMap (𝕜 := ℂ) (E := ↥((iSup fun (i : ℂ) ↦ ⨆ (_ : i ≠ k), Module.End.maxGenEigenspace (Matrix.toEuclideanLin g.val.val) i))) (F := ↥((iSup fun (i : ℂ) ↦ ⨆ (_ : i ≠ k), Module.End.maxGenEigenspace (Matrix.toEuclideanLin g.val.val) i)))]

        conv =>
          rhs
          equals 1 =>
            ext z
            simp
        rw [← ContinuousLinearMap.norm_map_iff_adjoint_comp_self]
        simp only [LinearMap.coe_toContinuousLinearMap']
        conv =>
          intro x
          rw [LinearMap.restrict_apply (by
            apply LinearMap.mapsTo_biSup_of_mapsTo
            intro z
            apply Module.End.mapsTo_maxGenEigenspace_of_comm
            apply comm_g_h
          )]
          simp
          rw [← LinearMap.coe_toContinuousLinearMap']


        apply_fun (fun f => LinearMap.toContinuousLinearMap f) at h_unitary
        simp [-EmbeddingLike.apply_eq_iff_eq] at h_unitary
        conv at h_unitary =>
          lhs
          rw [linearmap_comp_toContinuousLinearMap]
          rw [ContinuousLinearMap.mul_def]
          lhs
          rw [LinearMap.adjoint_toContinuousLinearMap (𝕜 := ℂ) (E := EuclideanSpace ℂ (Fin n)) (F := EuclideanSpace ℂ (Fin n))]

        conv at h_unitary =>
          rhs
          equals 1 =>
            ext x
            simp
        rw [← ContinuousLinearMap.norm_map_iff_adjoint_comp_self] at h_unitary
        intro x
        specialize h_unitary x.val
        exact h_unitary
        . exact LinearEquiv.injective LinearMap.toContinuousLinearMap
        . intro x y hxy
          simpa using hxy
    }

    let map_second_hom: MonoidHom (Subgroup.centralizer {g.val}) _ := {
      toFun := map_second_unitary
      -- TODO - deduplicate these with 'map_first_hom'
      map_one' := by
        simp [map_second_unitary, map_second]
        apply_fun Matrix.toLin (stdOrthonormalBasis ℂ _).toBasis (stdOrthonormalBasis ℂ _).toBasis
        .
          simp
          simp_rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
          ext a
          rfl
        . intro x y hxy
          simpa using hxy
      map_mul' := by
        intro x y
        simp [map_second_unitary, map_second]
        apply_fun Matrix.toLin (stdOrthonormalBasis ℂ _).toBasis (stdOrthonormalBasis ℂ _).toBasis
        .
          simp
          rw [LinearMap.ext_iff]
          intro a
          rw [← LinearMap.toMatrix_mul]
          simp
          simp_rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
          conv =>
            lhs
            arg 1
            arg 1
            -- TODO - figure out why toLin_mul doesn't work here
            equals ((Matrix.toLin (EuclideanSpace.basisFun (Fin n) ℂ).toBasis (EuclideanSpace.basisFun (Fin n) ℂ).toBasis) (↑↑↑x)) ∘ₗ (((Matrix.toLin (EuclideanSpace.basisFun (Fin n) ℂ).toBasis (EuclideanSpace.basisFun (Fin n) ℂ).toBasis) (↑↑↑y))) =>
              rw [← Matrix.toLin_mul]

          rfl
        . intro x y hxy
          simpa using hxy
    }

    let prod_hom := MonoidHom.prod map_first_hom.rangeRestrict map_second_hom.rangeRestrict
    let prod_iso := MulEquiv.ofBijective prod_hom (by
      unfold Function.Bijective
      refine ⟨?_, ?_⟩
      .
        -- TODO - this can probably be much simpler
        simp [prod_hom]
        intro x y hxy
        simp at hxy
        obtain ⟨first_eq, second_eq⟩ := hxy

        let map_first_x_new: ((Module.End.genEigenspace (Matrix.toEuclideanLin g.val.val) k) ⊤) →ₗ[ℂ] (EuclideanSpace ℂ (Fin n)) := {
          toFun := fun a => map_first x a
          map_add' := by simp
          map_smul' := by simp
        }

        let map_second_x_new: ↑((iSup fun (i : ℂ) ↦ ⨆ (_ : i ≠ k), Module.End.maxGenEigenspace (Matrix.toEuclideanLin g.val.val) i)) →ₗ[ℂ] (EuclideanSpace ℂ (Fin n)) := {
          toFun := fun a => map_second x a
          map_add' := by simp
          map_smul' := by simp
        }

        let x_map := LinearMap.ofIsCompl a_b_compl (map_first_x_new) (map_second_x_new)

        let map_first_y_new: ((Module.End.genEigenspace (Matrix.toEuclideanLin g.val.val) k) ⊤) →ₗ[ℂ] (EuclideanSpace ℂ (Fin n)) := {
          toFun := fun a => map_first y a
          map_add' := by simp
          map_smul' := by simp
        }

        let map_second_y_new: ↑((iSup fun (i : ℂ) ↦ ⨆ (_ : i ≠ k), Module.End.maxGenEigenspace (Matrix.toEuclideanLin g.val.val) i)) →ₗ[ℂ] (EuclideanSpace ℂ (Fin n)) := {
          toFun := fun a => map_second y a
          map_add' := by simp
          map_smul' := by simp
        }

        let y_map := LinearMap.ofIsCompl a_b_compl (map_first_y_new) (map_second_y_new)

        have first_eq_second: x_map = y_map := by
          simp [x_map]
          apply LinearMap.ofIsCompl_eq
          . intro z
            simp [y_map]
            simp [map_first_x_new, map_first_y_new]
            apply_fun (fun f => f.val) at first_eq
            simp at first_eq
            simp [map_first_hom, map_first_unitary] at first_eq
            rw [first_eq]
          . intro z
            simp [y_map]
            simp [map_second_x_new, map_second_y_new]
            apply_fun (fun f => f.val) at second_eq
            simp at second_eq
            simp [map_second_hom, map_second_unitary] at second_eq
            congr


        have x_map_eq: x_map = x.val.val.toEuclideanLin := by
          simp [x_map]
          apply LinearMap.ofIsCompl_eq
          . intro z
            rfl
          . intro z
            rfl

        have y_map_eq: y_map = y.val.val.toEuclideanLin := by
          simp [y_map]
          apply LinearMap.ofIsCompl_eq
          . intro z
            rfl
          . intro z
            rfl


        rw [x_map_eq, y_map_eq] at first_eq_second
        simp at first_eq_second
        exact first_eq_second
      .
        intro a
        have first_prop := a.fst.property
        have second_prop := a.snd.property
        simp only [prod_hom]
        rw [MonoidHom.mem_range] at first_prop
        rw [MonoidHom.mem_range] at second_prop

        obtain ⟨x, hx⟩ := first_prop
        obtain ⟨y, hy⟩ := second_prop

        let map_first_x_new: ((Module.End.genEigenspace (Matrix.toEuclideanLin g.val.val) k) ⊤) →ₗ[ℂ] (EuclideanSpace ℂ (Fin n)) := {
          toFun := fun a => map_first x a
          map_add' := by simp
          map_smul' := by simp
        }

        let map_second_y_new: ↑((iSup fun (i : ℂ) ↦ ⨆ (_ : i ≠ k), Module.End.maxGenEigenspace (Matrix.toEuclideanLin g.val.val) i)) →ₗ[ℂ] (EuclideanSpace ℂ (Fin n)) := {
          toFun := fun a => map_second y a
          map_add' := by simp
          map_smul' := by simp
        }

        have map_first_x_unitary: (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := ↥((Module.End.genEigenspace (Matrix.toEuclideanLin g.val.val) k) ⊤)) (F := EuclideanSpace ℂ (Fin n)) map_first_x_new.toContinuousLinearMap).comp map_first_x_new.toContinuousLinearMap = 1 := by
          rw [← ContinuousLinearMap.norm_map_iff_adjoint_comp_self]
          intro z
          simp [map_first_x_new, map_first]
          apply unitary_preserves_norm

        apply_fun (fun f => f.toLinearMap) at map_first_x_unitary
        simp at map_first_x_unitary

        have map_second_y_unitary: (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := ↥((iSup fun (i : ℂ) ↦ ⨆ (_ : i ≠ k), Module.End.maxGenEigenspace (Matrix.toEuclideanLin g.val.val) i))) (F := EuclideanSpace ℂ (Fin n)) map_second_y_new.toContinuousLinearMap).comp map_second_y_new.toContinuousLinearMap = 1 := by
          rw [← ContinuousLinearMap.norm_map_iff_adjoint_comp_self]
          intro z
          simp [map_second_y_new, map_second]
          apply unitary_preserves_norm

        apply_fun (fun f => f.toLinearMap) at map_second_y_unitary
        simp at map_second_y_unitary

        let new := LinearMap.ofIsCompl a_b_compl map_first_x_new map_second_y_new
        use ⟨⟨(Matrix.toEuclideanLin.symm new), (by
          simp [Matrix.mem_unitaryGroup_iff']
          apply_fun (fun f => Matrix.toEuclideanLin f)
          . simp [-EmbeddingLike.apply_eq_iff_eq, new]
            rw [Matrix.star_eq_conjTranspose]
            simp_rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
            simp
            rw [← LinearMap.toMatrix_adjoint]
            simp


            conv =>
              rhs
              equals 1 =>
                ext z
                simp


            apply ofIsCompl_adjoint_comp
            .
              rw [star_normal_maxGenEigenspace_eq_eigenspace (by simp)]
              conv =>
                rhs
                arg 1
                intro x
                arg 1
                intro x
                rw [star_normal_maxGenEigenspace_eq_eigenspace (by simp)]
              simp
              intro i hi
              apply eigenspace_orthogonal
              . simp
              . omega
            .
              apply map_first_x_unitary
            . intro v
              exact (map_first x v).2
            .
              apply map_second_y_unitary
            . intro v
              exact (map_second y v).2
          . intro x y hxy
            simpa using hxy
        )⟩, (by
          rw [Subgroup.mem_centralizer_iff]
          simp
          apply_fun (fun f => Matrix.toEuclideanLin f.val)
          simp only []
          simp_rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
          simp only [Matrix.toLin_symm, Submonoid.coe_mul]
          rw [Matrix.toLin_mul (v₂ := (EuclideanSpace.basisFun (Fin n) ℂ).toBasis )]
          simp
          rw [Matrix.toLin_mul (v₂ := (EuclideanSpace.basisFun (Fin n) ℂ).toBasis )]
          simp [new]
          rw [eq_comm]
          apply ofIsCompl_commute
          .
            intro z
            simp [map_first_x_new, map_first]
            simp_rw [← Matrix.toEuclideanLin_eq_toLin_orthonormal]
            have x_prop := x.property
            rw [Subgroup.mem_centralizer_iff] at x_prop
            simp at x_prop
            rw [Subtype.ext_iff] at x_prop
            simp at x_prop
            show (Matrix.toEuclideanLin (↑↑x : Matrix (Fin n) (Fin n) ℂ))
                  ((Matrix.toEuclideanLin (↑↑g : Matrix (Fin n) (Fin n) ℂ)) (↑z : EuclideanSpace ℂ (Fin n)))
                = (Matrix.toEuclideanLin (↑↑g : Matrix (Fin n) (Fin n) ℂ))
                  ((Matrix.toEuclideanLin (↑↑x : Matrix (Fin n) (Fin n) ℂ)) (↑z : EuclideanSpace ℂ (Fin n)))
            simp only [Matrix.toEuclideanLin_apply, WithLp.ofLp_toLp, Matrix.mulVec_mulVec]
            rw [x_prop]
          .
            intro z
            simp [map_second_y_new, map_second]
            simp_rw [← Matrix.toEuclideanLin_eq_toLin_orthonormal]
            rw [Matrix.toEuclideanLin_apply]
            rw [Matrix.toEuclideanLin_apply]
            rw [Matrix.toEuclideanLin_apply]
            rw [Matrix.toEuclideanLin_apply]
            simp
            have y_prop := y.property
            rw [Subgroup.mem_centralizer_iff] at y_prop
            simp at y_prop
            rw [Subtype.ext_iff] at y_prop
            simp at y_prop
            rw [y_prop]
          .
            intro z
            apply Module.End.mapsTo_maxGenEigenspace_of_comm
            rw [commute_iff_eq]
            rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
            simp
          .
            intro x
            apply LinearMap.mapsTo_biSup_of_mapsTo
            .
              intro z
              apply Module.End.mapsTo_maxGenEigenspace_of_comm
              rw [commute_iff_eq]
              rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
            . simp
          . intro a b hab
            simpa using hab

        )⟩


        apply Prod.ext
        .
          rw [Subtype.ext_iff]
          conv =>
            rhs
            rw [← hx]
          simp
          simp [map_first_hom, map_first_unitary]
          apply LinearMap.ext
          intro z
          apply Subtype.ext
          simp only [LinearMap.restrict_coe_apply, new, LinearEquiv.apply_symm_apply,
            LinearMap.ofIsCompl_apply_left, map_first_x_new, map_first, LinearMap.coe_mk,
            AddHom.coe_mk]
        .
          rw [Subtype.ext_iff]
          conv =>
            rhs
            rw [← hy]
          simp
          simp [map_second_hom, map_second_unitary]
          simp [map_second]
          rw [LinearMap.ext_iff]
          intro z
          rw [Subtype.ext_iff]
          simp [new]
          simp [map_second_y_new, map_second]
    )
    -- Submodule.finrank_add_eq_of_isCompl


    apply Nonempty.intro
    exact {
      a := d
      b := _
      hab := by
        have sum_eq := Submodule.finrank_add_eq_of_isCompl a_b_compl
        simp at sum_eq
        apply sum_eq
      ha := by
        rw [Nat.ne_zero_iff_zero_lt]
        unfold d
        rw [Module.End.genEigenspace_top_eq_maxUnifEigenspaceIndex]
        apply Module.End.pos_finrank_genEigenspace_of_hasEigenvalue
        . exact hk
        . by_contra!
          have eigen_one_le := Module.End.genEigenspace_le_genEigenspace_maxUnifEigenspaceIndex (Matrix.toEuclideanLin g.val.val) k 1
          simp at this
          simp [this] at eigen_one_le
          rw [Module.End.hasEigenvalue_iff] at hk
          rw [Module.End.eigenspace_def] at hk
          rw [← Module.End.genEigenspace_one] at hk
          contradiction
      hb := by
        rw [Nat.ne_zero_iff_zero_lt]
        by_contra!
        have sum_eq := Submodule.finrank_add_eq_of_isCompl a_b_compl
        simp at sum_eq
        rw [Nat.le_zero] at this
        rw [this] at sum_eq
        simp at sum_eq
        apply Submodule.finrank_lt at gen_eigenspace_top
        rw [sum_eq] at gen_eigenspace_top
        simp at gen_eigenspace_top
      A := _
      B := _
      iso := prod_iso
    }
end

theorem solution : type_of% @centralizer_iso_oai := @centralizer_iso_oai
