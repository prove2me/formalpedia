-- Prove2me | solution 1 for WeierstrassEllipticZeta.finite_generalized_eigenspace_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-10T16:27:19.926637+00:00
-- url     : https://prove2.me/submissions/0328390d-1ca4-4ea6-b165-748a8c4c864f

import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Algebra.DirectSum.Module

open scoped Classical



theorem solution
    (K M : Type*) [Field K] [IsAlgClosed K]
    [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    (f : Module.End K M) (s : Finset K)
    (hzero : ∀ z : K, z ∉ s →
      Module.finrank K (f.maxGenEigenspace z) = 0) :
    DirectSum.IsInternal (fun z : s => f.maxGenEigenspace z.val) ∧
    ∃ e : (∀ z : s, f.maxGenEigenspace z.val) ≃ₗ[K] M,
      ∀ x, e x = ∑ z : s, (x z : M) := by
  classical
  have hind : iSupIndep (fun z : s => f.maxGenEigenspace z.val) :=
    f.independent_maxGenEigenspace.comp Subtype.val_injective
  have hspan : (⨆ z : s, f.maxGenEigenspace z.val) = ⊤ := by
    apply top_unique
    rw [← f.iSup_maxGenEigenspace_eq_top]
    refine iSup_le fun z => ?_
    by_cases hz : z ∈ s
    · exact le_iSup (fun z : s => f.maxGenEigenspace z.val) ⟨z, hz⟩
    · rw [Submodule.finrank_eq_zero.mp (hzero z hz)]
      exact bot_le
  refine ⟨DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind hspan, ?_⟩
  let σ : (∀ z : s, f.maxGenEigenspace z.val) →ₗ[K] M :=
    { toFun := fun x => ∑ z : s, (x z : M)
      map_add' := by intros; simp [Finset.sum_add_distrib]
      map_smul' := by intros; simp [Finset.smul_sum] }
  have hinj : Function.Injective σ := by
    intro x y hxy
    funext z
    apply Subtype.ext
    exact (iSupIndep_iff_finsetSum_eq_imp_eq _).mp hind Finset.univ
      (fun z => (x z : M)) (fun z => (y z : M))
      (fun z _ => ⟨(x z).property, (y z).property⟩) hxy z (Finset.mem_univ z)
  have hsurj : Function.Surjective σ := by
    intro x
    have hx : x ∈ ⨆ z : s, f.maxGenEigenspace z.val := by
      rw [hspan]
      trivial
    obtain ⟨v, hv⟩ := (Submodule.mem_iSup_finset_iff_exists_sum
      (s := Finset.univ) (fun z : s => f.maxGenEigenspace z.val) x).mp
        (by simpa using hx)
    exact ⟨v, by simpa [σ] using hv⟩
  exact ⟨LinearEquiv.ofBijective σ ⟨hinj, hsurj⟩, fun _ => rfl⟩

