-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P40.lemma_4_7_17
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T13:50:30.686893+00:00
-- url     : https://prove2.me/submissions/ae7e3441-2b17-417d-8a44-45e76f013d5b

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P40

set_option autoImplicit false

universe u v w



namespace Prove2MeS08.P052

variable {R : Type u} [Ring R]
variable {M : Type v} {N : Type w}
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- An FG module embedded in a module with the desired submodule property is FP. -/
theorem fp_of_injective
    (hN : ∀ S : Submodule R N, S.FG → Module.FinitePresentation R S)
    [Module.Finite R M] (f : M →ₗ[R] N) (hf : Function.Injective f) :
    Module.FinitePresentation R M := by
  letI : Module.FinitePresentation R f.range := hN _ (Submodule.fg_range f)
  exact Module.FinitePresentation.of_equiv (LinearEquiv.ofInjective f hf).symm

/-- The property of FG submodules being FP is invariant under module equivalence. -/
theorem submodules_of_equiv (e : M ≃ₗ[R] N)
    (hM : ∀ S : Submodule R M, S.FG → Module.FinitePresentation R S) :
    ∀ S : Submodule R N, S.FG → Module.FinitePresentation R S := by
  intro S hS
  letI : Module.Finite R S := Module.Finite.of_fg hS
  exact fp_of_injective hM (e.symm.toLinearMap.comp S.subtype)
    (e.symm.injective.comp Subtype.val_injective)

/-- The property is preserved by products, using the kernel of first projection. -/
theorem submodules_prod
    (hM : ∀ S : Submodule R M, S.FG → Module.FinitePresentation R S)
    (hN : ∀ S : Submodule R N, S.FG → Module.FinitePresentation R S) :
    ∀ S : Submodule R (M × N), S.FG → Module.FinitePresentation R S := by
  intro S hS
  letI : Module.Finite R S := Module.Finite.of_fg hS
  let f : S →ₗ[R] M := (LinearMap.fst R M N).comp S.subtype
  letI : Module.FinitePresentation R f.range := hM _ (Submodule.fg_range f)
  let g := f.rangeRestrict
  have hg : Function.Surjective g := f.surjective_rangeRestrict
  letI : Module.Finite R (LinearMap.ker g) :=
    Module.Finite.of_fg (Module.FinitePresentation.fg_ker g hg)
  let k : LinearMap.ker g →ₗ[R] N :=
    (LinearMap.snd R M N).comp (S.subtype.comp (LinearMap.ker g).subtype)
  have hk : Function.Injective k := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · have hx : (x.val.val).1 = 0 := congrArg Subtype.val x.property
      have hy : (y.val.val).1 = 0 := congrArg Subtype.val y.property
      exact hx.trans hy.symm
    · exact hxy
  letI : Module.FinitePresentation R (LinearMap.ker g) :=
    fp_of_injective (M := LinearMap.ker g) hN k hk
  exact Module.finitePresentation_of_ker g hg

/-- The finite-free-rank gate, proved through finite product induction. -/
theorem finite_free (hR : ∀ I : Submodule R R, I.FG → Module.FinitePresentation R I)
    (n : ℕ) :
    ∀ S : Submodule R (Fin n → R), S.FG → Module.FinitePresentation R S := by
  refine Module.pi_induction'
    (motive := fun M _ _ ↦ ∀ S : Submodule R M, S.FG → Module.FinitePresentation R S)
    (motive' := fun M _ _ ↦ ∀ S : Submodule R M, S.FG → Module.FinitePresentation R S)
    R ?_ ?_ ?_ ?_ (fun _ : Fin n ↦ R) (fun _ ↦ hR)
  · exact fun e h ↦ submodules_of_equiv e h
  · exact fun e h ↦ submodules_of_equiv e h
  · intro S _
    infer_instance
  · exact fun h h' ↦ submodules_prod h h'

end Prove2MeS08.P052




namespace Prove2MeS08.P052

variable {R : Type u} [Ring R]
variable {M : Type v} {N : Type w}
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Lift a finitely generated submodule through a finite free presentation. -/
theorem finitely_presented_submodule
    (hR : ∀ I : Submodule R R, I.FG → Module.FinitePresentation R I)
    [Module.FinitePresentation R M] (S : Submodule R M) (hS : S.FG) :
    Module.FinitePresentation R S := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  have hfker : (LinearMap.ker f).FG := Module.FinitePresentation.fg_ker f hf
  let T := S.comap f
  have hle : LinearMap.ker f ≤ T := by
    intro x hx
    change f x ∈ S
    rw [show f x = 0 from hx]
    exact S.zero_mem
  have hT : T.FG := by
    apply Submodule.fg_of_fg_map_of_fg_inf_ker f
    · simpa only [T, Submodule.map_comap_eq_of_surjective hf] using hS
    · simpa only [inf_eq_right.mpr hle] using hfker
  letI : Module.FinitePresentation R T := finite_free hR n T hT
  let g : T →ₗ[R] S :=
    { toFun := fun x ↦ ⟨f x, x.property⟩
      map_add' := fun x y ↦ Subtype.ext (f.map_add x y)
      map_smul' := fun r x ↦ Subtype.ext (f.map_smul r x) }
  have hg : Function.Surjective g := by
    intro s
    obtain ⟨x, hx⟩ := hf s
    have hxT : x ∈ T := by
      change f x ∈ S
      rw [hx]
      exact s.property
    exact ⟨⟨x, hxT⟩, Subtype.ext hx⟩
  have hgker : (LinearMap.ker g).FG := by
    apply Submodule.fg_of_fg_map_injective T.subtype Subtype.val_injective
    have hmap : (LinearMap.ker g).map T.subtype = LinearMap.ker f := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact congrArg Subtype.val hy
      · intro hx
        refine ⟨⟨x, hle hx⟩, ?_, rfl⟩
        exact Subtype.ext hx
    rwa [hmap]
  exact Module.finitePresentation_of_surjective g hg hgker

/-- Kernels and cokernels between finitely presented modules remain finitely presented. -/
theorem kernels_cokernels
    (hR : ∀ I : Submodule R R, I.FG → Module.FinitePresentation R I)
    [Module.FinitePresentation R M] [Module.FinitePresentation R N]
    (f : M →ₗ[R] N) :
    Module.FinitePresentation R (LinearMap.ker f) ∧
      Module.FinitePresentation R (N ⧸ LinearMap.range f) := by
  letI : Module.FinitePresentation R f.range :=
    finitely_presented_submodule hR f.range (Submodule.fg_range f)
  have hk : (LinearMap.ker f).FG := by
    simpa only [LinearMap.ker_rangeRestrict] using
      Module.FinitePresentation.fg_ker f.rangeRestrict f.surjective_rangeRestrict
  refine ⟨finitely_presented_submodule hR _ hk, ?_⟩
  apply Module.finitePresentation_of_surjective f.range.mkQ f.range.mkQ_surjective
  simpa only [Submodule.ker_mkQ] using Submodule.fg_range f

end Prove2MeS08.P052

open QAlgorithms.Papers.Independent.Intakenext100.P40

/-- All three closure statements of the unchanged published root. -/
theorem solution (R : Type u) [Ring R] (hR : leftCoherent R) :
    (∀ (n : ℕ) (S : Submodule R (Fin n → R)),
      S.FG → Module.FinitePresentation R S) ∧
    (∀ (M : Type v) [AddCommGroup M] [Module R M],
      Module.FinitePresentation R M →
        ∀ S : Submodule R M, S.FG → Module.FinitePresentation R S) ∧
    (∀ (M : Type v) (N : Type w)
      [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N],
      Module.FinitePresentation R M → Module.FinitePresentation R N →
        ∀ f : M →ₗ[R] N,
          Module.FinitePresentation R (LinearMap.ker f) ∧
          Module.FinitePresentation R (N ⧸ LinearMap.range f)) := by
  refine ⟨Prove2MeS08.P052.finite_free hR, ?_, ?_⟩
  · intro M _ _ hM S hS
    letI := hM
    exact Prove2MeS08.P052.finitely_presented_submodule hR S hS
  · intro M N _ _ _ _ hM hN f
    letI := hM
    letI := hN
    exact Prove2MeS08.P052.kernels_cokernels hR f

#print axioms solution
