-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P04.generalized_symplectic_centralizer
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T10:22:02.29341+00:00
-- url     : https://prove2.me/submissions/08deb546-4ca6-4beb-9c7b-9719f3ba3f51

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P04
open QAlgorithms.Papers.Independent.Claimed50.P04
noncomputable section

open Set

attribute [local instance 100] LieRing.ofAssociativeRing

open QAlgorithms.Papers.Independent.Frontier30.P26
  (Invariant LieAdmissible ClosedCone CompactlyEmbedded CompactCartan Hermitian bracketSpan
    TubeType)

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P04.lieNormedGroup

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P04.lieNormedSpace

section Heisenberg

variable {V Z : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  [AddCommGroup Z] [Module ℝ Z] [FiniteDimensional ℝ Z]

theorem g58c_antisymm {E W : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup W] [Module ℝ W]
    (b : E →ₗ[ℝ] E →ₗ[ℝ] W) (halt : ∀ v, b v v = 0) (v w : E) : b v w = - b w v := by
  have := halt (v + w)
  simp [halt v, halt w] at this
  exact eq_neg_of_add_eq_zero_left this

/-- Remark 2.21, PDF p. 11: unique scalar-form operators, their symmetry, full
commutation, and equality of generalized sp with the simultaneous centralizer. -/
theorem solution
    (b : V →ₗ[ℝ] V →ₗ[ℝ] Z) (halt : ∀ v, b v v = 0)
    (f : Z →ₗ[ℝ] ℝ) (hs : Symplectic (scalarize b f)) :
    ∃ psi : (Z →ₗ[ℝ] ℝ) → Module.End ℝ V,
      (∀ g : Z →ₗ[ℝ] ℝ, ∀ T : Module.End ℝ V,
        (∀ v w, g (b v w) = scalarize b f (T v) w) ↔ T = psi g) ∧
      (∀ g, AdjointPair (scalarize b f) (psi g) (psi g)) ∧
      (∀ g, ∀ X : Module.End ℝ V, PreservesForm b X →
        (psi g).comp X = X.comp (psi g)) ∧
      (∀ S : Set (Z →ₗ[ℝ] ℝ), Submodule.span ℝ S = ⊤ →
        ∀ X : Module.End ℝ V, PreservesForm b X ↔
          PreservesForm (scalarize b f) X ∧
            ∀ g ∈ S, X.comp (psi g) = (psi g).comp X) := by
  set ω := scalarize b f with hωdef
  have hω : ∀ u w, ω u w = f (b u w) := fun _ _ => rfl
  have hinj : Function.Injective ω := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv; exact hs.2 v (fun w => by simp [hv])
  have hsurj : Function.Surjective ω :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq).symm).1 hinj
  let e : V ≃ₗ[ℝ] Module.Dual ℝ V := LinearEquiv.ofBijective ω ⟨hinj, hsurj⟩
  let psi : (Z →ₗ[ℝ] ℝ) → Module.End ℝ V := fun g => e.symm.toLinearMap ∘ₗ (b.compr₂ g)
  have hpsi : ∀ g v w, ω (psi g v) w = g (b v w) := by
    intro g v w
    have : ω (psi g v) = b.compr₂ g v := by
      change e (e.symm (b.compr₂ g v)) = _
      simp
    rw [this]; rfl
  have hext : ∀ u u' : V, (∀ w, ω u w = ω u' w) → u = u' := by
    intro u u' h; apply hinj; ext w; exact h w
  have hωa : ∀ u w, ω u w = - ω w u := g58c_antisymm ω hs.1
  have hba : ∀ u w, b u w = - b w u := g58c_antisymm b halt
  have hcomm : ∀ g, ∀ X : Module.End ℝ V, PreservesForm b X →
      (psi g).comp X = X.comp (psi g) := by
    intro g X hX
    ext v
    apply hext
    intro w
    simp only [LinearMap.comp_apply]
    rw [hpsi, hω, eq_neg_of_add_eq_zero_left (hX v w), eq_neg_of_add_eq_zero_left (hX (psi g v) w),
      map_neg, map_neg, ← hω, hpsi]
  refine ⟨psi, ?_, ?_, hcomm, ?_⟩
  · intro g T
    constructor
    · intro h
      ext v
      apply hext
      intro w
      rw [hpsi, h]
    · rintro rfl v w
      rw [hpsi]
  · intro g v w
    rw [hpsi, hωa, hpsi, hba, map_neg]
  · intro S hS X
    constructor
    · intro hX
      refine ⟨fun v w => ?_, fun g _ => (hcomm g X hX).symm⟩
      rw [hω, hω, ← map_add, hX v w, map_zero]
    · rintro ⟨hXω, hXc⟩ v w
      rw [← Module.forall_dual_apply_eq_zero_iff ℝ]
      intro g
      have hle : Submodule.span ℝ S ≤ LinearMap.ker (Module.Dual.eval ℝ Z (b (X v) w + b v (X w))) := by
        rw [Submodule.span_le]
        intro g hg
        simp only [SetLike.mem_coe, LinearMap.mem_ker, Module.Dual.eval_apply]
        rw [map_add, ← hpsi, ← hpsi]
        have := congrArg (fun T => T v) (hXc g hg)
        simp only [LinearMap.comp_apply] at this
        rw [← this]
        exact hXω (psi g v) w
      have : g ∈ LinearMap.ker (Module.Dual.eval ℝ Z (b (X v) w + b v (X w))) := by
        apply hle; rw [hS]; trivial
      simpa using this

end Heisenberg

end

