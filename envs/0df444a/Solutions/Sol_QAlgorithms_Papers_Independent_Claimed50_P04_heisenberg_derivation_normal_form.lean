-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P04.heisenberg_derivation_normal_form
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T10:21:50.890188+00:00
-- url     : https://prove2.me/submissions/3a741f3a-216d-41b5-8a04-cc2c056db92a

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

theorem g58c_fst_zero (b : V →ₗ[ℝ] V →ₗ[ℝ] Z)
    (hnd : ∀ v, (∀ w, b v w = 0) → v = 0)
    (D : Module.End ℝ (V × Z)) (hd : HeisenbergDerivation b D) (z : Z) :
    (D (0, z)).1 = 0 := by
  apply hnd
  intro w
  have h := congrArg Prod.snd (hd (0, z) (w, 0))
  simp [heisenbergBracket, Prod.mk_zero_zero] at h
  exact h.symm

theorem g58c_split (D : Module.End ℝ (V × Z)) (v : V) (z : Z) :
    D (v, z) = D (v, 0) + D (0, z) := by
  rw [← map_add]; simp

theorem g58c_compat (b : V →ₗ[ℝ] V →ₗ[ℝ] Z)
    (D : Module.End ℝ (V × Z)) (hd : HeisenbergDerivation b D) (v w : V) :
    (D (0, b v w)).2 = b (D (v, 0)).1 w + b v (D (w, 0)).1 := by
  have h := congrArg Prod.snd (hd (v, 0) (w, 0))
  simpa [heisenbergBracket] using h

theorem g58c_rep (omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hnd : ∀ v, (∀ w, omega v w = 0) → v = 0)
    (g : V →ₗ[ℝ] ℝ) : ∃ w, ∀ v, omega w v = g v := by
  have hinj : Function.Injective omega := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv; exact hnd v (fun w => by simp [hv])
  have hsurj : Function.Surjective omega :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq).symm).1 hinj
  obtain ⟨w, hw⟩ := hsurj g
  exact ⟨w, fun v => by rw [hw]⟩

/-- Example 3.5, PDF p. 17. The center scaling c has vector scaling c/2,
unlike the conformal-Jacobi parameter c,2c. The remaining central block is omega(w,-). -/
theorem solution
    (omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hs : Symplectic omega)
    (D : Module.End ℝ (V × ℝ)) (hd : HeisenbergDerivation omega D) :
    ∃ c : ℝ, ∃ A : Module.End ℝ V, ∃ w : V,
      PreservesForm omega A ∧
      (∀ v z, D (v, z) = ((c / 2) • v + A v, c * z + omega w v)) ∧
      HeisenbergDerivation omega (diagonalBlocks ((c / 2) • LinearMap.id) (c • LinearMap.id)) ∧
      (∀ z, D (0, z) = (0, c * z)) := by
  have h0 := g58c_fst_zero omega hs.2 D hd
  have hc := g58c_compat omega D hd
  set c := (D (0, 1)).2 with hcdef
  have hz : ∀ z : ℝ, D (0, z) = (0, c * z) := by
    intro z
    have : ((0 : V), z) = z • ((0 : V), (1 : ℝ)) := by ext <;> simp
    rw [this, map_smul]
    ext
    · simp [h0 1]
    · simp [hcdef, mul_comm]
  obtain ⟨w, hw⟩ := g58c_rep omega hs.2 ((LinearMap.snd ℝ V ℝ).comp (D.comp (LinearMap.inl ℝ V ℝ)))
  refine ⟨c, (LinearMap.fst ℝ V ℝ).comp (D.comp (LinearMap.inl ℝ V ℝ)) - (c / 2) • LinearMap.id,
    w, ?_, ?_, ?_, hz⟩
  · intro v w'
    have := hc v w'
    rw [hz] at this
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.coe_fst,
      LinearMap.inl_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub, map_smul,
      LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    simp only at this
    linarith
  · intro v z
    rw [g58c_split D v z, hz]
    ext
    · simp
    · have := hw v
      simp at this ⊢
      linarith
  · intro p q
    ext
    · simp [diagonalBlocks, heisenbergBracket]
    · simp [diagonalBlocks, heisenbergBracket]
      ring

end Heisenberg

end

