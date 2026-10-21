-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P04.generalized_heisenberg_derivations
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T10:21:39.977454+00:00
-- url     : https://prove2.me/submissions/0101c6d0-ee99-4568-a19f-881a68683d85

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

/-- Proposition 3.7, PDF p. 18: all three clauses, including the diagonal derivation
and invariance of generalized sp under ad(DV). Nondegeneracy is beta's LEFT radical. -/
theorem solution (b : V →ₗ[ℝ] V →ₗ[ℝ] Z)
    (halt : ∀ v, b v v = 0) (hnd : ∀ v, (∀ w, b v w = 0) → v = 0)
    (D : Module.End ℝ (V × Z)) (hd : HeisenbergDerivation b D) :
    ∃ DV : Module.End ℝ V, ∃ DVZ : V →ₗ[ℝ] Z, ∃ DZ : Module.End ℝ Z,
      (∀ v z, D (v, z) = (DV v, DVZ v + DZ z)) ∧
      (∀ z, D (0, z) = (0, DZ z)) ∧ BetaCompatiblePair b DV DZ ∧
      HeisenbergDerivation b (diagonalBlocks DV DZ) ∧
      (∀ X : Module.End ℝ V, PreservesForm b X →
        PreservesForm b (DV.comp X - X.comp DV)) := by
  have h0 := g58c_fst_zero b hnd D hd
  have hc := g58c_compat b D hd
  refine ⟨(LinearMap.fst ℝ V Z).comp (D.comp (LinearMap.inl ℝ V Z)),
    (LinearMap.snd ℝ V Z).comp (D.comp (LinearMap.inl ℝ V Z)),
    (LinearMap.snd ℝ V Z).comp (D.comp (LinearMap.inr ℝ V Z)), ?_, ?_, ?_, ?_, ?_⟩
  · intro v z
    rw [g58c_split D v z]
    ext <;> simp [h0]
  · intro z
    ext <;> simp [h0]
  · intro v w
    simpa using hc v w
  · intro p q
    ext
    · simp [diagonalBlocks, heisenbergBracket, h0]
    · simpa [diagonalBlocks, heisenbergBracket] using hc p.1 q.1
  · intro X hX v w
    have e1 := hc (X v) w
    have e2 := hc v (X w)
    have e3 := hX (D (v, 0)).1 w
    have e4 := hX v (D (w, 0)).1
    have e5 := hX v w
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.coe_fst, LinearMap.coe_snd,
      LinearMap.inl_apply, LinearMap.inr_apply, map_sub, LinearMap.sub_apply]
    have : (D (0, b (X v) w + b v (X w))).2 = 0 := by rw [e5]; simp [Prod.mk_zero_zero]
    rw [show ((0 : V), b (X v) w + b v (X w)) = (0, b (X v) w) + (0, b v (X w)) by ext <;> simp,
      map_add] at this
    simp only [Prod.snd_add] at this
    rw [e1, e2] at this
    linear_combination (norm := module) this - e3 - e4

end Heisenberg

end

