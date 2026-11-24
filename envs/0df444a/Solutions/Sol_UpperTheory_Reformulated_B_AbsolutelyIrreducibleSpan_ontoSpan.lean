-- Prove2me | solution 1 for UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.ontoSpan
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:21:50.624229+00:00
-- url     : https://prove2.me/submissions/9554069a-2303-44a3-98d4-b2f1d72619c6

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_AbsolutelyIrreducibleSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
private theorem UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.adjoin_top {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n]
    {G : Type} (ρ : G → Matrix n n k) (h : UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.AbsIrr ρ) :
    Algebra.adjoin k (Set.range ρ) = ⊤ := by
  classical
  obtain ⟨h1, h2⟩ := h
  set A : Subalgebra k (Module.End k (n → k)) :=
    (Algebra.adjoin k (Set.range ρ)).map (Matrix.toLinAlgEquiv' (R := k) (n := n)).toAlgHom with hA
  have hmem : ∀ g, Matrix.toLin' (ρ g) ∈ A := fun g =>
    ⟨ρ g, Algebra.subset_adjoin ⟨g, rfl⟩, rfl⟩
  have hsm : ∀ (a : A) (v : n → k), a • v = (a : Module.End k (n → k)) v := fun _ _ => rfl
  have hk : ∀ (c : k) (v : n → k), (algebraMap k A c) • v = c • v := fun c v => by
    rw [hsm]; simp
  haveI : IsSemisimpleModule A (n → k) := by
    rw [isSemisimpleModule_iff]
    constructor
    intro W
    let W' : Submodule k (n → k) :=
      { carrier := W
        add_mem' := fun ha hb => W.add_mem ha hb
        zero_mem' := W.zero_mem
        smul_mem' := fun c v hv => by
          rw [← hk]; exact W.smul_mem _ hv }
    have hW := h1 W' (fun g v hv => by
      have := W.smul_mem (⟨_, hmem g⟩ : A) hv
      rw [hsm] at this
      exact this)
    rcases hW with hW | hW
    · have : W = ⊥ := by
        ext v
        have : v ∈ W' ↔ v ∈ (⊥ : Submodule k (n → k)) := by rw [hW]
        exact this
      exact ⟨⊤, this ▸ isCompl_bot_top⟩
    · have : W = ⊤ := by
        ext v
        have : v ∈ W' ↔ v ∈ (⊤ : Submodule k (n → k)) := by rw [hW]
        exact this
      exact ⟨⊥, this ▸ isCompl_top_bot⟩
  have hsc : ∀ φ : Module.End A (n → k), ∃ c : k, ∀ v, φ v = c • v := by
    intro φ
    let ψ : Module.End k (n → k) :=
      { toFun := φ
        map_add' := φ.map_add
        map_smul' := fun c v => by
          rw [← hk, φ.map_smul, hk]; rfl }
    obtain ⟨c, hc⟩ := h2 (LinearMap.toMatrix' ψ) (fun g => by
      apply Matrix.toLin'.injective
      rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
      refine LinearMap.ext fun v => ?_
      exact φ.map_smul (⟨_, hmem g⟩ : A) v)
    refine ⟨c, fun v => ?_⟩
    have h3 : ψ = Matrix.toLin' (c • (1 : Matrix n n k)) := by
      rw [← hc, Matrix.toLin'_toMatrix']
    have h4 : φ v = ψ v := rfl
    rw [h4, h3]
    simp
  rw [eq_top_iff]
  intro M _
  let f : Module.End (Module.End A (n → k)) (n → k) :=
    { toFun := Matrix.toLin' M
      map_add' := (Matrix.toLin' M).map_add
      map_smul' := fun φ v => by
        obtain ⟨c, hc⟩ := hsc φ
        change Matrix.toLin' M (φ v) = φ (Matrix.toLin' M v)
        rw [hc, hc, map_smul] }
  obtain ⟨r, hr⟩ := jacobson_density f
    (Finset.univ.image fun i : n => (Pi.single i 1 : n → k))
  obtain ⟨r, N, hN, rfl⟩ := r
  have : M = N := by
    apply Matrix.toLin'.injective
    apply (Pi.basisFun k n).ext
    intro i
    rw [Pi.basisFun_apply]
    exact hr _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  exact this ▸ hN
end

set_option autoImplicit false

namespace UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan
theorem _root_.solution :
    UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.StatOntoSpan := by
  intro O _ _ n _ _ G _ ρ h
  have h1 := UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.adjoin_top _ h
  let π : Matrix n n O →+* Matrix n n (IsLocalRing.ResidueField O) :=
    (IsLocalRing.residue O).mapMatrix
  have h2 : Submodule.span (IsLocalRing.ResidueField O)
      (Set.range fun g => π (ρ g)) = ⊤ := by
    rw [← Algebra.adjoin_eq_span_of_subset]
    · exact (congrArg Subalgebra.toSubmodule h1).trans rfl
    · intro x hx
      apply Submodule.subset_span
      have : x ∈ MonoidHom.mrange (π.toMonoidHom.comp ρ) :=
        (Submonoid.closure_le (S := MonoidHom.mrange (π.toMonoidHom.comp ρ))).mpr
          (by rintro _ ⟨g, rfl⟩; exact ⟨g, rfl⟩) hx
      exact this
  have h3 : ∀ X : Matrix n n (IsLocalRing.ResidueField O),
      ∃ Y ∈ Submodule.span O (Set.range (ρ : G → Matrix n n O)), π Y = X := by
    intro X
    have hX : X ∈ Submodule.span (IsLocalRing.ResidueField O)
      (Set.range fun g => π (ρ g)) := h2 ▸ Submodule.mem_top
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact ⟨ρ g, Submodule.subset_span ⟨g, rfl⟩, rfl⟩
    | zero => exact ⟨0, Submodule.zero_mem _, map_zero _⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      exact ⟨a + b, Submodule.add_mem _ ha hb, map_add _ _ _⟩
    | smul c x _ hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨d, rfl⟩ := IsLocalRing.residue_surjective c
      refine ⟨d • a, Submodule.smul_mem _ _ ha, ?_⟩
      ext i j
      simp [π]
  rw [eq_top_iff]
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal O)
    Module.Finite.fg_top (IsLocalRing.maximalIdeal_le_jacobson _) ?_
  intro M _
  obtain ⟨Y, hY, hYM⟩ := h3 (π M)
  have h4 : M - Y ∈ IsLocalRing.maximalIdeal O • (⊤ : Submodule O (Matrix n n O)) := by
    rw [Matrix.matrix_eq_sum_single (M - Y)]
    refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
    have h5 : (M - Y) i j ∈ IsLocalRing.maximalIdeal O := by
      rw [← IsLocalRing.residue_eq_zero_iff]
      have h6 : π (M - Y) = 0 := by rw [map_sub, hYM, sub_self]
      exact congrFun (congrFun h6 i) j
    have h7 : Matrix.single i j ((M - Y) i j) = (M - Y) i j • Matrix.single i j (1 : O) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [h7]
    exact Submodule.smul_mem_smul h5 Submodule.mem_top
  have h8 : M = Y + (M - Y) := by abel
  rw [h8]
  exact Submodule.add_mem_sup hY h4
end UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan
