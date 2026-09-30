-- Prove2me | solution 1 for SP4Mission.punctured_closed_manifold_homology
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-12T22:20:58.113768+00:00
-- url     : https://prove2.me/submissions/c4c0aae7-79e9-4aa0-a3fd-9ca3db608cb9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_SP4Sphere
import Definitions.Def_SP4WeakHomotopy
import Definitions.Def_SP4Homology
import Definitions.Def_SP4HomologyMap
import Definitions.Def_SP4RelHomology
import Theorems.Thm_SP4Mission_pair_homology_exact
import Theorems.Thm_SP4Mission_local_homology_zero
import Theorems.Thm_SP4Mission_closed_manifold_top_homology_isIso

set_option autoImplicit false

open scoped Manifold ContDiff
open SP4Mission CategoryTheory Limits SP4Homology

/-!
# Homology of a punctured closed simply connected manifold (proof sketch)

Let `M` be a closed simply connected `n`-manifold, `p ∈ M`, `V := M ∖ {p}` with inclusion `ι`.
The long exact sequence of the pair `(M, V)` (`SP4Mission.pair_homology_exact`)

`H_{k+1}(M, V) → H_k(V) → H_k(M) → H_k(M, V) → H_{k-1}(V)`

together with the two inputs

* `SP4Mission.local_homology_zero`: `H_k(M, V) = 0` for `k ≠ n` (excision),
* `SP4Mission.closed_manifold_top_homology_isIso`: `H_n(M) → H_n(M, V)` is an isomorphism
  (fundamental class of the closed orientable manifold `M`),

gives by a diagram chase: `ι_* : H_k(V) → H_k(M)` is injective for every `k` (the connecting map
into `H_k(V)` is zero, either because its source `H_{k+1}(M, V)` vanishes or because it is
preceded by the surjection `H_n(M) → H_n(M, V)`), surjective for `k ≠ n` (its target `H_k(M, V)`
of `j_*` vanishes), and zero for `k = n` (`j_*` is injective); hence `ι_*` is an isomorphism for
`k ≠ n` and `H_n(V) = 0`.
-/

namespace PuncturedHomology

theorem ker_eq_top_of_subsingleton {A B : ModuleCat.{0} ℤ} [Subsingleton B] (f : A ⟶ B) :
    LinearMap.ker f.hom = ⊤ := by
  ext x
  simp only [LinearMap.mem_ker, Submodule.mem_top, iff_true]
  exact Subsingleton.elim _ _

theorem range_eq_bot_of_subsingleton {A B : ModuleCat.{0} ℤ} [Subsingleton A] (f : A ⟶ B) :
    LinearMap.range f.hom = ⊥ := by
  rw [LinearMap.range_eq_bot]
  ext x
  rw [Subsingleton.elim x 0, map_zero]
  rfl

variable {V M : Type} [TopologicalSpace V] [TopologicalSpace M]

/-- **Diagram chase** in the long exact sequence of the pair `(M, V)`. -/
theorem chase (ι : C(V, M)) (hι : Function.Injective ι) (n : ℕ)
    (hloc : ∀ k, k ≠ n → IsZero (Hrel k ι)) (htop : IsIso (toRel n ι)) :
    (∀ k, k ≠ n → IsIso (map k ι)) ∧ IsZero (H n V) := by
  have E2 : ∀ k, LinearMap.range (map k ι).hom = LinearMap.ker (toRel k ι).hom :=
    fun k => (pair_homology_exact ι hι k).1.moduleCat_range_eq_ker
  have E3 : ∀ k, LinearMap.range (toRel (k + 1) ι).hom = LinearMap.ker (relδ k ι hι).hom :=
    fun k => (pair_homology_exact ι hι k).2.1.moduleCat_range_eq_ker
  have E1 : ∀ k, LinearMap.range (relδ k ι hι).hom = LinearMap.ker (map k ι).hom :=
    fun k => (pair_homology_exact ι hι k).2.2.moduleCat_range_eq_ker
  have htop_bij : Function.Bijective (toRel n ι).hom := by
    have h1 : Mono (toRel n ι) := inferInstance
    have h2 : Epi (toRel n ι) := inferInstance
    exact ⟨(ModuleCat.mono_iff_injective _).mp h1, (ModuleCat.epi_iff_surjective _).mp h2⟩
  -- `ι_* : H_k(V) → H_k(M)` is injective for every `k`.
  have hinj : ∀ k, Function.Injective (map k ι).hom := by
    intro k
    rw [← LinearMap.ker_eq_bot, ← E1 k]
    by_cases hk : k + 1 = n
    · -- `∂ = 0` because `j_* : H_n(M) → H_n(M, V)` is surjective
      have hsurj : LinearMap.range (toRel (k + 1) ι).hom = ⊤ := by
        rw [LinearMap.range_eq_top]
        subst hk
        exact htop_bij.2
      have hker : LinearMap.ker (relδ k ι hι).hom = ⊤ := by rw [← E3 k, hsurj]
      rw [LinearMap.range_eq_bot]
      ext x
      have hx : x ∈ LinearMap.ker (relδ k ι hι).hom := by rw [hker]; trivial
      exact hx
    · -- `∂ = 0` because its source `H_{k+1}(M, V)` vanishes
      have : Subsingleton (Hrel (k + 1) ι) := ModuleCat.subsingleton_of_isZero (hloc (k + 1) hk)
      exact range_eq_bot_of_subsingleton _
  refine ⟨fun k hk => ?_, ?_⟩
  · -- surjectivity from `H_k(M, V) = 0`
    have : Subsingleton (Hrel k ι) := ModuleCat.subsingleton_of_isZero (hloc k hk)
    have hsurj : Function.Surjective (map k ι).hom := by
      rw [← LinearMap.range_eq_top, E2 k]
      exact ker_eq_top_of_subsingleton _
    have : Mono (map k ι) := (ModuleCat.mono_iff_injective _).mpr (hinj k)
    have : Epi (map k ι) := (ModuleCat.epi_iff_surjective _).mpr hsurj
    exact isIso_of_mono_of_epi _
  · -- `H_n(V) = 0`: `ι_*` is injective and zero
    have hzero : LinearMap.range (map n ι).hom = ⊥ := by
      rw [E2 n, LinearMap.ker_eq_bot]
      exact htop_bij.1
    have : Subsingleton (H n V) := by
      refine ⟨fun x y => hinj n ?_⟩
      have hx : (map n ι).hom x ∈ LinearMap.range (map n ι).hom := LinearMap.mem_range_self _ x
      have hy : (map n ι).hom y ∈ LinearMap.range (map n ι).hom := LinearMap.mem_range_self _ y
      rw [hzero, Submodule.mem_bot] at hx hy
      rw [hx, hy]
    exact ModuleCat.isZero_of_subsingleton _

end PuncturedHomology

/-- The target theorem. -/
theorem solution
    (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M] [SimplyConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (p : M) :
    (∀ k : ℕ, k ≠ n →
        IsIso (SP4Homology.map k (⟨Subtype.val, continuous_subtype_val⟩ : C({x : M // x ≠ p}, M)))) ∧
      IsZero (SP4Homology.H n {x : M // x ≠ p}) :=
  PuncturedHomology.chase (⟨Subtype.val, continuous_subtype_val⟩ : C({x : M // x ≠ p}, M))
    Subtype.val_injective n (fun k hk => local_homology_zero n M p k hk)
    (closed_manifold_top_homology_isIso n M p)
