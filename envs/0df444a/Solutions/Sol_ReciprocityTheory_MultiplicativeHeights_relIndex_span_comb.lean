-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.relIndex_span_comb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:14:44.448775+00:00
-- url     : https://prove2.me/submissions/6d80a217-07a7-45cb-8a88-264a2f69e683

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegBA
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegBB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (b : Fin k → Fin r → K) (hb : LinearIndependent K b) (M : Matrix (Fin k) (Fin k) (𝓞 K))
    (hM : M.det ≠ 0) :
    (((Submodule.span (𝓞 K) (Set.range (fun j => ∑ i, M i j • b i))).toAddSubgroup.relIndex
      (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup : ℕ) : ℤ) = |Algebra.norm ℤ M.det| := by
  set P := Submodule.span (𝓞 K) (Set.range b) with hPdef
  set Q := Submodule.span (𝓞 K) (Set.range (fun j => ∑ i, M i j • b i)) with hQdef
  have hbO : LinearIndependent (𝓞 K) b := hb.restrict_scalars' (𝓞 K)
  let bP : Module.Basis (Fin k) (𝓞 K) P := Module.Basis.span hbO
  let f : P →ₗ[𝓞 K] P := Matrix.toLin bP bP M
  have hfb : ∀ j, ((f (bP j) : P) : Fin r → K) = ∑ i, M i j • b i := by
    intro j
    simp only [f, Matrix.toLin_self, bP, Submodule.coe_sum, Submodule.coe_smul]
    exact Finset.sum_congr rfl fun i _ => by rw [Module.Basis.span_apply]
  have hQ : Submodule.map P.subtype (LinearMap.range f) = Q := by
    rw [LinearMap.range_eq_map, ← bP.span_eq, Submodule.map_span, Submodule.map_span,
      ← Set.range_comp, ← Set.range_comp, hQdef]
    congr 2
    funext j
    exact hfb j
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 := LinearMap.toMatrix_mulVec_repr bP bP f x
    rw [hx, map_zero, LinearMap.toMatrix_toLin] at h1
    have h2 : ⇑(bP.repr x) = 0 := Matrix.eq_zero_of_mulVec_eq_zero hM (by simpa using h1)
    have h3 : bP.repr x = 0 := DFunLike.coe_injective h2
    simpa using h3
  have hR : Q.toAddSubgroup.addSubgroupOf P.toAddSubgroup = (LinearMap.range f).toAddSubgroup := by
    ext x
    rw [AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup, ← hQ,
      Submodule.mem_toAddSubgroup, Submodule.mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      rwa [this] at hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have : Module.Free (𝓞 K) P := Module.Free.of_basis bP
  have : Module.Finite (𝓞 K) P := Module.Finite.of_basis bP
  have : Module.Free ℤ P := Module.Free.of_basis ((RingOfIntegers.basis K).smulTower bP)
  have : Module.Finite ℤ P := Module.Finite.of_basis ((RingOfIntegers.basis K).smulTower bP)
  set N : Submodule ℤ P := (LinearMap.range f).toAddSubgroup.toIntSubmodule with hN
  let e : P ≃+ N := (LinearEquiv.ofInjective f hf).toAddEquiv
  have hdet : N.subtype ∘ₗ (e : P →+ N).toIntLinearMap = f.restrictScalars ℤ := by
    ext x
    rfl
  have key := Submodule.natAbs_det_equiv N e
  rw [hdet, LinearMap.det_restrictScalars, LinearMap.det_toLin] at key
  rw [AddSubgroup.relIndex, hR]
  change ((Nat.card (P ⧸ N) : ℕ) : ℤ) = _
  rw [← key, Int.natCast_natAbs]
end ReciprocityTheory.MultiplicativeHeights
