-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.gaussRed_eval
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:22:07.608801+00:00
-- url     : https://prove2.me/submissions/7df561a5-3db5-477b-9cd5-d1caf102ee3a

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_ComapInclusionIsLocalHom
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussValExists

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MvPolynomial
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {Ω U : Type} [Field Ω] [Field U] [Algebra Ω U] {σ : Type}
    (t : σ → U) (V : ValuationSubring U) (ht : ∀ s, t s ∈ V) (p : MvPolynomial σ Ω)
    (hc : ∀ α, p.coeff α ∈ V.comap (algebraMap Ω U)) :
    letI := residueAlgebra V (algebraMap Ω U)
    ∃ h : aeval t p ∈ V, IsLocalRing.residue V ⟨aeval t p, h⟩ =
      aeval (fun s => IsLocalRing.residue V ⟨t s, ht s⟩) (gaussRed V p hc) := by
  try dsimp only
  letI := residueAlgebra V (algebraMap Ω U)
  classical
  obtain ⟨y, hydef⟩ : ∃ y : V, y = ∑ α ∈ p.support,
      comapInclusion V (algebraMap Ω U) ⟨p.coeff α, hc α⟩ *
        ∏ s ∈ α.support, (⟨t s, ht s⟩ : V) ^ α s := ⟨_, rfl⟩
  have hy : (y : U) = aeval t p := by
    change V.subtype y = _
    rw [hydef, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
    simp only [map_sum, map_mul, map_prod, map_pow]
    rfl
  have hmem : aeval t p ∈ V := by
    rw [← hy]
    exact y.2
  refine ⟨hmem, ?_⟩
  have hyy : (⟨aeval t p, hmem⟩ : V) = y := Subtype.ext hy.symm
  rw [hyy, hydef, map_sum]
  unfold gaussRed
  rw [map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [MvPolynomial.aeval_monomial]
  simp only [map_mul, map_prod, map_pow]
  congr 1
end ReciprocityTheory.MultiplicativeHeights
