-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.sum_r
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:44:18.271798+00:00
-- url     : https://prove2.me/submissions/3feba685-686c-4fd5-ae63-2e288a180a10

import Definitions.Def_ReciprocityTheory_DualLattices_EigenLengthFrobeniusStatement
import Definitions.Def_ReciprocityTheory_DualLattices_FrobEqOfLe
import Definitions.Def_ReciprocityTheory_DualLattices_StdJForm
import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLowerBoundOf
import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLengthOfLengthEigenLengthProduct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution (hS : HodgeTateSetting p v R O σ cp) (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) : ∑ i, U.r i = g := by
  haveI : Nontrivial R := (algebraMap R C).domain_nontrivial
  have hproj : ∀ i j (w : Fin g → R), w ∈ LinearMap.range (Matrix.mulVecLin (U.εL j)) →
      Matrix.mulVecLin (U.εL i) w = if i = j then w else 0 := by
    rintro i j w ⟨z, rfl⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, U.εL_orth]
    split_ifs with h
    · subst h; rfl
    · exact Matrix.zero_mulVec z
  let F : (Fin g → R) →ₗ[R] ((i : Fin U.m) → LinearMap.range (Matrix.mulVecLin (U.εL i))) :=
    LinearMap.pi fun i => (Matrix.mulVecLin (U.εL i)).rangeRestrict
  let G : ((i : Fin U.m) → LinearMap.range (Matrix.mulVecLin (U.εL i))) →ₗ[R] (Fin g → R) :=
    ∑ i, (LinearMap.range (Matrix.mulVecLin (U.εL i))).subtype ∘ₗ LinearMap.proj i
  have hG : ∀ y, G y = ∑ i, ((y i : LinearMap.range (Matrix.mulVecLin (U.εL i))) : Fin g → R) := by
    intro y
    simp only [G, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.coe_proj,
      Function.eval, Submodule.coe_subtype]
  have hFG : F ∘ₗ G = LinearMap.id := by
    refine LinearMap.ext fun y => funext fun i => Subtype.ext ?_
    change Matrix.mulVecLin (U.εL i) (G y) = (y i : Fin g → R)
    rw [hG, map_sum, Finset.sum_eq_single i]
    · rw [hproj i i _ (y i).2, if_pos rfl]
    · intro b _ hb
      rw [hproj i b _ (y b).2, if_neg (Ne.symm hb)]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hGF : G ∘ₗ F = LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    change G (F x) = x
    rw [hG]
    change ∑ i, Matrix.mulVecLin (U.εL i) x = x
    rw [← LinearMap.sum_apply, ← map_sum, U.εL_sum]
    exact Matrix.one_mulVec x
  let e : (Fin g → R) ≃ₗ[R] ((i : Fin U.m) → LinearMap.range (Matrix.mulVecLin (U.εL i))) :=
    LinearEquiv.ofLinear F G hFG hGF
  haveI : ∀ i, Module.Free R (LinearMap.range (Matrix.mulVecLin (U.εL i))) :=
    fun i => Module.Free.of_equiv (U.rank i).some.symm
  haveI : ∀ i, Module.Finite R (LinearMap.range (Matrix.mulVecLin (U.εL i))) :=
    fun i => Module.Finite.equiv (U.rank i).some.symm
  have h1 := e.finrank_eq
  rw [Module.finrank_fin_fun, Module.finrank_pi_fintype] at h1
  refine (Finset.sum_congr rfl fun i _ => ?_).trans h1.symm
  rw [(U.rank i).some.finrank_eq, Module.finrank_fin_fun]
end ReciprocityTheory.PGsh.Up
