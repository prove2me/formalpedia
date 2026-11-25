-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.idem_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:20:53.52782+00:00
-- url     : https://prove2.me/submissions/d3835541-fd2e-49ef-bf40-9882e7007347

import Definitions.Def_ReciprocityTheory_DualLattices_EigenQuotientSmithStatement
import Definitions.Def_ReciprocityTheory_DualLattices_PowMemCarrier
import Definitions.Def_ReciprocityTheory_DualLattices_SumValCoord
import Definitions.Def_ReciprocityTheory_DualLattices_VDetEqOneOfIntegral
import Definitions.Def_ReciprocityTheory_DualLattices_WdetDegreeOfSmithRestrict
import Theorems.Thm_ReciprocityTheory_PGsh_IsIntegralMat_mulVec


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
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution {S : Type} [CommRing S] [IsLocalRing S] {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι S) (hP : P * P = P) : ∃ (r : ℕ) (Bw : Matrix ι (Fin r) S),
      LinearMap.range (Matrix.mulVecLin Bw) = LinearMap.range (Matrix.mulVecLin P) ∧
      LinearMap.ker (Matrix.mulVecLin Bw) = ⊥ := by
  classical
  let f : (ι → S) →ₗ[S] (ι → S) := Matrix.mulVecLin P
  have hidem : ∀ x, f (f x) = f x := fun x => by
    simp only [f, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hP]
  let M := LinearMap.range f
  have hsplit : f.rangeRestrict ∘ₗ M.subtype = LinearMap.id := by
    apply LinearMap.ext
    rintro ⟨y, x, rfl⟩
    apply Subtype.ext
    simp [hidem]
  haveI : Module.Projective S M := Module.Projective.of_split M.subtype f.rangeRestrict hsplit
  haveI : Module.Free S M := Module.free_of_flat_of_isLocalRing
  let b := Module.finBasis S M
  have hBw : Matrix.mulVecLin (Matrix.of fun i j => (b j : ι → S) i) =
      M.subtype ∘ₗ b.equivFun.symm.toLinearMap := by
    apply LinearMap.ext
    intro c
    funext i
    simp [Matrix.mulVec, dotProduct, Module.Basis.equivFun_symm_apply, Finset.sum_apply, mul_comm]
  refine ⟨Module.finrank S M, Matrix.of fun i j => (b j : ι → S) i, ?_, ?_⟩
  · rw [hBw, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _), Submodule.range_subtype]
  · rw [hBw, LinearMap.ker_eq_bot]
    exact M.injective_subtype.comp b.equivFun.symm.injective
end ReciprocityTheory.PGsh.Up
