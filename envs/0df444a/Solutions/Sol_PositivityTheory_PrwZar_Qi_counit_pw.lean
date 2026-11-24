-- Prove2me | solution 1 for PositivityTheory.PrwZar.Qi.counit_pw
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:04:13.440538+00:00
-- url     : https://prove2.me/submissions/00f44ed6-61b0-4829-b9b5-34c47e9bdac6

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AbelianHeightsDuality_ZarhinTrick_QiCoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_AbelianHeightsDuality_ZarhinTrick_CompLmulMapId

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct
open PositivityTheory PositivityTheory.PrwZar PositivityTheory.PrwZar.Qi
variable {K H : Type} [Field K] [CommRing H] [Algebra K H]
namespace PositivityTheory.PrwZar.Qi
theorem _root_.solution (Δ : H →ₐ[K] H ⊗[K] H) (ε : H →ₐ[K] K) (hL : CounitL Δ ε) (hR : CounitR Δ ε) (n : ℕ) :
    ε.comp (pw Δ ε n) = ε := by
  induction n with
  | zero => ext x; simp [pw]
  | succ n ih =>
    ext x
    have key : ∀ t : H ⊗[K] H,
        ε (Algebra.TensorProduct.lmul' K (Algebra.TensorProduct.map (pw Δ ε n) (AlgHom.id K H) t)) =
          ε (Algebra.TensorProduct.lmul' K
            (Algebra.TensorProduct.map ((Algebra.ofId K H).comp ε) (AlgHom.id K H) t)) := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
        simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul, map_mul,
          AlgHom.comp_apply, Algebra.ofId_apply, AlgHom.commutes, AlgHom.id_apply]
        rw [← AlgHom.comp_apply ε (pw Δ ε n), ih]
        simp
      | add s t hs ht => simp only [map_add, hs, ht]
    have hx := DFunLike.congr_fun hL x
    simp only [CounitL, AlgHom.comp_apply, AlgHom.id_apply] at hx
    show ε (Algebra.TensorProduct.lmul' K (Algebra.TensorProduct.map (pw Δ ε n) (AlgHom.id K H) (Δ x))) = ε x
    rw [key, hx]
end PositivityTheory.PrwZar.Qi
