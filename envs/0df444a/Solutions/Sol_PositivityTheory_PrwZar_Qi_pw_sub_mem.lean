-- Prove2me | solution 1 for PositivityTheory.PrwZar.Qi.pw_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:37:45.253382+00:00
-- url     : https://prove2.me/submissions/70cc533b-0a07-4383-ab92-0e0e9b3d445d

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AbelianHeightsDuality_ZarhinTrick_QiCoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_AbelianHeightsDuality_ZarhinTrick_CompLmulMapId
import Theorems.Thm_PositivityTheory_PrwZar_Qi_comp_lmul_map_id
import Theorems.Thm_PositivityTheory_PrwZar_Qi_counit_pw

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
theorem _root_.solution (Δ : H →ₐ[K] H ⊗[K] H) (ε : H →ₐ[K] K) (hL : CounitL Δ ε) (hR : CounitR Δ ε) (n : ℕ)
    {x : H} (hx : x ∈ RingHom.ker ε) : pw Δ ε n x - (n : H) * x ∈ RingHom.ker ε ^ 2 := by
  have hx0 : ε x = 0 := hx
  set e : H →ₐ[K] H := (Algebra.ofId K H).comp ε with he
  have gen : ∀ f : H →ₐ[K] H, ε.comp f = ε → ∀ t : H ⊗[K] H,
      Algebra.TensorProduct.lmul' K (Algebra.TensorProduct.map f (AlgHom.id K H) t) -
        Algebra.TensorProduct.lmul' K (Algebra.TensorProduct.map e (AlgHom.id K H) t) -
        Algebra.TensorProduct.lmul' K (Algebra.TensorProduct.map f e t) +
        Algebra.TensorProduct.lmul' K (Algebra.TensorProduct.map e e t) ∈ RingHom.ker ε ^ 2 := by
    intro f hf t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul, AlgHom.id_apply, he,
        AlgHom.comp_apply, Algebra.ofId_apply]
      have e1 : f a * b - algebraMap K H (ε a) * b - f a * algebraMap K H (ε b) +
          algebraMap K H (ε a) * algebraMap K H (ε b) =
          (f a - algebraMap K H (ε a)) * (b - algebraMap K H (ε b)) := by ring
      rw [e1, pow_two]
      refine Ideal.mul_mem_mul ?_ ?_
      · rw [RingHom.mem_ker, map_sub, ← AlgHom.comp_apply, hf, AlgHom.commutes]; simp
      · rw [RingHom.mem_ker, map_sub, AlgHom.commutes]; simp
    | add s t hs ht =>
      simp only [map_add]
      convert Ideal.add_mem _ hs ht using 1
      ring
  induction n with
  | zero => simp [pw, hx0]
  | succ n ih =>
    have h1 := gen (pw Δ ε n) (counit_pw Δ ε hL hR n) (Δ x)
    have hLx := DFunLike.congr_fun hL x
    have hRx := DFunLike.congr_fun hR x
    simp only [CounitL, CounitR, AlgHom.comp_apply, AlgHom.id_apply] at hLx hRx
    rw [← comp_lmul_map_id ε (pw Δ ε n), ← comp_lmul_map_id ε e, hRx, hLx] at h1
    have hex : e x = 0 := by simp [he, hx0]
    rw [hex, add_zero] at h1
    have h2 := Ideal.add_mem _ h1 ih
    have hp : pw Δ ε (n + 1) x =
        Algebra.TensorProduct.lmul' K (Algebra.TensorProduct.map (pw Δ ε n) (AlgHom.id K H) (Δ x)) := rfl
    rw [hp]
    convert h2 using 1
    push_cast
    ring
end PositivityTheory.PrwZar.Qi
