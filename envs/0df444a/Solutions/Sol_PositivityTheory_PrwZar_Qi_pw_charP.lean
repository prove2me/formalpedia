-- Prove2me | solution 1 for PositivityTheory.PrwZar.Qi.pw_charP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:46:22.32637+00:00
-- url     : https://prove2.me/submissions/6284975d-3ae5-4ee9-bb00-0c215ca167f2

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AbelianHeightsDuality_ZarhinTrick_QiCoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_AbelianHeightsDuality_ZarhinTrick_CompLmulMapId
import Definitions.Def_Development_WeilBound_CoreStatements_AbelianHeightsDuality_ZarhinTrick_QiCharP
import Theorems.Thm_PositivityTheory_PrwZar_Qi_counit_pw
import Theorems.Thm_PositivityTheory_PrwZar_Qi_pw_sub_mem


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
theorem _root_.solution (p : ℕ) [Fact p.Prime] [CharP K p] (Δ : H →ₐ[K] H ⊗[K] H) (ε : H →ₐ[K] K)
    (hL : CounitL Δ ε) (hR : CounitR Δ ε) (hmul : ∀ a b : ℕ, pw Δ ε (a * b) = (pw Δ ε a).comp (pw Δ ε b))
    (r : ℕ) {x : H} (hx : x ∈ RingHom.ker ε) : pw Δ ε (p ^ r) x ∈ RingHom.ker ε ^ (2 ^ r) := by
  induction r generalizing x with
  | zero =>
    rw [pow_zero, pow_zero, pow_one, RingHom.mem_ker]
    have h := AlgHom.congr_fun (counit_pw Δ ε hL hR 1) x
    rw [AlgHom.comp_apply] at h
    rw [h]
    exact RingHom.mem_ker.1 hx
  | succ r ih =>
    have hp : (p : H) = 0 := by
      rw [← map_natCast (algebraMap K H), CharP.cast_eq_zero K p, map_zero]
    have h2 : pw Δ ε p x ∈ RingHom.ker ε ^ 2 := by
      have := pw_sub_mem Δ ε hL hR p hx
      rwa [hp, zero_mul, sub_zero] at this
    have hcomp : pw Δ ε (p ^ (r + 1)) = (pw Δ ε (p ^ r)).comp (pw Δ ε p) := by
      rw [pow_succ]
      exact hmul _ _
    rw [hcomp, AlgHom.comp_apply]
    have hmap : Ideal.map (pw Δ ε (p ^ r)) (RingHom.ker ε) ≤ RingHom.ker ε ^ (2 ^ r) :=
      Ideal.map_le_iff_le_comap.2 fun z hz => ih hz
    have hy : pw Δ ε (p ^ r) (pw Δ ε p x) ∈ Ideal.map (pw Δ ε (p ^ r)) (RingHom.ker ε ^ 2) :=
      Ideal.mem_map_of_mem _ h2
    rw [Ideal.map_pow] at hy
    have h3 := Ideal.pow_right_mono hmap 2 hy
    rwa [← pow_mul, ← pow_succ] at h3
end PositivityTheory.PrwZar.Qi
