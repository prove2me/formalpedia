-- Prove2me | solution 1 for ReciprocityTheory.Cheb.uphi_Hfun_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:36:26.67301+00:00
-- url     : https://prove2.me/submissions/1e387fd1-6d0f-4751-8c82-34650b918102

import Definitions.Def_ReciprocityTheory_Chebotarev_NormGsEmbZLe
import Definitions.Def_ReciprocityTheory_Chebotarev_RpowNegFinrankSubOne
import Definitions.Def_ReciprocityTheory_Chebotarev_IdealLat
import Definitions.Def_ReciprocityTheory_Chebotarev_MeanZero
import Definitions.Def_ReciprocityTheory_Chebotarev_LatSum
import Definitions.Def_ReciprocityTheory_Chebotarev_KHoldA
import Theorems.Thm_ReciprocityTheory_Cheb_norm_embZ
import Theorems.Thm_ReciprocityTheory_Cheb_preZ_embZ
import Theorems.Thm_ReciprocityTheory_Cheb_rsgn_mul_norm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units Set
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.Cheb
theorem _root_.solution {l : ℕ} (χ : DirichletCharacter ℂ l) (b c : NZIdeal E) (s : ℝ) (α : b.1) :
    ((uphi (embZ (α : 𝓞 E)) : ℝ) : ℂ) * Hfun χ b c s (Ideal.span {(α : 𝓞 E)}) =
      ((Ideal.absNorm b.1 : ℕ) : ℂ) ^ (s : ℂ) *
        (cfun χ b.1 c.1 (embZ (α : 𝓞 E)) * Gs χ s (embZ (α : 𝓞 E))) := by
  obtain ⟨q, hq⟩ := absNorm_dvd_algebraNorm α.2
  have hbc : (b.1 * c.1 ∣ Ideal.span {(α : 𝓞 E)}) ↔ (α : 𝓞 E) ∈ b.1 * c.1 := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  have hb : Ideal.absNorm b.1 ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact b.2
  have hsg := rsgn_mul_norm (α : 𝓞 E)
  have hchi : χ ((((Ideal.absNorm (Ideal.span {(α : 𝓞 E)})) / Ideal.absNorm b.1 : ℕ)) : ZMod l) =
      χ ((Algebra.norm ℤ (α : 𝓞 E) / (Ideal.absNorm b.1 : ℤ) : ℤ) : ZMod l) * χ (rsgn (embZ (α : 𝓞 E)) : ZMod l) := by
    rw [← map_mul, ← Int.cast_mul, ← Int.cast_natCast, Ideal.absNorm_span_singleton, Int.natCast_div,
      Int.natCast_natAbs, ← hsg, Int.mul_ediv_assoc _ (absNorm_dvd_algebraNorm α.2), mul_comm]
  have hn : ((mixedEmbedding.norm (embZ (α : 𝓞 E)) : ℝ) : ℂ) =
      ((Ideal.absNorm (Ideal.span {(α : 𝓞 E)}) : ℕ) : ℂ) := by
    rw [norm_embZ, Ideal.absNorm_span_singleton, Nat.cast_natAbs]
    rw [← Int.cast_abs, Complex.ofReal_intCast]
  simp only [Hfun, cfun, Gs, preZ_embZ, hbc, hchi, hn]
  ring
end ReciprocityTheory.Cheb
