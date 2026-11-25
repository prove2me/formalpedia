-- Prove2me | solution 1 for P2M_Formalism_HermitianLatticeCounting_P_absNorm_le_abs_norm_of_mem__e157af83ff11
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:41:59.315798+00:00
-- url     : https://prove2.me/submissions/006bf9c4-9f38-4834-a315-e8b4b29d575f

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset Real MeasureTheory NumberField Formalism.HermitianLatticeCounting.ExpansionTerms
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (E : Type) [Field E] [NumberField E]
    (aa : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (haa : aa ≠ 0) (x : E) (hx : x ∈ aa) (hx0 : x ≠ 0) :
    FractionalIdeal.absNorm aa ≤ |Algebra.norm ℚ x| := by
  set J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E :=
    FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) x * aa⁻¹ with hJ
  have hle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) x ≤ aa :=
    (FractionalIdeal.spanSingleton_le_iff_mem).2 hx
  have hJ1 : J ≤ 1 := by
    calc J ≤ aa * aa⁻¹ := by
            rw [hJ]; exact mul_le_mul_left hle _
      _ = 1 := mul_inv_cancel₀ haa
  obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hJ1
  have hJ0 : J ≠ 0 := by
    rw [hJ]
    exact mul_ne_zero (by simpa [FractionalIdeal.spanSingleton_eq_zero_iff] using hx0) (inv_ne_zero haa)
  have hI0 : I ≠ ⊥ := by
    rintro rfl
    apply hJ0; rw [← hI]; simp
  have hN : (1 : ℚ) ≤ FractionalIdeal.absNorm J := by
    rw [← hI, FractionalIdeal.coeIdeal_absNorm]
    have : Ideal.absNorm I ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hI0
    exact_mod_cast Nat.one_le_iff_ne_zero.2 this
  have hprod : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) x = J * aa := by
    rw [hJ, mul_assoc, inv_mul_cancel₀ haa, mul_one]
  rw [← FractionalIdeal.absNorm_span_singleton (R := 𝓞 E), hprod, map_mul]
  exact le_mul_of_one_le_left (FractionalIdeal.absNorm_nonneg _) hN
end Formalism.HermitianLatticeCounting.P
