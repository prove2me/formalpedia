-- Prove2me | solution 1 for PI.SplitIntLoc.Proof.prime_fst_ne_prime_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:44:11.534862+00:00
-- url     : https://prove2.me/submissions/7d71266c-8bf7-4c8f-b136-72ca899c14ad

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SplitIntLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitPrimeIntegers_EmbMemOfIsIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitPrimeIntegers_ExistsUnitDiff
import Theorems.Thm_PI_SplitIntLoc_Proof_exists_sep
import Theorems.Thm_PI_SplitIntLoc_Proof_emb_mem_of_mul
import Theorems.Thm_PI_SplitIntLoc_Proof_prime_ne_bot


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped TensorProduct
noncomputable section
open PI PI.SplitIntLoc PI.SplitIntLoc.Proof
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)} (spl : E ⊗[F] (v.adicCompletion F) ≃+* (v.adicCompletion F) × (v.adicCompletion F))
namespace PI.SplitIntLoc.Proof
theorem _root_.solution (hspl : ∀ a : (v.adicCompletion F), spl ((1 : E) ⊗ₜ[F] a) = (a, a)) :
    P spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F)) ≠ P spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) := by
  intro hPP
  obtain ⟨y, hy1, hy2⟩ := exists_sep spl hspl
  have hQ0 : P spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F)) ≠ ⊥ := prime_ne_bot spl hspl _ (fun _ => rfl)
  have : IsDiscreteValuationRing (Dloc (P spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F)))) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 E) hQ0 _
  have hloc : ∀ p : (v.adicCompletion F) × (v.adicCompletion F) →+* (v.adicCompletion F), P spl p = P spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F)) → ∀ z : E,
      IsLocalization.IsInteger (Dloc (P spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F)))) z → emb spl p z ∈ (v.adicCompletionIntegers F) := by
    rintro p hp z ⟨d, hd⟩
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (P spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F))).primeCompl d
    have hs : (s : 𝓞 E) ∉ P spl p := by rw [hp]; exact s.2
    have hspec := congrArg (algebraMap (Dloc (P spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F)))) E)
      (IsLocalization.mk'_spec (Dloc (P spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F)))) a s)
    rw [map_mul, hd, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at hspec
    exact emb_mem_of_mul spl p a s hs z hspec
  rcases ValuationRing.isInteger_or_isInteger (Dloc (P spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F)))) y with h | h
  · have h' : Valued.v (emb spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F)) y) ≤ 1 := hloc _ rfl y h
    exact absurd h' (not_le.2 hy1)
  · have h' : Valued.v (emb spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) y⁻¹) ≤ 1 := hloc _ hPP.symm y⁻¹ h
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [map_zero, Valuation.map_zero] at hy1
      exact absurd hy1 (not_lt.2 zero_le)
    have hu0 : emb spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) y ≠ 0 :=
      (map_ne_zero_iff _ (emb spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F))).injective).2 hy0
    rw [map_inv₀] at h'
    have h3 : Valued.v (emb spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) y) * Valued.v (emb spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) y)⁻¹ < 1 :=
      calc Valued.v (emb spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) y) * Valued.v (emb spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) y)⁻¹ ≤ Valued.v (emb spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) y) * 1 := by gcongr
        _ = Valued.v (emb spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) y) := mul_one _
        _ < 1 := hy2
    rw [← map_mul, mul_inv_cancel₀ hu0, map_one] at h3
    exact lt_irrefl _ h3
end PI.SplitIntLoc.Proof
