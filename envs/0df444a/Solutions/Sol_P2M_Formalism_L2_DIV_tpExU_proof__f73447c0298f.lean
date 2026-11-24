-- Prove2me | solution 1 for P2M_Formalism_L2_DIV_tpExU_proof__f73447c0298f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:55:26.656976+00:00
-- url     : https://prove2.me/submissions/3505472e-c0e7-4f3e-a82a-9ac3b0a1998d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
import Theorems.Thm_Formalism_L2_DIV_b_mul_mem_map
import Theorems.Thm_Formalism_L2_DIV_b_eps_mem
import Theorems.Thm_Formalism_L2_DIV_b_one_sub_eps_mem
import Theorems.Thm_Formalism_L2_DIV_b_mkU
import Theorems.Thm_Formalism_L2_DIV_b_mkU_supp
import Theorems.Thm_Formalism_L2_DIV_b_exists_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain TensorProduct Formalism.UG Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.UG.P
open scoped nonZeroDivisors
open Formalism Formalism.L2 Formalism.L2.DIV
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace Formalism.L2.DIV
theorem _root_.solution (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 F))
    (hPv : P.asIdeal.under (𝓞 F) = v.asIdeal) (a : (𝓞 E ⧸ P.asIdeal)ˣ) :
    ∃ (u : (RInt F E)ˣ) (b : 𝓞 E), Ideal.Quotient.mk P.asIdeal b = a ∧
      Units.map (RInt F E).subtype.toMonoidHom u ∈ suppAt E v ∧
      (u : RInt F E) - toRInt F E b ∈ P.asIdeal.map (toRInt F E) ∧
      ∀ P' : HeightOneSpectrum (𝓞 E), P' ≠ P → (u : RInt F E) - 1 ∈ P'.asIdeal.map (toRInt F E) := by
  classical
  obtain ⟨b0, hb0⟩ := Ideal.Quotient.mk_surjective (a : 𝓞 E ⧸ P.asIdeal)
  have hb0P : b0 ∉ P.asIdeal := by
    intro h
    rw [← Ideal.Quotient.eq_zero_iff_mem, hb0] at h
    have : Nontrivial (𝓞 E ⧸ P.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr P.isPrime.ne_top
    exact a.ne_zero h
  have hmap0 : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))]
    exact v.ne_bot
  have hfin := Ideal.finite_factors hmap0
  have hmemT : ∀ P' : HeightOneSpectrum (𝓞 E), P'.asIdeal.under (𝓞 F) = v.asIdeal → P' ∈ hfin.toFinset := by
    intro P' hP'
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, ← hP']
  obtain ⟨b', hb'⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := hfin.toFinset)
    (fun Q : HeightOneSpectrum (𝓞 E) => Q.asIdeal) (fun _ => 1) (fun Q _ => Q.prime)
    (fun Q _ Q' _ h h' => h (HeightOneSpectrum.ext h'))
    (fun Q => if (Q : HeightOneSpectrum (𝓞 E)) = P then b0 else 1)
  have hbP : b' - b0 ∈ P.asIdeal := by
    have := hb' P (hmemT P hPv)
    rwa [if_pos rfl, pow_one] at this
  have hbP' : ∀ P' : HeightOneSpectrum (𝓞 E), P' ≠ P → P'.asIdeal.under (𝓞 F) = v.asIdeal →
      b' - 1 ∈ P'.asIdeal := by
    intro P' hne hP'
    have := hb' P' (hmemT P' hP')
    rwa [if_neg hne, pow_one] at this
  have hnot : ∀ Q : HeightOneSpectrum (𝓞 E), Q.asIdeal.under (𝓞 F) = v.asIdeal → b' ∉ Q.asIdeal := by
    intro Q hQ hmem
    by_cases h : Q = P
    · subst h
      apply hb0P
      have := Q.asIdeal.sub_mem hmem hbP
      rwa [sub_sub_cancel] at this
    · apply Q.isPrime.ne_top
      rw [Ideal.eq_top_iff_one]
      have := Q.asIdeal.sub_mem hmem (hbP' Q h hQ)
      rwa [sub_sub_cancel] at this
  obtain ⟨c, r, hr, hbc⟩ := b_exists_mul v b' hnot
  obtain ⟨u, hu⟩ := b_mkU v b' c r hr hbc
  refine ⟨u, b0, hb0, b_mkU_supp v b' u hu, ?_, ?_⟩
  · have : (u : RInt F E) - toRInt F E b0 =
        toRInt F E (b' - b0) * bEps E v + (1 - toRInt F E b0) * (1 - bEps E v) := by
      rw [hu, map_sub]; ring
    rw [this]
    exact Ideal.add_mem _ (b_mul_mem_map _ _ hbP _) (Ideal.mul_mem_left _ _ (b_one_sub_eps_mem v P hPv))
  · intro P' hne
    have : (u : RInt F E) - 1 = toRInt F E (b' - 1) * bEps E v := by
      rw [hu, map_sub, map_one]; ring
    rw [this]
    by_cases hP' : P'.asIdeal.under (𝓞 F) = v.asIdeal
    · exact b_mul_mem_map _ _ (hbP' P' hne hP') _
    · exact Ideal.mul_mem_left _ _ (b_eps_mem v P' hP')
end Formalism.L2.DIV
