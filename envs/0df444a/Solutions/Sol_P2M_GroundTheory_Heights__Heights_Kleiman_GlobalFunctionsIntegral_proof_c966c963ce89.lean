-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_GlobalFunctionsIntegral_proof_c966c963ce89
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:02:44.188804+00:00
-- url     : https://prove2.me/submissions/9b757965-f314-4a5d-9845-4c29aa0287ea

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GlobalFunctionsIntegralSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PGlobalFunctionsIntegral
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_eq_X_pow_of_mem_monos_single_54014fef5774


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace GlobalFunctionsIntegral
theorem _root_.solution : GlobalFunctionsIntegral.Statement := by
  intro k _ K _ _ N y a hy ha
  classical

  have key : ∀ i : Fin (N + 1), ∃ (e : ℕ) (f : MvPolynomial (Fin (N + 1)) k),
      f.IsHomogeneous e ∧ a * y i ^ e = aeval y f := by
    intro i
    by_cases hi : y i = 0
    · exact ⟨1, 0, isHomogeneous_zero _ _ _, by simp [hi]⟩
    · obtain ⟨f, s, e, hs, hf, hse, hrep⟩ := ha i hi
      obtain ⟨n, rfl⟩ := exists_eq_X_pow_of_mem_monos_single hs
      have hne : (X i ^ n : MvPolynomial (Fin (N + 1)) k) ≠ 0 := pow_ne_zero _ (X_ne_zero i)
      have hn : n = e := (isHomogeneous_X_pow i n).inj_right hse hne
      subst hn
      refine ⟨n, f, hf, ?_⟩
      have hyn : y i ^ n ≠ 0 := pow_ne_zero _ hi
      rw [hrep, map_pow, aeval_X, div_mul_cancel₀ _ hyn]
  choose e f hf hrel using key
  set E := ∑ i, e i with hE
  let M : Submodule k K :=
    (homogeneousSubmodule (Fin (N + 1)) k E).map (aeval y : MvPolynomial (Fin (N + 1)) k →ₐ[k] K).toLinearMap
  refine isIntegral_of_smul_mem_submodule M ?_ ((homogeneousSubmodule_fg (Fin (N + 1)) k E).map _) a ?_
  ·
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
    refine (Submodule.ne_bot_iff M).mpr ⟨y i ^ E, ⟨X i ^ E, ?_, by simp⟩, pow_ne_zero _ hi⟩
    exact (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X_pow i E)
  ·
    rintro _ ⟨g, hg, rfl⟩
    have hgE : g.IsHomogeneous E := (mem_homogeneousSubmodule _ _).mp hg
    rw [smul_eq_mul, AlgHom.toLinearMap_apply, g.as_sum, map_sum, Finset.mul_sum]
    refine Submodule.sum_mem _ fun m hm => ?_
    have hmE : m.degree = E := by
      by_contra h
      exact mem_support_iff.mp hm (hgE.coeff_eq_zero h)
    have hsum : ∑ i, e i ≤ ∑ i, m i := by
      rw [← hE, ← hmE, Finsupp.degree_eq_sum]
    obtain ⟨i, -, hi⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
    set m' := m - Finsupp.single i (e i) with hm'
    have hsplit : m' + Finsupp.single i (e i) = m :=
      tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hi)
    have hdeg : m'.degree + e i = E := by
      rw [← hmE, ← hsplit, map_add, Finsupp.degree_single]
    refine ⟨monomial m' (coeff m g) * f i, ?_, ?_⟩
    · refine (mem_homogeneousSubmodule _ _).mpr ?_
      rw [← hdeg]
      exact (isHomogeneous_monomial _ rfl).mul (hf i)
    · have hmono : (monomial m (coeff m g) : MvPolynomial (Fin (N + 1)) k) =
          monomial m' (coeff m g) * X i ^ e i := by
        rw [X_pow_eq_monomial, monomial_mul, mul_one, hsplit]
      rw [AlgHom.toLinearMap_apply, map_mul, ← hrel i, hmono, map_mul, map_pow, aeval_X]
      ring
end GlobalFunctionsIntegral
end GroundTheory.Heights₂.Heights.Kleiman
