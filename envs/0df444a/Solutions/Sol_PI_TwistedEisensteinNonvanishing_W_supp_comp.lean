-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.supp_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:43:42.544607+00:00
-- url     : https://prove2.me/submissions/264e8f82-5428-44b7-b729-cec553d8a240

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IsUnitRedP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_JacobianTransformationLaw
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_fIdx_lt
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_fIdx_notD
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_fIdx_D
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_jq_DA
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_atN_of_lt
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_ent_comp
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_gm_int
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_ia_mul
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_ia_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open Loc LocE
variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}
variable (P)
variable {P}
variable {q k₀ r c' n' c n kj : ℕ} (hqq : q = qOf P) (h1 : r = kj + c) (h2 : k₀ ≤ kj) (h3 : kj ≤ n)
  (h4 : r ≤ n' + c') (h5 : k₀ ≤ n')
include hqq h1 h2 h3 h4 h5
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution {g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hg : g ∈ JQ P q kj n c) {y : HomE E (n' + c') (n + c)}
    (hy : CondQ P q k₀ r c' n' c n y) : CondQ P q k₀ r c' n' c n (g.toLinearMap ∘ₗ y) := by
  obtain ⟨hyA, hyB⟩ := hy
  refine ⟨fun p p' hp hp' => ?_, fun p p' hrp hp hp' => ?_⟩
  · rw [ent_comp hqq h1 h2 h3 h4 h5 g y p p' hp]
    exact ia_sum (P := P) _ _ (fun p'' hp'' => ia_mul (P := P)
      (gm_int hqq h1 h2 h3 h4 h5 hg p p'' hp) (hyA p'' p' (Finset.mem_range.mp hp'') hp'))
  · rw [ent_comp hqq h1 h2 h3 h4 h5 g y p p' hp, Finset.sum_div]
    refine ia_sum (P := P) _ _ (fun p'' hp'' => ?_)
    have hp''' := Finset.mem_range.mp hp''
    by_cases hr : r ≤ p''
    · rw [mul_div_assoc]
      exact ia_mul (P := P) (gm_int hqq h1 h2 h3 h4 h5 hg p p'' hp) (hyB p'' p' hr hp''' hp')
    · push_neg at hr
      rw [mul_div_right_comm]
      refine ia_mul (P := P) ?_ (hyA p'' p' hp''' (by omega))
      rw [atN_of_lt _ (fIdx_lt (le_trans h2 h3) hp)]
      have hD := fIdx_D (k₀ := k₀) (c := c) (n := n) (kj := kj) h2 (by omega) hp
      have hnD := fIdx_notD (k₀ := k₀) (c := c) (n := n) (kj := kj) (p := p'') h2 (by omega)
      exact jq_DA hg _ hnD ⟨_, fIdx_lt (le_trans h2 h3) hp⟩ hD
end PI.TwistedEisensteinNonvanishing.W
