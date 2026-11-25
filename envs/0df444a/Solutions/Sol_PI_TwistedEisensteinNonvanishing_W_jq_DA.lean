-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.jq_DA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:30:54.24423+00:00
-- url     : https://prove2.me/submissions/d221a4a7-8361-4e41-8744-3ae0019fc8b3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IsUnitRedP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_JacobianTransformationLaw
import Theorems.Thm_P2M_PI_TwistedEisensteinNonvanishing_W_mem_parL__cb7b47041a47
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_ia_one
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_ia_zero


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
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution {q kj n c : ℕ} {g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hg : g ∈ JQ P q kj n c) (j : ℕ)
    (hj : ¬(kj ≤ j ∧ j < n)) (l : Fin (n + c)) (hl : kj ≤ l.1 ∧ l.1 < n) :
    IntAt P (g (eN E (n + c) j) l / (q : E)) := by
  have h2 : ∀ x, g x ∈ parL P q kj n c ↔ x ∈ parL P q kj n c := (Subgroup.mem_inf.mp hg).2
  have hej : eN E (n + c) j ∈ parL P q kj n c := by
    rw [mem_parL']
    intro l'
    unfold eN
    by_cases hl' : l'.1 = j
    · rw [if_neg (by rw [hl']; exact hj), if_pos hl']
      simpa using ia_one (P := P)
    · rw [if_neg hl', mul_zero]
      exact ia_zero (P := P)
  have h3 := (mem_parL' _).mp ((h2 _).mpr hej) l
  rw [if_pos hl, zpow_one] at h3
  rwa [div_eq_inv_mul]
end PI.TwistedEisensteinNonvanishing.W
