-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.bounded_matrix_entries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:31:00.048968+00:00
-- url     : https://prove2.me/submissions/2a655673-f96b-4654-88ba-3b3ac2679bf1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_JacobianTransformationLaw
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_TestFunctionPeriodicity
import Theorems.Thm_P2M_PI_TwistedEisensteinNonvanishing_W_mem_stdAt__54b003285def

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IsDedekindDomain Module
noncomputable section
namespace PI.TwistedEisensteinNonvanishing.W
open Loc LocE
section PhiFacts
variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}
end PhiFacts
private theorem one_not_mem_asIdeal {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} : (1 : 𝓞 E) ∉ P.asIdeal :=
  fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)
private theorem intAt_natCast_twisted_eisenstein_coset {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} (m : ℕ) : IntAt P (m : E) :=
  ⟨m, 1, one_not_mem_asIdeal, by simp⟩
end PI.TwistedEisensteinNonvanishing.W
end
end

set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open Loc LocE
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution : BddEntP := by
  intro E _ _ _ P R j h hb
  have hmem : ∀ x : Sp E (R.N j + cOf R j),
      x ∈ LocE.lamY P (qOf P) (R.N j) (cOf R j) 0 ↔ ∀ l, IntAt P (x l) := by
    intro x
    simp [LocE.lamY, LocE.sclLat, mem_stdAt', LocE.scE]
  have he : ∀ s, eN E (R.N j + cOf R j) s ∈ LocE.lamY P (qOf P) (R.N j) (cOf R j) 0 := by
    intro s
    rw [hmem]
    intro l
    simp only [eN]
    split_ifs
    · simpa using intAt_natCast_twisted_eisenstein_coset (P := P) 1
    · simpa using intAt_natCast_twisted_eisenstein_coset (P := P) 0
  refine ⟨fun s l => ?_, fun s l => ?_⟩
  · have h1 := (hmem _).mp (hb _ (he s)).2 l
    first
      | exact h1
      | simpa using h1
  · have h1 := (hmem _).mp (hb _ (he s)).1 l
    first
      | exact h1
      | simpa using h1
end PI.TwistedEisensteinNonvanishing.W
