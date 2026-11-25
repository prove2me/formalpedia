-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.BetaLUniq.EigA.exists_common
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:37:55.14634+00:00
-- url     : https://prove2.me/submissions/d2f9ef1e-3d76-469d-9924-8a5ced5a068b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BetaUniqueness_EqZeroOfNormLtOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.BetaLUniq PI.UnitaryGroupMassFormula.BetaLUniq.EigA
variable {E : Type} [Field E] [NumberField E]
namespace PI.UnitaryGroupMassFormula.BetaLUniq.EigA
theorem _root_.solution (P : Ideal (𝓞 E)) [P.IsPrime] (I : Submodule (𝓞 E) E) (hfg : I.FG) (x : E)
    (hx : ∀ c ∈ I, ∃ s : 𝓞 E, s ∉ P ∧ algebraMap (𝓞 E) E s * x * c ∈ I) :
    ∃ s : 𝓞 E, s ∉ P ∧ ∀ c ∈ I, algebraMap (𝓞 E) E s * x * c ∈ I := by
  classical
  obtain ⟨S, hS⟩ := hfg
  have hS' : ∀ c ∈ S, ∃ s : 𝓞 E, s ∉ P ∧ algebraMap (𝓞 E) E s * x * c ∈ I :=
    fun c hc => hx c (hS ▸ Submodule.subset_span hc)
  choose! f hfP hfI using hS'
  refine ⟨∏ c ∈ S, f c, ?_, ?_⟩
  · intro hmem
    obtain ⟨c, hc, hcP⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact hfP c hc hcP
  · intro c hc
    rw [← hS] at hc
    induction hc using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem f hc
      have : algebraMap (𝓞 E) E (f c * r) * x * c = r • (algebraMap (𝓞 E) E (f c) * x * c) := by
        rw [Algebra.smul_def, map_mul]; ring
      rw [hr, this]
      exact I.smul_mem r (hfI c hc)
    | zero => simpa using I.zero_mem
    | add a b _ _ ha hb => rw [mul_add]; exact I.add_mem ha hb
    | smul a c _ hc =>
      have : algebraMap (𝓞 E) E (∏ c ∈ S, f c) * x * (a • c) =
          a • (algebraMap (𝓞 E) E (∏ c ∈ S, f c) * x * c) := by
        rw [Algebra.smul_def, Algebra.smul_def]; ring
      rw [this]
      exact I.smul_mem a hc
end PI.UnitaryGroupMassFormula.BetaLUniq.EigA
