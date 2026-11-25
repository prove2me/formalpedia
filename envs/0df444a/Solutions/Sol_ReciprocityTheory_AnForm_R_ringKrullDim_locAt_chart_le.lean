-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.ringKrullDim_locAt_chart_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:09:26.146232+00:00
-- url     : https://prove2.me/submissions/7d3915e7-fffb-448f-98f0-8a2e8d53f6aa

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHyp
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_MemConePtsIffChartIdeal
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChartA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChartB
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChart
import Theorems.Thm_ReciprocityTheory_AnForm_R_chartIdeal_le_ptIdealOf
import Theorems.Thm_ReciprocityTheory_AnForm_R_ringKrullDim_le_of_forall_quotient
import Theorems.Thm_ReciprocityTheory_AnForm_R_ringKrullDim_locAt
import Theorems.Thm_ReciprocityTheory_AnForm_R_ringKrullDim_quotient_le_of_chartIdeal_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial IsLocalRing
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)}
    (hP : IsMultiHomogIdeal P) (e : ℕ)
    (hdim : ∀ Q ∈ P.minimalPrimes,
      ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ Q) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞))
    (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ) (hz : ∀ h ∈ chartIdeal P p, eval z h = 0) :
    ringKrullDim (locAt (chartIdeal P p) z) ≤ e := by
  have hle := chartIdeal_le_ptIdealOf hz
  rw [ringKrullDim_locAt _ z hle]
  have : ((ptIdealOf z).map (Ideal.Quotient.mk (chartIdeal P p))).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hle)
  refine (Ideal.height_le_ringKrullDim_of_isPrime).trans ?_
  refine ringKrullDim_le_of_forall_quotient _ fun 𝔓 h𝔓 => ?_
  have : (𝔓.comap (Ideal.Quotient.mk (chartIdeal P p))).IsPrime := Ideal.comap_isPrime _ _
  have hI : chartIdeal P p ≤ 𝔓.comap (Ideal.Quotient.mk (chartIdeal P p)) := fun x hx => by
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact 𝔓.zero_mem
  refine le_trans ?_ (ringKrullDim_quotient_le_of_chartIdeal_le hP e hdim p _ hI)
  let g : MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔓.comap (Ideal.Quotient.mk (chartIdeal P p)) →+*
      (MvPolynomial (Σ k, ι k) ℂ ⧸ chartIdeal P p) ⧸ 𝔓 :=
    Ideal.Quotient.lift _ ((Ideal.Quotient.mk 𝔓).comp (Ideal.Quotient.mk _))
      (fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr ha)
  refine ringKrullDim_le_of_surjective g ?_
  intro x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact ⟨Ideal.Quotient.mk _ a, rfl⟩
end ReciprocityTheory.AnForm.R
