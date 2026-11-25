-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.key_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:03:56.76712+00:00
-- url     : https://prove2.me/submissions/abc78883-d66f-41ce-a50c-ef9875575425

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_XPderivMono
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_FunctionalRepresentationByContraction
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_mem_cand
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_mapDomain_pE_pE
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_partner_support_first_family
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_centre
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_contr_mono
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_contr_smul
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_contr_sum
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_pE_apply
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_pE_pE
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_wt_pos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Sw.LC.CoreC.pE_apply
attribute [local simp] PositivityTheory.Rg.Sw.LC.CoreC.pE_pE



set_option autoImplicit false
noncomputable section
open MvPolynomial Finsupp
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw.LC.CoreC
open PositivityTheory.Rg.Sw G
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.CoreC
theorem _root_.solution (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) (Λ : PX m n →ₗ[ℂ] ℂ) (hΛ : ∀ a b p, Λ (Dop ε c a b p) = 0)
    {s u : Fin m × Fin n × Bool →₀ ℕ} (hs : ∀ k ∈ s.support, inF1 ε k) (hu : ∀ k ∈ u.support, ¬ inF1 ε k) :
    Λ (monomial s 1 * monomial u 1) = contr c (Bm ε c Λ s * monomial u 1) := by
  unfold Bm
  rw [if_pos hs, Finset.sum_mul, contr_sum]
  simp_rw [smul_mul_assoc, contr_smul]
  have e : ∀ t ∈ cand ε (rdeg ε s), contr c (monomial t 1 * monomial u 1) =
      if t = u.mapDomain pE then (wt c t : ℂ) else 0 := fun t ht => by
    rw [contr_mono ε c ((mem_cand ε _ t).mp ht).1 hu]; simp
  rw [Finset.sum_congr rfl fun t ht => by rw [e t ht]]
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  split_ifs with hmem
  · rw [mapDomain_pE_pE, div_mul_cancel₀]
    exact_mod_cast (wt_pos hc _).ne'
  · refine centre ε c Λ hΛ hs hu fun h => hmem ?_
    rw [mem_cand]; exact ⟨partner_support_first_family ε hu, h.symm⟩
end PositivityTheory.Rg.Sw.LC.CoreC
