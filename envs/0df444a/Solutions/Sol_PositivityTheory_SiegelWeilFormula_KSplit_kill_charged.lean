-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KSplit.kill_charged
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:10:47.626998+00:00
-- url     : https://prove2.me/submissions/dac4a69c-f871-4437-8c0b-5924acc6ca86

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_NullSec
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ThetaSplitting_ActUDiagMonomial
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_actU_diag_monomial
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_prod_phase
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KSplit_star_exp_mul_I

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KSplit
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
namespace PositivityTheory.SiegelWeilFormula.KSplit
theorem _root_.solution (Λ : PX m n →ₗ[ℂ] ℂ) (hΛ : ∀ u ∈ unitaryGroup (Fin m) ℂ, ∀ P, Λ (actU u P) = Λ P)
    (s : Fin m × Fin n × Bool →₀ ℕ) (a : Fin m) (h : chg a s ≠ 0) : Λ (monomial s 1) = 0 := by
  set q := chg a s
  set z : ℂ := Complex.exp ((Real.pi / q : ℝ) * Complex.I)
  have hz : star z * z = 1 := star_exp_mul_I _
  have hq : z ^ q = -1 := by
    rw [← Complex.exp_int_mul]
    rw [show (q : ℂ) * (((Real.pi / q : ℝ) : ℂ) * Complex.I) = Real.pi * Complex.I by
      push_cast; field_simp]
    exact Complex.exp_pi_mul_I
  set ζ : Fin m → ℂ := fun c => if c = a then z else 1
  have hu : diagonal ζ ∈ unitaryGroup (Fin m) ℂ := by
    rw [mem_unitaryGroup_iff', star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one]
    congr 1; ext c; simp only [ζ, Pi.star_apply, Pi.mul_apply, Pi.one_apply]; split_ifs
    · exact hz
    · simp
  have e := hΛ _ hu (monomial s 1)
  rw [actU_diag_monomial, C_mul', map_smul, smul_eq_mul] at e
  have e2 : (s.prod fun k e => (if k.2.2 then star (ζ k.1) else ζ k.1) ^ e) = -1 := by
    rw [← hq]; exact prod_phase a z hz s
  rw [e2] at e
  linear_combination -e / 2
end PositivityTheory.SiegelWeilFormula.KSplit
