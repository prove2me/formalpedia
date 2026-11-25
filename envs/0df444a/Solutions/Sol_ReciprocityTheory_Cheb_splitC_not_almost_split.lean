-- Prove2me | solution 1 for ReciprocityTheory.Cheb.splitC_not_almost_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:18:16.526393+00:00
-- url     : https://prove2.me/submissions/0e800870-3ac1-472d-80e6-bf30ecf2b836

import Definitions.Def_ReciprocityTheory_Chebotarev_SplitDef
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitF
import Definitions.Def_ReciprocityTheory_Chebotarev_ChebyshevLambdaSubPsiBounded
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitC
import Theorems.Thm_ReciprocityTheory_Cheb_splitC_bound
import Theorems.Thm_ReciprocityTheory_Cheb_chebyshev_log_bounded


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
open ReciprocityTheory ReciprocityTheory.Cheb
namespace ReciprocityTheory.Cheb
theorem _root_.solution (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E']
    (k : ℕ) (hk : 2 ≤ k)
    (h : {q : Prm E | ¬ k ≤ {P : Prm E' | under P = q ∧ Nrm P = Nrm q}.ncard}.Finite) : False := by
  set S := {q : Prm E | ¬ k ≤ {P : Prm E' | under P = q ∧ Nrm P = Nrm q}.ncard} with hSdef
  have hfib : ∀ q ∉ S, k ≤ {P : Prm E' | under P = q ∧ Nrm P = Nrm q}.ncard := by
    intro q hq
    by_contra hc
    exact hq hc
  obtain ⟨C1, hC1⟩ := chebyshev_log_bounded E
  obtain ⟨C2, hC2⟩ := chebyshev_log_bounded E'
  set N : ℝ := (h.toFinset.card : ℝ)
  set M : ℝ := max (C2 + k * (N + C1)) 0
  set s : ℝ := 1 + Real.exp (-(M + 1))
  have he : 0 < Real.exp (-(M + 1)) := Real.exp_pos _
  have he1 : Real.exp (-(M + 1)) ≤ 1 := Real.exp_le_one_iff.mpr (by
    have : 0 ≤ M := le_max_right _ _
    linarith)
  have hs1 : 1 < s := by simp only [s]; linarith
  have hs2 : s ∈ Set.Ioc 1 2 := ⟨hs1, by simp only [s]; linarith⟩
  have hlog : Real.log (1 / (s - 1)) = M + 1 := by
    simp only [s, add_sub_cancel_left, one_div, ← Real.exp_neg, neg_neg, Real.log_exp]
  have hb := splitC_bound E E' k S h hfib s hs1
  have h1 := hC1 s hs2
  have h2 := hC2 s hs2
  rw [hlog] at h1 h2
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hM : C2 + k * (N + C1) ≤ M := le_max_left _ _
  have hM0 : 0 ≤ M := le_max_right _ _
  have a1 := abs_le.mp h1
  have a2 := abs_le.mp h2
  have : (k : ℝ) * (M + 1 - C1) ≤ k * PE E s := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  nlinarith
end ReciprocityTheory.Cheb
