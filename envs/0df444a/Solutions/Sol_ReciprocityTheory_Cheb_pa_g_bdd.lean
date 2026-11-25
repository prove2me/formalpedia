-- Prove2me | solution 1 for ReciprocityTheory.Cheb.pa_g_bdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:26:46.274622+00:00
-- url     : https://prove2.me/submissions/56a26d18-252e-458c-9ec1-62e51e3ac0ce

import Definitions.Def_ReciprocityTheory_Chebotarev_CasimirPowerSurjectiveSymmetric
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerLim
import Definitions.Def_ReciprocityTheory_Chebotarev_PrimeAsymp
import Theorems.Thm_ReciprocityTheory_Cheb_pa_Z_ge_one
import Theorems.Thm_ReciprocityTheory_Cheb_pa_Z_anti
import Theorems.Thm_ReciprocityTheory_Cheb_pa_Z_lim

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
theorem _root_.solution (E : Type) [Field E] [NumberField E] :
    ∃ m M : ℝ, 0 < m ∧ ∀ s ∈ Set.Ioc (1 : ℝ) 2,
      m ≤ (s - 1) * ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-s) ∧
      (s - 1) * ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-s) ≤ M := by
  set r := dedekindZeta_residue E
  have hr : 0 < r := dedekindZeta_residue_pos E
  have hmem := pa_Z_lim E (Icc_mem_nhds (by linarith : r / 2 < r) (by linarith : r < 2 * r))
  obtain ⟨u, hu, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' (by norm_num : (1 : ℝ) < 2)).mp hmem
  have hu1 : 1 < u := hu
  set t := min ((1 + u) / 2) 2 with htdef
  have ht1 : 1 < t := lt_min (by linarith) (by norm_num)
  have htu : t < u := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have ht2 : t ≤ 2 := min_le_right _ _
  set Zt := ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-t)
  refine ⟨min (r / 2) (t - 1), max (2 * r) Zt, lt_min (by linarith) (by linarith), fun s hs => ?_⟩
  obtain ⟨hs1, hs2⟩ := hs
  have hZ1 := pa_Z_ge_one E hs1
  rcases le_total s t with hst | hst
  · have hin := hsub ⟨hs1, lt_of_le_of_lt hst htu⟩
    obtain ⟨h1, h2⟩ := hin
    exact ⟨(min_le_left _ _).trans h1, h2.trans (le_max_left _ _)⟩
  · have hZ := pa_Z_anti E ht1 hst
    constructor
    · refine (min_le_right _ _).trans ?_
      nlinarith
    · refine le_trans ?_ (le_max_right _ _)
      have hZ0 : 0 ≤ ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℝ) ^ (-s) := by linarith
      nlinarith
end ReciprocityTheory.Cheb
