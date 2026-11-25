-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas.surj_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:55:32.584185+00:00
-- url     : https://prove2.me/submissions/24a38768-78a8-4226-9c64-80f4cf3aaba4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IsUnitOfValEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValuationResidueLemmas_wt_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValuationResidueLemmas_mem_max_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas
namespace ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas
theorem _root_.solution {K : Type} [Field K] [NumberField K] (ν : AddValuation K (WithTop ℤ))
    (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hnn : ∀ a : 𝓞 K, algebraMap (𝓞 K) K a ∈ vRing ν)
    (hpos : ∀ a : 𝓞 K, 0 < ν (algebraMap (𝓞 K) K a) ↔ a ∈ la.asIdeal) :
    Function.Surjective ((residue (vRing ν)).comp
      ((algebraMap (𝓞 K) K).codRestrict (vRing ν) hnn)) := by
  intro z
  obtain ⟨c, rfl⟩ := residue_surjective z
  have hc : 0 ≤ ν (c : K) := c.2
  have hz : ∀ a : 𝓞 K, a ∉ la.asIdeal → ν (algebraMap (𝓞 K) K a) = 0 := fun a ha =>
    le_antisymm (not_lt.mp (fun h => ha ((hpos a).mp h))) (hnn a)
  obtain ⟨n, d, hd, hnd⟩ : ∃ n d : 𝓞 K, d ∉ la.asIdeal ∧
      (c : K) * algebraMap (𝓞 K) K d = algebraMap (𝓞 K) K n := by
    obtain ⟨n, d, h | h⟩ := IsDedekindDomain.HeightOneSpectrum.exists_primeCompl_mul_eq_or_mul_eq la (c : K)
    · exact ⟨n, d, d.2, h⟩
    · refine ⟨d, n, ?_, h⟩
      intro hn
      have h1 : ν ((c : K) * algebraMap (𝓞 K) K n) = ν (algebraMap (𝓞 K) K d) := by rw [h]
      rw [AddValuation.map_mul, hz d d.2] at h1
      have h2 := wt_pos hc ((hpos n).mpr hn)
      rw [h1] at h2
      exact lt_irrefl _ h2
  obtain ⟨y, i, hi, hyi⟩ := la.isMaximal.exists_inv hd
  refine ⟨n * y, ?_⟩
  rw [RingHom.comp_apply, eq_comm, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff, mem_max_iff]
  have hval : ν ((c : K) - algebraMap (𝓞 K) K (n * y)) + ν (algebraMap (𝓞 K) K d) =
      ν (algebraMap (𝓞 K) K n) + ν (algebraMap (𝓞 K) K i) := by
    rw [← AddValuation.map_mul, ← AddValuation.map_mul, ← map_mul]
    congr 1
    rw [sub_mul, hnd, ← map_mul, ← map_sub]
    congr 1
    linear_combination (-n) * hyi
  rw [hz d hd, add_zero] at hval
  show 0 < ν ((c : K) - algebraMap (𝓞 K) K (n * y))
  rw [hval]
  exact wt_pos (hnn n) ((hpos i).mpr hi)
end ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas
