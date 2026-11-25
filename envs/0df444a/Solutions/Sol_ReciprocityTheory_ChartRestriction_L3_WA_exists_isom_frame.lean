-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L3.WA.exists_isom_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:57:18.535593+00:00
-- url     : https://prove2.me/submissions/4ee843b2-d5ae-4ceb-9475-e962480cfaf3

import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_ExistsNormOneOfPair
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_ExistsIsomFix
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_ExistsIsomFrame
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_exists_next
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_exists_isom_fix


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {h : V →ₗ⋆[K] V →ₗ[K] K} {M : AddSubgroup V}
namespace ReciprocityTheory.ChartRestriction.L3.WA
theorem _root_.solution (hS : IsHermSemilocal S) (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0)
    (hM : IsSelfDualMod S h M) {n : ℕ} (e : Fin n → V)
    (he : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) :
    ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, ∀ i, g (e i) ∈ M := by
  have P : ∀ k, k ≤ n → ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, ∀ i : Fin n, i.val < k → g (e i) ∈ M := by
    intro k
    induction k with
    | zero => intro _; exact ⟨1, one_mem _, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ k ih =>
      intro hk
      obtain ⟨g, hg, hgM⟩ := ih (by omega)
      have hg' : ∀ u v, h (g u) (g v) = h u v := hg
      have hx : ∀ i i', h (g (e i)) (g (e i')) = if i = i' then 1 else 0 := fun i i' => by
        rw [hg']; exact he i i'
      obtain ⟨z, hzM, hzz, hzo⟩ := exists_next hS hs hM (fun i => g (e i)) hx
        (Finset.univ.filter (fun i : Fin n => i.val < k))
        (fun i hi => hgM i (Finset.mem_filter.mp hi).2) ⟨k, hk⟩ (by simp)
      obtain ⟨τ, hτ, hτj, hτfix⟩ := exists_isom_fix hs hd (x := g (e ⟨k, hk⟩)) (y := z)
        (by rw [hx, if_pos rfl]) hzz
      refine ⟨τ * g, mul_mem hτ hg, fun i hi => ?_⟩
      show τ (g (e i)) ∈ M
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h1 | h1
      · rw [hτfix]
        · exact hgM i h1
        · rw [hx, if_neg]
          intro hc
          rw [← hc] at h1
          exact lt_irrefl _ h1
        · have := hzo i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩)
          rw [← hs.eq, this, map_zero]
      · have : i = ⟨k, hk⟩ := Fin.ext h1
        rw [this, hτj]
        exact hzM
  obtain ⟨g, hg, hgM⟩ := P n le_rfl
  exact ⟨g, hg, fun i => hgM i i.isLt⟩
end ReciprocityTheory.ChartRestriction.L3.WA
