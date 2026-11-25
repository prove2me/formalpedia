-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.sumBd_sep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:46:00.244821+00:00
-- url     : https://prove2.me/submissions/cd4656f0-cb41-477c-896b-0965860ffa5b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatementPfB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBd_inv_entry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open Matrix Topology Filter
open scoped Matrix ComplexOrder ENNReal
noncomputable section
variable {p q : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up
theorem _root_.solution {f : ℕ} (Γ : Subgroup (Fin f → GL (Fin p ⊕ Fin q) ℂ)) (hd : DiscreteTopology Γ)
    (hU : ∀ γ ∈ Γ, ∀ k, IsUpq ((γ k : GL (Fin p ⊕ Fin q) ℂ) :
      Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ γ ∈ Γ, γ ≠ 1 → ∃ k i j,
      c ≤ ‖((γ k : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j -
        (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j‖ := by
  by_contra hcon
  push_neg at hcon
  have hc' : ∀ n : ℕ, ∃ γ ∈ Γ, γ ≠ 1 ∧ ∀ k i j,
      ‖((γ k : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j -
        (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j‖ < 1 / ((n : ℝ) + 1) :=
    fun n => hcon _ (by positivity)
  choose γ hγΓ hγ1 hγc using hc'
  have hent : ∀ k i j, Filter.Tendsto
      (fun n => ((γ n k : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j)
      Filter.atTop (𝓝 ((1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j)) := by
    intro k i j
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => (hγc n k i j).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hinv : ∀ k i j, Filter.Tendsto
      (fun n => (((γ n k)⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j)
      Filter.atTop (𝓝 ((1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j)) := by
    intro k i j
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    rw [Matrix.coe_units_inv, sumBd_inv_entry (hU _ (hγΓ n) k) i j]
    exact (hγc n k j i).le
  have hT : Filter.Tendsto γ Filter.atTop (𝓝 1) := by
    rw [tendsto_pi_nhds]
    intro k
    rw [(Units.isEmbedding_embedProduct (M := Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)).tendsto_nhds_iff]
    simp only [Function.comp_def, Units.embedProduct_apply, Pi.one_apply, inv_one, Units.val_one]
    refine Filter.Tendsto.prodMk_nhds ?_ ?_
    · exact tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => hent k i j
    · exact (MulOpposite.continuous_op.tendsto _).comp
        (tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => hinv k i j)
  have hδ : Filter.Tendsto (fun n => (⟨γ n, hγΓ n⟩ : Γ)) Filter.atTop (𝓝 1) := tendsto_subtype_rng.mpr hT
  have hev : ∀ᶠ n in Filter.atTop, (⟨γ n, hγΓ n⟩ : Γ) ∈ ({1} : Set Γ) :=
    hδ ((isOpen_discrete ({1} : Set Γ)).mem_nhds rfl)
  obtain ⟨n, hn⟩ := hev.exists
  exact hγ1 n (congrArg Subtype.val hn)
end ReciprocityTheory.ChartRestriction.G.AR.Up
