-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.urepHom_mem_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:12:28.818304+00:00
-- url     : https://prove2.me/submissions/689b20a3-d816-4249-a6c2-75509b5ef912

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_DerivExistsAllPosStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_URepHom
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_urepHom_toMK_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_urepHom_toMK_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Topology
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (Kset ε) σ)
    (k : KG ε) : σ (toMK k) ∈ unitary (H →L[ℂ] H) := by
  have hmem : ∀ k : KG ε, toMK k ∈ Kset ε := fun k => k.2
  set a := σ (toMK k)
  set c := σ (toMK k⁻¹)

  have h1 : star a * a = 1 :=
    (ContinuousLinearMap.norm_map_iff_adjoint_comp_self a).1 (hσ.2.1 _ (hmem k))

  have h2 : a * c = 1 := by
    have e : toMK k * toMK k⁻¹ = 1 := by
      rw [← urepHom_toMK_mul, mul_inv_cancel, urepHom_toMK_one]
    have := hσ.1.2 _ (hmem k) _ (hmem k⁻¹)
    rw [e, hσ.1.1] at this
    exact this.symm
  have h3 : a * star a = 1 := by
    calc a * star a = a * star a * (a * c) := by rw [h2, mul_one]
      _ = a * (star a * a) * c := by noncomm_ring
      _ = 1 := by rw [h1, mul_one, h2]
  exact Unitary.mem_iff.2 ⟨h1, h3⟩
end ReciprocityTheory.ChartRestriction.DS.HW
