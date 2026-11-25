-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.DataX.Mmat_cong
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:32:45.98358+00:00
-- url     : https://prove2.me/submissions/5765d100-aa4b-45e7-ba07-bb6a116639a6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MmatMulVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DiscrMulHermitianIntegral
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_smul_mem_of_int
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_DataX_discr_mul_hermitian_integral
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_Mmat_mulVec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Module Matrix
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.DataX
variable {r : ℕ} (X : DataX E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.DataX
theorem _root_.solution (u : Fin 2 → Fin r → E) (hmem : ∀ i, u i ∈ X.Λ) (β : Matrix (Fin 2) (Fin 2) E)
    (hβ : ∀ i k, ∃ γ : E, IsIntegral ℤ γ ∧ β i k = ((X.g * dEnat E : ℕ) : E) / 2 * γ) :
    ∀ v ∈ X.Λ, ∃ y ∈ X.Λ, X.Mmat u β *ᵥ v - v = (X.g : E) • y := by
  intro v hv
  choose γ hγi hγ using hβ
  set d := (NumberField.discr E).natAbs with hd
  have hint : ∀ k, IsIntegral ℤ ((d : E) * (X.ξ0 * herm X.Gm v (u k))) :=
    fun k => X.discr_mul_hermitian_integral hv (hmem k)
  have hc : ∀ i k, IsIntegral ℤ (X.κ0 / 2 * d * γ i k * herm X.Gm v (u k)) := by
    intro i k
    rcases X.κ0_xi with h | h
    · have e1 : X.κ0 / 2 * d * γ i k * herm X.Gm v (u k) = γ i k * ((d : E) * (X.ξ0 * herm X.Gm v (u k))) := by
        rw [h]; ring
      rw [e1]; exact (hγi i k).mul (hint k)
    · have e1 : X.κ0 / 2 * d * γ i k * herm X.Gm v (u k) = -(γ i k * ((d : E) * (X.ξ0 * herm X.Gm v (u k)))) := by
        rw [h]; ring
      rw [e1]; exact ((hγi i k).mul (hint k)).neg
  set c : Fin 2 → E := fun i => ∑ k, X.κ0 / 2 * d * γ i k * herm X.Gm v (u k) with hcdef
  have hci : ∀ i, IsIntegral ℤ (c i) := fun i => by
    simp only [hcdef, Fin.sum_univ_two]; exact (hc i 0).add (hc i 1)
  refine ⟨∑ i, c i • u i, Submodule.sum_mem _ fun i _ => smul_mem_of_int X.Λ (hci i) (hmem i), ?_⟩
  rw [X.Mmat_mulVec, add_sub_cancel_left, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul]
  congr 1
  simp only [hcdef, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hγ i k, hd]
  unfold dEnat
  push_cast
  ring
end ReciprocityTheory.ChartRestriction.G.FD.DataX
