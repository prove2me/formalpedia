-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.two_le_krullDim_of_relevant_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:28:16.411099+00:00
-- url     : https://prove2.me/submissions/64541869-3e62-4205-b67f-7c10c6920aba

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CardPieceIrrelevantIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_TwoLeKrullDimOfRelevantPrime
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_two_le_krullDim_of_chain
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_i2kill_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_le_comap_kill_of_homogeneous
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_comap_kill_variables_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {ι : Fin 2 → Type} [∀ k, Fintype (ι k)] {q : Ideal (MRing ι)}
    (hq : IsMultiProjPrime q) : ((2 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MRing ι ⧸ q) := by
  obtain ⟨hp, hh, hr⟩ := hq
  obtain ⟨i0, hi0⟩ := hr 0
  obtain ⟨i1, hi1⟩ := hr 1
  have : (q.comap (i2kill (ι := ι) 0)).IsPrime := Ideal.comap_isPrime _ _
  have : (q.comap ((i2kill (ι := ι) 1).comp (i2kill 0))).IsPrime := Ideal.comap_isPrime _ _
  have e00 : i2kill (ι := ι) 0 (X ⟨0, i0⟩) = 0 := by rw [i2kill_X, if_pos rfl]
  have e01 : i2kill (ι := ι) 0 (X ⟨1, i1⟩) = X ⟨1, i1⟩ := by
    rw [i2kill_X, if_neg (show (1 : Fin 2) ≠ 0 by decide)]
  have e11 : i2kill (ι := ι) 1 (X ⟨1, i1⟩) = 0 := by rw [i2kill_X, if_pos rfl]
  have m1 : (X ⟨1, i1⟩ : MRing ι) ∈ q.comap ((i2kill (ι := ι) 1).comp (i2kill 0)) := by
    rw [Ideal.mem_comap, AlgHom.comp_apply, e01, e11]
    exact zero_mem _
  have m1' : (X ⟨1, i1⟩ : MRing ι) ∉ q.comap (i2kill (ι := ι) 0) := by
    rw [Ideal.mem_comap, e01]
    exact hi1
  have m0 : (X ⟨0, i0⟩ : MRing ι) ∈ q.comap (i2kill (ι := ι) 0) := by
    rw [Ideal.mem_comap, e00]
    exact zero_mem _
  exact two_le_krullDim_of_chain q _ _ (lt_of_le_of_ne (le_comap_kill_of_homogeneous hh 0) fun h => hi0 (h ▸ m0))
    (lt_of_le_of_ne (comap_kill_variables_le hh) fun h => m1' (h ▸ m1))
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
