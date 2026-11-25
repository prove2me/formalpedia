-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_form_eq_zero_of_unitPoint_13babd4cbc4a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:31:49.074122+00:00
-- url     : https://prove2.me/submissions/5f246d4c-d5da-44b1-9c05-510233b1bb34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Examples
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightObjects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_TargetSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Reading

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G
open scoped ContDiff
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable (n)
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {f : MvPolynomial (Coord fun _ : Unit ↦ 0) ℤ} {δ : Unit → ℕ}
    (hf : IsWeightedHomogeneous (coordDeg fun _ : Unit ↦ 0) f δ) (h : aeval unitPoint f = 0) : f = 0 := by
  have hm : ∀ m ∈ f.support, m = Finsupp.single ⟨(), 0⟩ (δ ()) := by
    intro m hm
    have h1 := (geoMultiHomog_iff f δ).mpr hf m hm ()
    ext ⟨u, i⟩
    cases u
    have hi : i = 0 := Subsingleton.elim (α := Fin 1) i 0
    subst hi
    have h2 : ∑ i : Fin 1, m ⟨(), i⟩ = m ⟨(), 0⟩ := Fin.sum_univ_one _
    rw [Finsupp.single_eq_same, ← h2]
    exact h1
  by_contra h0
  have hs : f.support = {Finsupp.single ⟨(), 0⟩ (δ ())} := by
    obtain ⟨m, hmem⟩ := Finset.nonempty_of_ne_empty (mt support_eq_empty.mp h0)
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, hm⟩
    rw [← hm m hmem]
    exact hmem
  have hc : coeff (Finsupp.single ⟨(), 0⟩ (δ ())) f ≠ 0 :=
    mem_support_iff.mp (by rw [hs]; exact Finset.mem_singleton_self _)
  rw [aeval_def, eval₂_eq, hs, Finset.sum_singleton] at h
  simp only [unitPoint, one_pow, Finset.prod_const_one, mul_one] at h
  have h3 : ((coeff (Finsupp.single ⟨(), 0⟩ (δ ())) f : ℤ) : ℚ) = 0 := by simpa using h
  exact hc (by exact_mod_cast h3)
end GroundTheory.Heights₂.Heights
