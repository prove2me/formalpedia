-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.exists_scaleOff_isProjFrame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:26:05.327807+00:00
-- url     : https://prove2.me/submissions/420d434e-bdff-4752-a20c-b46f289e79e3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ProjDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsNatMulMemConeRingIntFin
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_isIntegral_of_mem_subalgebra
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_exists_nat_mul_isIntegral_int
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_scaleOff_comp_self
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo Polynomial
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} [Finite κ] {D : ℕ}
section Int
variable {ι : Type*}
end Int
section SlopeTestRemainingChoices
variable {ι : Type*}
end SlopeTestRemainingChoices
private theorem isIntegral_natCast_mul_coneRing {ι : Type*} (y : ι → Ω) (k : ℕ) {a : Polynomial Ω}
    (ha : IsIntegral (coneRing ℤ y) a) : IsIntegral (coneRing ℤ y) ((k : Polynomial Ω) * a) := by
  have hk : IsIntegral (coneRing ℤ y) (k : Polynomial Ω) := by
    have h := isIntegral_algebraMap (R := coneRing ℤ y) (A := Polynomial Ω) (x := (k : coneRing ℤ y))
    rwa [map_natCast] at h
  exact hk.mul ha
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo Polynomial
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} [Finite κ] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (x : κ → Ω) (e : Fin (D + 1) → κ)
    (h : IsRatProjFrame x e) : ∃ m : ℕ, 0 < m ∧ IsProjFrame (scaleOff e m x) e := by

  classical
  haveI := Fintype.ofFinite κ
  choose n hn hint using fun i => exists_nat_mul_isIntegral_int (x ∘ e) _ (h.integral i)
  refine ⟨∏ i, n i, Finset.prod_pos (fun i _ => hn i), ⟨h.inj, ?_, ?_⟩⟩
  · rw [scaleOff_comp_self]; exact h.free
  · intro i
    rw [scaleOff_comp_self]
    by_cases hi : i ∈ Set.range e
    · obtain ⟨j, rfl⟩ := hi
      have e1 : C (scaleOff e (∏ i, n i) x (e j)) * X = coneMap ℤ (x ∘ e) (MvPolynomial.X j) := by
        simp [scaleOff, coneMap]
      rw [e1]
      apply isIntegral_of_mem_subalgebra
      rw [coneRing, AlgHom.mem_range]
      exact ⟨_, rfl⟩
    · have e1 : C (scaleOff e (∏ i, n i) x i) * X =
          ((∏ j ∈ Finset.univ.erase i, n j : ℕ) : Polynomial Ω) * ((n i : Polynomial Ω) * (C (x i) * X)) := by
        rw [← mul_assoc, ← Nat.cast_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
        simp only [scaleOff, if_neg hi, map_mul, map_natCast]
        ring
      rw [e1]
      exact isIntegral_natCast_mul_coneRing (x ∘ e) _ (hint i)
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
