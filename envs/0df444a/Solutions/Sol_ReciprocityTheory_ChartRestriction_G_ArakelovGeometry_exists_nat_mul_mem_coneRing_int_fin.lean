-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.exists_nat_mul_mem_coneRing_int_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:52:26.363162+00:00
-- url     : https://prove2.me/submissions/a950b7a4-19c3-4340-ab07-e4f24d0db2db

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ProjDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsNatMulMemConeRingIntFin
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_exists_nat_mul_coneMap_mem_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo Polynomial
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} [Finite κ] {D : ℕ}
variable {ι : Type*}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (y : ι → Ω) (f : ℕ → (Polynomial Ω)) (hf : ∀ i, f i ∈ coneRing ℚ y) (d : ℕ) :
    ∃ n : ℕ, 0 < n ∧ ∀ i < d, (n : (Polynomial Ω)) * f i ∈ coneRing ℤ y := by

  induction d with
  | zero => exact ⟨1, one_pos, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ d ih =>
    obtain ⟨n, hn, h⟩ := ih
    have hfd := hf d
    rw [coneRing, AlgHom.mem_range] at hfd
    obtain ⟨p, hp⟩ := hfd
    obtain ⟨n', hn', h'⟩ := exists_nat_mul_coneMap_mem_int y p
    refine ⟨n * n', Nat.mul_pos hn hn', fun i hi => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
    · have e : ((n * n' : ℕ) : Polynomial Ω) * f i = (n' : Polynomial Ω) * ((n : Polynomial Ω) * f i) := by
        push_cast; ring
      rw [e]; exact mul_mem (natCast_mem _ _) (h i hi)
    · have e : ((n * n' : ℕ) : Polynomial Ω) * f i =
          (n : Polynomial Ω) * ((n' : Polynomial Ω) * coneMap ℚ y p) := by
        rw [hp, hi]; push_cast; ring
      rw [e]; exact mul_mem (natCast_mem _ _) h'
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
