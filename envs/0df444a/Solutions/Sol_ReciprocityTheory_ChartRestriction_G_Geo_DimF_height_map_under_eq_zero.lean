-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.DimF.height_map_under_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:01:05.818454+00:00
-- url     : https://prove2.me/submissions/e5cec6a3-b775-4e29-9979-dbd5e80cd9a6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.DimF
open Ideal
namespace ReciprocityTheory.ChartRestriction.G.Geo.DimF
theorem _root_.solution {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    [Algebra.IsIntegral R B] (M : Ideal B) [M.IsPrime] :
    (M.map (Ideal.Quotient.mk ((M.under R).map (algebraMap R B)))).height = 0 := by
  classical
  have hIM : (M.under R).map (algebraMap R B) ≤ M := Ideal.map_comap_le
  set I := (M.under R).map (algebraMap R B) with hIdef
  haveI hp : (M.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hIM)
  have hMc : (M.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = M := by
    rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
      sup_eq_left.mpr hIM]
  have h0 : M.map (Ideal.Quotient.mk I) ∈ minimalPrimes (B ⧸ I) := by
    refine ⟨⟨hp, bot_le⟩, ?_⟩
    intro Q hQ hQM
    haveI hQp : Q.IsPrime := hQ.1
    set Q' := Q.comap (Ideal.Quotient.mk I) with hQ'def
    have hQ'M : Q' ≤ M := by
      rw [← hMc]
      exact Ideal.comap_mono hQM
    have hIQ' : I ≤ Q' := by
      intro x hx
      rw [hQ'def, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      exact Q.zero_mem
    have hQ'eq : Q' = M := by
      by_contra hne
      have hlt : Q' < M := lt_of_le_of_ne hQ'M hne
      obtain ⟨x, hxM, hxQ⟩ := SetLike.exists_of_lt hlt
      have hcl := Ideal.comap_lt_comap_of_integral_mem_sdiff (R := R) hQ'M ⟨hxM, hxQ⟩
        (Algebra.IsIntegral.isIntegral x)
      have hge : M.under R ≤ Q'.comap (algebraMap R B) :=
        (Ideal.le_comap_map).trans (Ideal.comap_mono hIQ')
      exact absurd (lt_of_le_of_lt hge hcl) (lt_irrefl _)
    have hmq : M.map (Ideal.Quotient.mk I) = Q := by
      rw [← hQ'eq, hQ'def, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
    exact hmq.le
  exact Ideal.height_eq_zero_iff.mpr h0
end ReciprocityTheory.ChartRestriction.G.Geo.DimF
