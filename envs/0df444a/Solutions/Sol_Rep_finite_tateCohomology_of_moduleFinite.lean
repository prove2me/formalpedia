-- Prove2me | solution 1 for Rep.finite_tateCohomology_of_moduleFinite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/36a8bd74-9a35-5dae-85e0-7dc1dc63d4ee

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Theorems.Thm_groupCohomology_finite_groupCohomology_succ_of_moduleFinite_int
import Theorems.Thm_Rep_card_smul_eq_zero_of_tateCohomology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_finite_tateCohomology_of_moduleFinite
p2m_attr_erase "simp" "Rep.coe_tateδneg2_apply"

set_option autoImplicit false
open CategoryTheory Rep

universe u

namespace P2mS26Fin

variable {k G : Type u} [CommRing k] [IsNoetherianRing k] [Group G]

theorem moduleFinite_groupHomology [Finite G] (L : Rep.{u} k G) [Module.Finite k L] (n : ℕ) :
    Module.Finite k (groupHomology L n) := by
  haveI : Module.Finite k ((groupHomology.inhomogeneousChains L).X n) := by
    change Module.Finite k ((Fin n → G) →₀ L)
    infer_instance
  haveI : IsNoetherian k ((groupHomology.inhomogeneousChains L).X n) := isNoetherian_of_isNoetherianRing_of_finite k _
  haveI : Module.Finite k (groupHomology.cycles L n) :=
    Module.Finite.of_injective (groupHomology.iCycles L n).hom ((ModuleCat.mono_iff_injective _).1 inferInstance)
  have hπ : Function.Surjective ((groupHomology.inhomogeneousChains L).homologyπ n).hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  exact Module.Finite.of_surjective ((groupHomology.inhomogeneousChains L).homologyπ n).hom hπ

variable [Fintype G]

theorem moduleFinite_tateH0 (L : Rep.{u} k G) [Module.Finite k L] : Module.Finite k L.tateH0 := by
  haveI : IsNoetherian k L := isNoetherian_of_isNoetherianRing_of_finite k L
  change Module.Finite k (L.ρ.invariants ⧸ LinearMap.range L.ρ.normBar)
  infer_instance

theorem moduleFinite_tateHneg1 (L : Rep.{u} k G) [Module.Finite k L] : Module.Finite k L.tateHneg1 := by
  haveI : IsNoetherian k L := isNoetherian_of_isNoetherianRing_of_finite k L
  haveI : Module.Finite k L.ρ.Coinvariants := by
    change Module.Finite k (L ⧸ Representation.Coinvariants.ker L.ρ)
    infer_instance
  haveI : IsNoetherian k L.ρ.Coinvariants := isNoetherian_of_isNoetherianRing_of_finite k _
  change Module.Finite k (LinearMap.ker L.ρ.normBar)
  infer_instance

theorem moduleFinite_tateCohomology_of_le_zero (L : Rep.{u} k G) [Module.Finite k L] (n : ℕ) :
    Module.Finite k (L.tateCohomology (Int.negSucc n)) ∧ Module.Finite k (L.tateCohomology 0) := by
  refine ⟨?_, moduleFinite_tateH0 L⟩
  rcases n with _ | m
  · exact moduleFinite_tateHneg1 L
  · exact moduleFinite_groupHomology L (m + 1)

end P2mS26Fin

open P2mS26Fin in
theorem solution {G : Type} [Group G] [Fintype G]
    (L : Rep ℤ G) [Module.Finite ℤ L] (n : ℤ) :
    Finite (L.tateCohomology n) := by
  have hL : Module.Finite ℤ L := ‹_›
  have hG : (Fintype.card G : ℤ) ∈ nonZeroDivisors ℤ :=
    mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast Fintype.card_ne_zero)
  rcases n with (_ | m) | n
  · haveI := (@moduleFinite_tateCohomology_of_le_zero ℤ G _ _ _ _ L (by convert hL <;> first | rfl | exact Subsingleton.elim _ _) 0).2
    refine Module.finite_of_fg_torsion _ fun x => ⟨⟨(Fintype.card G : ℤ), hG⟩, ?_⟩
    exact Rep.card_smul_eq_zero_of_tateCohomology L 0 x
  · exact groupCohomology.finite_groupCohomology_succ_of_moduleFinite_int L m
  · haveI := (@moduleFinite_tateCohomology_of_le_zero ℤ G _ _ _ _ L (by convert hL <;> first | rfl | exact Subsingleton.elim _ _) n).1
    refine Module.finite_of_fg_torsion _ fun x => ⟨⟨(Fintype.card G : ℤ), hG⟩, ?_⟩
    exact Rep.card_smul_eq_zero_of_tateCohomology L (Int.negSucc n) x

end S_Rep_finite_tateCohomology_of_moduleFinite
end P2MW
export P2MW.S_Rep_finite_tateCohomology_of_moduleFinite (solution)
