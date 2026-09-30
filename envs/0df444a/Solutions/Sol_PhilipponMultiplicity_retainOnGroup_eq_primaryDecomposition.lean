-- Prove2me | solution 1 for PhilipponMultiplicity.retainOnGroup_eq_primaryDecomposition
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-27T18:42:23.80801+00:00
-- url     : https://prove2.me/submissions/19e4c7dd-e0f3-47f7-969e-fa14065263da

import Definitions.Def_PhilipponMultiplicity_SectionFour
import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
set_option autoImplicit false
open scoped BigOperators Topology
open PhilipponMultiplicity
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.OperatorSupport
open SectionThreeSupport
variable {K : Type*} [NontriviallyNormedField K] (G : EmbeddedGroupProduct K)

theorem retainAtRepresentative_iInf {ι : Type*} [Finite ι]
    (J : ι → Ideal G.CoordinateRing) (x : GroupHomogeneousRepresentative G) :
    retainAtRepresentative G (⨅ i, J i) x = ⨅ i, retainAtRepresentative G (J i) x := by
  classical
  letI := Fintype.ofFinite ι
  let S := (representativeMaximalIdeal G x).asIdeal.primeCompl
  let B := Localization.AtPrime (representativeMaximalIdeal G x).asIdeal
  have hm : (⨅ i, J i).map (algebraMap G.CoordinateRing B) =
      ⨅ i, (J i).map (algebraMap G.CoordinateRing B) := by
    simpa only [Finset.inf_univ_eq_iInf, Function.comp_def, IsLocalization.mapFrameHom_apply]
      using map_finset_inf (IsLocalization.mapFrameHom S B) Finset.univ J
  unfold retainAtRepresentative
  rw [hm]
  exact Ideal.comap_iInf _ _

theorem retainAtRepresentative_primary (J : Ideal G.CoordinateRing) (hJ : J.IsPrimary)
    (x : GroupHomogeneousRepresentative G) :
    retainAtRepresentative G J x = (by
      classical
      exact if J ≤ (representativeMaximalIdeal G x).asIdeal then J else ⊤) := by
  classical
  split_ifs with hx
  · exact IsLocalization.under_map_of_isPrimary_disjoint
      (representativeMaximalIdeal G x).asIdeal.primeCompl
      (Localization.AtPrime (representativeMaximalIdeal G x).asIdeal) hJ
      (Set.disjoint_left.mpr fun s hs hsi => hs (hx hsi))
  · unfold retainAtRepresentative
    rw [IsLocalization.AtPrime.map_eq_top_of_not_le
      (S := Localization.AtPrime (representativeMaximalIdeal G x).asIdeal) hx]
    exact Ideal.comap_top

/-- Definition 4.2: retention keeps exactly the actual primary components
whose support contains a genuine homogeneous representative of a group point. -/
theorem retainOnGroup_eq_primaryDecomposition (I : Ideal G.CoordinateRing)
    (D : PrimaryDecomposition G.ambient I) :
    retainOnGroup G I =
      ⨅ i : {i : Fin D.count // ∃ x : GroupHomogeneousRepresentative G,
        D.component i ≤ (representativeMaximalIdeal G x).asIdeal}, D.component i.1 := by
  classical
  conv_lhs => rw [D.intersection_eq]
  unfold retainOnGroup
  simp_rw [retainAtRepresentative_iInf]
  rw [iInf_comm]
  apply le_antisymm
  · apply le_iInf
    rintro ⟨i, x, hx⟩
    apply le_trans (iInf_le (fun j => ⨅ x, retainAtRepresentative G (D.component j) x) i)
    apply le_trans (iInf_le (fun y => retainAtRepresentative G (D.component i) y) x)
    rw [retainAtRepresentative_primary G _ (D.primary i) x, if_pos hx]
  · apply le_iInf
    intro i
    apply le_iInf
    intro x
    rw [retainAtRepresentative_primary G _ (D.primary i) x]
    split_ifs with hx
    · exact iInf_le (fun j : {j : Fin D.count // ∃ x : GroupHomogeneousRepresentative G,
        D.component j ≤ (representativeMaximalIdeal G x).asIdeal} => D.component j.1) ⟨i,x,hx⟩
    · exact le_top


end PhilipponMultiplicity.OperatorSupport

end

theorem solution
    (K : Type*) [NontriviallyNormedField K] (G : EmbeddedGroupProduct K)
    (I : Ideal G.CoordinateRing) (D : SectionThreeSupport.PrimaryDecomposition G.ambient I) :
    retainOnGroup G I =
      ⨅ i : {i : Fin D.count // ∃ x : GroupHomogeneousRepresentative G,
        D.component i ≤ (representativeMaximalIdeal G x).asIdeal}, D.component i.1 := by
  exact OperatorSupport.retainOnGroup_eq_primaryDecomposition G I D
