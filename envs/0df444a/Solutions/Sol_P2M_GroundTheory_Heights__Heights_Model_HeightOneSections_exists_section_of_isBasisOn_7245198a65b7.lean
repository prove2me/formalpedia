-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_HeightOneSections_exists_section_of_isBasisOn_7245198a65b7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:25:27.404449+00:00
-- url     : https://prove2.me/submissions/bb19a766-f72d-4f90-bdf8-8cd6abdc04bb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PBundlesAgree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PHeightOneSectionsLocal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_HeightOneSections_genericPoint_mem_02612281dbe5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_HeightOneSections_fromSpec_mem_de0322f741f7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_HeightOneSections_isIntegrallyClosed_of_isAffineOpen_f6cbad469fed
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_HeightOneSections_germ_comb_8d6e321d74e3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_HeightOneSections_germ_coeff_unique_f4d9ebe0d3b7

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
open GroundTheory.Heights₂.Heights.Model.HeightOneSections
variable {X : Scheme.{0}} [IsIntegral X]
namespace GroundTheory.Heights₂.Heights.Model.HeightOneSections
theorem _root_.solution (hHOI : HeightOneIntersection.Statement)
    [IsLocallyNoetherian X] (hN : IsNormalScheme X) (E : X.Modules) {V : X.Opens}
    (hV : IsAffineOpen V) (hη : genericPoint X ∈ V) {n : ℕ} {s : Fin n → Γ(E, V)}
    (hs : IsBasisOn E V s) (v : E.presheaf.stalk (genericPoint X))
    (hv : ∀ y : X, y ∈ V → ringKrullDim (X.presheaf.stalk y) = 1 → v ∈ genericImage E y) :
    ∃ σ : Γ(E, V), E.presheaf.germ V (genericPoint X) hη σ = v := by
  have : Nonempty V := ⟨⟨genericPoint X, hη⟩⟩
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have := isIntegrallyClosed_of_isAffineOpen hN hV
  have := functionField_isFractionRing_of_isAffineOpen X V hV

  obtain ⟨W0, hW0, t0, ht0⟩ := E.presheaf.exists_germ_eq v
  have hW1 : genericPoint X ∈ W0 ⊓ V := ⟨hW0, hη⟩
  obtain ⟨r, hr⟩ := (hs (W0 ⊓ V) inf_le_right).2
    ((E.presheaf.map (homOfLE (inf_le_left : W0 ⊓ V ≤ W0)).op).hom t0)
  have hvc : v = ∑ i, X.presheaf.germ (W0 ⊓ V) _ hW1 (r i) •
      E.presheaf.germ V (genericPoint X) hη (s i) := by
    rw [← germ_comb E s (W0 ⊓ V) inf_le_right r _ hW1]
    change v = E.presheaf.germ (W0 ⊓ V) _ hW1 (comb E s (W0 ⊓ V) inf_le_right r)
    rw [show comb E s (W0 ⊓ V) inf_le_right r = _ from hr, ← ht0]
    exact (TopCat.Presheaf.germ_res_apply E.presheaf _ _ hW1 t0).symm

  have hmem : ∀ i, X.presheaf.germ (W0 ⊓ V) _ hW1 (r i) ∈
      Subalgebra.toSubmodule (⊥ : Subalgebra Γ(X, V) X.functionField) := by
    intro i
    rw [hHOI Γ(X, V) X.functionField, Submodule.mem_iInf]
    intro p
    rw [Submodule.mem_iInf]
    intro hp1
    have hy := fromSpec_mem hV p
    let y := hV.fromSpec p
    let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨y, hy⟩ : V)
    have hloc : IsLocalization.AtPrime (X.presheaf.stalk y) p.asIdeal :=
      hV.isLocalization_stalk' p hy
    have hdim : ringKrullDim (X.presheaf.stalk y) = 1 := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal, hp1]
      rfl
    obtain ⟨w, hw⟩ := hv y hy hdim
    obtain ⟨W2, hW2, t, rfl⟩ := E.presheaf.exists_germ_eq w
    have hη3 : genericPoint X ∈ W2 ⊓ V := genericPoint_mem (show y ∈ W2 ⊓ V from ⟨hW2, hy⟩)
    obtain ⟨r', hr'⟩ := (hs (W2 ⊓ V) inf_le_right).2
      ((E.presheaf.map (homOfLE (inf_le_left : W2 ⊓ V ≤ W2)).op).hom t)
    have hvc' : v = ∑ i, X.presheaf.germ (W2 ⊓ V) _ hη3 (r' i) •
        E.presheaf.germ V (genericPoint X) hη (s i) := by
      rw [← germ_comb E s (W2 ⊓ V) inf_le_right r' _ hη3]
      change v = E.presheaf.germ (W2 ⊓ V) _ hη3 (comb E s (W2 ⊓ V) inf_le_right r')
      rw [show comb E s (W2 ⊓ V) inf_le_right r' = _ from hr', ← hw]
      rw [TopCat.Presheaf.germ_res_apply]
      exact TopCat.Presheaf.germ_stalkSpecializes_apply E.presheaf hW2
        (genericPoint_specializes y) t
    have hc := germ_coeff_unique E hs _ hη inf_le_right inf_le_right hW1 hη3 r r'
      (hvc.symm.trans hvc') i
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj p.asIdeal.primeCompl
      (X.presheaf.germ (W2 ⊓ V) y ⟨hW2, hy⟩ (r' i))
    refine ⟨b, b.2, Algebra.mem_bot.mpr ⟨a, ?_⟩⟩
    have hab' := congrArg (X.presheaf.stalkSpecializes (genericPoint_specializes y)) hab
    rw [map_mul] at hab'
    have h1 : X.presheaf.stalkSpecializes (genericPoint_specializes y)
        (X.presheaf.germ (W2 ⊓ V) y ⟨hW2, hy⟩ (r' i)) = X.presheaf.germ (W2 ⊓ V) _ hη3 (r' i) :=
      TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
    have h2 : ∀ c : Γ(X, V), X.presheaf.stalkSpecializes (genericPoint_specializes y)
        (algebraMap Γ(X, V) (X.presheaf.stalk y) c) = algebraMap Γ(X, V) X.functionField c :=
      fun c => TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
    rw [h1, h2, h2, ← hc] at hab'
    rw [Algebra.smul_def, ← hab', mul_comm]
  choose a ha using fun i => Algebra.mem_bot.mp (hmem i)
  refine ⟨∑ i, a i • s i, ?_⟩
  rw [map_sum, hvc]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [BundlesAgree.germ_smul', ← ha i]
  rfl
end GroundTheory.Heights₂.Heights.Model.HeightOneSections
