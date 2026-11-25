-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.genericImageFinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:32:00.028092+00:00
-- url     : https://prove2.me/submissions/43650aef-d914-430b-84a8-26485eb80cb0

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_ComapInclusionIsLocalHom
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExistsDualDerivations
import Definitions.Def_ReciprocityTheory_SemistableReduction_GenericImageFinite
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_trdeg_sField
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_DerivationAlgebraicIndependence_eIdx_injective
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_DerivationAlgebraicIndependence_gFam_indep
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_DerivationAlgebraicIndependence_sImage_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MvPolynomial DerivationAlgebraicIndependence
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution : FieldOfSStatement := by
  classical
  unfold FieldOfSStatement
  intro K Ω _ _ _ _ D m x hfg htr hJ
  obtain ⟨J, hJ⟩ := hJ
  set v : Fin D → KaehlerDifferential K Ω := fun a => KaehlerDifferential.D K Ω (x (J a)) with hv
  have hli : LinearIndependent Ω v := hJ
  have hφ : ∀ a : Fin D, ∃ φ : KaehlerDifferential K Ω →ₗ[Ω] Ω,
      ∀ b, φ (v b) = if a = b then 1 else 0 := by
    intro a
    obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Finsupp.lapply a).comp hli.repr)
    refine ⟨g, fun b => ?_⟩
    have hb : v b ∈ Submodule.span Ω (Set.range v) := Submodule.subset_span ⟨b, rfl⟩
    have h := congrArg (fun f => f ⟨v b, hb⟩) hg
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h
    rw [h, Finsupp.lapply_apply, hli.repr_eq_single b ⟨v b, hb⟩ rfl, Finsupp.single_apply]
    simp [eq_comm]
  choose φ hφ using hφ
  let δ : Fin D → Derivation K Ω Ω := fun a => (φ a).compDer (KaehlerDifferential.D K Ω)
  have hδ : ∀ a b, δ a (x (J b)) = if a = b then 1 else 0 := fun a b => hφ a b
  have hg := DerivationAlgebraicIndependence.gFam_indep (K := K) x J δ hδ
  have hind : AlgebraicIndependent K (sImage (D := D) x) := by
    have h1 := hg.comp _ (DerivationAlgebraicIndependence.eIdx_injective D m)
    have h2 := h1.map'
      (f := IsScalarTower.toAlgHom K (MvPolynomial (SVars D m) Ω) (SField Ω D m))
      (IsFractionRing.injective _ _)
    convert h2 using 1
    funext p
    simp [DerivationAlgebraicIndependence.sImage_eq]
  refine ⟨hind, ?_⟩
  have htrS : Algebra.trdeg K (SField Ω D m) = (((D + 1) * (m + 1) : ℕ) : Cardinal) := by
    rw [trdeg_sField, htr, ← Nat.cast_add]
    congr 1
    ring
  have hTB : IsTranscendenceBasis K (sImage (D := D) x) := by
    refine hind.isTranscendenceBasis_of_lift_trdeg_le ?_ ?_
    · rw [htrS]
      exact Cardinal.nat_lt_aleph0 _
    · rw [htrS]
      simp
  have halg := hTB.isAlgebraic_field
  set E := IntermediateField.adjoin K (Set.range (sImage (D := D) x))
  obtain ⟨s, hs⟩ := hfg
  let f : Ω →ₐ[K] SField Ω D m :=
    (IsScalarTower.toAlgHom K (MvPolynomial (SVars D m) Ω) (SField Ω D m)).comp
      (IsScalarTower.toAlgHom K Ω (MvPolynomial (SVars D m) Ω))
  let S : Set (SField Ω D m) := f '' (s : Set Ω) ∪
    Set.range (fun i => algebraMap (MvPolynomial (SVars D m) Ω) (SField Ω D m) (MvPolynomial.X i))
  have hSfin : S.Finite := (s.finite_toSet.image _).union (Set.finite_range _)
  haveI : Finite S := hSfin.to_subtype
  let L := IntermediateField.adjoin E S
  have hK : IntermediateField.adjoin K (f '' (s : Set Ω)) ≤ L.restrictScalars K := by
    rw [IntermediateField.adjoin_le_iff]
    intro z hz
    exact IntermediateField.subset_adjoin E S (Or.inl hz)
  have hω : ∀ ω : Ω, f ω ∈ L := by
    intro ω
    have h1 : f ω ∈ (IntermediateField.adjoin K (s : Set Ω)).map f :=
      (IntermediateField.mem_map _).2 ⟨ω, by rw [hs]; trivial, rfl⟩
    rw [IntermediateField.adjoin_map] at h1
    exact hK h1
  have hP : ∀ p : MvPolynomial (SVars D m) Ω,
      algebraMap (MvPolynomial (SVars D m) Ω) (SField Ω D m) p ∈ L := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      have h := hω a
      simpa [f, MvPolynomial.algebraMap_eq] using h
    | add p q hp hq =>
      rw [map_add]
      exact L.add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul]
      exact L.mul_mem hp (IntermediateField.subset_adjoin E S (Or.inr ⟨i, rfl⟩))
  have htop : L = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (SVars D m) Ω) z
    exact L.div_mem (hP a) (hP b)
  have hfd : FiniteDimensional E L :=
    IntermediateField.finiteDimensional_adjoin fun z _ => (halg.isAlgebraic z).isIntegral
  rw [htop] at hfd
  exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional
end ReciprocityTheory.MultiplicativeHeights
