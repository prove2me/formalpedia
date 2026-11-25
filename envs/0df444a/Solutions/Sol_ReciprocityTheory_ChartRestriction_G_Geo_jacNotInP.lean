-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.jacNotInP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:51:12.983796+00:00
-- url     : https://prove2.me/submissions/242e70ef-039d-4a3a-8a17-b088819077ec

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterPC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExtCContract
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_GenSmooth
import Definitions.Def_Lemmata_GeneralBFactThirdLast_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterPCProof
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_horizontal_spec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_withBot_eq_of_add_one
import Theorems.Thm_ReciprocityTheory_AnForm_R_exists_jacobian_minor_not_mem
import Theorems.Thm_ReciprocityTheory_AnForm_R_extQ_spec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial ReciprocityTheory.AnForm.R
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution : JacNotInPStatement := by
  classical
  intro K _ ι _ P e hP
  obtain ⟨_, hMP, hH, hdim⟩ := hP
  haveI : P.IsPrime := hMP.1
  obtain ⟨S, hShom, hSspan⟩ := hMP.2.1
  obtain ⟨hpr, _, hd⟩ := extQ_spec P (horizontal_spec hH)
  haveI := hpr
  obtain ⟨F0, hF0⟩ : P.FG := IsNoetherian.noetherian P
  have hfin : ∀ x ∈ F0, ∃ T : Finset (MRing ι), (↑T : Set (MRing ι)) ⊆ S ∧
      x ∈ Submodule.span (MRing ι) (↑T : Set (MRing ι)) := by
    intro x hx
    have hxP : x ∈ P := hF0 ▸ Submodule.subset_span hx
    rw [hSspan] at hxP
    exact Submodule.mem_span_finite_of_mem_span hxP
  choose T hTS hxT using hfin
  let T' : Finset (MRing ι) := F0.attach.biUnion fun x => T x.1 x.2
  have hT'S : (↑T' : Set (MRing ι)) ⊆ S := by
    intro y hy
    obtain ⟨x, _, hyx⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hy)
    exact hTS x.1 x.2 hyx
  have hspanT' : Ideal.span (↑T' : Set (MRing ι)) = P := by
    apply le_antisymm
    · rw [hSspan]
      exact Ideal.span_mono hT'S
    · rw [← hF0]
      apply Submodule.span_le.mpr
      intro x hx
      exact Ideal.span_mono (fun y hy => Finset.mem_coe.mpr
        (Finset.mem_biUnion.mpr ⟨⟨x, hx⟩, Finset.mem_attach _ _, hy⟩)) (hxT x hx)
  let G : Fin T'.card → MRing ι := fun i => (T'.equivFin.symm i : MRing ι)
  have hrange : Set.range G = ↑T' := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact (T'.equivFin.symm i).2
    · intro hy
      exact ⟨T'.equivFin ⟨y, hy⟩, by simp [G]⟩
  refine ⟨T'.card, G, fun i => hShom _ (hT'S (T'.equivFin.symm i).2), by rw [hrange, hspanT'], ?_⟩
  let Gq : Fin T'.card → MvPolynomial (Σ k, ι k) ℚ := fun i => MvPolynomial.map (Int.castRingHom ℚ) (G i)
  have hGq : Ideal.span (Set.range Gq) = extQ P := by
    unfold extQ
    rw [← hspanT', ← hrange, Ideal.map_span, ← Set.range_comp]
    rfl
  have hdq : ringKrullDim (MvPolynomial (Σ k, ι k) ℚ ⧸ extQ P) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    apply withBot_eq_of_add_one
    rw [hd, hdim, show e + 1 + Fintype.card K = e + Fintype.card K + 1 by omega]
  obtain ⟨a, b, hab⟩ := exists_jacobian_minor_not_mem (extQ P) Gq hGq (e + Fintype.card K) hdq
  intro hle
  apply hab
  have hmem : Matrix.det (Matrix.of fun i j => pderiv (b j) (G (a i))) ∈ P :=
    hle (Submodule.subset_span ⟨a, b, rfl⟩)
  have hmap : MvPolynomial.map (Int.castRingHom ℚ) (Matrix.det (Matrix.of fun i j => pderiv (b j) (G (a i)))) ∈
      extQ P := Ideal.mem_map_of_mem _ hmem
  rw [RingHom.map_det] at hmap
  convert hmap using 2
  ext i j
  simp [Gq, RingHom.mapMatrix_apply, MvPolynomial.pderiv_map]
end ReciprocityTheory.ChartRestriction.G.Geo
