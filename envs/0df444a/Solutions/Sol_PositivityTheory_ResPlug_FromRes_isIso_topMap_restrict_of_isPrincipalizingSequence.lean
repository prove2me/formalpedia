-- Prove2me | solution 1 for PositivityTheory.ResPlug.FromRes.isIso_topMap_restrict_of_isPrincipalizingSequence
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:19:29.308498+00:00
-- url     : https://prove2.me/submissions/d9fd274e-6332-4847-9517-f9cc12c40bb4

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Statements
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupIsoOffCenter
import Definitions.Def_Development_WeilBound_CoreStatements_ResolutionCharZero_FromResIso
import Theorems.Thm_FunctorialResolution_Blowup_IsBlowupAlongIdealSheaf_isIso_of_top
import Theorems.Thm_FunctorialResolution_Blowup_IsBlowupAlongIdealSheaf_restrict
import Theorems.Thm_FunctorialResolution_Blowup_comap_eq_top_of_notMem_support

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
namespace PositivityTheory.ResPlug.FromRes
open FunctorialResolution
private theorem isIso_restrict_comp' {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (V : Z.Opens)
    (h1 : IsIso (f ∣_ (g ⁻¹ᵁ V))) (h2 : IsIso (g ∣_ V)) : IsIso ((f ≫ g) ∣_ V) := by
  have h : IsIso (f ∣_ (g ⁻¹ᵁ V) ≫ g ∣_ V) := @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2
  rw [morphismRestrict_comp]
  exact h
private theorem structMap_zero' {X : Scheme.{0}} (s : BlowupSequence X) : s.structMap 0 = s.isoZero.hom := by
  simp only [BlowupSequence.structMap, BlowupSequence.down]
  have : (homOfLE (Nat.zero_le 0)).op = 𝟙 (op (0 : ℕ)) := Subsingleton.elim _ _
  rw [this, CategoryTheory.Functor.map_id, Category.id_comp]
end PositivityTheory.ResPlug.FromRes
end
end

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open PositivityTheory PositivityTheory.ResPlug PositivityTheory.ResPlug.FromRes
open FunctorialResolution
namespace PositivityTheory.ResPlug.FromRes
theorem _root_.solution {k : Type} [Field k] {X : Scheme.{0}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {E : List X.IdealSheafData} {s : BlowupSequence X}
    (h : IsPrincipalizingSequence p I E s) : IsIso (s.topMap ∣_ I.support.compl) := by
  obtain ⟨ideal, boundary, h0, -, -, -, hle, hsucc, -, -, -, -, -⟩ := h

  have hsupp : ∀ i, i ≤ s.length → ∀ x ∈ ((ideal i).support : Set (s.obj i)),
      (s.structMap i).base x ∈ (I.support : Set X) := by
    intro i
    induction i with
    | zero =>
      intro _ x hx
      rw [h0, Scheme.IdealSheafData.support_comap] at hx
      exact hx
    | succ i ih =>
      intro hi x hx
      have hlt : i < s.length := hi
      have e := congrArg Scheme.IdealSheafData.support (hsucc i hlt)
      rw [Scheme.IdealSheafData.support_mul] at e
      have hx' : x ∈ (((s.center i).comap (s.blowupMap i)).support ⊔ (ideal (i + 1)).support : Closeds _) :=
        Or.inr hx
      rw [e, Scheme.IdealSheafData.support_comap] at hx'
      have := ih hlt.le _ hx'
      rw [← s.structMap_down (Nat.le_succ i)]
      simpa [BlowupSequence.blowupMap] using this

  have hiso : ∀ i, i ≤ s.length → IsIso (s.structMap i ∣_ I.support.compl) := by
    intro i
    induction i with
    | zero =>
      intro _
      have : IsIso (s.structMap 0) := by rw [structMap_zero']; infer_instance
      infer_instance
    | succ i ih =>
      intro hi
      have hlt : i < s.length := hi
      have h2 := ih hlt.le
      have hb : Blowup.IsBlowupAlongIdealSheaf (s.blowupMap i) (s.center i) := s.isBlowup i hlt
      have hres := hb.restrict (s.structMap i ⁻¹ᵁ I.support.compl)
      have htop : (s.center i).comap (s.structMap i ⁻¹ᵁ I.support.compl).ι = ⊤ := by
        apply Blowup.comap_eq_top_of_notMem_support
        intro x hx
        have h1 := hsupp i hlt.le _ (hle i hlt |> Scheme.IdealSheafData.support_antitone <| hx)
        have hxV : (s.structMap i ⁻¹ᵁ I.support.compl).ι.base x
            ∈ ((s.structMap i ⁻¹ᵁ I.support.compl : (s.obj i).Opens) : Set (s.obj i)) := by
          rw [← Scheme.Opens.range_ι]
          exact Set.mem_range_self x
        exact hxV h1
      rw [htop] at hres
      have h1 : IsIso (s.blowupMap i ∣_ (s.structMap i ⁻¹ᵁ I.support.compl)) := hres.isIso_of_top
      have key := isIso_restrict_comp' (s.blowupMap i) (s.structMap i) I.support.compl h1 h2
      have hcomp : s.blowupMap i ≫ s.structMap i = s.structMap (i + 1) := s.structMap_down (Nat.le_succ i)
      rw [hcomp] at key
      exact key
  exact hiso s.length le_rfl
end PositivityTheory.ResPlug.FromRes
