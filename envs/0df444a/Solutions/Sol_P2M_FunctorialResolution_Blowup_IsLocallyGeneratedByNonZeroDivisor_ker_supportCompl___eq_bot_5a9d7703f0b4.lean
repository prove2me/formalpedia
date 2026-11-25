-- Prove2me | solution 1 for P2M_FunctorialResolution_Blowup_IsLocallyGeneratedByNonZeroDivisor_ker_supportCompl___eq_bot_5a9d7703f0b4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:49:05.455396+00:00
-- url     : https://prove2.me/submissions/3513bfbd-e9df-4c10-92f4-c0b19461d198

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_OrderReduction_IsomorphismTransport
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_ClosedEmbedding_IsoBlowupPushforward
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_section_eq_zero_of_locally_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
private theorem map_homOfLE_map_homOfLE {X : Scheme.{u}} {V V' V'' : X.Opens} (h1 : V' ≤ V) (h2 : V'' ≤ V')
    (s : Γ(X, V)) :
    X.presheaf.map (homOfLE h2).op (X.presheaf.map (homOfLE h1).op s)
      = X.presheaf.map (homOfLE (h2.trans h1)).op s := by
  have hcomp : X.presheaf.map (homOfLE h1).op ≫ X.presheaf.map (homOfLE h2).op
      = X.presheaf.map (homOfLE (h2.trans h1)).op := by
    rw [← Functor.map_comp]
    rfl
  exact congrArg (fun φ : Γ(X, V) ⟶ Γ(X, V'') => (ConcreteCategory.hom φ) s) hcomp
private theorem map_eq_zero_of_app_ι_eq_zero {X : Scheme.{u}} (W V V' : X.Opens) (s : Γ(X, V))
    (hs : (W.ι.app V).hom s = 0) (h1 : V' ≤ V) (h2 : ∀ y : ↥X, y ∈ V' → y ∈ W) :
    X.presheaf.map (homOfLE h1).op s = 0 := by
  have hT : W.ι ''ᵁ W.ι ⁻¹ᵁ V ≤ V := by
    rintro y ⟨z, hz, rfl⟩
    exact hz
  have hle : V' ≤ W.ι ''ᵁ W.ι ⁻¹ᵁ V := by
    intro y hy
    exact ⟨⟨y, h2 y hy⟩, h1 hy, rfl⟩
  have hzero : X.presheaf.map (homOfLE hT).op s = 0 := by
    rw [Scheme.Opens.ι_app] at hs
    exact hs
  rw [← map_homOfLE_map_homOfLE hT hle s, hzero, map_zero]
private theorem algebraMap_basicOpen {X : Scheme.{u}} {U : X.Opens} (f : Γ(X, U)) (t : Γ(X, U)) :
    algebraMap Γ(X, U) Γ(X, X.basicOpen f) t
      = X.presheaf.map (homOfLE (X.basicOpen_le f)).op t := rfl
private theorem notMem_support_of_mem_basicOpen {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens)
    (f : Γ(X, U.1)) (hf : f ∈ I.ideal U) (y : ↥X) (hy : y ∈ X.basicOpen f) :
    y ∉ I.support := by
  intro hmem
  have h1 : y ∈ I.supportSet := hmem
  rw [Scheme.IdealSheafData.mem_supportSet_iff] at h1
  have h2 := h1 U
  rw [Scheme.mem_zeroLocus_iff] at h2
  exact h2 f hf hy
private theorem map_basicOpen_eq_zero_of_app_ι_eq_zero {X : Scheme.{u}} (W V U₀ : X.Opens)
    (hU₀ : IsAffineOpen U₀)
    (s : Γ(X, V)) (hs : (W.ι.app V).hom s = 0)
    (f : Γ(X, U₀)) (hf : f ∈ nonZeroDivisors Γ(X, U₀))
    (hWf : ∀ y : ↥X, y ∈ X.basicOpen f → y ∈ W)
    (b : Γ(X, U₀)) (hbV : X.basicOpen b ≤ V) :
    X.presheaf.map (homOfLE hbV).op s = 0 := by
  have hAaff : IsAffineOpen (X.basicOpen b) := hU₀.basicOpen b
  have := hU₀.isLocalization_basicOpen b
  have hAU₀ : X.basicOpen b ≤ U₀ := X.basicOpen_le b
  have hgnzd : X.presheaf.map (homOfLE hAU₀).op f ∈ nonZeroDivisors Γ(X, X.basicOpen b) := by
    have hq : X.presheaf.map (homOfLE hAU₀).op f
        = algebraMap Γ(X, U₀) Γ(X, X.basicOpen b) f := rfl
    rw [hq]
    exact IsLocalization.nonZeroDivisors_le_comap (Submonoid.powers b) Γ(X, X.basicOpen b) hf
  have hbg : X.basicOpen (X.presheaf.map (homOfLE hAU₀).op f)
      = X.basicOpen b ⊓ X.basicOpen f := by
    rw [Scheme.basicOpen_res]
  have hgV : X.basicOpen (X.presheaf.map (homOfLE hAU₀).op f) ≤ V :=
    (X.basicOpen_le _).trans hbV
  have hres : X.presheaf.map (homOfLE hgV).op s = 0 := by
    refine map_eq_zero_of_app_ι_eq_zero W V _ s hs hgV ?_
    intro y hy
    rw [hbg] at hy
    exact hWf y hy.2
  have := hAaff.isLocalization_basicOpen (X.presheaf.map (homOfLE hAU₀).op f)
  have hres' : algebraMap Γ(X, X.basicOpen b)
      Γ(X, X.basicOpen (X.presheaf.map (homOfLE hAU₀).op f))
      (X.presheaf.map (homOfLE hbV).op s) = 0 := by
    rw [algebraMap_basicOpen, map_homOfLE_map_homOfLE]
    exact hres
  obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff
    (Submonoid.powers (X.presheaf.map (homOfLE hAU₀).op f))
    Γ(X, X.basicOpen (X.presheaf.map (homOfLE hAU₀).op f))
    (X.presheaf.map (homOfLE hbV).op s)).mp hres'
  obtain ⟨n, hn⟩ := m.2
  have hmem : (m : Γ(X, X.basicOpen b)) ∈ nonZeroDivisors Γ(X, X.basicOpen b) := by
    rw [← hn]
    exact pow_mem hgnzd n
  refine (mem_nonZeroDivisors_iff.mp hmem).1 (X.presheaf.map (homOfLE hbV).op s) ?_
  exact hm
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
namespace _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor
theorem _root_.solution {X : Scheme.{u}} {I : X.IdealSheafData}
    (h : FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor I) :
    (Scheme.Opens.ι (X := X) I.support.compl).ker = ⊥ := by
  refine le_antisymm (fun U => ?_) bot_le
  intro s hs
  have hs' : s ∈ RingHom.ker ((Scheme.Opens.ι (X := X) I.support.compl).app U.1).hom :=
    Scheme.IdealSheafData.ideal_ofIdeals_le _ U hs
  rw [show (⊥ : X.IdealSheafData).ideal U = ⊥ from by simp, Ideal.mem_bot]
  refine EmbeddedResolution.section_eq_zero_of_locally_zero U.1 s ?_
  intro x hx
  obtain ⟨U₀, f, hxU₀, hfnzd, hIf⟩ := h x
  obtain ⟨a, b, hab, hxa⟩ := exists_basicOpen_le_affine_inter U.2 U₀.2 x ⟨hx, hxU₀⟩
  have hbV : X.basicOpen b ≤ U.1 := hab ▸ X.basicOpen_le a
  refine ⟨X.basicOpen b, hbV, hab ▸ hxa, ?_⟩
  refine _root_.FunctorialResolution.EmbeddedResolution.map_basicOpen_eq_zero_of_app_ι_eq_zero I.support.compl U.1 U₀.1 U₀.2 s
    (RingHom.mem_ker.mp hs') f hfnzd ?_ b hbV
  intro y hy
  show y ∉ I.support
  refine _root_.FunctorialResolution.EmbeddedResolution.notMem_support_of_mem_basicOpen I U₀ f ?_ y hy
  rw [hIf]
  exact Ideal.mem_span_singleton_self f
end _root_.FunctorialResolution.Blowup.IsLocallyGeneratedByNonZeroDivisor
end FunctorialResolution.EmbeddedResolution
