-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L3.exists_isom_loc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:46:35.831104+00:00
-- url     : https://prove2.me/submissions/643ecece-bc43-4c20-9d8a-96bf5f304bea

import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_GmapLocEqOfFrame
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_ExistsIsomLoc
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_exists_isom_frame
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_gmap_loc_eq_of_frame
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_isHermSemilocal_locRing
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_isSelfDualMod_loc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_isTotPosDef_of_ortho
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L3
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace ReciprocityTheory.ChartRestriction.L3
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    {I : Submodule (𝓞 K) V} {n : ℕ} (hI : Formalism.HermitianLatticesTheory.IsOrthoLattice h I n)
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) (p : Ideal (𝓞 K)) (hp : p.IsMaximal)
    (hu : Formalism.HermitianLatticesTheory.IsUnimodularAt h p L) :
    ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g (Formalism.HermitianLatticesTheory.loc (K := K) p I) = Formalism.HermitianLatticesTheory.loc (K := K) p L := by
  have hpos := isTotPosDef_of_ortho hK hs hI
  have hd : ∀ x, h x x = 0 → x = 0 := by
    intro x hx
    by_contra hne
    obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have := hpos x hne φ
    rw [hx, map_zero] at this
    simp at this
  obtain ⟨e, -, hspan, rfl, he⟩ := hI
  obtain ⟨g, hg, hge⟩ := WA.exists_isom_frame (WA.isHermSemilocal_locRing hK hp) hs hd
    (WA.isSelfDualMod_loc hL hp.isPrime hu) e he
  exact ⟨g, hg, WA.gmap_loc_eq_of_frame hp.isPrime hu hspan he hg hge⟩
end ReciprocityTheory.ChartRestriction.L3
