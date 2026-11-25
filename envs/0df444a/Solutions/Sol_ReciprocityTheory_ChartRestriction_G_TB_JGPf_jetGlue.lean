-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.JGPf.jetGlue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:46:47.096843+00:00
-- url     : https://prove2.me/submissions/b22d0ee2-062c-48d1-b4ca-e7032a4dfd79

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_JetGlue
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_JetGlue
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_JGPf_ext_of_fromSpecStalk
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_JGPf_comp_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.JGPf
universe u
namespace ReciprocityTheory.ChartRestriction.G.TB.JGPf
theorem _root_.solution : JetGlueSt := by
  intro S _ κ _ m X f g h
  apply ext_of_fromSpecStalk
  intro y
  classical
  have hy := y.isPrime
  let 𝔭 : Ideal S := y.asIdeal.comap (algebraMap S (JetRing S κ m))
  have : 𝔭.IsPrime := Ideal.comap_isPrime _ _
  let ψ := (Scheme.ΓSpecIso (CommRingCat.of (JetRing S κ m))).inv ≫
    (Spec (CommRingCat.of (JetRing S κ m))).presheaf.germ ⊤ y trivial
  have hM : ∀ a : Algebra.algebraMapSubmonoid (JetRing S κ m) 𝔭.primeCompl, IsUnit (ψ.hom a) := by
    rintro ⟨a, ⟨s, hs, rfl⟩⟩
    refine (Scheme.mem_basicOpen _ ((Scheme.ΓSpecIso (CommRingCat.of (JetRing S κ m))).inv.hom
      (algebraMap S (JetRing S κ m) s)) y trivial).1 ?_
    rw [basicOpen_eq_of_affine]
    exact (PrimeSpectrum.mem_basicOpen _ _).2 hs
  let φ := IsLocalization.lift (S := JetLoc S κ m 𝔭) hM
  have hfac : ψ = CommRingCat.ofHom (algebraMap (JetRing S κ m) (JetLoc S κ m 𝔭)) ≫ CommRingCat.ofHom φ := by
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    simp [φ]
  have e : (Spec (CommRingCat.of (JetRing S κ m))).fromSpecStalk y =
      Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom (algebraMap (JetRing S κ m) (JetLoc S κ m 𝔭))) := by
    rw [Spec.fromSpecStalk_eq, ← Spec.map_comp, ← hfac]
  rw [e]
  exact comp_eq _ _ f g (h 𝔭)
end ReciprocityTheory.ChartRestriction.G.TB.JGPf
