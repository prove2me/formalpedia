-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.emb_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:29:26.634139+00:00
-- url     : https://prove2.me/submissions/9506a4ee-e1be-49f5-9417-ca3c738b2789

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SacSuccAbove
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_sac_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_sac_succAbove
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_sH_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_algC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_KTtoS_alg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
variable (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (sg : K →+* ℂ) (pt : TVar d.D d.N → ℂ)
  (hpt : ∀ q : MvPolynomial (TVar d.D d.N) K, q ≠ 0 → eval₂ sg pt q ≠ 0)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (σ₁ σ₂ : OmS (Ω c) d.D d.N →+* ℂ) (h₁ : σ₁.comp (d.KTtoS h c) = tauPev sg pt hpt)
    (h₂ : σ₂.comp (d.KTtoS h c) = tauPev sg pt hpt)
    (he : σ₁.comp (algebraMap (Ω c) _) = σ₂.comp (algebraMap (Ω c) _)) : σ₁ = σ₂ := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors (MvPolynomial (SVar d.D d.N) (Ω c)))
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply]
    rw [d.algC c a]
    exact RingHom.congr_fun he a
  · intro v
    have hs : ∀ p, σ₁ (d.sH c (X p)) = σ₂ (d.sH c (X p)) := by
      intro p
      rw [← d.KTtoS_alg h c, ← RingHom.comp_apply, h₁, ← h₂, RingHom.comp_apply]
    simp only [RingHom.comp_apply]
    rcases v with ⟨⟩ | ⟨i, k⟩
    · have h0 := hs (0, d.jc c)
      simpa [d.sH_eq, sHp, pImg, sac_self] using h0
    · have h0 := hs (i, (d.jc c).succAbove k)
      simpa [d.sH_eq, sHp, pImg, sac_succAbove] using h0
end ReciprocityTheory.ChartRestriction.G.T0.Data
