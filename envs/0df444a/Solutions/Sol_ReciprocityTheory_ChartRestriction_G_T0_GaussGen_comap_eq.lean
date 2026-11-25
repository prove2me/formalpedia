-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.GaussGen.comap_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:52:11.54137+00:00
-- url     : https://prove2.me/submissions/5a85e814-7715-4d9c-ad69-600019bee54b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtLeafSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussGenericHeight_GaussGenericStatements_GaussGenericLemmas_TranslationDomainMaps_MapDomainMemOfDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussGenericHeight_GaussGenericStatements_GaussGenericLemmas_TranslationDomainMaps_TranslSEquivApply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_sHom_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_translSEquiv_apply
import Theorems.Thm_BlockPoly_translEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] BlockPoly.translEquiv_apply


attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.GaussGen.translSEquiv_apply

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open ReciprocityTheory.ChartRestriction.G.T0.GaussGen
open MvPolynomial NumberField BlockPoly
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)) (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.GaussGen
theorem _root_.solution (hx1 : LeafSt.PlaceTrivialOrPositive 𝒜 d) (hx2 : LeafSt.AdmissibleValuationPrimeUnique 𝒜 d)
    (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (p : Ideal (KTp K d.D d.N)) (hp : p ∈ d.HtOne)
    (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (hw : w ∈ d.GoodP c p)
    (σ : KTp K d.D d.N ≃ₐ[K] KTp K d.D d.N)
    (τ : MvPolynomial (SVar d.D d.N) (Ω c) ≃ₐ[Ω c] MvPolynomial (SVar d.D d.N) (Ω c))
    (hc : ∀ t, τ (Pimg (d.jc c) (d.x c) t) = aeval (Pimg (d.jc c) (d.x c)) (σ (X t))) :
    p.comap σ = p := by
  let e : OmS (Ω c) d.D d.N ≃+* OmS (Ω c) d.D d.N :=
    IsFractionRing.ringEquivOfRingEquiv τ.toRingEquiv
  have he : ∀ r, e (algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N) r) =
      algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N) (τ r) :=
    fun r => IsFractionRing.ringEquivOfRingEquiv_algebraMap τ.toRingEquiv r
  have hτ : ∀ y : KTp K d.D d.N, τ (aeval (Pimg (d.jc c) (d.x c)) y) =
      aeval (Pimg (d.jc c) (d.x c)) (σ y) := by
    intro y
    have hcomp : ((τ : MvPolynomial (SVar d.D d.N) (Ω c) →ₐ[Ω c] _).restrictScalars K).comp
        (aeval (Pimg (d.jc c) (d.x c))) =
        (aeval (Pimg (d.jc c) (d.x c))).comp (σ : KTp K d.D d.N →ₐ[K] KTp K d.D d.N) := by
      apply MvPolynomial.algHom_ext
      intro t
      show τ (aeval (Pimg (d.jc c) (d.x c)) (X t)) = aeval (Pimg (d.jc c) (d.x c)) (σ (X t))
      rw [aeval_X]
      exact hc t
    exact DFunLike.congr_fun hcomp y
  have hsH : ∀ y, d.sH c y = algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N)
      (aeval (Pimg (d.jc c) (d.x c)) y) := fun y => sHom_eq (d.jc c) (d.x c) y
  have hw' : ∀ y, (w.comap (e : OmS (Ω c) d.D d.N →+* OmS (Ω c) d.D d.N)) (d.sH c y) =
      w (d.sH c (σ y)) := by
    intro y
    show w (e (d.sH c y)) = w (d.sH c (σ y))
    rw [hsH, hsH, he, hτ]
  have hWres : d.Wres c (w.comap (e : OmS (Ω c) d.D d.N →+* OmS (Ω c) d.D d.N)) = d.Wres c w := by
    refine AddValuation.ext fun a => ?_
    show w (e (algebraMap (Ω c) (OmS (Ω c) d.D d.N) a)) = w (algebraMap (Ω c) (OmS (Ω c) d.D d.N) a)
    rw [IsScalarTower.algebraMap_apply (Ω c) (MvPolynomial (SVar d.D d.N) (Ω c))
      (OmS (Ω c) d.D d.N), he, AlgEquiv.commutes]
  have hpσ : p.comap σ ∈ d.HtOne := by
    refine ⟨?_, ?_⟩
    · have := hp.1
      exact Ideal.comap_isPrime σ p
    · exact (RingEquiv.height_comap (σ : KTp K d.D d.N ≃+* KTp K d.D d.N) p).trans hp.2
  have hmem : w.comap (e : OmS (Ω c) d.D d.N →+* OmS (Ω c) d.D d.N) ∈ d.GoodP c (p.comap σ) := by
    obtain ⟨⟨⟨hfin, π, hπ⟩, hov⟩, a, ha, hwa⟩ := hw
    refine ⟨⟨⟨fun z hz => ?_, e.symm π, ?_⟩, fun y => ?_⟩, a, ha, ?_⟩
    · show w (e z) ≠ ⊤
      exact hfin _ ((map_ne_zero e).mpr hz)
    · show w (e (e.symm π)) = 1
      rw [RingEquiv.apply_symm_apply]
      exact hπ
    · rw [hw', Ideal.mem_comap]
      exact hov (σ y)
    · rw [hWres]
      exact hwa
  rcases hx1 hd h c p hp w hw.1 with h0 | ⟨hadm, htriv, -⟩
  · obtain ⟨a, ha, hwa⟩ := hw.2
    exact absurd (h0 a ha) hwa
  · have m1 : p.comap σ ∈ {q | q ∈ d.HtOne ∧ ∃ w₁ ∈ d.GoodP c q, d.Wres c w₁ = d.Wres c w} :=
      ⟨hpσ, _, hmem, hWres⟩
    have m2 : p ∈ {q | q ∈ d.HtOne ∧ ∃ w₁ ∈ d.GoodP c q, d.Wres c w₁ = d.Wres c w} :=
      ⟨hp, w, hw, rfl⟩
    exact hx2 hd h c (d.Wres c w) hadm htriv m1 m2
end ReciprocityTheory.ChartRestriction.G.T0.GaussGen
