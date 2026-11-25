-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_normalOpenMapping_local_fin_e3b173e5219f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:07:07.703834+00:00
-- url     : https://prove2.me/submissions/cef9311d-ce67-429f-8546-d05545f94f66

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLinearNoetherNormalization
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalLocallyIrreducible
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolomorphicIsolatedFibreOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalOpenMapping
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalOpenMapping
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eval_pullback_eq_33c6b9794aef
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_eval_ne_zero_of_mem_nhds_2a51585cbfc4

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Topology Metric Matrix
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution
    (hNLI : NormalLocallyIrreducible.Statement)
    (hLNN : GroundTheory.Heights₂.Heights.ComplexSets.LinearNoetherNormalization.Statement)
    (hFB : GroundTheory.Heights₂.Heights.ComplexSets.FibreBound.Statement)
    (hDC : GroundTheory.Heights₂.Heights.ComplexSets.DiscriminantCover.Statement)
    (hIFO : HolomorphicIsolatedFibreOpen.Statement)
    {n k : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) (U : Set (Fin k → ℂ)) (φ : (Fin k → ℂ) → Fin n → ℂ)
    (hI : I.IsPrime) (hic : IsIntegrallyClosed (MvPolynomial (Fin n) ℂ ⧸ I))
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) = (k : ℕ)) (hU : IsOpen U)
    (hφ : DifferentiableOn ℂ φ U) (hinj : Set.InjOn φ U) (hmaps : Set.MapsTo φ U (zeroSetIn I))
    (u₀ : Fin k → ℂ) (hu₀ : u₀ ∈ U) :
    ∃ B : Set (Fin n → ℂ), IsOpen B ∧ φ u₀ ∈ B ∧ zeroSetIn I ∩ B ⊆ φ '' U := by
  classical

  obtain ⟨A, hA⟩ := hLNN n k I hdim
  obtain ⟨P, hP0, hPcov⟩ := hDC n k I A hI hdim hA
  set X := zeroSetIn I with hXdef
  set Lc : (Fin n → ℂ) →L[ℂ] (Fin k → ℂ) := LinearMap.toContinuousLinearMap (Matrix.mulVecLin A) with hLcdef
  have hLcA : ∀ z, Lc z = A *ᵥ z := fun z => rfl
  set w₀ := φ u₀ with hw₀
  set a₀ := A *ᵥ w₀ with ha₀
  set g : (Fin k → ℂ) → Fin k → ℂ := fun v => A *ᵥ φ v with hg
  have hgd : DifferentiableOn ℂ g U := Lc.differentiable.comp_differentiableOn hφ
  have hw₀X : w₀ ∈ X := hmaps hu₀

  have hfin : (GroundTheory.Heights₂.Heights.ComplexSets.fibre I A a₀).Finite := (hFB n k I A hI hdim hA a₀).2.1
  set W₀ : Set (Fin n → ℂ) := ((GroundTheory.Heights₂.Heights.ComplexSets.fibre I A a₀) \ {w₀})ᶜ with hW₀
  have hW₀o : IsOpen W₀ := (hfin.subset Set.sdiff_subset).isClosed.isOpen_compl
  have hw₀W₀ : w₀ ∈ W₀ := fun h => h.2 rfl
  have hφc : ContinuousAt φ u₀ := (hφ.differentiableAt (hU.mem_nhds hu₀)).continuousAt

  obtain ⟨r, hr0, hrU⟩ : ∃ r > 0, closedBall u₀ r ⊆ U ∩ φ ⁻¹' W₀ :=
    Metric.nhds_basis_closedBall.mem_iff.1
      (Filter.inter_mem (hU.mem_nhds hu₀) (hφc.preimage_mem_nhds (hW₀o.mem_nhds hw₀W₀)))
  set K := closedBall u₀ r with hK
  set V := ball u₀ r with hV
  have hKU : K ⊆ U := fun v hv => (hrU hv).1
  have hKc : IsCompact K := isCompact_closedBall u₀ r
  have hφK : ContinuousOn φ K := hφ.continuousOn.mono hKU
  have hgK : ContinuousOn g K := Lc.continuous.comp_continuousOn hφK
  have hVK : V ⊆ K := ball_subset_closedBall
  have hiso : ∀ v ∈ K, g v = a₀ → v = u₀ := by
    intro v hv hgv
    have h1 : φ v ∈ GroundTheory.Heights₂.Heights.ComplexSets.fibre I A a₀ := ⟨hmaps (hKU hv), hgv⟩
    have h3 : φ v = w₀ := by
      by_contra hne
      exact (hrU hv).2 ⟨h1, hne⟩
    exact hinj (hKU hv) hu₀ h3

  have hSK : sphere u₀ r ⊆ K := sphere_subset_closedBall
  have hgS : IsCompact (g '' sphere u₀ r) := (isCompact_sphere u₀ r).image_of_continuousOn (hgK.mono hSK)
  have ha₀S : a₀ ∉ g '' sphere u₀ r := by
    rintro ⟨v, hv, hgv⟩
    have h := hiso v (hSK hv) hgv
    rw [h, mem_sphere, dist_self] at hv
    exact hr0.ne hv
  obtain ⟨ε, hε, hεS⟩ : ∃ ε > 0, ball a₀ ε ⊆ (g '' sphere u₀ r)ᶜ :=
    Metric.isOpen_iff.1 hgS.isClosed.isOpen_compl a₀ ha₀S

  have hcl : ∀ x, A *ᵥ x ∈ ball a₀ ε → x ∈ closure (φ '' V) → x ∈ φ '' V := by
    intro x hxD hx
    have hKimg : IsCompact (φ '' K) := hKc.image_of_continuousOn hφK
    obtain ⟨v, hvK, rfl⟩ : x ∈ φ '' K :=
      hKimg.isClosed.closure_subset (closure_mono (Set.image_mono hVK) hx)
    refine ⟨v, ?_, rfl⟩
    by_contra hvV
    have hvS : v ∈ sphere u₀ r := by
      rw [mem_sphere]
      rw [mem_closedBall] at hvK
      rw [mem_ball, not_lt] at hvV
      exact le_antisymm hvK hvV
    exact hεS hxD ⟨v, hvS, rfl⟩

  set h := GroundTheory.Heights₂.Heights.ComplexSets.pullback A P with hh
  have hevh : ∀ z, eval z h = eval (A *ᵥ z) P := fun z => eval_pullback_eq A P z
  have hhI : h ∉ I := by
    intro hmem
    apply hP0
    apply hA.injective
    rw [map_zero]
    show (Ideal.Quotient.mkₐ ℂ I) h = 0
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact hmem
  have hND : (fun z => A *ᵥ z) ⁻¹' ball a₀ ε ∈ 𝓝 w₀ :=
    Lc.continuous.continuousAt.preimage_mem_nhds (ball_mem_nhds a₀ hε)
  obtain ⟨B, hBo, hw₀B, hBD, hconn, hdense⟩ := hNLI (Fin n) I h w₀ hI hic hhI hw₀X _ hND
  set C := (X ∩ B) \ {z | eval z h = 0} with hC

  have hop : ∀ v ∈ V, eval (g v) P ≠ 0 →
      ∃ W' : Set (Fin n → ℂ), IsOpen W' ∧ φ v ∈ W' ∧ X ∩ W' ⊆ φ '' V := by
    intro v hv hPv
    have hvU : v ∈ U := hKU (hVK hv)
    have hfib : φ v ∈ GroundTheory.Heights₂.Heights.ComplexSets.fibre I A (g v) := ⟨hmaps hvU, rfl⟩
    obtain ⟨-, -, hsec⟩ := hPcov (g v) hPv
    obtain ⟨O, W, s, hOo, hgvO, hWo, hvW, -, -, hsA, hXW⟩ := hsec (φ v) hfib
    have hφV : ContinuousOn φ V := hφK.mono hVK
    have hgV : ContinuousOn g V := hgK.mono hVK
    set V1 := (V ∩ φ ⁻¹' W) ∩ (V ∩ g ⁻¹' O) with hV1
    have hV1o : IsOpen V1 :=
      (hφV.isOpen_inter_preimage isOpen_ball hWo).inter (hgV.isOpen_inter_preimage isOpen_ball hOo)
    have hv1 : v ∈ V1 := ⟨⟨hv, hvW⟩, ⟨hv, hgvO⟩⟩
    have hrep : ∀ v' ∈ V1, φ v' = s (g v') := by
      intro v' hv'
      have hmem : φ v' ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet I ∩ W :=
        ⟨hmaps (hKU (hVK hv'.1.1)), hv'.1.2⟩
      rw [hXW] at hmem
      obtain ⟨o, ho, hso⟩ := hmem
      have hgo : g v' = o := by
        show A *ᵥ φ v' = o
        rw [← hso]
        exact hsA o ho
      rw [hgo, hso]
    have hginj : Set.InjOn g V1 := by
      intro v1 h1 v2 h2 he
      apply hinj (hKU (hVK h1.1.1)) (hKU (hVK h2.1.1))
      rw [hrep v1 h1, hrep v2 h2, he]
    have hgV1d : DifferentiableOn ℂ g V1 := hgd.mono (fun x hx => hKU (hVK hx.1.1))
    have himo : IsOpen (g '' V1) := by
      rw [isOpen_iff_mem_nhds]
      rintro _ ⟨v', hv', rfl⟩
      exact hIFO k V1 g v' hV1o hv' hgV1d
        ⟨V1, hV1o.mem_nhds hv', fun x _ hx he => hginj hx hv' he⟩ V1 (hV1o.mem_nhds hv')
    refine ⟨W ∩ (fun z => A *ᵥ z) ⁻¹' (g '' V1), hWo.inter (himo.preimage Lc.continuous),
      ⟨hvW, v, hv1, rfl⟩, ?_⟩
    rintro z ⟨hzX, hzW, v', hv', hv'z⟩
    have hmem : z ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet I ∩ W := ⟨hzX, hzW⟩
    rw [hXW] at hmem
    obtain ⟨o, ho, rfl⟩ := hmem
    have hgo : g v' = o := hv'z.trans (hsA o ho)
    exact ⟨v', hv'.1.1, by rw [hrep v' hv', hgo]⟩

  set Uo : Set (Fin n → ℂ) := ⋃₀ {W | IsOpen W ∧ X ∩ W ⊆ φ '' V} with hUo
  have hUoo : IsOpen Uo := isOpen_sUnion (fun W hW => hW.1)
  have hUoX : X ∩ Uo ⊆ φ '' V := by
    rintro z ⟨hzX, W, hW, hzW⟩
    exact hW.2 ⟨hzX, hzW⟩
  have hCX : ∀ z ∈ C, z ∈ X ∧ z ∈ B ∧ eval (A *ᵥ z) P ≠ 0 :=
    fun z hz => ⟨hz.1.1, hz.1.2, fun h0 => hz.2 ((hevh z).trans h0)⟩
  have hCin : ∀ z ∈ C, z ∈ φ '' V → z ∈ Uo := by
    rintro z hz ⟨v, hv, rfl⟩
    obtain ⟨W', hW'o, hvW', hW'⟩ := hop v hv (hCX _ hz).2.2
    exact ⟨W', ⟨hW'o, hW'⟩, hvW'⟩

  obtain ⟨z₁, hz₁C, hz₁V⟩ : ∃ z ∈ C, z ∈ φ '' V := by
    have hV2 : V ∩ φ ⁻¹' B ∈ 𝓝 u₀ :=
      Filter.inter_mem (ball_mem_nhds u₀ hr0) (hφc.preimage_mem_nhds (hBo.mem_nhds hw₀B))
    have himg : g '' (V ∩ φ ⁻¹' B) ∈ 𝓝 a₀ :=
      hIFO k U g u₀ hU hu₀ hgd ⟨K, closedBall_mem_nhds u₀ hr0, fun v hv _ he => hiso v hv he⟩ _ hV2
    obtain ⟨y, ⟨v, hv, rfl⟩, hy⟩ := exists_eval_ne_zero_of_mem_nhds hP0 himg
    exact ⟨φ v, ⟨⟨hmaps (hKU (hVK hv.1)), hv.2⟩, fun h0 => hy ((hevh _).symm.trans h0)⟩, v, hv.1, rfl⟩

  have hCsub : C ⊆ Uo := by
    have hsplit : C ⊆ Uo ∪ (closure (φ '' V))ᶜ := by
      intro z hz
      by_cases hzc : z ∈ closure (φ '' V)
      · exact Or.inl (hCin z hz (hcl z (hBD (hCX z hz).2.1) hzc))
      · exact Or.inr hzc
    by_contra hns
    obtain ⟨z, hzC, hzU⟩ := Set.not_subset.1 hns
    obtain ⟨z', hz'C, hz'U, hz'c⟩ := hconn Uo (closure (φ '' V))ᶜ hUoo isClosed_closure.isOpen_compl hsplit
      ⟨z₁, hz₁C, hCin z₁ hz₁C hz₁V⟩ ⟨z, hzC, (hsplit hzC).resolve_left hzU⟩
    exact hz'c (subset_closure (hUoX ⟨(hCX z' hz'C).1, hz'U⟩))

  refine ⟨B, hBo, hw₀B, ?_⟩
  intro x hx
  have hxcl : x ∈ closure (φ '' V) :=
    closure_mono (fun z hz => hUoX ⟨(hCX z hz).1, hCsub hz⟩) (hdense hx)
  obtain ⟨v, hv, hvx⟩ := hcl x (hBD hx.2) hxcl
  exact ⟨v, hKU (hVK hv), hvx⟩
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
