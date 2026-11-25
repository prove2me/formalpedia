-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.stalkId_eq_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:29:31.635823+00:00
-- url     : https://prove2.me/submissions/bb254fa8-91af-41ca-aa89-3d3205ef6d1a

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsBasicOpenCover
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_Monomial
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WMultB
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkIdEqMonomial
import Theorems.Thm_ReciprocityTheory_AnForm_R_WMult_mem_support_fromSpec_iff
import Theorems.Thm_ReciprocityTheory_AnForm_R_WMult_ord_isLocalization_eq_exponent
import Theorems.Thm_ReciprocityTheory_AnForm_R_WMult_stalkId_eq_map_germ
import Theorems.Thm_ReciprocityTheory_AnForm_R_eq_unit_mul_monomial
import Theorems.Thm_ReciprocityTheory_AnForm_R_prime_of_regular_params


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open AlgebraicGeometry CategoryTheory MvPolynomial
noncomputable section
variable {W : Scheme.{0}}
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution [IsNoetherian W] {Z G : W.IdealSheafData} (hG : FinalTheorems.EffCartier G)
    (hGZ : (G.support : Set W) ⊆ Z.support) (y : W) (U : W.affineOpens) (hy : y ∈ U.1) {n : ℕ}
    (f : Fin n → Γ(W, U.1)) (J : Finset (Fin n)) [IsRegularLocalRing (W.presheaf.stalk y)]
    (hrsp : FinalTheorems.Rsp (W.presheaf.stalk y) n (fun i => W.presheaf.germ U.1 y hy (f i)))
    (hZy : FinalTheorems.stalkId Z y = Ideal.span {∏ i ∈ J, W.presheaf.germ U.1 y hy (f i)})
    (σ : Fin n → Set W) (hσ : ∀ i ∈ J, IsBranch (Z.support : Set W) (f i) y (σ i)) :
    FinalTheorems.stalkId G y =
      Ideal.span {∏ i ∈ J, W.presheaf.germ U.1 y hy (f i) ^ ordAlong G (σ i)} := by
  classical
  have hU : IsAffineOpen U.1 := U.2
  let yU : U.1 := ⟨y, hy⟩
  let algY : Algebra Γ(W, U.1) (W.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk W.presheaf yU
  have hlocY : IsLocalization.AtPrime (W.presheaf.stalk y) (hU.primeIdealOf yU).asIdeal :=
    hU.isLocalization_stalk yU
  set Py := hU.primeIdealOf yU with hPy
  set f' : Fin n → W.presheaf.stalk y := fun i => W.presheaf.germ U.1 y hy (f i) with hf'

  obtain ⟨U', g, hyU', hg, hGU'⟩ := hG y
  set γ : W.presheaf.stalk y := W.presheaf.germ U'.1 y hyU' g with hγ
  have hGy : FinalTheorems.stalkId G y = Ideal.span {γ} := by
    rw [WMult.stalkId_eq_map_germ G y U' hyU', hGU', Ideal.map_span, Set.image_singleton]
  have hγ0 : γ ≠ 0 := by
    intro h0
    have hU' : IsAffineOpen U'.1 := U'.2
    let : Algebra Γ(W, U'.1) (W.presheaf.stalk y) :=
      TopCat.Presheaf.algebra_section_stalk W.presheaf (⟨y, hyU'⟩ : U'.1)
    have := hU'.isLocalization_stalk ⟨y, hyU'⟩
    obtain ⟨⟨c, hc⟩, hcg⟩ := (IsLocalization.map_eq_zero_iff
      (M := (hU'.primeIdealOf ⟨y, hyU'⟩).asIdeal.primeCompl) (S := W.presheaf.stalk y) g).mp h0
    have hc0 : c = 0 := (mul_right_mem_nonZeroDivisors_eq_zero_iff hg).mp hcg
    exact hc (by rw [hc0]; exact Ideal.zero_mem _)

  have hrad : (∏ i ∈ J, f' i) ∈ (Ideal.span {γ}).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro Q ⟨hQγ, hQ⟩
    have := hQ
    let P : PrimeSpectrum Γ(W, U.1) := ⟨Q.comap (W.presheaf.germ U.1 y hy).hom, inferInstance⟩
    have h1 : hU.fromSpec P ∈ (G.support : Set W) := by
      rw [WMult.mem_support_fromSpec_iff G U hU]
      show G.ideal U ≤ Q.comap (W.presheaf.germ U.1 y hy).hom
      rw [← Ideal.map_le_iff_le_comap, ← WMult.stalkId_eq_map_germ G y U hy, hGy]
      exact hQγ
    have h2 := hGZ h1
    rw [WMult.mem_support_fromSpec_iff Z U hU] at h2
    have h3 : FinalTheorems.stalkId Z y ≤ Q := by
      rw [WMult.stalkId_eq_map_germ Z y U hy]; exact Ideal.map_le_iff_le_comap.mpr h2
    rw [hZy] at h3
    exact h3 (Ideal.mem_span_singleton_self _)
  obtain ⟨u, m, hmJ, hγu⟩ := eq_unit_mul_monomial f' hrsp.1 hrsp.2 J hγ0 hrad

  have hord : ∀ i ∈ J, ordAlong G (σ i) = m i := by
    intro i hi
    obtain ⟨hCc, hyC, hirr, hηU, hηf⟩ := hσ i hi
    have hCm : Maximal (fun C => IsIrreducible C ∧ C ⊆ (Z.support : Set W)) (σ i) := hCc
    have hCcl : IsClosed (σ i) := by
      have h := hCm.eq_of_subset ⟨hirr.closure, closure_minimal hCm.1.2 Z.support.isClosed⟩
        subset_closure
      rw [h]; exact isClosed_closure
    have hgen : IsGenericPoint hirr.genericPoint (σ i) := by
      have := hirr.isGenericPoint_genericPoint_closure
      rwa [hCcl.closure_eq] at this
    set η := hirr.genericPoint with hη
    have hηy : η ⤳ y := hgen.specializes hyC
    let Pη := hU.primeIdealOf ⟨η, hηU⟩
    have hfromη : hU.fromSpec Pη = η := hU.fromSpec_primeIdealOf ⟨η, hηU⟩
    have hfromy : hU.fromSpec Py = y := hU.fromSpec_primeIdealOf yU
    have emb := hU.fromSpec.isOpenEmbedding
    have hspec : ∀ P Q : PrimeSpectrum Γ(W, U.1), hU.fromSpec P ⤳ hU.fromSpec Q ↔ P ≤ Q := by
      intro P Q
      rw [PrimeSpectrum.le_iff_specializes]
      exact emb.isInducing.specializes_iff
    have hle : Pη ≤ Py := (hspec _ _).mp (by rw [hfromη, hfromy]; exact hηy)
    have hfη : f i ∈ Pη.asIdeal := by
      have h' : η ∈ W.zeroLocus {f i} ∩ U.1 := ⟨hηf, hηU⟩
      rw [← hU.fromSpec_image_zeroLocus] at h'
      obtain ⟨Q, hQ, hQη⟩ := h'
      rw [← hfromη] at hQη
      have := emb.injective hQη
      subst this
      exact (PrimeSpectrum.mem_zeroLocus _ _).mp hQ (Set.mem_singleton _)
    have hpi : Prime (f' i) := prime_of_regular_params f' hrsp.1 hrsp.2 i
    have hQi : (Ideal.span {f' i}).IsPrime := (Ideal.span_singleton_prime hpi.ne_zero).mpr hpi
    let Pi : PrimeSpectrum Γ(W, U.1) :=
      ⟨(Ideal.span {f' i}).comap (algebraMap Γ(W, U.1) (W.presheaf.stalk y)), inferInstance⟩
    have hdisj : Disjoint (Py.asIdeal.primeCompl : Set Γ(W, U.1)) Pη.asIdeal :=
      Set.disjoint_left.mpr fun x hx hx' => hx ((show Pη.asIdeal ≤ Py.asIdeal from hle) hx')
    have hPiη : Pi ≤ Pη := by
      show (Ideal.span {f' i}).comap (algebraMap Γ(W, U.1) (W.presheaf.stalk y)) ≤ Pη.asIdeal
      calc _ ≤ (Pη.asIdeal.map (algebraMap Γ(W, U.1) (W.presheaf.stalk y))).comap
              (algebraMap Γ(W, U.1) (W.presheaf.stalk y)) := by
            apply Ideal.comap_mono
            rw [Ideal.span_le, Set.singleton_subset_iff]
            exact Ideal.mem_map_of_mem _ hfη
        _ = Pη.asIdeal := IsLocalization.under_map_of_isPrime_disjoint Py.asIdeal.primeCompl
              (W.presheaf.stalk y) Pη.isPrime hdisj
    have hζZ : hU.fromSpec Pi ∈ (Z.support : Set W) := by
      rw [WMult.mem_support_fromSpec_iff Z U hU]
      show Z.ideal U ≤ (Ideal.span {f' i}).comap (W.presheaf.germ U.1 y hy).hom
      rw [← Ideal.map_le_iff_le_comap, ← WMult.stalkId_eq_map_germ Z y U hy, hZy, Ideal.span_le,
        Set.singleton_subset_iff]
      exact Ideal.mem_span_singleton.mpr (Finset.dvd_prod_of_mem _ hi)
    have hζη : hU.fromSpec Pi ⤳ η := by rw [← hfromη]; exact (hspec _ _).mpr hPiη
    have hcl : closure {η} = σ i := hgen
    have hsub : σ i ⊆ closure {hU.fromSpec Pi} := by
      intro z hz
      rw [← hcl] at hz
      exact specializes_iff_closure_subset.mp hζη hz
    have hirrζ : IsIrreducible (closure {hU.fromSpec Pi}) := isIrreducible_singleton.closure
    have hsubZ : closure {hU.fromSpec Pi} ⊆ (Z.support : Set W) :=
      closure_minimal (Set.singleton_subset_iff.mpr hζZ) Z.support.isClosed
    have hCeq : σ i = closure {hU.fromSpec Pi} := hCm.eq_of_subset ⟨hirrζ, hsubZ⟩ hsub
    have hηζ : η ⤳ hU.fromSpec Pi := by
      rw [specializes_iff_mem_closure, hcl, hCeq]
      exact subset_closure (Set.mem_singleton _)
    have hηPi : Pη ≤ Pi := (hspec _ _).mp (by rw [hfromη]; exact hηζ)
    have hPeq : Pη.asIdeal =
        (Ideal.span {f' i}).comap (algebraMap Γ(W, U.1) (W.presheaf.stalk y)) :=
      congrArg PrimeSpectrum.asIdeal (le_antisymm hηPi hPiη)

    let T := Localization.AtPrime (Ideal.span {f' i})
    have hT : IsLocalization.AtPrime T
        ((Ideal.span {f' i}).comap (algebraMap Γ(W, U.1) (W.presheaf.stalk y))) :=
      IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        (M := Py.asIdeal.primeCompl) (S := W.presheaf.stalk y) (T := T) (Ideal.span {f' i})
    have hT' : IsLocalization Pη.asIdeal.primeCompl T := by
      have hsm : Pη.asIdeal.primeCompl =
          (Ideal.comap (algebraMap Γ(W, U.1) (W.presheaf.stalk y)) (Ideal.span {f' i})).primeCompl := by
        ext x; rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, hPeq]
      rw [hsm]; exact hT
    let ηU : U.1 := ⟨η, hηU⟩
    let algη : Algebra Γ(W, U.1) (W.presheaf.stalk η) :=
      TopCat.Presheaf.algebra_section_stalk W.presheaf ηU
    have hlocη : IsLocalization.AtPrime (W.presheaf.stalk η) Pη.asIdeal :=
      hU.isLocalization_stalk ηU
    let φ : W.presheaf.stalk η ≃ₐ[Γ(W, U.1)] T := IsLocalization.algEquiv Pη.asIdeal.primeCompl _ _
    let algYη : Algebra (W.presheaf.stalk y) (W.presheaf.stalk η) :=
      (φ.symm.toRingEquiv.toRingHom.comp (algebraMap (W.presheaf.stalk y) T)).toAlgebra
    have hlocYη : IsLocalization.AtPrime (W.presheaf.stalk η) (Ideal.span {f' i}) :=
      (IsLocalization.isLocalization_iff_of_ringEquiv (M := (Ideal.span {f' i}).primeCompl)
        (S := T) φ.symm.toRingEquiv).mp inferInstance
    have hgerm : ∀ a : Γ(W, U.1), W.presheaf.germ U.1 η hηU a =
        algebraMap (W.presheaf.stalk y) (W.presheaf.stalk η) (W.presheaf.germ U.1 y hy a) :=
by
      intro a
      have h1 := (φ.symm.commutes a).symm
      rw [IsScalarTower.algebraMap_apply Γ(W, U.1) (W.presheaf.stalk y) T] at h1
      exact h1
    have hGη : FinalTheorems.stalkId G η =
        Ideal.span {algebraMap (W.presheaf.stalk y) (W.presheaf.stalk η) γ} := by
      rw [WMult.stalkId_eq_map_germ G η U hηU]
      have hcomp : (W.presheaf.germ U.1 η hηU).hom =
          (algebraMap (W.presheaf.stalk y) (W.presheaf.stalk η)).comp
            (W.presheaf.germ U.1 y hy).hom :=
        RingHom.ext fun a => hgerm a
      rw [hcomp, ← Ideal.map_map, ← WMult.stalkId_eq_map_germ G y U hy, hGy, Ideal.map_span,
        Set.image_singleton]
    have hordS := WMult.ord_isLocalization_eq_exponent f' hrsp.1 hrsp.2 J u m i hi
      (W.presheaf.stalk η)
    have hlen : Module.length (W.presheaf.stalk η) (W.presheaf.stalk η ⧸ FinalTheorems.stalkId G η) =
        (m i : ℕ∞) := by
      rw [hGη, hγu]; exact hordS
    unfold ordAlong
    rw [dif_pos hirr, ← hη, hlen]
    exact ENat.toNat_natCast (m i)
  rw [hGy, hγu]
  have hprod : ∏ i ∈ J, f' i ^ m i = ∏ i ∈ J, f' i ^ ordAlong G (σ i) :=
    Finset.prod_congr rfl fun i hi => by rw [hord i hi]
  rw [hprod]
  exact Ideal.span_singleton_mul_left_unit u.isUnit _
end ReciprocityTheory.AnForm.R
