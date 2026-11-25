-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.evalAtPoint_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:29:06.793856+00:00
-- url     : https://prove2.me/submissions/9cf1ee2e-8edc-4179-bc74-4751951cf74a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SacSuccAbove
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_sH_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_evP_sHp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_KTtoS_alg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_omS_finite


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
include hd h hpt
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (P : Ω c →+* ℂ) (hP : P ∈ d.ST c sg (fun i j => pt (i.succ, j))) :
    Function.Injective (d.evP c P pt) := by
  obtain ⟨hPT, hPeq⟩ := hP
  have hcomp : (d.evP c P pt).comp (d.sHp c).toRingHom = eval₂Hom sg pt :=
    RingHom.ext fun q => d.evP_sHp c sg pt hd P hPT hPeq q
  rw [injective_iff_map_eq_zero]
  intro F hF
  by_contra hF0
  letI alg1 : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  haveI := (d.omS_finite hd h c).1
  letI alg2 : Algebra (KTp K d.D d.N) (OmS (Ω c) d.D d.N) := (d.sH c).toRingHom.toAlgebra
  haveI : IsScalarTower (KTp K d.D d.N) (KTf K d.D d.N) (OmS (Ω c) d.D d.N) :=
    IsScalarTower.of_algebraMap_eq fun q => (d.KTtoS_alg h c q).symm

  have halg : IsAlgebraic (KTf K d.D d.N)
      (algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N) F) :=
    Algebra.IsAlgebraic.isAlgebraic _
  rw [← IsFractionRing.isAlgebraic_iff (KTp K d.D d.N) (KTf K d.D d.N)] at halg
  obtain ⟨q, hq0, hq⟩ := halg
  have e : (algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N)).comp
      (d.sHp c).toRingHom = algebraMap (KTp K d.D d.N) (OmS (Ω c) d.D d.N) :=
    RingHom.ext fun r => (d.sH_eq c r).symm
  have hq' : Polynomial.eval₂ (d.sHp c).toRingHom F q = 0 := by
    apply IsFractionRing.injective (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N)
    rw [map_zero, Polynomial.hom_eval₂, e, ← Polynomial.aeval_def, hq]

  obtain ⟨q', hqq, hndvd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd q hq0 0
  simp only [map_zero, sub_zero] at hqq hndvd
  rw [Polynomial.X_dvd_iff] at hndvd
  rw [hqq, Polynomial.eval₂_mul, Polynomial.eval₂_X_pow] at hq'
  have hq'' : Polynomial.eval₂ (d.sHp c).toRingHom F q' = 0 :=
    (mul_eq_zero.mp hq').resolve_left (pow_ne_zero _ hF0)
  have h3 := congrArg (d.evP c P pt) hq''
  rw [Polynomial.hom_eval₂, map_zero, hF, hcomp, Polynomial.eval₂_at_zero] at h3
  exact hpt _ hndvd h3
end ReciprocityTheory.ChartRestriction.G.T0.Data
