-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.tauF_sHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:36:46.089932+00:00
-- url     : https://prove2.me/submissions/d4ffb144-db17-41ce-80ac-f0670b64d357

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ScaleMultiHomogeneous
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_scaleEquiv_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_scaleEquiv_C
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_scale_sImg_expr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_algebraMap_K_OmS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial
section Scale
variable {S σ : Type*} [CommRing S]
end Scale
section Blocks
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ}
end Blocks
section Norm
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ}
private theorem tauF_algebraMap' (b : Fin (D + 1)) (u : Kˣ)
    (q : MvPolynomial (SVar D N) Ω) :
    tauF (Ω := Ω) (D := D) (N := N) b u (algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N) q) =
      algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N)
        (scaleEquiv (InBlock b) (Units.map (algebraMap K Ω).toMonoidHom u) q) := by
  unfold tauF
  first
    | (rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]; rfl)
    | exact IsLocalization.ringEquivOfRingEquiv_eq _ _
end Norm
namespace Data
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (NumberField.RingOfIntegers K) (A c)]
variable (d : Data K ι Ω WT A)
end Data
end ReciprocityTheory.ChartRestriction.G.T0
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution (b : Fin (D + 1)) (hb : b ≠ 0) (u : Kˣ) (j₀ : Fin (N + 1)) (x : Fin N → Ω)
    (F : MvPolynomial (TVar D N) K) :
    tauF b u (sHom j₀ x F) = sHom j₀ x (sigP b u F) := by
  induction F using MvPolynomial.induction_on
  next a =>
    have e1 : (sHom (K := K) (Ω := Ω) (D := D) (N := N) j₀ x) (C a) =
        algebraMap K (OmS Ω D N) a :=
      (sHom (K := K) (Ω := Ω) (D := D) (N := N) j₀ x).commutes a
    have e2 : sigP (K := K) (D := D) (N := N) b u (C a) = C a := scaleEquiv_C _ _ _
    rw [e2, e1, algebraMap_K_OmS, tauF_algebraMap', scaleEquiv_C]
  next p q hp hq =>
    simp only [map_add, hp, hq]
  next p v hp =>
    simp only [map_mul, hp]
    congr 1
    have hs : ∀ w : TVar D N, (sHom (K := K) (Ω := Ω) (D := D) (N := N) j₀ x) (X w) =
        sImg j₀ x w := fun w => MvPolynomial.aeval_X _ _
    have e2 : sigP (K := K) (D := D) (N := N) b u (X v) =
        if v.1 = b then C (u : K) * X v else X v := scaleEquiv_X _ _ _
    have e3 : (sHom (K := K) (Ω := Ω) (D := D) (N := N) j₀ x) (C (u : K)) =
        algebraMap K (OmS Ω D N) (u : K) :=
      (sHom (K := K) (Ω := Ω) (D := D) (N := N) j₀ x).commutes (u : K)
    rw [e2, hs, sImg, tauF_algebraMap', scale_sImg_expr b hb _ j₀ x v]
    by_cases hv : v.1 = b
    · rw [if_pos hv]
      try rw [if_pos hv]
      simp only [map_mul]
      rw [hs, sImg, e3, algebraMap_K_OmS]
      rfl
    · rw [if_neg hv]
      try rw [if_neg hv]
      rw [one_mul, hs, sImg]
end ReciprocityTheory.ChartRestriction.G.T0
