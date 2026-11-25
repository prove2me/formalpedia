-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SliceLocalDimUpperZariski_quotient_dim_le_one_99e9070a5a50
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:29:45.626078+00:00
-- url     : https://prove2.me/submissions/910bf0a4-3858-4825-95d5-4d33e51d39ef

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceLocalDimUpperZariski
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionsContainOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjHomInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsExists
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLeadIdealDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLinearFormCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHomogDimZeroPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceLocalDimUpperZariski
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceLocalDimUpperZariski_ringKrullDim_le_of_finite_37324c18be2a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Matrix ComplexSets
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace SliceLocalDimUpperZariski
theorem _root_.solution {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ))
    (L : Matrix (Fin d) (Fin n) ℂ) (q : Fin n → ℂ) (M : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (hML : ∀ i j, M (Fin.castSucc i) j = L i j) (hfin : (projHom J M).toRingHom.Finite) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ sliceIdeal J L q) ≤ (1 : ℕ) := by
  set I := sliceIdeal J L q with hI
  have hJI : J ≤ I := le_sup_left
  let g : MvPolynomial (Fin (d + 1)) ℂ →+* MvPolynomial (Fin n) ℂ ⧸ I :=
    (Ideal.Quotient.factor hJI).comp (projHom J M).toRingHom
  have hg : g.Finite :=
    RingHom.Finite.comp (RingHom.Finite.of_surjective _ (Ideal.Quotient.factor_surjective hJI)) hfin
  let π : MvPolynomial (Fin (d + 1)) ℂ →+* Polynomial ℂ :=
    (aeval (Fin.lastCases (motive := fun _ => Polynomial ℂ) Polynomial.X
      (fun k => Polynomial.C ((L *ᵥ q) k)))).toRingHom
  let ψ : Polynomial ℂ →+* MvPolynomial (Fin n) ℂ ⧸ I :=
    Polynomial.eval₂RingHom (algebraMap ℂ _) (Ideal.Quotient.mk I (linPoly M (Fin.last d)))
  have hlin : ∀ k : Fin d, linPoly M k.castSucc = linPoly L k := by
    intro k
    simp only [linPoly, hML]
  have hCI : ∀ c : ℂ, algebraMap ℂ (MvPolynomial (Fin n) ℂ ⧸ I) c = Ideal.Quotient.mk I (C c) :=
    fun c => rfl
  have hcomp : ψ.comp π = g := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [π, ψ, g, projHom, pullback, hCI]
    · intro i
      refine Fin.lastCases ?_ (fun k => ?_) i
      · simp [π, ψ, g, projHom, pullback]
      · have hmem : linPoly L k - C ((L *ᵥ q) k) ∈ I :=
          Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)
        have hq : Ideal.Quotient.mk I (linPoly L k) = Ideal.Quotient.mk I (C ((L *ᵥ q) k)) :=
          Ideal.Quotient.eq.mpr hmem
        simp [π, ψ, g, projHom, pullback, hlin, hq, hCI]
  have hψ : ψ.Finite := RingHom.Finite.of_comp_finite (f := π) (by rw [hcomp]; exact hg)
  calc ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) ≤ ringKrullDim (Polynomial ℂ) :=
        SliceLocalDimUpperZariski.ringKrullDim_le_of_finite ψ hψ
    _ = (1 : ℕ) := by
        rw [Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
        rfl
end SliceLocalDimUpperZariski
end GroundTheory.Heights₂.Heights
