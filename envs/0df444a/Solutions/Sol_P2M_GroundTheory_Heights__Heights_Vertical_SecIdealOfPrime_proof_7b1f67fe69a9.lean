-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SecIdealOfPrime_proof_7b1f67fe69a9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:40:15.975076+00:00
-- url     : https://prove2.me/submissions/99251ea4-953c-4937-98d1-85d47eeba71c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsSecIdealOfPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsGenSecKer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecIdealOfPrime
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecIdealOfPrime_secAlg_of_ratFunc_ed8075505960
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecIdealOfPrime_residue_surj_a014fc5c050d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
namespace GroundTheory.Heights₂.Heights.Vertical
namespace SecIdealOfPrime
theorem _root_.solution (hDim : SpecCompDim.Statement) (hExist : ChowFormExists.Statement)
    (hInd : ResidueAlgIndep.Statement) (hField : SecAlgField.Statement) (hKer : GenSecKer.Statement) :
    SecIdealOfPrime.Statement := by
  intro K _ _ n e I f v hI hf W hW
  have : v.asIdeal.IsMaximal := v.isMaximal
  obtain ⟨hQ, hQdim⟩ := hDim K n e I f v hI hf W hW
  obtain ⟨g, hg⟩ := hExist v.asIdeal.ResidueField n (e + 1) (reduceMod v W) hQ hQdim

  have hψ : Function.Injective (eval₂Hom (resToKappa e n v) (parYκ e n v)) := fun _ _ hpq =>
    hInd K e n v hpq
  obtain ⟨hFieldE, hkerE⟩ := SecIdealOfPrime.secAlg_of_ratFunc n e (resToKappa e n v) (parYκ e n v) hψ
    (SecIdealOfPrime.residue_surj e n v) (reduceMod v W) (hField _ n e _ g hQ hg) (hKer _ n e _ g hQ hg)

  let R := ParDVR e n v
  let E := (IsLocalRing.maximalIdeal R).ResidueField
  let k := v.asIdeal.ResidueField
  let QE := (reduceMod v W).map (MvPolynomial.map (resToKappa e n v))
  let T := secIdeal QE (parYκ e n v)
  have hmm : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (φ₁ : A →+* B) (φ₂ : B →+* C),
      (MvPolynomial.map φ₂).comp (MvPolynomial.map φ₁) =
        (MvPolynomial.map (φ₂.comp φ₁) : MvPolynomial (Fin n) A →+* MvPolynomial (Fin n) C) :=
    fun φ₁ φ₂ ↦ RingHom.ext fun p ↦ MvPolynomial.map_map _ _ p
  let ι : 𝓞 K →+* R := algebraMap (𝓞 K) R
  let ρ : R →+* E := algebraMap R E
  have hρ : Function.Surjective ρ := Ideal.algebraMap_residueField_surjective _
  let Ψ : MvPolynomial (Fin n) R →+* MvPolynomial (Fin n) E := MvPolynomial.map ρ
  have hΨ : Function.Surjective Ψ := MvPolynomial.map_surjective _ hρ
  have hcomp : ρ.comp ι = (resToKappa e n v).comp (algebraMap (𝓞 K) k) := by
    ext a
    exact (Ideal.ResidueField.map_algebraMap v.asIdeal (IsLocalRing.maximalIdeal (ParDVR e n v))
        (algebraMap (𝓞 K) (ParDVR e n v)) (comap_maximalIdeal_parDVR e n v).symm a).symm
  have hJW : integralModel I ⊔ Ideal.map C v.asIdeal ≤ W := hW.1.1.2
  let WR : Ideal (MvPolynomial (Fin n) R) := W.map (MvPolynomial.map ι)
  let S := secIdeal (modelR e I v) (parY e n v)
  have hWR : WR.map Ψ = QE := by
    simp only [WR, QE, reduceMod, Ideal.map_map, Ψ, hmm, hcomp]
    rfl
  have hM : (modelR e I v).map Ψ ≤ QE := by
    rw [← hWR]
    exact Ideal.map_mono (Ideal.map_mono (le_sup_left.trans hJW))
  have hA : (Ideal.span (Set.range (secForm (parY e n v)))).map Ψ =
      Ideal.span (Set.range (secForm (parYκ e n v))) := by
    rw [Ideal.map_span, ← Set.range_comp]
    congr 2
    funext i
    simp [Ψ, secForm, linForm, parYκ, ρ]
    rfl
  have hB : (Ideal.span {chartForm (parY e n v) - 1}).map Ψ =
      Ideal.span {chartForm (parYκ e n v) - 1} := by
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    simp [Ψ, chartForm, linForm, parYκ, ρ]
    rfl
  have hT : (S ⊔ WR).map Ψ = T := by
    simp only [S, T, secIdeal, Ideal.map_sup, hA, hB, hWR]
    apply le_antisymm
    · exact sup_le (sup_le (sup_le (hM.trans (le_sup_left.trans le_sup_left))
        (le_sup_right.trans le_sup_left)) le_sup_right) (le_sup_left.trans le_sup_left)
    · exact sup_le (sup_le le_sup_right (le_sup_right.trans (le_sup_left.trans le_sup_left)))
        (le_sup_right.trans le_sup_left)
  have hkerΨ : RingHom.ker Ψ ≤ WR := by
    have h1 : ι = (algebraMap (MvPolynomial (Par e n) (𝓞 K)) R).comp C :=
      IsScalarTower.algebraMap_eq _ _ _
    have hmax : IsLocalRing.maximalIdeal R = v.asIdeal.map ι := by
      rw [h1, ← Ideal.map_map]
      exact Localization.AtPrime.map_eq_maximalIdeal.symm
    rw [MvPolynomial.ker_map, Ideal.ker_algebraMap_residueField, hmax, Ideal.map_map,
      ← MvPolynomial.map_comp_C, ← Ideal.map_map]
    exact Ideal.map_mono (le_sup_right.trans hJW)
  let Φ : MvPolynomial (Fin n) R →+* SecAlg QE (parYκ e n v) := (Ideal.Quotient.mk T).comp Ψ
  have hker : RingHom.ker Φ = S ⊔ WR := by
    have : RingHom.ker Φ = T.comap Ψ := by
      ext x
      simp [Φ, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
    rw [this, ← hT, Ideal.comap_map_of_surjective _ hΨ, ← RingHom.ker_eq_comap_bot]
    exact sup_eq_left.mpr (hkerΨ.trans le_sup_right)

  have hkerPrime : (RingHom.ker Φ).IsPrime := by
    let _ := hFieldE.toField
    exact RingHom.ker_isPrime Φ
  have hSle : S ≤ RingHom.ker Φ := hker ▸ le_sup_left
  have hsec : secIdealOf e I v W = (RingHom.ker Φ).map (Ideal.Quotient.mk S) := by
    rw [hker, Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq]
    rfl
  have hcomap : (secIdealOf e I v W).comap (Ideal.Quotient.mk S) = RingHom.ker Φ := by
    rw [hsec, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker]
    exact sup_eq_left.mpr hSle
  refine ⟨?_, ?_⟩
  · rw [hsec]
    exact Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hSle)
  ·
    have hto : toSecB e I v = (Ideal.Quotient.mk S).comp (MvPolynomial.map ι) := rfl
    have hπ : Function.Surjective (MvPolynomial.map (algebraMap (𝓞 K) k) :
        MvPolynomial (Fin n) (𝓞 K) →+* MvPolynomial (Fin n) k) :=
      MvPolynomial.map_surjective _ (Ideal.algebraMap_residueField_surjective v.asIdeal)
    rw [hto, ← Ideal.comap_comap, hcomap]
    ext p
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have hΦp : Φ (MvPolynomial.map ι p) =
        ((Ideal.Quotient.mk T).comp (MvPolynomial.map (resToKappa e n v)))
          (MvPolynomial.map (algebraMap (𝓞 K) k) p) := by
      simp only [Φ, Ψ, RingHom.comp_apply, MvPolynomial.map_map, hcomp]
    rw [hΦp, ← RingHom.mem_ker, hkerE]
    change MvPolynomial.map (algebraMap (𝓞 K) k) p ∈ W.map (MvPolynomial.map (algebraMap (𝓞 K) k)) ↔ p ∈ W
    rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective _ hπ, ← RingHom.ker_eq_comap_bot,
      MvPolynomial.ker_map, Ideal.ker_algebraMap_residueField,
      sup_eq_left.mpr (le_sup_right.trans hJW)]
end SecIdealOfPrime
end GroundTheory.Heights₂.Heights.Vertical
