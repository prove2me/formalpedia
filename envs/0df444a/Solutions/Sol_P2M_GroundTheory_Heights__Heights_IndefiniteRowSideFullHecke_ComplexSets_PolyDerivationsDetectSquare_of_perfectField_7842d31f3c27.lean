-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolyDerivationsDetectSquare_of_perfectField_7842d31f3c27
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:31:50.752562+00:00
-- url     : https://prove2.me/submissions/2f53db31-e93a-4111-9653-a0b7ec545a1f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPolyDerivationsDetectSquare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPerfectFieldExtensionFormallySmooth
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPolyKaehlerFree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPolyDerivationsDetectSquare

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
noncomputable section
open IsLocalRing KaehlerDifferential TensorProduct
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace PolyDerivationsDetectSquare
theorem _root_.solution
    (h₁ : PerfectFieldExtensionFormallySmooth.Statement) (h₂ : PolyKaehlerFree.Statement)
    (F k : Type) [Field F] [Field k] [Algebra F k] [PerfectField F] (n : ℕ)
    (p : Ideal (MvPolynomial (Fin n) k)) [p.IsPrime] (g : MvPolynomial (Fin n) k) (hg : g ∈ p)
    (hD : ∀ D : Derivation ℤ (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k), D g ∈ p) :
    algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime p) g ∈
      maximalIdeal (Localization.AtPrime p) ^ 2 := by
  classical

  have : Algebra.FormallySmooth F k := h₁ F k
  have : Algebra.FormallySmooth F p.ResidueField := h₁ F p.ResidueField
  have : Algebra.FormallySmooth F (MvPolynomial (Fin n) k) :=
    Algebra.FormallySmooth.comp F k (MvPolynomial (Fin n) k)
  have hsurj : Function.Surjective (algebraMap (Localization.AtPrime p) p.ResidueField) :=
    IsLocalRing.residue_surjective
  obtain ⟨ret, hret⟩ := (Algebra.FormallySmooth.iff_split_injection (R := F)
    (P := Localization.AtPrime p) hsurj).mp inferInstance
  have hinj : Function.Injective (kerCotangentToTensor F (Localization.AtPrime p) p.ResidueField) :=
    Function.LeftInverse.injective (g := ret) fun x => LinearMap.congr_fun hret x
  have hgI : algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime p) g ∈
      RingHom.ker (algebraMap (Localization.AtPrime p) p.ResidueField) := by
    rw [RingHom.mem_ker, ← IsScalarTower.algebraMap_apply]
    exact Ideal.algebraMap_residueField_eq_zero.mpr hg

  have : Module.Free (MvPolynomial (Fin n) k) Ω[MvPolynomial (Fin n) k⁄F] := h₂ F k n
  let b := Module.Free.chooseBasis (MvPolynomial (Fin n) k) Ω[MvPolynomial (Fin n) k⁄F]
  have hc : ∀ α, b.repr (D F (MvPolynomial (Fin n) k) g) α ∈ p := fun α =>
    hD (((b.coord α).compDer (D F (MvPolynomial (Fin n) k))).restrictScalars ℤ)

  have hzero : kerCotangentToTensor F (Localization.AtPrime p) p.ResidueField
      (Ideal.toCotangent _ ⟨_, hgI⟩) = 0 := by
    change (1 : p.ResidueField) ⊗ₜ[Localization.AtPrime p]
      D F (Localization.AtPrime p) (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime p) g) = 0
    rw [← map_D F F (MvPolynomial (Fin n) k) (Localization.AtPrime p),
      ← b.linearCombination_repr (D F (MvPolynomial (Fin n) k) g), Finsupp.linearCombination_apply,
      map_finsuppSum, Finsupp.sum, tmul_sum]
    refine Finset.sum_eq_zero fun α _ => ?_
    rw [LinearMap.map_smul, ← algebraMap_smul (Localization.AtPrime p), tmul_smul,
      ← algebraMap_smul p.ResidueField, ← IsScalarTower.algebraMap_apply,
      Ideal.algebraMap_residueField_eq_zero.mpr (hc α), zero_smul]
  have h0 := hinj (hzero.trans (map_zero _).symm)
  have hker : RingHom.ker (algebraMap (Localization.AtPrime p) p.ResidueField) =
      maximalIdeal (Localization.AtPrime p) := IsLocalRing.ker_residue
  rw [Ideal.toCotangent_eq_zero] at h0
  rw [← hker]
  exact h0
end PolyDerivationsDetectSquare
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
