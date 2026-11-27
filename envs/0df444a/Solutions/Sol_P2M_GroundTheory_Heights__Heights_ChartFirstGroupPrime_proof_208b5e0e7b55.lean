-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartFirstGroupPrime_proof_208b5e0e7b55
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:57:27.170303+00:00
-- url     : https://prove2.me/submissions/223764d4-c7e5-47a0-b2f8-287810964993

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartFirstGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartFirstGroupPrime
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isChowForm_iff_656fe0f0fba5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_incIdeal_iff_08da98833496

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
private theorem firstGroup_eq {F : Type*} [Field F] {n e : ℕ} (g : MvPolynomial (Fin (e + 1) × Fin n) F) :
    firstGroup g = ((renameEquiv F (firstGroupVars e n)).trans (sumAlgEquiv F (Fin n) (Fin e × Fin n))) g := by
  have h : (aeval (fun ij : Fin (e + 1) × Fin n =>
      Fin.cases (motive := fun _ => MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F))
        (X ij.2) (fun i => C (X (i, ij.2))) ij.1) :
        MvPolynomial (Fin (e + 1) × Fin n) F →ₐ[F] _) =
      ((renameEquiv F (firstGroupVars e n)).trans (sumAlgEquiv F (Fin n) (Fin e × Fin n))).toAlgHom := by
    apply MvPolynomial.algHom_ext
    rintro ⟨i, m⟩
    cases i using Fin.cases <;> simp [firstGroupVars]
  exact DFunLike.congr_fun h g
end
end GroundTheory.Heights₂.Heights
end

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace ChartFirstGroupPrime
theorem _root_.solution (h₁ : IncIdealPrime.Statement) (h₂ : IncIdealBelow.Statement) :
    ChartFirstGroupPrime.Statement := by
  intro F _ n e I f p _ hI hf
  obtain ⟨hf0, hspan⟩ := isChowForm_iff.mp hf
  have hfp : Prime f := by
    have := h₁ F n (e + 1) I hI.isPrime hI.isRelevant
    rw [hspan] at this
    exact (Ideal.span_singleton_prime hf0).mp this
  set Φ := (renameEquiv F (firstGroupVars e n)).trans (sumAlgEquiv F (Fin n) (Fin e × Fin n)) with hΦ
  have hg : Prime (firstGroup f) := by
    rw [firstGroup_eq]
    exact (MulEquiv.prime_iff Φ).mpr hfp

  have hC : ∀ s : MvPolynomial (Fin e × Fin n) F,
      (C s : MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F)) =
        Φ (rename (fun im : Fin e × Fin n => ((im.1.succ, im.2) : Fin (e + 1) × Fin n)) s) := by
    intro s
    have hcomp : (firstGroupVars e n) ∘ (fun im : Fin e × Fin n => ((im.1.succ, im.2) : Fin (e + 1) × Fin n)) =
        Sum.inr := by
      funext im
      rfl
    rw [hΦ, AlgEquiv.trans_apply, renameEquiv_apply, rename_rename, hcomp]
    have := DFunLike.congr_fun (sumAlgEquiv_comp_rename_inr F (Fin n) (Fin e × Fin n)) s
    simp only [AlgHom.coe_comp, Function.comp_apply] at this
    exact (this.trans (by rw [IsScalarTower.coe_toAlgHom', algebraMap_eq])).symm
  have hdisj : Disjoint ((p.primeCompl.map (C : MvPolynomial (Fin e × Fin n) F →+*
      MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F)) : Submonoid _) : Set _)
      ((Ideal.span {firstGroup f} : Ideal (MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F))) :
        Set (MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F))) := by
    rw [Set.disjoint_left]
    intro y hy hmem
    obtain ⟨s, hs, rfl⟩ := Submonoid.mem_map.mp hy
    rw [SetLike.mem_coe, Ideal.mem_span_singleton, hC, firstGroup_eq, map_dvd_iff] at hmem
    have hvan := (hf.2 _).mpr hmem
    have hsI : s ∈ incIdeal I e := by
      rw [mem_incIdeal_iff]
      rintro v ⟨x, hx0, hxI, hxv⟩
      have := hvan (fun ij => Fin.cases (motive := fun _ => AlgebraicClosure F) 0 (fun i => v (i, ij.2)) ij.1)
        ⟨x, hx0, hxI, fun i => by
          cases i using Fin.cases with
          | zero => simp
          | succ i => simpa using hxv i⟩
      rwa [aeval_rename] at this
    rw [h₂ F n e I f hI hf, Ideal.mem_bot] at hsI
    exact hs (hsI ▸ p.zero_mem)
  letI := MvPolynomial.algebraMvPolynomial (σ := Fin n) (R := MvPolynomial (Fin e × Fin n) F)
    (S := Localization.AtPrime p)
  have hprime := IsLocalization.isPrime_of_isPrime_disjoint
    (p.primeCompl.map (C : MvPolynomial (Fin e × Fin n) F →+*
      MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F)))
    (MvPolynomial (Fin n) (Localization.AtPrime p)) _
    ((Ideal.span_singleton_prime hg.ne_zero).mpr hg) hdisj
  rw [Ideal.map_span, Set.image_singleton, MvPolynomial.algebraMap_def] at hprime
  refine (Ideal.span_singleton_prime fun h => hg.ne_zero ?_).mp hprime
  exact map_injective _ (IsLocalization.injective (Localization.AtPrime p) p.primeCompl_le_nonZeroDivisors)
    (h.trans (map_zero _).symm)
end ChartFirstGroupPrime
end GroundTheory.Heights₂.Heights
