-- Prove2me | solution 1 for TractableDRO.MeanSupport.remark_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T08:53:54.729303+00:00
-- url     : https://prove2.me/submissions/191748e0-3ebe-4db8-b9d2-a64022bf8442

import Mathlib
import Definitions.Def_TractableDRO_MeanSupport_Model

open MeasureTheory

namespace TractableDRO.MeanSupport

theorem remark_nonpos {n : ℕ} (V Vhat : Set (Fin n → ℝ)) (hsub : Vhat ⊆ V)
    (hne : Vhat.Nonempty) (r0 : ℝ) (r : Fin n → ℝ) (hnp : ∀ ζ ∈ V, r0 + r ⬝ᵥ ζ ≤ 0) :
    worstCase (family1 V Vhat) r0 r = 0 ∧
      pi1Obj V Vhat r0 r 0 = pi1 V Vhat r0 r ∧ pi1 V Vhat r0 r = 0 := by
  classical
  obtain ⟨zh, hzh⟩ := hne
  have hV := hsub hzh
  have hdir : Measure.dirac zh ∈ family1 V Vhat := by
    refine ⟨inferInstance, ?_, ?_, ?_⟩
    · intro i; exact integrable_dirac (f := fun ζ : Fin n → ℝ => ζ i) (by simp)
    · have hm : MomentDRO.Conf.meanVec (Measure.dirac zh) = zh := by
        funext i
        simp [MomentDRO.Conf.meanVec, integral_dirac]
      rw [hm]; exact hzh
    · simpa using hV
  have he (P : Measure (Fin n → ℝ)) (hP : P ∈ family1 V Vhat) :
      expPos P r0 r = 0 := by
    unfold expPos
    have hzero : (fun ζ => max (r0 + r ⬝ᵥ ζ) 0) =ᵐ[P] (fun _ => (0:ℝ)) := by
      filter_upwards [hP.2.2.2] with ζ hζ
      exact max_eq_right (hnp ζ hζ)
    rw [integral_congr_ae hzero, integral_zero]
  have hw : worstCase (family1 V Vhat) r0 r = 0 := by
    apply le_antisymm
    · apply iSup_le; intro P; apply iSup_le; intro hP
      simp [he P hP]
    · exact le_iSup_of_le (Measure.dirac zh)
        (le_iSup_of_le hdir (by simp [he _ hdir]))
  have hobj : pi1Obj V Vhat r0 r 0 = 0 := by
    have hleft : (⨆ z ∈ Vhat, (((0 : Fin n → ℝ) ⬝ᵥ z : ℝ) : EReal)) = 0 := by
      apply le_antisymm
      · apply iSup_le; intro z; apply iSup_le; intro _; simp
      · exact le_iSup_of_le zh (le_iSup_of_le hzh (by simp))
    have hright : (⨆ z ∈ V, ((max (r0 + r ⬝ᵥ z - (0 : Fin n → ℝ) ⬝ᵥ z)
        (-((0 : Fin n → ℝ) ⬝ᵥ z)) : ℝ) : EReal)) = 0 := by
      apply le_antisymm
      · apply iSup_le; intro z; apply iSup_le; intro hz
        simp [max_eq_right (hnp z hz)]
      · exact le_iSup_of_le zh (le_iSup_of_le hV (by simp [max_eq_right (hnp zh hV)]))
    unfold pi1Obj
    rw [hleft, hright, zero_add]
  have hpi : pi1 V Vhat r0 r = 0 := by
    apply le_antisymm
    · exact iInf_le_of_le 0 (le_of_eq hobj)
    · apply le_iInf
      intro s
      have hleft : ((s ⬝ᵥ zh : ℝ) : EReal) ≤ ⨆ z ∈ Vhat, ((s ⬝ᵥ z : ℝ) : EReal) :=
        le_iSup_of_le zh (le_iSup_of_le hzh le_rfl)
      have hright : ((-(s ⬝ᵥ zh) : ℝ) : EReal) ≤
          ⨆ z ∈ V, ((max (r0 + r ⬝ᵥ z - s ⬝ᵥ z) (-(s ⬝ᵥ z)) : ℝ) : EReal) :=
        le_iSup_of_le zh (le_iSup_of_le hV (by exact_mod_cast le_max_right _ _))
      have hadd := add_le_add hleft hright
      have hzsum : ((s ⬝ᵥ zh : ℝ) : EReal) + ((-(s ⬝ᵥ zh) : ℝ) : EReal) = 0 := by
        rw [← EReal.coe_add]; simp
      rw [hzsum] at hadd
      exact hadd
  exact ⟨hw, hobj.trans hpi.symm, hpi⟩


end TractableDRO.MeanSupport

theorem solution {n : ℕ} (V Vhat : Set (Fin n → ℝ)) (hsub : Vhat ⊆ V)
    (hne : Vhat.Nonempty) (r0 : ℝ) (r : Fin n → ℝ) (hnp : ∀ ζ ∈ V, r0 + r ⬝ᵥ ζ ≤ 0) :
    TractableDRO.MeanSupport.worstCase (TractableDRO.MeanSupport.family1 V Vhat) r0 r = 0 ∧
      TractableDRO.MeanSupport.pi1Obj V Vhat r0 r 0 = TractableDRO.MeanSupport.pi1 V Vhat r0 r ∧
      TractableDRO.MeanSupport.pi1 V Vhat r0 r = 0 :=
  TractableDRO.MeanSupport.remark_nonpos V Vhat hsub hne r0 r hnp
#print axioms solution
