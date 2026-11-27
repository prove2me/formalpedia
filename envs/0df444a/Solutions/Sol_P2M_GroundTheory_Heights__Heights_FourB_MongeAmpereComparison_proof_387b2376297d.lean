-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_proof_387b2376297d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:54:55.327675+00:00
-- url     : https://prove2.me/submissions/121877e9-c610-4106-b51f-88b863ed3f78

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffOnFubiniStudyProfileInvNormSqFirst
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PMongeAmpereComparison
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_contDiff_cutoff_231a9780e2e3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_cutoff_of_nonpos_5bfb8c5110c3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_cutoff_of_one_le_7e6202384246
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_hessC_add_const_e6d88f46ef03
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_isPsh_shift_53d0a2783a24
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_maMeasure_congr_open_0e6366f8399e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_maMeasure_compact_eq_d1a3cdb552e8
import Theorems.Thm_ReciprocityTheory_AnForm_M_hessCGerm
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_isPotentialAdd
import Theorems.Thm_ReciprocityTheory_AnForm_M_isPotential_ofFun
import Theorems.Thm_ReciprocityTheory_AnForm_M_maDens_congr_hessC
import Theorems.Thm_ReciprocityTheory_AnForm_M_projLine_continuous_of_smooth
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.FourB.MongeAmpereComparison
namespace GroundTheory.Heights₂.Heights.FourB.MongeAmpereComparison
theorem _root_.solution (h : MongeAmpereCompactChange.Statement) : MongeAmpereComparison.Statement := by
  intro e X _ _ _ _ A P a b hyp
  obtain ⟨hP, ha, hb, hPa, hPb, hK⟩ := hyp
  by_cases hne : Nonempty (ChartPartition A)
  swap
  · unfold maMeasure
    rw [dif_neg hne, dif_neg hne]
  have hac := projLine_continuous_of_smooth A ha
  have hbc := projLine_continuous_of_smooth A hb
  let v : ℕ → X → ℝ := fun k x => cutoff (b x - a x + (k : ℝ))
  let S : ℕ → Set X := fun k => {x | -(k : ℝ) + 1 < b x - a x}
  let K : ℕ → Set X := fun k => {x | -(k : ℝ) ≤ b x - a x}
  have hSo : ∀ k, IsOpen (S k) := fun k => isOpen_lt continuous_const (hbc.sub hac)
  have hSK : ∀ k, S k ⊆ K k := fun k x hx => by
    simp only [S, K, Set.mem_ofPred_eq] at hx ⊢
    linarith
  have hSmono : Monotone S := fun k l hkl x hx => by
    simp only [S, Set.mem_ofPred_eq] at hx ⊢
    have : (k : ℝ) ≤ l := by exact_mod_cast hkl
    linarith
  have hSU : (⋃ k, S k) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_
    obtain ⟨k, hk⟩ := exists_nat_gt (1 - (b x - a x))
    exact ⟨k, by simp only [S, Set.mem_ofPred_eq]; linarith⟩
  have hPa' : IsPotential A (P + LocPot.ofFun a) := isPotentialAdd A _ _ hP (isPotential_ofFun A a ha)
  have hv : ∀ k, A.Smooth (v k) := fun k j =>
    contDiff_cutoff.comp_contDiffOn (((hb j).sub (ha j)).add contDiffOn_const)
  have hPk : ∀ k, IsPotential A ((P + LocPot.ofFun a) + LocPot.ofFun (v k)) := fun k =>
    isPotentialAdd A _ _ hPa' (isPotential_ofFun A _ (hv k))
  have hPsk : ∀ k : ℕ, IsPsh A ((P + LocPot.ofFun a) + LocPot.ofFun (v k)) := fun k =>
    isPsh_shift A P a b k hP ha hb hPa hPb
  have step : ∀ k : ℕ, maMeasure A (fun _ => P + LocPot.ofFun b) (S k) ≤
      maMeasure A (fun _ => P + LocPot.ofFun a) Set.univ := by
    intro k
    have hKc : IsCompact (K k) := hK k
    have hsupp : Function.support (v k) ⊆ K k := by
      intro x hx
      simp only [Function.mem_support] at hx
      simp only [K, Set.mem_ofPred_eq]
      by_contra hlt
      exact hx (cutoff_of_nonpos (by linarith [not_le.mp hlt]))
    have htsupp : tsupport (v k) ⊆ K k := closure_minimal hsupp hKc.isClosed
    have hcs : HasCompactSupport (v k) := hKc.of_isClosed_subset (isClosed_tsupport _) htsupp
    have h2 := h A (P + LocPot.ofFun a) (v k) (K k) ⟨hPa', hv k, hcs, hKc, htsupp⟩
    have hloc : maMeasure A (fun _ => P + LocPot.ofFun b) (S k) =
        maMeasure A (fun _ => (P + LocPot.ofFun a) + LocPot.ofFun (v k)) (S k) := by
      apply maMeasure_congr_open A _ _ (hSo k)
      intro j y hy hyS
      unfold locDens
      apply maDens_congr_hessC
      intro i
      have hV : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S k) :=
        (A.chart j).isOpen_inter_preimage_symm (hSo k)
      have hev : (fun y' => ((P + LocPot.ofFun a) + LocPot.ofFun (v k)).φ ((A.chart j).symm y)
            ((A.chart j).symm y')) =ᶠ[𝓝 y]
          fun y' => (P + LocPot.ofFun b).φ ((A.chart j).symm y) ((A.chart j).symm y') +
            ((k : ℝ) - (1 - cutoff 1)) := by
        filter_upwards [hV.mem_nhds ⟨hy, hyS⟩] with y' hy'
        have h1 : 1 ≤ b ((A.chart j).symm y') - a ((A.chart j).symm y') + k := by
          have := hy'.2
          simp only [S, Set.mem_preimage, Set.mem_ofPred_eq] at this
          linarith
        show (P.φ _ _ + a _) + cutoff (b _ - a _ + (k : ℝ)) = (P.φ _ _ + b _) + ((k : ℝ) - (1 - cutoff 1))
        rw [cutoff_of_one_le h1]
        ring
      show hessC (fun y' => (P + LocPot.ofFun b).φ ((A.chart j).symm y) ((A.chart j).symm y')) y =
        hessC (fun y' => ((P + LocPot.ofFun a) + LocPot.ofFun (v k)).φ ((A.chart j).symm y)
          ((A.chart j).symm y')) y
      rw [hessCGerm _ _ _ hev, hessC_add_const]
    calc maMeasure A (fun _ => P + LocPot.ofFun b) (S k)
        = maMeasure A (fun _ => (P + LocPot.ofFun a) + LocPot.ofFun (v k)) (S k) := hloc
      _ ≤ maMeasure A (fun _ => (P + LocPot.ofFun a) + LocPot.ofFun (v k)) (K k) :=
          measure_mono (hSK k)
      _ = ENNReal.ofReal (mInt A (fun _ => (P + LocPot.ofFun a) + LocPot.ofFun (v k))
            ((K k).indicator 1)) :=
          maMeasure_compact_eq A _ hne (fun _ => hPk k) (fun _ => hPsk k) hKc
      _ = ENNReal.ofReal (mInt A (fun _ => P + LocPot.ofFun a) ((K k).indicator 1)) := by rw [h2]
      _ = maMeasure A (fun _ => P + LocPot.ofFun a) (K k) :=
          (maMeasure_compact_eq A _ hne (fun _ => hPa') (fun _ => hPa) hKc).symm
      _ ≤ maMeasure A (fun _ => P + LocPot.ofFun a) Set.univ := measure_mono (Set.subset_univ _)
  calc maMeasure A (fun _ => P + LocPot.ofFun b) Set.univ
      = ⨆ k, maMeasure A (fun _ => P + LocPot.ofFun b) (S k) := by
        rw [← hSU]
        exact hSmono.measure_iUnion
    _ ≤ maMeasure A (fun _ => P + LocPot.ofFun a) Set.univ := iSup_le step
end GroundTheory.Heights₂.Heights.FourB.MongeAmpereComparison
