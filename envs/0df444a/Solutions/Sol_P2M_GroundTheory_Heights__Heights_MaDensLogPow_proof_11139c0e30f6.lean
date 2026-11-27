-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MaDensLogPow_proof_11139c0e30f6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:09:50.056345+00:00
-- url     : https://prove2.me/submissions/18182dfa-3bb8-4357-b088-c13467c35fb7

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsPiola
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StMaDensLogPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaDensChain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaDensLogPow
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MaDensLogPow_mdisc_eq_zero_of_two_rankOne_744d0b65b8a4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MaDensLogPow_mdisc_expand_29cfce2fc705
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MaDensLogPow_cons_const_apply_5310b6bbe09d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MaDensLogPow_mdisc_update_eq_40eeca4a8c4a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MaDensLogPow_hessC_log_comp_d38474af266b
import Theorems.Thm_ReciprocityTheory_AnForm_A_gradMat_eq_vecMulVec


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
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Filter Topology Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.MaDensLogPow
variable {D : ℕ}
namespace GroundTheory.Heights₂.Heights.MaDensLogPow
theorem _root_.solution : MaDensLogPow.Statement := by
  intro e φ₀ p y hp hpos
  set H := hessC p y with hH
  set G := gradMat p p y with hGdef
  set A₀ := hessC φ₀ y with hA₀
  set a : ℝ := (p y)⁻¹ with ha
  set b : ℝ := -((p y) ^ 2)⁻¹ with hb
  have hlog : hessC (Real.log ∘ p) y = (a : ℂ) • H + (b : ℂ) • G := hessC_log_comp hp hpos
  have hG : ∀ (A : Fin (e + 1 + 1) → Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ) (i j : Fin (e + 1 + 1)),
      i ≠ j → A i = G → A j = G → mdisc A = 0 := fun A i j hij hi hj =>
    mdisc_eq_zero_of_two_rankOne A _ hij _ _ (hi.trans (gradMat_eq_vecMulVec p p y))
      (hj.trans (gradMat_eq_vecMulVec p p y))
  set s : Finset (Fin (e + 1 + 1)) := Finset.univ.erase 0 with hs
  have hscard : s.card = e + 1 := by simp [hs]
  set C : Fin (e + 1 + 1) → Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ :=
    Fin.cons A₀ (fun _ : Fin (e + 1) => H) with hC
  have hCs : ∀ i ∈ s, C i = H := fun i hi => by
    rw [hC, cons_const_apply, if_neg (Finset.ne_of_mem_erase hi)]
  have key := mdisc_expand (a : ℂ) (b : ℂ) H G hG s C hCs
  rw [Finset.sum_congr rfl fun i hi => mdisc_update_eq G A₀ H i (Finset.ne_of_mem_erase hi),
    Finset.sum_const, hscard, Nat.add_sub_cancel, nsmul_eq_mul] at key
  have hfam1 : (fun k => hessC ((Fin.cons φ₀ fun _ : Fin (e + 1) => Real.log ∘ p :
      Fin (e + 1 + 1) → (Fin (e + 1 + 1) → ℂ) → ℝ) k) y) =
      fun i => if i ∈ s then (a : ℂ) • H + (b : ℂ) • G else C i := by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · simp [hs, hC, hA₀]
    · simp [hs, Fin.succ_ne_zero, hlog]
  have hfam2 : (fun k => hessC ((Fin.cons φ₀ fun _ : Fin (e + 1) => p :
      Fin (e + 1 + 1) → (Fin (e + 1 + 1) → ℂ) → ℝ) k) y) = C := by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · simp [hC, hA₀]
    · simp [hC, hH]
  have hfam3 : (fun i => hessC ((Fin.cons φ₀ fun _ : Fin e => p :
      Fin (e + 1) → (Fin (e + 1 + 1) → ℂ) → ℝ) i) y) = Fin.cons A₀ (fun _ : Fin e => H) := by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · simp [hA₀]
    · simp [hH]
  unfold maDens gradDens
  rw [hfam1, hfam2, hfam3, key]
  have hp0 : p y ≠ 0 := hpos.ne'
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.add_re,
    Complex.re_ofReal_mul]
  rw [← hGdef, ha, hb]
  simp only [inv_pow, Nat.cast_add, Nat.cast_one]
  field_simp
  ring
end GroundTheory.Heights₂.Heights.MaDensLogPow
