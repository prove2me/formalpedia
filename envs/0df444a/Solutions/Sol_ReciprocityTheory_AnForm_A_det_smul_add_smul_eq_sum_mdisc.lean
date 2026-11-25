-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.det_smul_add_smul_eq_sum_mdisc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:04:59.837929+00:00
-- url     : https://prove2.me/submissions/0a4a5f85-2b42-463b-a4e8-475b3c820378

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscPos
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_eq_sum_perm
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_comp_perm
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_const
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.AnForm.A
open Matrix
open scoped ComplexOrder
variable {D : ℕ}
private lemma mdiscML_apply (A : Fin D → Matrix (Fin D) (Fin D) ℂ) : mdiscML A = mdisc A := by
  rw [mdisc_eq_sum_perm, mdiscML, _root_.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [_root_.smul_apply, smul_eq_mul, MultilinearMap.domDomCongr_apply,
    MultilinearMap.compLinearMap_apply]
  congr 1
  rw [← Matrix.det_transpose]
  rfl
private lemma exists_perm_mem_iff (T : Finset (Fin D)) :
    ∃ σ : Equiv.Perm (Fin D), ∀ k, σ k ∈ T ↔ (k : ℕ) < T.card := by
  classical
  have h1 : Fintype.card {k : Fin D // (k : ℕ) < T.card} = Fintype.card {k : Fin D // k ∈ T} := by
    rw [Fintype.card_subtype, Fintype.card_subtype, Fin.card_filter_val_lt,
      Finset.filter_mem_eq_inter, Finset.univ_inter]
    exact min_eq_right (by simpa using T.card_le_univ)
  have h2 : Fintype.card {k : Fin D // ¬ (k : ℕ) < T.card} = Fintype.card {k : Fin D // k ∉ T} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, h1]
  refine ⟨Equiv.subtypeCongr (Fintype.equivOfCardEq h1) (Fintype.equivOfCardEq h2), fun k => ?_⟩
  by_cases hk : (k : ℕ) < T.card
  · have e : (Equiv.sumCompl (fun x : Fin D => (x : ℕ) < T.card)).symm k = Sum.inl ⟨k, hk⟩ :=
      Equiv.sumCompl_symm_apply_of_pos (p := fun x : Fin D => (x : ℕ) < T.card) hk
    simp only [Equiv.subtypeCongr, Equiv.trans_apply, e, Equiv.sumCongr_apply, Sum.map_inl,
      Equiv.sumCompl_apply_inl]
    exact iff_of_true (Fintype.equivOfCardEq h1 ⟨k, hk⟩).2 hk
  · have e : (Equiv.sumCompl (fun x : Fin D => (x : ℕ) < T.card)).symm k = Sum.inr ⟨k, hk⟩ :=
      Equiv.sumCompl_symm_apply_of_neg (p := fun x : Fin D => (x : ℕ) < T.card) hk
    simp only [Equiv.subtypeCongr, Equiv.trans_apply, e, Equiv.sumCongr_apply, Sum.map_inr,
      Equiv.sumCompl_apply_inr]
    exact iff_of_false (Fintype.equivOfCardEq h2 ⟨k, hk⟩).2 hk
private lemma mdisc_piecewise (T : Finset (Fin D)) (A B : Matrix (Fin D) (Fin D) ℂ) :
    mdisc (fun k => if k ∈ T then A else B) = mdisc (fun k : Fin D => if (k : ℕ) < T.card then A else B) := by
  obtain ⟨σ, hσ⟩ := exists_perm_mem_iff T
  rw [← mdisc_comp_perm _ σ]
  congr 1
  funext k
  simp only [Function.comp_apply, hσ]
end ReciprocityTheory.AnForm.A
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open Matrix
open scoped ComplexOrder
variable {D : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (s t : ℂ) (A B : Matrix (Fin D) (Fin D) ℂ) :
    (s • A + t • B).det =
      ∑ i ∈ Finset.range (D + 1), (D.choose i : ℂ) * s ^ i * t ^ (D - i) *
        mdisc (fun k : Fin D => if (k : ℕ) < i then A else B) := by
  classical
  rw [← mdisc_const, ← mdiscML_apply]
  have h : (fun _ : Fin D => s • A + t • B) = (fun _ : Fin D => s • A) + (fun _ => t • B) := rfl
  rw [h, MultilinearMap.map_add_univ]
  have h2 : ∀ T : Finset (Fin D), mdiscML (T.piecewise (fun _ => s • A) (fun _ => t • B)) =
      s ^ T.card * t ^ (D - T.card) * mdisc (fun k : Fin D => if (k : ℕ) < T.card then A else B) := by
    intro T
    have e : T.piecewise (fun _ : Fin D => s • A) (fun _ => t • B) =
        fun k => (if k ∈ T then s else t) • (if k ∈ T then A else B) := by
      funext k; by_cases hk : k ∈ T <;> simp [Finset.piecewise, hk]
    rw [e, MultilinearMap.map_smul_univ, smul_eq_mul, mdiscML_apply, mdisc_piecewise,
      Finset.prod_ite, Finset.prod_const, Finset.prod_const]
    congr 2
    · simp
    · congr 1
      rw [Finset.filter_not, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.card_sdiff,
        Finset.card_univ, Fintype.card_fin]
      simp
  simp only [h2]
  rw [← Finset.powerset_univ,
    Finset.sum_powerset_apply_card (fun i => s ^ i * t ^ (D - i) *
      mdisc (fun k : Fin D => if (k : ℕ) < i then A else B)) (x := Finset.univ)]
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]
end ReciprocityTheory.AnForm.A
