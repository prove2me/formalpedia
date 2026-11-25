-- Prove2me | solution 1 for PI.ScRefExists.WF.wFrame_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:13:16.343917+00:00
-- url     : https://prove2.me/submissions/ee17f444-44fe-4495-a9ee-70bb0857d2ff

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_MemLAOfNsmul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_WBasis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_WFrameOf
import Theorems.Thm_PI_ScRefExists_WF_fam_li
import Theorems.Thm_PI_ScRefExists_WF_fam_sp
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_ScRefExists_WF_L_le_LA
import Theorems.Thm_PI_ScRefExists_WF_dual_LA
import Theorems.Thm_PI_ScRefExists_WF_hG_LA
import Theorems.Thm_PI_ScRefExists_WF_hG_add_left
import Theorems.Thm_PI_ScRefExists_WF_hG_add_right
import Theorems.Thm_PI_ScRefExists_WF_hG_e_proj
import Theorems.Thm_PI_ScRefExists_WF_hG_f_proj
import Theorems.Thm_PI_ScRefExists_WF_hG_nondeg
import Theorems.Thm_PI_ScRefExists_WF_hG_smul_left
import Theorems.Thm_PI_ScRefExists_WF_hG_smul_right
import Theorems.Thm_PI_ScRefExists_WF_hG_sub_right
import Theorems.Thm_PI_ScRefExists_WF_hG_sum_right
import Theorems.Thm_PI_ScRefExists_WF_hG_symm
import Theorems.Thm_PI_ScRefExists_WF_hG_zero_left
import Theorems.Thm_PI_ScRefExists_WF_hG_zero_right
import Theorems.Thm_PI_ScRefExists_WF_mem_LA_of_nsmul
import Theorems.Thm_PI_ScRefExists_WF_proj_mem
import Theorems.Thm_PI_ScRefExists_WF_proj_span
import Theorems.Thm_PI_ScRefExists_WF_star_mem_Ap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S
open PI.ScRefExists.Sk
open PI PI.ScRefExists PI.ScRefExists.WF
variable {I : Formalism.MainNotions.S.AutInst} {p : ℕ}
namespace PI.ScRefExists.WF
theorem _root_.solution (hPID : ApPID) (hWB : WBasis) : WFrame := by
  intro I p r k e f M hp hn he hf hef hM heM
  obtain ⟨w, hw1, hwli, hwsp⟩ := hWB I p r k e f M hp (hPID I p hp) hn he hf hef hM heM
  have heA : ∀ a, e a ∈ LA I p := fun a => mem_LA_of_nsmul hp hM (heM a).1
  have hfA : ∀ a, f a ∈ LA I p := fun a => mem_LA_of_nsmul hp hM (heM a).2
  have hwA : ∀ i, w i ∈ LA I p := fun i => (hw1 i).1
  have hwo : ∀ i a, hG I (e a) (w i) = 0 ∧ hG I (f a) (w i) = 0 := fun i a => (hw1 i).2 a
  have hli := fam_li he hf hef hwo hwli
  have hsp := fam_sp hp he hf hef heA hfA hwsp
  have hT0 : ∀ u, (∀ j, hG I (fam e f w j) u = 0) → u = 0 := by
    intro u hu
    apply hG_nondeg
    intro x
    have hx : x ∈ Submodule.span I.E (Set.range (fam e f w)) := hsp Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact hu j
    | zero => exact hG_zero_left I u
    | add x y _ _ hx hy => rw [hG_add_left, hx, hy, add_zero]
    | smul c x _ hx => rw [hG_smul_left, hx, mul_zero]
  let T : (Fin I.n → I.E) →ₗ[I.E] (Fin r ⊕ (Fin r ⊕ Fin (k + 1)) → I.E) :=
    { toFun := fun d j => hG I (fam e f w j) d
      map_add' := fun x y => by
        ext j
        simp [hG_add_right]
      map_smul' := fun c x => by
        ext j
        simp [hG_smul_right] }
  have hTi : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    exact hT0 u (fun j => congrFun hu j)
  have hdim : Module.finrank I.E (Fin I.n → I.E) =
      Module.finrank I.E (Fin r ⊕ (Fin r ⊕ Fin (k + 1)) → I.E) := by
    rw [Module.finrank_fin_fun, Module.finrank_fintype_fun_eq_card, Fintype.card_sum,
      Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, hn]
    ring
  have hTs : Function.Surjective T :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hTi
  have hex : ∀ i : Fin (k + 1), ∃ d : Fin I.n → I.E, ∀ j,
      hG I (fam e f w j) d = if j = Sum.inr (Sum.inr i) then 1 else 0 := by
    intro i
    obtain ⟨d, hd⟩ := hTs (fun j => if j = Sum.inr (Sum.inr i) then 1 else 0)
    exact ⟨d, fun j => congrFun hd j⟩
  choose wd hwd using hex
  have hewd : ∀ a i, hG I (e a) (wd i) = 0 := fun a i => by
    simpa [fam] using hwd i (Sum.inl a)
  have hfwd : ∀ a i, hG I (f a) (wd i) = 0 := fun a i => by
    simpa [fam] using hwd i (Sum.inr (Sum.inl a))
  have hwwd : ∀ j i, hG I (w j) (wd i) = if j = i then 1 else 0 := fun j i => by
    simpa [fam] using hwd i (Sum.inr (Sum.inr j))
  have hdual : ∀ i j, hG I (wd i) (w j) = if i = j then 1 else 0 := by
    intro i j
    rw [hG_symm I (w j) (wd i), hwwd j i]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]
  have hyS : ∀ y ∈ I.L,
      y ∈ Submodule.span (Ap I p) (Set.range e ∪ Set.range f ∪ Set.range w) := by
    intro y hy
    have hyA : y ∈ LA I p := L_le_LA hy
    have hz : y - proj e f y ∈ Submodule.span (Ap I p) (Set.range w) := by
      apply hwsp _ (sub_mem hyA (proj_mem hp heA hfA hyA))
      intro a
      rw [hG_sub_right, hG_sub_right, hG_e_proj he hef, hG_f_proj hf hef, sub_self, sub_self]
      exact ⟨rfl, rfl⟩
    have h1 := proj_span e f hp heA hfA hyA (Set.range e ∪ Set.range f ∪ Set.range w)
      Set.subset_union_left
    have h2 : y - proj e f y ∈
        Submodule.span (Ap I p) (Set.range e ∪ Set.range f ∪ Set.range w) :=
      Submodule.span_mono Set.subset_union_right hz
    have := add_mem h1 h2
    simpa using this
  have hwdAp : ∀ i, ∀ y ∈ Submodule.span (Ap I p) (Set.range e ∪ Set.range f ∪ Set.range w),
      hG I (wd i) y ∈ Ap I p := by
    intro i y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      rcases hx with (⟨a, rfl⟩ | ⟨a, rfl⟩) | ⟨j, rfl⟩
      · rw [hG_symm I (e a) (wd i), hewd a i, star_zero]
        exact zero_mem _
      · rw [hG_symm I (f a) (wd i), hfwd a i, star_zero]
        exact zero_mem _
      · rw [hdual i j]
        split_ifs
        · exact one_mem _
        · exact zero_mem _
    | zero => rw [hG_zero_right]; exact zero_mem _
    | add x y _ _ hx hy => rw [hG_add_right]; exact add_mem hx hy
    | smul c x _ hx =>
      show hG I (wd i) ((c : I.E) • x) ∈ Ap I p
      rw [hG_smul_right]
      exact mul_mem c.2 hx
  have hwdA : ∀ i, wd i ∈ LA I p := fun i => dual_LA hp fun y hy => by
    rw [hG_symm I (wd i) y]
    exact star_mem_Ap (hwdAp i y (hyS y hy))
  have hyS' : ∀ y ∈ I.L,
      y ∈ Submodule.span (Ap I p) (Set.range e ∪ Set.range f ∪ Set.range wd) := by
    intro y hy
    have hyA : y ∈ LA I p := L_le_LA hy
    have hzA : y - proj e f y ∈ LA I p := sub_mem hyA (proj_mem hp heA hfA hyA)
    have hze : ∀ a, hG I (e a) (y - proj e f y) = 0 := fun a => by
      rw [hG_sub_right, hG_e_proj he hef, sub_self]
    have hzf : ∀ a, hG I (f a) (y - proj e f y) = 0 := fun a => by
      rw [hG_sub_right, hG_f_proj hf hef, sub_self]
    have hzeq : y - proj e f y = ∑ i, hG I (w i) (y - proj e f y) • wd i := by
      rw [← sub_eq_zero]
      apply hT0
      intro j
      rw [hG_sub_right, hG_sum_right]
      simp only [hG_smul_right]
      rcases j with a | a | j
      · simp [fam, hze a, hewd]
      · simp [fam, hzf a, hfwd]
      · simp [fam, hwwd]
    have hz' : y - proj e f y ∈ Submodule.span (Ap I p) (Set.range wd) := by
      rw [hzeq]
      refine Submodule.sum_mem _ fun i _ => ?_
      exact Submodule.smul_mem _ (⟨_, hG_LA hp (hwA i) hzA⟩ : Ap I p)
        (Submodule.subset_span ⟨i, rfl⟩)
    have h1 := proj_span e f hp heA hfA hyA (Set.range e ∪ Set.range f ∪ Set.range wd)
      Set.subset_union_left
    have h2 : y - proj e f y ∈
        Submodule.span (Ap I p) (Set.range e ∪ Set.range f ∪ Set.range wd) :=
      Submodule.span_mono Set.subset_union_right hz'
    have := add_mem h1 h2
    simpa using this
  exact ⟨w, wd, fun i => ⟨hwA i, hwdA i⟩,
    fun a i => ⟨(hwo i a).1, (hwo i a).2, hewd a i, hfwd a i⟩, hdual,
    fun y hy => ⟨hyS y hy, hyS' y hy⟩⟩
end PI.ScRefExists.WF
