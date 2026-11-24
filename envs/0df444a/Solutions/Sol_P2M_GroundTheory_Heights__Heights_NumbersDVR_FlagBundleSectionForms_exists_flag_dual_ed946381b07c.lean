-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionForms_exists_flag_dual_ed946381b07c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:00:21.217767+00:00
-- url     : https://prove2.me/submissions/bea18b39-113d-4790-ae4e-89a31794be25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundleForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagBundleSectionFormsTools
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionForms_chartPow_ne_zero_53c4f1e3f5a9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.NumbersDVR.FlagBundleSectionForms
variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω]
  {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {N : ℕ} {E : Type} [AddCommGroup E] [Module Ω E]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.FlagBundleSectionForms
theorem _root_.solution (y : (Σ k, ι k) → Ω) (B : ChartBundle F (segreVec y) N E)
    (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ) (hfl : IsFlagFrame y B w b)
    (c : ∀ k, ι k) (hc : segreVec y c ≠ 0) (i : Fin N) :
    ∃ ψ : Module.Dual Ω E, (∀ v ∈ B.lat c, ψ v ∈ chartRing F (segreVec y) c) ∧
      (∀ j, j < i → ψ (w j) = 0) ∧ ψ (w i) = (chartPow y c (b i))⁻¹ := by
  have hY : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (Finset.prod_ne_zero_iff.1 hc) k (Finset.mem_univ _)
  have hp : ∀ j, chartPow y c (b j) ≠ 0 := fun j => chartPow_ne_zero hY _
  have hgr : ∀ (j : Fin N) (s : Ω), (∃ v ∈ B.lat c, (∀ m, j < m → w.repr v m = 0) ∧ w.repr v j = s) ↔
      ∃ r ∈ chartRing F (segreVec y) c, s = r * chartPow y c (b j) := fun j s => by
    have h := hfl.graded c hc j
    rw [Set.ext_iff] at h
    exact h s
  have he : ∀ j : Fin N, ∃ v ∈ B.lat c, (∀ m, j < m → w.repr v m = 0) ∧
      w.repr v j = chartPow y c (b j) := fun j =>
    (hgr j _).2 ⟨1, one_mem _, (one_mul _).symm⟩
  choose e heL heT heD using he

  have hx : ∀ j : Fin N, e j - chartPow y c (b j) • w j ∈
      Submodule.span Ω (w '' {m | (m : ℕ) < j}) := by
    intro j
    rw [w.mem_span_image]
    intro m hm
    simp only [Finset.mem_coe, Finsupp.mem_support_iff] at hm
    simp only [Set.mem_setOf_eq]
    by_contra hjm
    push_neg at hjm
    apply hm
    rcases hjm.lt_or_eq with h | h
    · have hne : j ≠ m := fun h' => (ne_of_lt h) (congrArg Fin.val h')
      simp [heT j m h, Finsupp.single_apply, hne]
    · have : m = j := Fin.ext h.symm
      subst this
      simp [heD]
  have hspan : ∀ m ≤ N, Submodule.span Ω (e '' {j | (j : ℕ) < m}) =
      Submodule.span Ω (w '' {j | (j : ℕ) < m}) := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have hS : {j : Fin N | (j : ℕ) < m + 1} = insert (⟨m, hm⟩ : Fin N) {j : Fin N | (j : ℕ) < m} := by
        ext j
        simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Fin.ext_iff]
        omega
      rw [hS, Set.image_insert_eq, Set.image_insert_eq, Submodule.span_insert, Submodule.span_insert,
        ih (by omega)]
      have hxm := hx ⟨m, hm⟩
      apply le_antisymm
      · refine sup_le ?_ le_sup_right
        rw [Submodule.span_singleton_le_iff_mem]
        have := Submodule.add_mem_sup
          (Submodule.smul_mem _ (chartPow y c (b ⟨m, hm⟩)) (Submodule.mem_span_singleton_self (w ⟨m, hm⟩)))
          hxm
        simpa using this
      · refine sup_le ?_ le_sup_right
        rw [Submodule.span_singleton_le_iff_mem]
        have := Submodule.smul_mem _ (chartPow y c (b ⟨m, hm⟩))⁻¹ (Submodule.sub_mem_sup
          (Submodule.mem_span_singleton_self (e ⟨m, hm⟩)) hxm)
        simpa [smul_smul, inv_mul_cancel₀ (hp _)] using this
  have htop : ⊤ ≤ Submodule.span Ω (Set.range e) := by
    have h := hspan N le_rfl
    have hu : {j : Fin N | (j : ℕ) < N} = Set.univ := Set.eq_univ_of_forall fun j => j.isLt
    rw [hu, Set.image_univ, Set.image_univ, w.span_eq] at h
    rw [h]
  have hli : LinearIndependent Ω e :=
    linearIndependent_of_top_le_span_of_card_eq_finrank htop (by rw [Module.finrank_eq_card_basis w])
  let eb := Module.Basis.mk hli htop
  have heb : ⇑eb = e := funext (Module.Basis.mk_apply hli htop)
  have hvan : ∀ x ∈ Submodule.span Ω (w '' {j : Fin N | (j : ℕ) < i}), eb.repr x i = 0 := by
    intro x hx'
    rw [← hspan i i.isLt.le, ← heb, eb.mem_span_image] at hx'
    by_contra h
    exact lt_irrefl (i : ℕ) (hx' (Finsupp.mem_support_iff.2 h))
  have hself : ∀ j m, eb.repr (e j) m = Finsupp.single j 1 m := fun j m => by
    rw [← heb, eb.repr_self]
  have hint : ∀ m ≤ N, ∀ v ∈ B.lat c, (∀ j : Fin N, m ≤ (j : ℕ) → w.repr v j = 0) →
      ∀ j, eb.repr v j ∈ chartRing F (segreVec y) c := by
    intro m
    induction m with
    | zero =>
      intro _ v _ hv j
      have : v = 0 := w.repr.injective (by ext j; simp [hv j (Nat.zero_le _)])
      simp [this]
    | succ m ih =>
      intro hm v hvL hv j
      obtain ⟨r, hr, hrv⟩ := (hgr ⟨m, hm⟩ (w.repr v ⟨m, hm⟩)).1 ⟨v, hvL, fun j hj => hv j hj, rfl⟩
      have hv' : v - r • e ⟨m, hm⟩ ∈ B.lat c := sub_mem hvL (B.stable c r hr _ (heL _))
      have h' := ih (by omega) _ hv' (by
        intro j hj
        rcases hj.lt_or_eq with h | h
        · simp [hv j h, heT ⟨m, hm⟩ j h]
        · have : j = ⟨m, hm⟩ := Fin.ext h.symm
          subst this
          simp [heD, hrv])
      have hsplit : eb.repr v j = eb.repr (v - r • e ⟨m, hm⟩) j + r * eb.repr (e ⟨m, hm⟩) j := by
        rw [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul, sub_add_cancel]
      rw [hsplit, hself]
      refine add_mem (h' j) (mul_mem hr ?_)
      rw [Finsupp.single_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
  refine ⟨eb.coord i, fun v hv => ?_, fun j hj => ?_, ?_⟩
  · exact hint N le_rfl v hv (fun j hj => absurd j.isLt (by omega)) i
  · exact hvan _ (Submodule.subset_span ⟨j, hj, rfl⟩)
  · have hw : w i = (chartPow y c (b i))⁻¹ • (e i - (e i - chartPow y c (b i) • w i)) := by
      rw [sub_sub_cancel, smul_smul, inv_mul_cancel₀ (hp i), one_smul]
    rw [Module.Basis.coord_apply, hw, map_smul, map_sub, Finsupp.smul_apply, Finsupp.sub_apply,
      hself, hvan _ (hx i)]
    simp
end GroundTheory.Heights₂.Heights.NumbersDVR.FlagBundleSectionForms
